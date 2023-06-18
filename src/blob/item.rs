use core::fmt::{self, Debug, Display, Formatter, Write};

use fallible_iterator::FallibleIterator;

use crate::{
	blob::{self, Cursor, Devicetree, Token, TOKEN_SIZE},
	node, util, DeserializeProperty, NodeContext, Result,
};

/// A property contained in a [`Node`].
#[derive(Clone, Copy)]
pub struct Property<'dtb> {
	pub(super) name_blob: &'dtb [u8],
	pub(super) value: &'dtb [u8],
}

impl<'dtb> Property<'dtb> {
	/// The property's name.
	///
	/// # Errors
	/// Fails if the string is invalid.
	pub fn name(self) -> blob::Result<&'dtb str> {
		util::get_c_str(self.name_blob)
	}

	/// The property's value.
	pub fn value(self) -> &'dtb [u8] {
		debug_assert_eq!(self.value.as_ptr() as usize % 4, 0);
		self.value
	}

	/// Parses the value. Equivalent to `DeserializeProperty` except that the
	/// default [`NodeContext`] is used.
	pub fn contextless_parse<T: DeserializeProperty<'dtb>>(self) -> Result<T> {
		T::deserialize(self, NodeContext::default())
	}
}

impl<'dtb> Debug for Property<'dtb> {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		f.debug_struct("Property")
			.field("name", &self.name())
			.field("value", &self.value)
			.finish()
	}
}

impl<'dtb> Display for Property<'dtb> {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		const HEX_STRING: &[u8] = b"0123456789abcdef";

		struct HexArray<const N: usize>([u8; N]);

		impl<const N: usize> Display for HexArray<N> {
			fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
				let mut buf = [(0, 0); N];
				for (out, n) in core::iter::zip(&mut buf, self.0) {
					out.0 = HEX_STRING[n as usize >> 4];
					out.1 = HEX_STRING[n as usize & 0x0f];
				}
				unsafe {
					let buf = core::slice::from_raw_parts(&buf as *const _ as *const u8, N * 2);
					f.write_str(core::str::from_utf8_unchecked(buf))
				}
			}
		}

		f.write_str(self.name().map_err(|_| fmt::Error)?)?;
		if let [ref rest @ .., last_byte] = *self.value {
			f.write_str(" = ")?;
			let is_strings = last_byte == 0 && {
				// an all-zero value shouldn't be displayed as a bunch of empty strings
				let mut prev_was_printing_char = false;
				rest.iter().all(|&b| {
					match b {
						0 if prev_was_printing_char => prev_was_printing_char = false,
						b' '..=b'~' => prev_was_printing_char = true,
						_ => return false,
					}
					true
				}) && prev_was_printing_char
			};
			if is_strings {
				f.write_char('"')?;
				for &b in rest {
					if b == 0 {
						f.write_str("\", \"")?;
					} else {
						f.write_char(b as char)?;
					};
				}
				f.write_char('"')?;
			} else {
				f.write_char('[')?;
				let len = self.value.len();
				if len % 4 == 0 {
					for bytes in rest.chunks_exact(4) {
						write!(f, "{} ", HexArray(<[u8; 4]>::try_from(bytes).unwrap()))?;
					}
					// last byte is written below
					HexArray(<[u8; 3]>::try_from(&rest[len - 4..]).unwrap()).fmt(f)?;
				} else {
					for &b in rest {
						write!(f, "{} ", HexArray([b]))?;
					}
				}
				write!(f, "{}]", HexArray([last_byte]))?;
			}
		}
		f.write_char(';')
	}
}

/// A node of the tree structure in a [`Devicetree`] blob's struct block.
/// It contains [`Property`]s and child nodes.
#[derive(Clone, Debug)]
pub struct Node<'dtb> {
	pub(crate) dt: &'dtb Devicetree,
	pub(crate) name: &'dtb str,
	pub(crate) contents: Cursor,
}

impl<'dtb> Node<'dtb> {
	/// The devicetree containing this node.
	pub fn devicetree(&self) -> &'dtb Devicetree {
		self.dt
	}

	/// The node's name.
	pub fn name(&self) -> &'dtb str {
		self.name
	}

	/// The name as it would show up in a devicetree source file.
	pub fn source_name(&self) -> &'dtb str {
		if self.name.is_empty() {
			"/"
		} else {
			self.name
		}
	}

	/// Splits the node's name as follows:
	/// ```text
	/// <node-name> [@ <unit-address>]
	/// ```
	///
	/// # Errors
	///
	/// There cannot be more than one `@`.
	pub fn split_name(&self) -> Result<(&'dtb str, Option<&'dtb str>)> {
		util::split_node_name(self.name)
	}

	/// Cursor pointing to this node's [`Token`].
	pub fn start_cursor(&self) -> Cursor {
		Cursor {
			depth: self.contents.depth - 1,
			offset: ((self.contents.offset - self.name.len() as u32 - 1)
				& TOKEN_SIZE.wrapping_neg())
				- TOKEN_SIZE,
		}
	}

	/// Cursor pointing to the first [`Token`] inside this node.
	pub fn content_cursor(&self) -> Cursor {
		self.contents
	}

	/// Cursor pointing to the next [`Token`] after this node. Expensive to
	/// determine.
	pub fn end_cursor(&self) -> Result<Cursor> {
		self.items().end_cursor()
	}

	/// Iterator over the [`Item`]s ([`Property`]s and child [`Node`]s)
	/// contained in the node.
	///
	/// Fused (see [`core::iter::FusedIterator`]).
	///
	/// In compliant devicetrees, the properties always come before the child
	/// nodes.
	pub fn items(&self) -> node::Items<'dtb> {
		node::Items::new(self, self.contents)
	}

	/// Iterator over the [`Property`]s contained in the node.
	///
	/// This is currently more efficient than filtering the [`Items`] manually.
	///
	/// [`Items`]: node::Items
	pub fn properties(&self) -> node::Properties<'dtb> {
		node::Properties::new(self.dt, self.contents)
	}

	/// An iterator over the child [`Node`]s contained in a node.
	///
	/// This is currently not any more efficient than filtering the [`Items`]
	/// manually.
	///
	/// Fused (see [`core::iter::FusedIterator`]).
	///
	/// [`Items`]: node::Items
	pub fn children(&self) -> node::Children<'dtb> {
		node::Children::new(self, self.contents)
	}

	/// Finds a contained property by name.
	pub fn get_property(&self, name: &str) -> Result<Option<Property<'dtb>>> {
		node::Properties::new(self.dt, self.contents).find_by_name(|n| n == name)
	}

	/// Finds a child node by (loosely-matching) name.
	/// Try using [`Self::get_child_strict`] instead.
	///
	/// The input string needs not match the node name exactly; the unit address
	/// (the part starting with an `@`) can be left out. If it is, the node name
	/// has to be unambiguous.
	pub fn get_child(&self, name: &str) -> Result<Option<Node<'dtb>>> {
		let mut iter = node::Children::new(self, self.contents);
		if util::split_node_name(name)?.1.is_some() {
			iter.find(|n| Ok(n.name() == name))
		} else if let Some((candidate, (_, candidate_addr))) = (&mut iter)
			.map(|n| n.split_name().map(|split| (n, split)))
			.find(|&(_, (n, _))| Ok(n == name))?
		{
			if candidate_addr.is_some() {
				iter.find_by_name(|n| n == name)
					.map(|n| n.or(Some(candidate)))
			} else {
				Ok(Some(candidate))
			}
		} else {
			Ok(None)
		}
	}

	/// Finds a child node by name.
	///
	/// The input string has to match the node name exactly; the unit address
	/// (the part starting with an `@`) cannot be left out.
	pub fn get_child_strict(&self, name: &str) -> Result<Option<Node<'dtb>>> {
		node::Children::new(self, self.contents).find_by_name(|n| n == name)
	}

	/// Finds child nodes by (loosely-matching) name.
	///
	/// The input string should not contain a unit address.
	pub fn get_children<'n>(
		&self,
		name: &'n str,
	) -> fallible_iterator::Filter<node::Children<'dtb>, impl FnMut(&Node<'dtb>) -> Result<bool> + 'n>
	{
		node::Children::new(self, self.contents)
			.filter(move |n| n.split_name().map(|(n, _)| n == name))
	}
}

impl<'dtb> Display for Node<'dtb> {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		fn write_indent(f: &mut Formatter<'_>, depth: u32) -> fmt::Result {
			for _ in 0..depth {
				f.write_char('\t')?;
			}
			Ok(())
		}

		let mut cursor = self.start_cursor();
		let base_depth = cursor.depth;
		let mut first_line = true;
		let mut just_began_node = false;
		let mut prev_depth = base_depth;
		loop {
			let token = self
				.dt
				.next_token(&mut cursor)
				.map_err(|_| fmt::Error)?
				.unwrap();
			let depth = cursor.depth - base_depth;
			if first_line {
				first_line = false;
			} else {
				f.write_char('\n')?;
			}

			match token {
				Token::BeginNode(node) => {
					write_indent(f, prev_depth)?;
					let name = if node.name.is_empty() { "/" } else { node.name };
					write!(f, "{name} {{")?;
					just_began_node = true;
				}
				Token::EndNode => {
					if !just_began_node {
						write_indent(f, depth)?;
					}
					f.write_str("};")?;
					if depth == 0 {
						return Ok(());
					}
					just_began_node = false;
				}
				Token::Property(prop) => {
					write_indent(f, prev_depth)?;
					Display::fmt(&prop, f)?;
					just_began_node = false;
				}
			}
			prev_depth = depth;
		}
	}
}

/// Either a property or a node.
#[derive(Clone, Debug)]
pub enum Item<'dtb> {
	Property(Property<'dtb>),
	Child(Node<'dtb>),
}

impl<'dtb> Item<'dtb> {
	/// The property's name.
	///
	/// # Errors
	/// Fails if this is a property and the string is invalid.
	pub fn name(self) -> blob::Result<&'dtb str> {
		match self {
			Self::Property(prop) => prop.name(),
			Self::Child(node) => Ok(node.name()),
		}
	}
}
