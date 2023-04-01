use crate::{
	blob::{Cursor, Devicetree, Error, Result, Token},
	util, DeserializeProperty, NodeContext,
};
use core::{
	fmt::{self, Debug, Display, Formatter, Write},
	slice,
};

use fallible_iterator::FallibleIterator;

/// A property contained in a [`Node`].
#[derive(Clone, Copy)]
pub struct Property<'dtb> {
	pub(super) name_blob: &'dtb [u8],
	pub(super) value: &'dtb [u8],
}

impl<'dtb> Property<'dtb> {
	pub fn name(self) -> Result<&'dtb str> {
		util::get_c_str(self.name_blob)
	}

	pub fn value(self) -> &'dtb [u8] {
		debug_assert_eq!(self.value.as_ptr() as usize % 4, 0);
		self.value
	}

	pub(crate) fn value_u32(self) -> Option<&'dtb [u32]> {
		let value = self.value();
		(value.len() % 4 == 0).then(|| unsafe {
			slice::from_raw_parts(value as *const _ as *const u32, value.len() / 4)
		})
	}

	pub fn contextless_parse<T: DeserializeProperty<'dtb>>(self) -> crate::Result<T> {
		T::deserialize(self, &NodeContext::default())
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
		let _ = f.write_str(self.name().map_err(|_| fmt::Error)?);
		if let [ref rest @ .., last_byte] = *self.value {
			let _ = f.write_str(" = ");
			let is_strings = last_byte == 0 && {
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
				let _ = f.write_char('"');
				for &b in rest {
					if b == 0 {
						let _ = f.write_str("\", \"");
					} else {
						let _ = f.write_char(b as char);
					};
				}
				let _ = f.write_char('"');
			} else {
				let _ = f.write_char('[');
				let len = self.value.len();
				if len % 4 == 0 {
					for b in rest.chunks_exact(4) {
						let (a, b, c, d) = (b[0], b[1], b[2], b[3]);
						let _ = write!(f, "{a:02x}{b:02x}{c:02x}{d:02x} ");
					}
					let (a, b, c) = (rest[len - 4], rest[len - 3], rest[len - 2]);
					// last byte is written below
					let _ = write!(f, "{a:02x}{b:02x}{c:02x}");
				} else {
					for &b in rest {
						let _ = write!(f, "{b:02x} ");
					}
				}
				let _ = write!(f, "{last_byte:02x}]");
			}
		}
		f.write_char(';')
	}
}

/// A node of the tree structure in a [`Devicetree`] blob's struct block. It
/// contains [`Property`]s and child nodes.
#[derive(Clone, Debug)]
pub struct Node<'dtb> {
	pub(super) dt: &'dtb Devicetree,
	pub(super) name: &'dtb str,
	pub(super) contents: Cursor,
}

impl<'dtb> Node<'dtb> {
	pub fn devicetree(&self) -> &'dtb Devicetree {
		self.dt
	}

	pub fn name(&self) -> &'dtb str {
		self.name
	}

	pub fn display_name(&self) -> &'dtb str {
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

	pub fn start_cursor(&self) -> Cursor {
		Cursor {
			depth: self.contents.depth - 1,
			offset: (self.contents.offset - self.name.len() as u32 - 1) / 4 * 4
				- super::token::TOKEN_SIZE,
		}
	}

	pub fn content_cursor(&self) -> Cursor {
		self.contents
	}

	pub fn end_cursor(&self) -> Result<Cursor> {
		self.items().end_cursor()
	}

	pub fn items(&self) -> NodeItems<'dtb> {
		NodeItems::new(self, self.contents)
	}

	pub fn properties(&self) -> NodeProperties<'dtb> {
		NodeProperties::new(self.dt, self.contents)
	}

	pub fn children(&self) -> NodeChildren<'dtb> {
		NodeChildren(NodeItems::new(self, self.contents))
	}

	pub fn get_property(&self, name: &str) -> Result<Option<Property<'dtb>>> {
		NodeProperties::new(self.dt, self.contents).find_by_name(|n| n == name)
	}

	pub fn get_child(&self, name: &str) -> Result<Option<Node<'dtb>>> {
		let mut iter = NodeChildren(NodeItems::new(self, self.contents));
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

	pub fn get_child_strict(&self, name: &str) -> Result<Option<Node<'dtb>>> {
		NodeChildren(NodeItems::new(self, self.contents)).find_by_name(|n| n == name)
	}

	pub fn get_children<'n>(
		&self,
		name: &'n str,
	) -> fallible_iterator::Filter<NodeChildren<'dtb>, impl FnMut(&Node<'dtb>) -> Result<bool> + 'n>
	{
		NodeChildren(NodeItems::new(self, self.contents))
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
				Token::BeginNode { mut name } => {
					write_indent(f, prev_depth)?;
					if name.is_empty() {
						name = "/";
					}
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
	pub fn name(self) -> Result<&'dtb str> {
		match self {
			Self::Property(prop) => prop.name(),
			Self::Child(node) => Ok(node.name()),
		}
	}
}

/// An iterator over the [`Item`]s ([`Property`]s and child [`Node`]s)
/// contained in a node.
///
/// Fused (see [`core::iter::FusedIterator`]).
///
/// In compliant devicetrees, the properties always come before the child nodes.
#[derive(Clone, Debug)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct NodeItems<'dtb> {
	dt: &'dtb Devicetree,
	at_depth: u32,
	cursor: Cursor,
}

impl<'dtb> NodeItems<'dtb> {
	/// The cursor has to be inside the node.
	pub fn new(node: &Node<'dtb>, cursor: Cursor) -> Self {
		debug_assert!(cursor >= node.contents && cursor.depth >= node.contents.depth);
		Self {
			dt: node.dt,
			at_depth: node.contents.depth,
			cursor,
		}
	}

	pub fn cursor(&self) -> Cursor {
		self.cursor
	}

	pub fn end_cursor(mut self) -> Result<Cursor> {
		while self.next()?.is_some() {}
		Ok(self.cursor)
	}
}

impl<'dtb> FallibleIterator for NodeItems<'dtb> {
	type Item = Item<'dtb>;
	type Error = Error;

	fn next(&mut self) -> Result<Option<Self::Item>, Self::Error> {
		while self.cursor.depth >= self.at_depth {
			let token_depth = self.cursor.depth;
			let Some(token) = self.dt.next_token(&mut self.cursor)? else { return Ok(None) };
			if token_depth == self.at_depth {
				return Ok(token.to_item(self.dt, self.cursor));
			}
		}
		Ok(None)
	}
}

/// An iterator over the [`Property`]s contained in a node.
///
/// This is currently more efficient than filtering the [`NodeItems`] manually.
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct NodeProperties<'dtb> {
	dt: &'dtb Devicetree,
	cursor: Cursor,
}

impl<'dtb> NodeProperties<'dtb> {
	pub fn new(dt: &'dtb Devicetree, cursor: Cursor) -> Self {
		Self { dt, cursor }
	}

	pub fn cursor(&self) -> Cursor {
		self.cursor
	}

	pub fn find_by_name(
		&mut self,
		mut predicate: impl FnMut(&str) -> bool,
	) -> Result<Option<Property<'dtb>>> {
		self.find(|p| p.name().map(&mut predicate))
	}
}

impl<'dtb> FallibleIterator for NodeProperties<'dtb> {
	type Item = Property<'dtb>;
	type Error = Error;

	fn next(&mut self) -> Result<Option<Self::Item>, Self::Error> {
		if let Some(Token::Property(prop)) = self.dt.next_token(&mut self.cursor)? {
			Ok(Some(prop))
		} else {
			Ok(None)
		}
	}
}

/// An iterator over the child [`Node`]s contained in a node.
///
/// This is currently not any more efficient than filtering the [`NodeItems`]
/// manually.
///
/// Fused (see [`core::iter::FusedIterator`]).
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct NodeChildren<'dtb>(NodeItems<'dtb>);

impl<'dtb> NodeChildren<'dtb> {
	pub fn new(node: &Node<'dtb>, cursor: Cursor) -> Self {
		Self(NodeItems::new(node, cursor))
	}

	pub fn cursor(&self) -> Cursor {
		self.0.cursor
	}

	pub fn find_by_name(
		&mut self,
		mut predicate: impl FnMut(&str) -> bool,
	) -> Result<Option<Node<'dtb>>> {
		self.find(|n| Ok(predicate(n.name())))
	}

	pub fn find_by_split_name(
		&mut self,
		mut predicate: impl FnMut(&str, Option<&str>) -> bool,
	) -> Result<Option<Node<'dtb>>> {
		self.find(|n| n.split_name().map(|(n, a)| predicate(n, a)))
	}

	pub fn filter_by_split_name(
		&mut self,
		mut predicate: impl FnMut(&str, Option<&str>) -> bool,
	) -> fallible_iterator::Filter<&mut Self, impl FnMut(&Node<'dtb>) -> Result<bool>> {
		self.filter(move |n| n.split_name().map(|(n, a)| predicate(n, a)))
	}
}

impl<'dtb> FallibleIterator for NodeChildren<'dtb> {
	type Item = Node<'dtb>;
	type Error = Error;

	fn next(&mut self) -> Result<Option<Self::Item>, Self::Error> {
		self.0.find_map(|i| match i {
			Item::Property(_) => Ok(None),
			Item::Child(node) => Ok(Some(node)),
		})
	}
}
