use crate::{
	blob::{Devicetree, Error, Item, Node, Property, Result},
	util, DeserializeNode, NodeContext,
};
use core::{
	cmp::Ordering,
	hash::{Hash, Hasher},
	marker::PhantomData,
	mem::size_of,
};

use fallible_iterator::FallibleIterator;

pub(super) const TOKEN_SIZE: u32 = 4;

/// A parsed token from the [`Devicetree`] blob's struct block.
///
/// Does not directly correspond to a 4-byte token from the blob.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum Token<'dtb> {
	BeginNode(Node<'dtb>),
	EndNode,
	Property(Property<'dtb>),
}

impl<'dtb> Token<'dtb> {
	/// Returns an item if this is a `BeginNode` or `Property` token.
	pub fn into_item(self) -> Option<Item<'dtb>> {
		match self {
			Self::BeginNode(node) => Some(Item::Child(node)),
			Self::EndNode => None,
			Self::Property(prop) => Some(Item::Property(prop)),
		}
	}
}

/// A position inside the [`Devicetree`] blob's struct block.
///
/// Can be obtained from [`Node::content_cursor`] and advanced using
/// [`Devicetree::next_token`].
///
/// Do not compare cursors from different devicetrees.
///
/// [`NodeChildren`]: super::NodeChildren
#[derive(Clone, Copy, Debug, Eq)]
pub struct Cursor {
	pub(super) depth: u32,
	pub(super) offset: u32,
}

impl PartialOrd for Cursor {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(Ord::cmp(self, other))
	}
}

impl Ord for Cursor {
	fn cmp(&self, other: &Self) -> Ordering {
		let res = Ord::cmp(&self.offset, &other.offset);
		if res == Ordering::Equal {
			debug_assert_eq!(self.depth, other.depth);
		}
		res
	}
}

impl PartialEq for Cursor {
	fn eq(&self, other: &Self) -> bool {
		Ord::cmp(self, other) == Ordering::Equal
	}
}

impl Cursor {
	fn increase_offset(&mut self, add: usize, blob: &[u8]) -> Result<()> {
		// basically u32::div_ceil(offset + add, 4) * 4
		let offset = u32::checked_add(self.offset, add as u32)
			.and_then(|offset| u32::checked_add(offset, TOKEN_SIZE - 1))
			.ok_or(Error::UnexpectedEnd)?
			& TOKEN_SIZE.wrapping_neg();

		blob.get(offset as usize..).ok_or(Error::UnexpectedEnd)?;
		self.offset = offset;
		Ok(())
	}
}

/// A range of nodes, represented by cursors to them.
///
/// Do not use compare cursor ranges from different devicetrees.
/// Only `extend` a range with nodes with the same valid node name from the same
/// devicetree. (Cannot be used with `#[dt_children(rest)]`.)
/// Empty ranges do not belong to any node name/devicetree.
///
/// Can be used with [`Devicetree::nodes_in_range`] or
/// [`Devicetree::deserialize_in_range`] or by advancing cursors manually.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct CursorRange<'dtb>(pub(super) Option<CursorRangeInner<'dtb>>);

#[derive(Clone, Copy, Debug, Eq)]
pub(super) struct CursorRangeInner<'dtb> {
	depth: u32,
	first_offset: u32,
	last_offset: u32,
	filter_name: &'dtb str,
}

impl PartialEq for CursorRangeInner<'_> {
	fn eq(&self, other: &Self) -> bool {
		let ret = self.first_offset == other.first_offset && self.last_offset == other.last_offset;
		if ret {
			debug_assert_eq!(self.depth, other.depth);
			debug_assert_eq!(self.filter_name, other.filter_name);
		}
		ret
	}
}

impl Hash for CursorRangeInner<'_> {
	fn hash<H: Hasher>(&self, state: &mut H) {
		self.first_offset.hash(state);
		self.last_offset.hash(state);
	}
}

impl<'dtb> CursorRange<'dtb> {
	/// Default empty range.
	pub const EMPTY: Self = Self(None);

	/// Creates a new range spanning a single node.
	pub fn new_single(node: Node<'dtb>) -> Result<Self> {
		let cursor = node.start_cursor();
		Ok(Self(Some(CursorRangeInner {
			depth: cursor.depth,
			first_offset: cursor.offset,
			last_offset: cursor.offset,
			filter_name: node.split_name()?.0,
		})))
	}

	/// Determines if this range spans only a single node.
	pub fn is_single(&self) -> bool {
		self.0.map_or(false, |i| i.first_offset == i.last_offset)
	}

	/// Cursor pointing to the first node's [`Token`].
	pub fn first(&self) -> Option<Cursor> {
		let inner = self.0?;
		Some(Cursor {
			depth: inner.depth,
			offset: inner.first_offset,
		})
	}

	/// Cursor pointing to the last node's [`Token`].
	pub fn last(&self) -> Option<Cursor> {
		let inner = self.0?;
		Some(Cursor {
			depth: inner.depth,
			offset: inner.last_offset,
		})
	}
}

impl<'dtb> Extend<Node<'dtb>> for CursorRange<'dtb> {
	fn extend<T: IntoIterator<Item = Node<'dtb>>>(&mut self, iter: T) {
		for node in iter {
			let Some(ref mut inner) = self.0 else {
				*self = Self::new_single(node).unwrap();
				continue;
			};
			let cursor = node.start_cursor();
			debug_assert_eq!(cursor.depth, inner.depth);
			inner.first_offset = Ord::min(inner.first_offset, cursor.offset);
			inner.last_offset = Ord::max(inner.last_offset, cursor.offset);
		}
	}
}

impl<'dtb> FromIterator<Node<'dtb>> for CursorRange<'dtb> {
	fn from_iter<T: IntoIterator<Item = Node<'dtb>>>(iter: T) -> Self {
		let mut this = Self::EMPTY;
		this.extend(iter);
		this
	}
}

#[repr(u32)]
enum RawToken {
	BeginNode = 1_u32.to_be(),
	EndNode = 2_u32.to_be(),
	Prop = 3_u32.to_be(),
	Nop = 4_u32.to_be(),
	End = 9_u32.to_be(),
}

impl Devicetree {
	/// The devicetree's root node.
	pub fn root_node(&self) -> Result<Node<'_>> {
		self.struct_blob()?;

		let mut cursor = Cursor {
			depth: 0,
			offset: u32::from_be(self.header().off_dt_struct),
		};
		match self.next_token(&mut cursor)? {
			Some(Token::BeginNode(node)) if node.name.is_empty() => Ok(node),
			_ => Err(Error::InvalidRootNode),
		}
	}

	/// Returns the token pointed to by the cursor and advance the cursor.
	pub fn next_token(&self, cursor: &mut Cursor) -> Result<Option<Token<'_>>> {
		const PROP_HEADER_SIZE: usize = size_of::<PropHeader>();

		#[repr(C)]
		struct PropHeader {
			len: u32,
			nameoff: u32,
		}

		let blob = self.blob_u8();
		loop {
			let token = self.next_raw(cursor)?.ok_or(Error::UnexpectedEnd)?;
			let offset = cursor.offset as usize;

			let token = match token {
				RawToken::BeginNode => {
					let name = &blob[cursor.offset as usize..];
					let name = util::get_c_str(name)?;

					cursor.increase_offset(name.len() + 1, blob)?;
					cursor.depth += 1;
					Token::BeginNode(Node {
						dt: self,
						name,
						contents: *cursor,
					})
				}
				RawToken::EndNode => {
					let depth =
						u32::checked_sub(cursor.depth, 1).ok_or(Error::UnexpectedEndNodeToken)?;
					cursor.depth = depth;

					Token::EndNode
				}
				RawToken::Prop => {
					let header = util::slice_get_with_len(blob, offset, PROP_HEADER_SIZE)
						.ok_or(Error::InvalidPropertyHeader)?;

					let header = unsafe { &*(header as *const _ as *const PropHeader) };
					let name_blob = self
						.strings_blob()?
						.get(u32::from_be(header.nameoff) as usize..)
						.ok_or(Error::InvalidString)?;

					cursor.offset += PROP_HEADER_SIZE as u32;
					let offset = cursor.offset as usize;

					let len = u32::from_be(header.len) as usize;
					let value = util::slice_get_with_len(blob, offset, len)
						.ok_or(Error::InvalidPropertyHeader)?;

					cursor.increase_offset(len, blob)?;

					Token::Property(Property { name_blob, value })
				}
				RawToken::Nop => continue,
				RawToken::End => {
					if cursor.depth == 0 {
						return Ok(None);
					} else {
						return Err(Error::UnexpectedEndToken);
					}
				}
			};
			return Ok(Some(token));
		}
	}

	fn next_raw(&self, cursor: &mut Cursor) -> Result<Option<RawToken>> {
		const BEGIN_NODE: u32 = RawToken::BeginNode as u32;
		const END_NODE: u32 = RawToken::EndNode as u32;
		const PROP: u32 = RawToken::Prop as u32;
		const NOP: u32 = RawToken::Nop as u32;
		const END: u32 = RawToken::End as u32;

		let offset = cursor.offset as usize;
		let Some(token) = util::slice_get_with_len(self.blob_u8(), offset, TOKEN_SIZE as usize)
		else {
			return Ok(None)
		};
		let token = unsafe { *(token as *const _ as *const u32) };

		cursor.offset += TOKEN_SIZE;
		let token = match token {
			BEGIN_NODE => RawToken::BeginNode,
			END_NODE => RawToken::EndNode,
			PROP => RawToken::Prop,
			NOP => RawToken::Nop,
			END => RawToken::End,
			_ => return Err(Error::UnknownToken),
		};
		Ok(Some(token))
	}

	/// Iterator over the [`Node`]s in the range.
	pub fn nodes_in_range<'dtb>(&'dtb self, range: CursorRange<'dtb>) -> NodesInRange<'dtb> {
		NodesInRange { dt: self, range }
	}

	/// Iterator over the [`Node`]s in the range, with each node being parsed
	/// into type `T`.
	pub fn deserialize_in_range<'a, 'dtb, T: DeserializeNode<'dtb>>(
		&'dtb self,
		range: CursorRange<'dtb>,
		cx: NodeContext<'a>,
	) -> DeserializeInRange<'a, 'dtb, T> {
		DeserializeInRange {
			nodes: self.nodes_in_range(range),
			cx,
			_marker: PhantomData,
		}
	}
}

/// Iterator over the [`Node`]s in a range.
/// Obtained from [`Devicetree::nodes_in_range`].
#[derive(Clone, Debug)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct NodesInRange<'dtb> {
	dt: &'dtb Devicetree,
	range: CursorRange<'dtb>,
}

impl<'dtb> NodesInRange<'dtb> {
	/// Advances the iterator and passes the next node to the given closure.
	///
	/// The closure's second return value is a cursor pointing to the next token
	/// after the node.
	pub fn walk_next<T>(
		&mut self,
		mut f: impl FnMut(Node<'dtb>) -> crate::Result<(T, Cursor)>,
	) -> crate::Result<Option<T>> {
		let Some(inner) = self.range.0 else { return Ok(None) };
		let mut cursor = Cursor {
			depth: inner.depth,
			offset: inner.first_offset,
		};
		loop {
			if cursor.offset == inner.last_offset {
				self.range = CursorRange::EMPTY;
			}
			let node = loop {
				match self.dt.next_token(&mut cursor)? {
					Some(Token::BeginNode(node)) => break node,
					None | Some(Token::EndNode) => return Ok(None),
					Some(Token::Property(_)) => (),
				}
			};

			if node.split_name()?.0 == inner.filter_name {
				let val;
				(val, cursor) = f(node)?;
				if let CursorRange(Some(ref mut inner)) = self.range {
					inner.first_offset = cursor.offset;
				}
				return Ok(Some(val));
			} else {
				cursor = node.end_cursor()?;
				if self.range == CursorRange::EMPTY {
					return Ok(None);
				}
			}
		}
	}

	/// The range of nodes that has not been visited yet.
	pub fn remaining_range(&self) -> CursorRange<'dtb> {
		self.range
	}
}

/// Iterator over the [`Node`]s in a range, with each node being parsed into
/// type `T`.
#[derive(Clone, Debug)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct DeserializeInRange<'a, 'dtb, T> {
	pub nodes: NodesInRange<'dtb>,
	pub cx: NodeContext<'a>,
	_marker: PhantomData<fn() -> T>,
}

impl<'a, 'dtb, T: DeserializeNode<'dtb>> FallibleIterator for DeserializeInRange<'a, 'dtb, T> {
	type Item = T;
	type Error = crate::Error;

	fn next(&mut self) -> core::result::Result<Option<Self::Item>, Self::Error> {
		self.nodes.walk_next(|n| T::deserialize(&n, self.cx))
	}
}
