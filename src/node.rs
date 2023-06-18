use core::hash::{Hash, Hasher};

use fallible_iterator::FallibleIterator;

use crate::{
	blob::{self, Cursor, Node, NodeChildren},
	NodeContext, PushDeserializedNode, Result,
};

/// A range over all the child nodes with the same name, represented by cursors
/// to them.
///
/// Do not compare cursor ranges from different devicetrees.
/// Empty ranges do not belong to any node name/devicetree.
///
/// Can be used with [`Devicetree::nodes_in_range`] or
/// [`Devicetree::deserialize_in_range`] or by advancing cursors manually.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct NamedRange<'dtb>(pub(super) Option<NamedRangeInner<'dtb>>);

#[derive(Clone, Copy, Debug, Eq)]
pub(super) struct NamedRangeInner<'dtb> {
	depth: u32,
	first_offset: u32,
	len: u32,
	filter_name: &'dtb str,
}

impl PartialEq for NamedRangeInner<'_> {
	fn eq(&self, other: &Self) -> bool {
		let ret = self.first_offset == other.first_offset && self.len == other.len;
		if ret {
			debug_assert_eq!(self.depth, other.depth);
			debug_assert_eq!(self.filter_name, other.filter_name);
		}
		ret
	}
}

impl Hash for NamedRangeInner<'_> {
	fn hash<H: Hasher>(&self, state: &mut H) {
		self.first_offset.hash(state);
		self.len.hash(state);
	}
}

impl<'dtb> NamedRange<'dtb> {
	/// Default empty range.
	pub const EMPTY: Self = Self(None);

	/// Creates a new range spanning a single node.
	pub fn new_single(node: Node<'dtb>) -> Result<Self> {
		let cursor = node.start_cursor();
		Ok(Self(Some(NamedRangeInner {
			depth: cursor.depth,
			first_offset: cursor.offset,
			len: 1,
			filter_name: node.split_name()?.0,
		})))
	}

	/// Cursor pointing to the first node's [`Token`](crate::blob::Token).
	pub fn first(self) -> Option<Cursor> {
		let inner = self.0?;
		Some(Cursor {
			depth: inner.depth,
			offset: inner.first_offset,
		})
	}

	pub fn len(self) -> usize {
		self.0.map_or(0, |i| i.len) as usize
	}

	pub fn is_empty(self) -> bool {
		self.0.is_none()
	}
}

impl<'dtb> PushDeserializedNode<'dtb> for NamedRange<'dtb> {
	type Node = Node<'dtb>;

	fn push_node(&mut self, node: Self::Node, _cx: NodeContext<'_>) {
		let Some(ref mut inner) = self.0 else {
			*self = Self::new_single(node).unwrap();
			return;
		};
		let cursor = node.start_cursor();
		debug_assert_eq!(cursor.depth, inner.depth);
		inner.len += 1;
	}
}

/// Iterator over the [`Node`]s in a named range.
/// Obtained from [`Devicetree::nodes_in_range`].
#[derive(Clone, Debug)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct NamedRangeIter<'dtb> {
	children: NodeChildren<'dtb>,
	filter_name: &'dtb str,
}

impl<'dtb> NamedRangeIter<'dtb> {}

impl<'dtb> FallibleIterator for NamedRangeIter<'dtb> {
	type Item = Node<'dtb>;
	type Error = blob::Error;

	fn next(&mut self) -> Result<Option<Self::Item>, Self::Error> {
		self.children
			.find(|c| c.split_name().map(|(n, _)| n == self.filter_name))
	}
}
