//! Efficient `#![no_std]` parser for devicetree blobs compliant (hopefully)
//! with version 0.4 of [the specification][spec].
//!
//! [spec]: https://www.devicetree.org/specifications

#![no_std]
#![deny(unsafe_op_in_unsafe_fn)]

#[cfg(feature = "alloc")]
extern crate alloc as std_alloc;
#[cfg(feature = "std")]
extern crate std;

#[cfg(feature = "alloc")]
pub mod alloc;
pub mod blob;
#[cfg(feature = "model")]
pub mod model;
pub mod prop_value;

use core::{
	any::Any,
	fmt::{self, Debug, Display, Formatter},
	iter, slice,
};

use ascii::AsciiStr;
#[cfg(feature = "derive")]
pub use deforest_derive::*;
pub use fallible_iterator;
use fallible_iterator::FallibleIterator;
use zerocopy::{FromBytes, IntoBytes};

use blob::{Cursor, Item, Node, Property};

/// Any error caused by this crate.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Error {
	/// Not produced by this crate.
	Unknown,
	Blob(BlobError),
	DevicetreeTooLarge,
	IntOverflow,
	InvalidDeviceType,
	InvalidNodeName,
	InvalidPath,
	TooManyCells,
	UnsuitableNode,
	UnsuitableProperty,
}

impl Display for Error {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		use Error::*;

		let description = match self {
			Unknown => "unknown",
			Blob(err) => return Display::fmt(err, f),
			DevicetreeTooLarge => "devicetree too large",
			IntOverflow => "integer overflow",
			InvalidDeviceType => "invalid device_type",
			InvalidNodeName => "invalid node name",
			InvalidPath => "invalid path",
			TooManyCells => "too many cells",
			UnsuitableNode => "unsuitable node",
			UnsuitableProperty => "unsuitable property",
		};
		write!(f, "devicetree error: {description}")
	}
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}

pub type Result<T, E = Error> = core::result::Result<T, E>;

/// Any error related to the blob representation caused by this crate.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum BlobError {
	BlockOutOfBounds,
	IncompatibleVersion,
	InvalidBlockOrder,
	InvalidPropertyHeader,
	InvalidRootNode,
	InvalidString,
	InvalidTotalsize,
	NoMagicSignature,
	UnalignedBlock,
	UnexpectedEnd,
	UnexpectedEndToken,
	UnexpectedEndNodeToken,
	UnknownToken,
}

impl Display for BlobError {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		let description = match *self {
			Self::BlockOutOfBounds => "block out of bounds",
			Self::IncompatibleVersion => "incompatible devicetree version",
			Self::InvalidBlockOrder => "invalid block order",
			Self::InvalidPropertyHeader => "invalid property header",
			Self::InvalidRootNode => "invalid root node",
			Self::InvalidString => "invalid string",
			Self::InvalidTotalsize => "invalid totalsize field",
			Self::NoMagicSignature => "no magic signature",
			Self::UnalignedBlock => "unaligned block",
			Self::UnexpectedEnd => "unexpected end",
			Self::UnexpectedEndToken => "unexpected End token",
			Self::UnexpectedEndNodeToken => "unexpected EndNode token",
			Self::UnknownToken => "unknown token",
		};
		write!(f, "devicetree blob error: {description}")
	}
}

#[cfg(feature = "std")]
impl std::error::Error for BlobError {}

impl From<BlobError> for Error {
	#[inline]
	fn from(err: BlobError) -> Self {
		Self::Blob(err)
	}
}

/// Number of 4-byte cells. This crate has an upper limit of 4 cells, but that
/// is not part of the spec.
pub type Cells = u8;
/// Numerical identifier for a node.
pub type Phandle = u32;

/// Absolute path of an item.
///
/// Either a slice of path components or a string with `/`-separated components.
/// A leading slash is required for a string path, other than that the path can
/// be empty.
pub trait Path {
	/// Iterator over the components of the path.
	type ComponentsIter<'a>: DoubleEndedIterator<Item = &'a str>
	where
		Self: 'a;

	/// An iterator over this path's components.
	fn as_components(&self) -> Result<Self::ComponentsIter<'_>>;
}

impl Path for [&str] {
	type ComponentsIter<'a>
		= iter::Copied<slice::Iter<'a, &'a str>>
	where
		Self: 'a;

	fn as_components(&self) -> Result<Self::ComponentsIter<'_>> {
		Ok(self.iter().copied())
	}
}

impl<const N: usize> Path for [&str; N] {
	type ComponentsIter<'a>
		= iter::Copied<slice::Iter<'a, &'a str>>
	where
		Self: 'a;

	fn as_components(&self) -> Result<Self::ComponentsIter<'_>> {
		Ok(self.iter().copied())
	}
}

impl Path for str {
	type ComponentsIter<'a>
		= core::str::Split<'a, char>
	where
		Self: 'a;

	fn as_components(&self) -> Result<Self::ComponentsIter<'_>> {
		let mut components = self.split('/');
		if self.is_empty() || components.next() != Some("") {
			return Err(Error::InvalidPath);
		}
		if self.len() == 1 {
			// for the root node, the iterator should be empty
			components.next();
		}
		Ok(components)
	}
}

/// An entry from a blob's memory reservation block, obtained from
/// [`MemReserveEntries`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct MemReserveEntry {
	pub address: u64,
	pub size: u64,
}

/// An iterator over the [`MemReserveEntry`] from a [`Devicetree`] blob's memory
/// reservation block.
///
/// [`Devicetree`]: blob::Devicetree
#[derive(Clone)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct MemReserveEntries<'dtb> {
	blob: &'dtb [u64],
}

impl FallibleIterator for MemReserveEntries<'_> {
	type Item = MemReserveEntry;
	type Error = Error;

	fn next(&mut self) -> Result<Option<Self::Item>, Self::Error> {
		let (raw, _) = blob::RawReserveEntry::read_from_prefix(self.blob.as_bytes())
			.map_err(|_| BlobError::UnexpectedEnd)?;
		self.blob = &self.blob[blob::RawReserveEntry::FIELD_COUNT..];

		let entry = (raw.address != 0 || raw.size != 0).then(|| MemReserveEntry {
			address: u64::from_be(raw.address),
			size: u64::from_be(raw.size),
		});
		Ok(entry)
	}
}

impl Debug for MemReserveEntries<'_> {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		let mut iter = self.clone();
		let mut list = f.debug_list();
		loop {
			match iter.next() {
				Ok(None) => return list.finish(),
				Ok(Some(entry)) => {
					list.entry(&entry);
				}
				Err(_) => return Err(fmt::Error),
			}
		}
	}
}

/// Holds information for deserialization.
#[derive(Clone, Copy, Debug)]
#[non_exhaustive]
pub struct NodeContext<'a> {
	pub custom: Option<&'a dyn Any>,
	/// `#address-cells` property of the parent node.
	pub address_cells: Cells,
	/// `#size-cells` property of the parent node.
	pub size_cells: Cells,
}

impl Default for NodeContext<'_> {
	#[inline]
	fn default() -> Self {
		Self {
			custom: None,
			address_cells: prop_value::AddressCells::default().0,
			size_cells: prop_value::SizeCells::default().0,
		}
	}
}

impl NodeContext<'_> {
	/// Helps you deserialize a node by creating the `NodeContext` for the child
	/// nodes for you.
	///
	/// `f_prop` is called with the name of each property and that property.
	///
	/// `f_child` is called with each node, the new `NodeContext` and a mutable
	/// reference to a cursor. The cursor points to that child node, but the
	/// function has to replace it with a cursor which points to next token
	/// after that child.
	pub fn deserialize_node<'dtb>(
		self,
		blob_node: &Node<'dtb>,
		mut f_prop: impl FnMut(&'dtb str, Property<'dtb>) -> Result<()>,
		mut f_child: impl FnMut(Node<'dtb>, Self, &mut Cursor) -> Result<()>,
	) -> Result<(Self, Cursor)> {
		let mut child_cx = Self {
			custom: self.custom,
			..Self::default()
		};

		let mut items = blob_node.items();
		while let Some(item) = items.next()? {
			match item {
				Item::Property(prop) => {
					let name = prop.name()?;
					match name {
						"#address-cells" => {
							child_cx.address_cells =
								prop_value::AddressCells::deserialize(prop, self)?.0
						}
						"#size-cells" => {
							child_cx.size_cells = prop_value::SizeCells::deserialize(prop, self)?.0
						}
						_ => (),
					}
					f_prop(name, prop)?;
				}
				Item::Child(node) => {
					f_child(node, child_cx, &mut items.cursor)?;
				}
			}
		}
		Ok((child_cx, items.cursor))
	}
}

/// Types that can be parsed from a devicetree property.
pub trait DeserializeProperty<'dtb>: Sized {
	/// Parses a devicetree property into this type.
	fn deserialize(blob_prop: Property<'dtb>, cx: NodeContext<'_>) -> Result<Self>;
}

impl<'dtb> DeserializeProperty<'dtb> for Property<'dtb> {
	#[inline]
	fn deserialize(blob_prop: Self, _cx: NodeContext<'_>) -> Result<Self> {
		Ok(blob_prop)
	}
}

impl<'dtb> DeserializeProperty<'dtb> for () {
	fn deserialize(blob_prop: Property<'dtb>, _cx: NodeContext<'_>) -> Result<Self> {
		if !blob_prop.value().is_empty() {
			return Err(Error::UnsuitableProperty);
		}
		Ok(())
	}
}

impl<'dtb> DeserializeProperty<'dtb> for bool {
	fn deserialize(blob_prop: Property<'dtb>, _cx: NodeContext<'_>) -> Result<Self> {
		if !blob_prop.value().is_empty() {
			return Err(Error::UnsuitableProperty);
		}
		Ok(true)
	}
}

impl<'dtb> DeserializeProperty<'dtb> for &'dtb [u8] {
	#[inline]
	fn deserialize(blob_prop: Property<'dtb>, _cx: NodeContext<'_>) -> Result<Self> {
		Ok(blob_prop.value())
	}
}

impl<'dtb> DeserializeProperty<'dtb> for &'dtb [u32] {
	/// Gives a devicetree property value as a big-endian u32 slice.
	fn deserialize(blob_prop: Property<'dtb>, _cx: NodeContext<'_>) -> Result<Self> {
		<[u32]>::ref_from_bytes(blob_prop.value()).map_err(|_| Error::UnsuitableProperty)
	}
}

impl<'dtb> DeserializeProperty<'dtb> for u32 {
	/// Gives a devicetree property value as a native-endian u32.
	fn deserialize(blob_prop: Property<'dtb>, _cx: NodeContext<'_>) -> Result<Self> {
		match blob_prop.value().try_into() {
			Ok(arr) => Ok(Self::from_be_bytes(arr)),
			Err(_) => Err(Error::UnsuitableProperty),
		}
	}
}

impl<'dtb> DeserializeProperty<'dtb> for u64 {
	/// Gives a devicetree property value as a native-endian u64.
	fn deserialize(blob_prop: Property<'dtb>, _cx: NodeContext<'_>) -> Result<Self> {
		match blob_prop.value().try_into() {
			Ok(arr) => Ok(Self::from_be_bytes(arr)),
			Err(_) => Err(Error::UnsuitableProperty),
		}
	}
}

impl<'dtb> DeserializeProperty<'dtb> for &'dtb str {
	fn deserialize(blob_prop: Property<'dtb>, _cx: NodeContext<'_>) -> Result<Self> {
		let [rest @ .., 0] = blob_prop.value() else {
			return Err(Error::UnsuitableProperty);
		};
		util::str_from_ascii(rest).ok_or(Error::UnsuitableProperty)
	}
}

impl<'dtb, T: DeserializeProperty<'dtb>> DeserializeProperty<'dtb> for Option<T> {
	fn deserialize(blob_prop: Property<'dtb>, cx: NodeContext<'_>) -> Result<Self> {
		T::deserialize(blob_prop, cx).map(Some)
	}
}

/// Types that can be parsed from a devicetree node.
pub trait DeserializeNode<'dtb>: Sized {
	/// Parses a devicetree node into this type.
	///
	/// The second return value is a cursor pointing to the next token after the
	/// node.
	fn deserialize(blob_node: &Node<'dtb>, cx: NodeContext<'_>) -> Result<(Self, Cursor)>;
}

impl<'dtb> DeserializeNode<'dtb> for Node<'dtb> {
	fn deserialize(blob_node: &Self, _cx: NodeContext<'_>) -> Result<(Self, Cursor)> {
		Ok((blob_node.clone(), blob_node.end_cursor()?))
	}
}

impl<'dtb> DeserializeNode<'dtb> for Cursor {
	fn deserialize(blob_node: &Node<'dtb>, _cx: NodeContext<'_>) -> Result<(Self, Cursor)> {
		Ok((blob_node.start_cursor(), blob_node.end_cursor()?))
	}
}

impl<'dtb, T: DeserializeNode<'dtb>> DeserializeNode<'dtb> for Option<T> {
	fn deserialize(blob_node: &Node<'dtb>, cx: NodeContext<'_>) -> Result<(Self, Cursor)> {
		T::deserialize(blob_node, cx).map(|(v, c)| (Some(v), c))
	}
}

/// Types that can collect several devicetree nodes.
pub trait PushDeserializedNode<'dtb> {
	type Node: DeserializeNode<'dtb>;

	/// Appends a node to the back of the collection.
	///
	/// This function has to be called with the nodes in the same order as they
	/// appear in the devicetree, without skipping any qualified ones.
	fn push_node(&mut self, node: Self::Node, _cx: NodeContext<'_>) -> Result<()>;
}

/// Utility functions.
pub mod util {
	use crate::*;

	/// Splits a node name as follows:
	/// ```text
	/// <node-name> [@ <unit-address>]
	/// ```
	///
	/// # Errors
	/// There cannot be more than one `@`.
	///
	/// # Examples
	/// ```
	/// # use deforest::{util::split_node_name, Error};
	/// assert_eq!(split_node_name("compatible"), Ok(("compatible", None)));
	/// assert_eq!(split_node_name("clock@0"), Ok(("clock", Some("0"))));
	/// assert_eq!(split_node_name("a@b@2"), Err(Error::InvalidNodeName));
	/// ```
	pub fn split_node_name(name: &str) -> Result<(&str, Option<&str>)> {
		let mut parts = name.split('@');
		let node_name = parts.next().unwrap();
		let unit_address = parts.next();
		if parts.next().is_some() {
			return Err(Error::InvalidNodeName);
		}
		Ok((node_name, unit_address))
	}

	/// Parses the 4-byte cells of a property value.
	///
	/// Returns something only if `value` is long enough and the cell count is
	/// no bigger than 16 bytes. The 16-byte limit is not part of the spec.
	/// Defaults to 0 if zero cells are to be parsed.
	pub fn parse_cells(value: &mut &[u32], cells: Cells) -> Option<u128> {
		if cells > 4 {
			return None;
		}
		let mut ret: u128 = 0;
		for &word in value.get(..cells as usize)? {
			ret = ret << 0x20 | u32::from_be(word) as u128;
		}
		*value = &value[cells as usize..];
		Some(ret)
	}

	pub(crate) fn parse_cells_back(value: &mut &[u32], cells: Cells) -> Option<u128> {
		if cells > 4 {
			return None;
		}
		let idx = value.len().checked_sub(cells as usize)?;
		let mut ret: u128 = 0;
		for &word in &value[idx..] {
			ret = ret << 0x20 | u32::from_be(word) as u128;
		}
		*value = &value[..idx];
		Some(ret)
	}

	pub(crate) fn get_c_str(blob: &[u8]) -> Result<&[u8], BlobError> {
		let mut iter = blob.splitn(2, |&b| b == 0);
		let blob = iter.next().unwrap();
		iter.next().ok_or(BlobError::InvalidString)?;
		Ok(blob)
	}

	pub(crate) fn str_from_ascii(blob: &[u8]) -> Option<&str> {
		AsciiStr::from_ascii(blob).ok().map(AsciiStr::as_str)
	}

	/// Same as `<[_]>::get` with a range except that it takes a length, not an end
	/// offset.
	#[inline]
	pub(crate) fn slice_get_with_len<T>(slice: &[T], offset: usize, len: usize) -> Option<&[T]> {
		slice.get(offset..offset + len)
	}

	/// Same as `<[_]>::get_unchecked` with a range except that it takes a length,
	/// not an end offset.
	///
	/// # Safety
	/// `offset + len >= slice.len()`
	#[inline]
	pub(crate) unsafe fn slice_get_with_len_unchecked<T>(
		slice: &[T],
		offset: usize,
		len: usize,
	) -> &[T] {
		unsafe { slice.get_unchecked(offset..offset + len) }
	}
}
