//! Parser for devicetree blobs compliant with version 0.4-rc1 of
//! [the specification][spec].
//!
//! [spec]: https://www.devicetree.org/specifications

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

pub mod blob;
pub mod prop_value;

#[cfg(feature = "derive")]
pub use devicetree_derive::*;

use blob::{Cursor, Node, Property};
use core::{
	fmt::{self, Display, Formatter},
	iter, slice,
};

use ascii::AsciiStr;

/// Any error caused by this crate.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Error {
	/// Not produced by this crate.
	Unknown,
	Blob(blob::Error),
	InvalidPath,
	TooManyCells,
	UnsuitableProperty,
}

impl Display for Error {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		use Error::*;

		if let Blob(err) = self {
			return Display::fmt(err, f);
		}

		f.write_str("devicetree error: ")?;
		match self {
			Unknown => f.write_str("unknown"),
			Blob(_) => Ok(()),
			InvalidPath => f.write_str("invalid path"),
			TooManyCells => f.write_str("too many cells"),
			UnsuitableProperty => f.write_str("unsuitable property"),
		}
	}
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}

pub type Result<T, E = Error> = core::result::Result<T, E>;

pub type Cells = u8;
pub type Phandle = u32;

/// Absolute path of an item.
///
/// Either a slice of path components or a string with `/`-separated components.
/// A leading slash is required for a string path, other than that the path can
/// be empty.
pub trait Path {
	type ComponentsIter<'a>: DoubleEndedIterator<Item = &'a str>
	where
		Self: 'a;

	/// An iterator over this path's components.
	fn as_components(&self) -> Result<Self::ComponentsIter<'_>>;
}

impl<'b> Path for [&'b str] {
	type ComponentsIter<'a> = iter::Copied<slice::Iter<'a, &'a str>>
	where
		Self: 'a;

	fn as_components(&self) -> Result<Self::ComponentsIter<'_>> {
		Ok(self.iter().copied())
	}
}

impl Path for str {
	type ComponentsIter<'a> = core::str::Split<'a, char>
	where
		Self: 'a;

	fn as_components(&self) -> Result<Self::ComponentsIter<'_>> {
		let mut components = self.split('/');
		if components.next() == Some("") {
			if self.len() == 1 {
				// for the root node, the iterator should be empty
				components.next();
			}
			Ok(components)
		} else {
			Err(Error::InvalidPath)
		}
	}
}

/// Holds information for deserialization.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct NodeContext {
	pub address_cells: Cells,
	pub size_cells: Cells,
}

impl Default for NodeContext {
	fn default() -> Self {
		Self {
			address_cells: prop_value::AddressCells::default().0,
			size_cells: prop_value::SizeCells::default().0,
		}
	}
}

pub trait DeserializeProperty<'dtb>: Sized {
	fn deserialize(blob_prop: Property<'dtb>, cx: &NodeContext) -> Result<Self>;
}

impl<'dtb> DeserializeProperty<'dtb> for Property<'dtb> {
	fn deserialize(blob_prop: Property<'dtb>, _cx: &NodeContext) -> Result<Self> {
		Ok(blob_prop)
	}
}

impl<'dtb> DeserializeProperty<'dtb> for () {
	fn deserialize(blob_prop: Property<'dtb>, _cx: &NodeContext) -> Result<Self> {
		if !blob_prop.value().is_empty() {
			return Err(Error::UnsuitableProperty);
		}
		Ok(())
	}
}

impl<'dtb> DeserializeProperty<'dtb> for &'dtb [u8] {
	fn deserialize(blob_prop: Property<'dtb>, _cx: &NodeContext) -> Result<Self> {
		Ok(blob_prop.value())
	}
}

impl<'dtb> DeserializeProperty<'dtb> for &'dtb [u32] {
	fn deserialize(blob_prop: Property<'dtb>, _cx: &NodeContext) -> Result<Self> {
		let val = blob_prop.value();
		if val.len() % 4 != 0 {
			return Err(Error::UnsuitableProperty);
		}
		Ok(unsafe { slice::from_raw_parts(val as *const _ as *const u32, val.len() / 4) })
	}
}

impl<'dtb> DeserializeProperty<'dtb> for u32 {
	fn deserialize(blob_prop: Property<'dtb>, _cx: &NodeContext) -> Result<Self> {
		match blob_prop.value().try_into() {
			Ok(arr) => Ok(Self::from_be_bytes(arr)),
			Err(_) => Err(Error::UnsuitableProperty),
		}
	}
}

impl<'dtb> DeserializeProperty<'dtb> for u64 {
	fn deserialize(blob_prop: Property<'dtb>, _cx: &NodeContext) -> Result<Self> {
		match blob_prop.value().try_into() {
			Ok(arr) => Ok(Self::from_be_bytes(arr)),
			Err(_) => Err(Error::UnsuitableProperty),
		}
	}
}

impl<'dtb> DeserializeProperty<'dtb> for &'dtb str {
	fn deserialize(blob_prop: Property<'dtb>, _cx: &NodeContext) -> Result<Self> {
		if let [rest @ .., 0] = blob_prop.value() {
			match AsciiStr::from_ascii(rest) {
				Ok(s) => Ok(s.as_str()),
				Err(_) => Err(Error::UnsuitableProperty),
			}
		} else {
			Err(Error::UnsuitableProperty)
		}
	}
}

impl<'dtb, T: DeserializeProperty<'dtb>> DeserializeProperty<'dtb> for Option<T> {
	fn deserialize(blob_prop: Property<'dtb>, cx: &NodeContext) -> Result<Self> {
		T::deserialize(blob_prop, cx).map(Some)
	}
}

pub trait DeserializeNode<'dtb>: Sized {
	fn deserialize(blob_node: &Node<'dtb>, cx: &NodeContext) -> Result<(Self, Cursor)>;
}

impl<'dtb> DeserializeNode<'dtb> for Node<'dtb> {
	fn deserialize(blob_node: &Node<'dtb>, _cx: &NodeContext) -> Result<(Self, Cursor)> {
		Ok((blob_node.clone(), blob_node.end_cursor()?))
	}
}

impl<'dtb> DeserializeNode<'dtb> for Cursor {
	fn deserialize(blob_node: &Node<'dtb>, _cx: &NodeContext) -> Result<(Self, Cursor)> {
		Ok((blob_node.content_cursor(), blob_node.end_cursor()?))
	}
}

impl<'dtb, T: DeserializeNode<'dtb>> DeserializeNode<'dtb> for Option<T> {
	fn deserialize(blob_node: &Node<'dtb>, cx: &NodeContext) -> Result<(Self, Cursor)> {
		T::deserialize(blob_node, cx).map(|(v, c)| (Some(v), c))
	}
}

#[cfg(feature = "alloc")]
mod alloc_impl {
	use crate::*;
	use alloc::{boxed::Box, string::String, vec::Vec};
	use blob::Item;

	use ::fallible_iterator::FallibleIterator;

	impl Path for [String] {
		type ComponentsIter<'a> = iter::Map<slice::Iter<'a, String>, fn(&String) -> &str>
		where
			Self: 'a;

		fn as_components(&self) -> Result<Self::ComponentsIter<'_>> {
			Ok(self.iter().map(String::as_str))
		}
	}

	impl<'dtb> DeserializeProperty<'dtb> for Vec<u8> {
		fn deserialize(blob_prop: Property<'dtb>, _cx: &NodeContext) -> Result<Self> {
			Ok(blob_prop.value().to_vec())
		}
	}

	impl<'dtb> DeserializeProperty<'dtb> for Box<[u8]> {
		fn deserialize(blob_prop: Property<'dtb>, _cx: &NodeContext) -> Result<Self> {
			Ok(blob_prop.value().into())
		}
	}

	impl<'dtb> DeserializeProperty<'dtb> for Vec<u32> {
		fn deserialize(blob_prop: Property<'dtb>, cx: &NodeContext) -> Result<Self> {
			<&[u32]>::deserialize(blob_prop, cx).map(<[u32]>::to_vec)
		}
	}

	impl<'dtb> DeserializeProperty<'dtb> for Box<[u32]> {
		fn deserialize(blob_prop: Property<'dtb>, cx: &NodeContext) -> Result<Self> {
			<&[u32]>::deserialize(blob_prop, cx).map(Box::from)
		}
	}

	impl<'dtb> DeserializeProperty<'dtb> for String {
		fn deserialize(blob_prop: Property<'dtb>, cx: &NodeContext) -> Result<Self> {
			<&str>::deserialize(blob_prop, cx).map(String::from)
		}
	}

	impl<'dtb> DeserializeProperty<'dtb> for Box<str> {
		fn deserialize(blob_prop: Property<'dtb>, cx: &NodeContext) -> Result<Self> {
			<&str>::deserialize(blob_prop, cx).map(Box::from)
		}
	}

	impl<'dtb> DeserializeProperty<'dtb> for Vec<&'dtb str> {
		fn deserialize(blob_prop: Property<'dtb>, cx: &NodeContext) -> Result<Self> {
			prop_value::Strings::deserialize(blob_prop, cx).and_then(collect_vec)
		}
	}

	impl<'dtb> DeserializeProperty<'dtb> for Vec<String> {
		fn deserialize(blob_prop: Property<'dtb>, cx: &NodeContext) -> Result<Self> {
			let strs = prop_value::Strings::deserialize(blob_prop, cx)?;
			collect_vec(strs.map(|s| Ok(s.into())))
		}
	}

	impl<'dtb> DeserializeProperty<'dtb> for Vec<Box<str>> {
		fn deserialize(blob_prop: Property<'dtb>, cx: &NodeContext) -> Result<Self> {
			let strs = prop_value::Strings::deserialize(blob_prop, cx)?;
			collect_vec(strs.map(|s| Ok(s.into())))
		}
	}

	impl<'dtb> DeserializeProperty<'dtb> for Box<[&'dtb str]> {
		fn deserialize(blob_prop: Property<'dtb>, cx: &NodeContext) -> Result<Self> {
			<Vec<&str>>::deserialize(blob_prop, cx).map(Vec::into_boxed_slice)
		}
	}

	impl<'dtb> DeserializeProperty<'dtb> for Box<[String]> {
		fn deserialize(blob_prop: Property<'dtb>, cx: &NodeContext) -> Result<Self> {
			<Vec<String>>::deserialize(blob_prop, cx).map(Vec::into_boxed_slice)
		}
	}

	impl<'dtb> DeserializeProperty<'dtb> for Box<[Box<str>]> {
		fn deserialize(blob_prop: Property<'dtb>, cx: &NodeContext) -> Result<Self> {
			<Vec<Box<str>>>::deserialize(blob_prop, cx).map(Vec::into_boxed_slice)
		}
	}

	impl<'dtb> DeserializeNode<'dtb> for Vec<Item<'dtb>> {
		fn deserialize(blob_node: &Node<'dtb>, _cx: &NodeContext) -> Result<(Self, Cursor)> {
			let mut items = blob_node.items();
			Ok((collect_vec(&mut items)?, items.cursor()))
		}
	}

	impl<'dtb> DeserializeNode<'dtb> for Box<[Item<'dtb>]> {
		fn deserialize(blob_node: &Node<'dtb>, _cx: &NodeContext) -> Result<(Self, Cursor)> {
			let mut items = blob_node.items();
			Ok((collect_vec(&mut items)?.into_boxed_slice(), items.cursor()))
		}
	}

	fn collect_vec<T, E>(mut it: impl FallibleIterator<Item = T, Error = E>) -> Result<Vec<T>, E> {
		let (lower, upper) = it.size_hint();
		if upper == Some(0) {
			return Ok(Vec::new());
		}
		let mut vec = Vec::with_capacity(Ord::max(lower - 1, 4));
		while let Some(v) = it.next()? {
			vec.push(v);
		}
		Ok(vec)
	}
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
	/// # use devicetree::{blob::Error, util::split_node_name};
	/// assert_eq!(split_node_name("compatible"), Ok(("compatible", None)));
	/// assert_eq!(split_node_name("clock@0"), Ok(("clock", Some("0"))));
	/// assert_eq!(split_node_name("a@b@2"), Err(Error::InvalidNodeName));
	/// ```
	pub fn split_node_name(name: &str) -> Result<(&str, Option<&str>), blob::Error> {
		let mut parts = name.split('@');
		let node_name = parts.next().unwrap();
		let unit_address = parts.next();
		if parts.next().is_some() {
			return Err(blob::Error::InvalidNodeName);
		}
		Ok((node_name, unit_address))
	}

	/// Parses the 4-byte cells of a property value.
	///
	/// Returns something only if `bytes` is long enough and the cell count is
	/// no bigger than 16 bytes. The 16-byte limit is not part of the spec.
	/// Defaults to 0 if zero cells are to be parsed.
	pub fn parse_cells(bytes: &mut &[u32], cells: Cells) -> Option<u128> {
		let mut value: u128 = 0;
		for &byte in bytes.get(..cells as usize)? {
			value = (value << 0x20) | u32::from_be(byte) as u128;
		}
		*bytes = &bytes[cells as usize..];
		Some(value)
	}

	pub(crate) fn parse_cells_back(bytes: &mut &[u32], cells: Cells) -> Option<u128> {
		let idx = usize::checked_sub(bytes.len(), cells as usize)?;
		let mut value: u128 = 0;
		for &byte in &bytes[idx..] {
			value = (value << 0x20) | u32::from_be(byte) as u128;
		}
		*bytes = &bytes[..idx];
		Some(value)
	}

	/// Parses the value of a `reg` property, returning the address and size in
	/// that order.
	///
	/// Returns something only if the length of the value is a multiple of 4 and
	/// both cell counts are no bigger than 16 bytes each. The 16-byte limit is
	/// not part of the spec. The address and size each default to 0 if zero
	/// cells are to be parsed.
	pub fn parse_reg_value(
		bytes: &mut &[u32],
		address_cells: Cells,
		size_cells: Cells,
	) -> Option<(u128, u128)> {
		let address = parse_cells(bytes, address_cells)?;
		let length = parse_cells(bytes, size_cells)?;
		Some((address, length))
	}

	pub(crate) fn get_c_str(blob: &[u8]) -> Result<&str, blob::Error> {
		let mut iter = blob.split(|&b| b == 0);
		let blob = iter.next().unwrap();
		iter.next().ok_or(blob::Error::InvalidString)?;

		match AsciiStr::from_ascii(blob) {
			Ok(s) => Ok(s.as_str()),
			Err(_) => Err(blob::Error::InvalidString),
		}
	}

	/// Same as `<[_]>::get` with a range except that it takes a length, not an end
	/// offset.
	pub(crate) fn slice_get_with_len<T>(slice: &[T], offset: usize, len: usize) -> Option<&[T]> {
		slice.get(offset..offset + len)
	}
}

/// Crate `fallible_iterator`.
pub mod fallible_iterator {
	pub use fallible_iterator::*;

	pub fn from_fn<T, E, F: FnMut() -> Result<Option<T>, E>>(f: F) -> FromFn<F> {
		FromFn(f)
	}

	pub struct FromFn<F>(F);

	impl<T, E, F: FnMut() -> Result<Option<T>, E>> FallibleIterator for FromFn<F> {
		type Item = T;
		type Error = E;

		fn next(&mut self) -> Result<Option<Self::Item>, Self::Error> {
			self.0()
		}
	}
}
