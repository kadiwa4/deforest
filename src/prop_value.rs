//! Types representing property values.

use crate::{blob::Property, util, Cells, DeserializeProperty, Error, NodeContext, Result};
use core::{
	fmt::{self, Display, Formatter},
	iter::FusedIterator,
};

use fallible_iterator::{DoubleEndedFallibleIterator, FallibleIterator};

/// Value of `#address-cells`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AddressCells(pub Cells);

impl Default for AddressCells {
	fn default() -> Self {
		Self(2)
	}
}

impl<'dtb> DeserializeProperty<'dtb> for AddressCells {
	#[inline]
	fn deserialize(blob_prop: Property<'dtb>, cx: NodeContext<'_>) -> Result<Self> {
		let cells = u32::deserialize(blob_prop, cx)?;
		if cells > 4 {
			return Err(Error::TooManyCells);
		}
		Ok(Self(cells as u8))
	}
}

/// Value of `#size-cells`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SizeCells(pub Cells);

impl Default for SizeCells {
	fn default() -> Self {
		Self(1)
	}
}

impl<'dtb> DeserializeProperty<'dtb> for SizeCells {
	#[inline]
	fn deserialize(blob_prop: Property<'dtb>, cx: NodeContext<'_>) -> Result<Self> {
		let cells = u32::deserialize(blob_prop, cx)?;
		if cells > 4 {
			return Err(Error::TooManyCells);
		}
		Ok(Self(cells as u8))
	}
}

/// Value of `status`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Status<'a> {
	#[default]
	Ok,
	Disabled,
	Reserved,
	Fail,
	FailCondition(&'a str),
}

impl<'dtb> DeserializeProperty<'dtb> for Status<'dtb> {
	fn deserialize(blob_prop: Property<'dtb>, cx: NodeContext<'_>) -> Result<Self> {
		<&str>::deserialize(blob_prop, cx)?.try_into()
	}
}

impl<'a> TryFrom<&'a str> for Status<'a> {
	type Error = Error;

	fn try_from(string: &'a str) -> Result<Self, Self::Error> {
		let ret = match string {
			"okay" => Self::Ok,
			"disabled" => Self::Disabled,
			"reserved" => Self::Reserved,
			"fail" => Self::Fail,
			_ => Self::FailCondition(
				string
					.strip_prefix("fail-")
					.ok_or(Error::UnsuitableProperty)?,
			),
		};
		Ok(ret)
	}
}

impl Display for Status<'_> {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		match *self {
			Self::Ok => f.write_str("okay"),
			Self::Disabled => f.write_str("disabled"),
			Self::Reserved => f.write_str("reserved"),
			Self::Fail => f.write_str("fail"),
			Self::FailCondition(condition) => write!(f, "fail-{condition}"),
		}
	}
}

/// Iterator over the strings contained in the property's value.
///
/// Fused (see [`core::iter::FusedIterator`]).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Strings<'a> {
	value: &'a [u8],
}

impl<'a> Strings<'a> {
	/// Empty iterator. Cannot be obtained from deserializing a property.
	pub const EMPTY: Self = Self { value: &[] };

	/// Creates a new iterator over the strings contained in the value.
	///
	/// Returns `None` if the value does not end in a null byte.
	pub fn new(value: &'a [u8]) -> Option<Self> {
		matches!(value, [.., 0]).then_some(Self { value })
	}
}

impl<'dtb> DeserializeProperty<'dtb> for Strings<'dtb> {
	fn deserialize(blob_prop: Property<'dtb>, _cx: NodeContext<'_>) -> Result<Self> {
		Self::new(blob_prop.value()).ok_or(Error::UnsuitableProperty)
	}
}

impl<'a> FallibleIterator for Strings<'a> {
	type Item = &'a str;
	type Error = Error;

	fn next(&mut self) -> Result<Option<Self::Item>, Self::Error> {
		let Some(idx) = self.value.iter().position(|&b| b == 0) else {
			return Ok(None);
		};
		let bytes = &self.value[..idx];
		self.value = &self.value[idx + 1..];
		let s = util::str_from_ascii(bytes).ok_or(Error::UnsuitableProperty)?;
		Ok(Some(s))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		if self.value.is_empty() {
			(0, Some(0))
		} else {
			(1, Some(self.value.len()))
		}
	}
}

impl<'a> DoubleEndedFallibleIterator for Strings<'a> {
	fn next_back(&mut self) -> Result<Option<Self::Item>, Self::Error> {
		let [value @ .., _] = self.value else {
			return Ok(None);
		};
		let idx = value.iter().rposition(|&b| b == 0).map_or(0, |i| i + 1);
		self.value = &self.value[..idx];
		let s = util::str_from_ascii(&value[idx..]).ok_or(Error::UnsuitableProperty)?;
		Ok(Some(s))
	}
}

impl Default for Strings<'_> {
	fn default() -> Self {
		Self::EMPTY
	}
}

/// Iterator over the _(address, length)_ pairs of `reg`'s value.
#[derive(Clone, Debug, Default)]
pub struct Reg<'dtb> {
	pub(crate) value: &'dtb [u32],
	pub(crate) address_cells: Cells,
	pub(crate) size_cells: Cells,
}

impl<'dtb> Reg<'dtb> {
	/// Creates a new iterator over the _(address, length)_ pairs of the value.
	pub fn new(value: &'dtb [u32], address_cells: Cells, size_cells: Cells) -> Result<Self> {
		if address_cells > 4 || size_cells > 4 {
			return Err(Error::TooManyCells);
		}
		if value.len() % (address_cells + size_cells) as usize != 0 {
			return Err(Error::UnsuitableProperty);
		}

		Ok(Self {
			value,
			address_cells,
			size_cells,
		})
	}
}

impl<'dtb> DeserializeProperty<'dtb> for Reg<'dtb> {
	fn deserialize(blob_prop: Property<'dtb>, cx: NodeContext<'_>) -> Result<Self> {
		if cx.address_cells > 4 || cx.size_cells > 4 {
			return Err(Error::TooManyCells);
		}
		let value = <&[u32]>::deserialize(blob_prop, cx)?;
		Self::new(value, cx.address_cells, cx.size_cells)
	}
}

impl Iterator for Reg<'_> {
	type Item = RegBlock;

	fn next(&mut self) -> Option<Self::Item> {
		RegBlock::parse(&mut self.value, self.address_cells, self.size_cells)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.value.len() / (self.address_cells + self.size_cells) as usize;
		(len, Some(len))
	}

	fn nth(&mut self, n: usize) -> Option<RegBlock> {
		let idx = usize::checked_mul(n, (self.address_cells + self.size_cells) as usize)?;
		self.value = self.value.get(idx..)?;
		self.next()
	}
}

impl DoubleEndedIterator for Reg<'_> {
	fn next_back(&mut self) -> Option<Self::Item> {
		let size = util::parse_cells_back(&mut self.value, self.size_cells)?;
		let address = util::parse_cells_back(&mut self.value, self.address_cells).unwrap();
		Some(RegBlock(address, size))
	}
}

impl ExactSizeIterator for Reg<'_> {}
impl FusedIterator for Reg<'_> {}

/// _(address, length)_ pair contained in [`reg`](Reg).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RegBlock(pub u128, pub u128);

impl RegBlock {
	/// Parses an element of a [`reg`](Reg) property.
	///
	/// Returns something only if the length of the value is a multiple of 4 and
	/// none of the cell counts are bigger than 16 bytes each. The 16-byte limit
	/// is not part of the spec. The fields each default to 0 if zero cells are
	/// to be parsed.
	pub fn parse(bytes: &mut &[u32], address_cells: Cells, size_cells: Cells) -> Option<Self> {
		let address = util::parse_cells(bytes, address_cells)?;
		let size = util::parse_cells(bytes, size_cells)?;
		Some(Self(address, size))
	}

	/// The end address of the region (unless there's an overflow).
	pub fn end_address(self) -> Option<u128> {
		let Self(address, size) = self;
		u128::checked_add(address, size)
	}

	/// Maps an _(address, length)_ pair from child to parent address space.
	///
	/// This entire region has to be contained in the `ranges` block for
	/// something to be returned.
	///
	/// # Examples
	/// ```
	/// # use deforest::prop_value::{RangesBlock, RegBlock};
	/// let range = RangesBlock(0x1000, 0x4000, 0x0800);
	/// let reg = RegBlock(0x1200, 0x0600);
	/// assert_eq!(reg.map_to_parent(range), Some(RegBlock(0x4200, 0x0600)));
	/// let reg = RegBlock(0x1200, 0x0800);
	/// assert_eq!(reg.map_to_parent(range), None);
	/// ```
	#[must_use]
	pub fn map_to_parent(self, range: RangesBlock) -> Option<Self> {
		let Self(child_address, size) = self;
		let parent_address = range.map_to_parent(child_address)?;
		(self.end_address()? <= range.child_end_address()?).then_some(Self(parent_address, size))
	}

	/// Maps an _(address, length)_ pair from parent to child address space.
	///
	/// This entire region has to be contained in the `ranges` block for
	/// something to be returned.
	///
	/// # Examples
	/// ```
	/// # use deforest::prop_value::{RangesBlock, RegBlock};
	/// let range = RangesBlock(0x1000, 0x4000, 0x0800);
	/// let reg = RegBlock(0x4200, 0x0600);
	/// assert_eq!(reg.map_to_child(range), Some(RegBlock(0x1200, 0x0600)));
	/// let reg = RegBlock(0x4200, 0x0800);
	/// assert_eq!(reg.map_to_child(range), None);
	/// ```
	#[must_use]
	pub fn map_to_child(self, range: RangesBlock) -> Option<Self> {
		let Self(parent_address, size) = self;
		let child_address = range.map_to_child(parent_address)?;
		(self.end_address()? <= range.parent_end_address()?).then_some(Self(child_address, size))
	}
}

/// Value of `ranges`.
#[derive(Clone, Copy, Debug, Default)]
pub struct Ranges<'dtb> {
	value: &'dtb [u32],
	address_cells: Cells,
}

impl<'dtb> Ranges<'dtb> {
	/// Creates a new iterator over the _(child-bus-address, parent-bus-address,
	/// length)_ triplets of the value.
	pub fn iter(
		self,
		child_address_cells: Cells,
		child_size_cells: Cells,
	) -> Result<RangesIter<'dtb>> {
		RangesIter::new(
			self.value,
			child_address_cells,
			self.address_cells,
			child_size_cells,
		)
	}
}

impl<'dtb> DeserializeProperty<'dtb> for Ranges<'dtb> {
	fn deserialize(blob_prop: Property<'dtb>, cx: NodeContext<'_>) -> Result<Self> {
		if cx.address_cells > 4 {
			return Err(Error::TooManyCells);
		}
		Ok(Self {
			value: <&[u32]>::deserialize(blob_prop, cx)?,
			address_cells: cx.address_cells,
		})
	}
}

/// Iterator over the _(child-bus-address, parent-bus-address, length)_ triplets
/// of [`ranges`](Ranges)' value.
///
/// # Examples
/// ```
/// # use deforest::prop_value::{RangesBlock, RangesIter};
///
/// let data = [
///     0x0200_0000, 0x0000_0000, 0x4000_0000,
///     0x0000_0000, 0x4000_0000,
///     0x0000_0000, 0x4000_0000,
/// ]
/// .map(u32::to_be);
/// let iter = RangesIter::new(&data, 3, 2, 2).unwrap();
/// let expected = RangesBlock(
///     0x0200_0000_0000_0000_4000_0000,
///     0x4000_0000,
///     0x4000_0000,
/// );
/// assert_eq!(iter.collect::<Vec<_>>(), [expected]);
/// ```
#[derive(Clone, Debug)]
pub struct RangesIter<'dtb> {
	pub(crate) value: &'dtb [u32],
	pub(crate) child_address_cells: Cells,
	pub(crate) address_cells: Cells,
	pub(crate) child_size_cells: Cells,
}

impl<'dtb> RangesIter<'dtb> {
	/// Creates a new iterator over the _(child-bus-address, parent-bus-address,
	/// length)_ triplets of a [`ranges`](Ranges) value.
	pub fn new(
		value: &'dtb [u32],
		child_address_cells: Cells,
		address_cells: Cells,
		child_size_cells: Cells,
	) -> Result<Self> {
		if child_address_cells > 4 || address_cells > 4 || child_size_cells > 4 {
			return Err(Error::TooManyCells);
		}
		if value.len() as u32 % (child_address_cells + address_cells + child_size_cells) as u32 != 0
		{
			return Err(Error::UnsuitableProperty);
		}

		Ok(Self {
			value,
			child_address_cells,
			address_cells,
			child_size_cells,
		})
	}

	fn ranges_block_cells(&self) -> Cells {
		self.child_address_cells + self.address_cells + self.child_size_cells
	}
}

impl Iterator for RangesIter<'_> {
	type Item = RangesBlock;

	fn next(&mut self) -> Option<Self::Item> {
		RangesBlock::parse(
			&mut self.value,
			self.child_address_cells,
			self.address_cells,
			self.child_size_cells,
		)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.value.len() as u32 / self.ranges_block_cells() as u32;
		(len as usize, Some(len as usize))
	}

	fn nth(&mut self, n: usize) -> Option<RangesBlock> {
		let idx = u32::checked_mul(n as u32, self.ranges_block_cells() as u32)?;
		self.value = self.value.get(idx as usize..)?;
		self.next()
	}
}

impl DoubleEndedIterator for RangesIter<'_> {
	fn next_back(&mut self) -> Option<Self::Item> {
		let size = util::parse_cells_back(&mut self.value, self.child_size_cells)?;
		let parent_bus_address =
			util::parse_cells_back(&mut self.value, self.address_cells).unwrap();
		let child_bus_address =
			util::parse_cells_back(&mut self.value, self.child_address_cells).unwrap();
		Some(RangesBlock(child_bus_address, parent_bus_address, size))
	}
}

impl ExactSizeIterator for RangesIter<'_> {}
impl FusedIterator for RangesIter<'_> {}

/// _(child-bus-address, parent-bus-address, length)_ triplets in
/// [`ranges`](Ranges). Obtained from [`RangesIter`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RangesBlock(pub u128, pub u128, pub u128);

impl RangesBlock {
	/// Parses an element of a `ranges` property.
	///
	/// Returns something only if the length of the value is a multiple of 4 and
	/// none of the cell counts are bigger than 16 bytes each. The 16-byte limit
	/// is not part of the spec. The fields each default to 0 if zero cells are
	/// to be parsed.
	pub fn parse(
		bytes: &mut &[u32],
		child_address_cells: Cells,
		address_cells: Cells,
		child_size_cells: Cells,
	) -> Option<Self> {
		let child_bus_address = util::parse_cells(bytes, child_address_cells)?;
		let parent_bus_address = util::parse_cells(bytes, address_cells)?;
		let size = util::parse_cells(bytes, child_size_cells)?;
		Some(Self(child_bus_address, parent_bus_address, size))
	}

	/// The child end address of the range (unless there's an overflow).
	pub fn child_end_address(self) -> Option<u128> {
		let Self(child_bus_address, _, size) = self;
		u128::checked_add(child_bus_address, size)
	}

	/// The parent end address of the range (unless there's an overflow).
	pub fn parent_end_address(self) -> Option<u128> {
		let Self(_, parent_bus_address, size) = self;
		u128::checked_add(parent_bus_address, size)
	}

	/// Maps a child address to the parent address.
	///
	/// The address at the end of the range is not considered part of the range.
	///
	/// # Examples
	/// ```
	/// # use deforest::prop_value::RangesBlock;
	/// let range = RangesBlock(0x1000, 0x4000, 0x0800);
	/// assert_eq!(range.map_to_parent(0x1234), Some(0x4234));
	/// assert_eq!(range.map_to_parent(0x1800), None);
	/// ```
	pub fn map_to_parent(self, child_address: u128) -> Option<u128> {
		let Self(child_bus_address, parent_bus_address, size) = self;
		let offset = u128::checked_sub(child_address, child_bus_address);
		u128::checked_add(parent_bus_address, offset.filter(|&o| o < size)?)
	}

	/// Maps a parent address to the child address.
	///
	/// The address at the end of the range is not considered part of the range.
	///
	/// # Examples
	/// ```
	/// # use deforest::prop_value::RangesBlock;
	/// let range = RangesBlock(0x1000, 0x4000, 0x0800);
	/// assert_eq!(range.map_to_child(0x4321), Some(0x1321));
	/// assert_eq!(range.map_to_child(0x4800), None);
	/// ```
	pub fn map_to_child(self, parent_address: u128) -> Option<u128> {
		let Self(child_bus_address, parent_bus_address, size) = self;
		let offset = u128::checked_sub(parent_address, parent_bus_address);
		u128::checked_add(child_bus_address, offset.filter(|&o| o < size)?)
	}
}

/// Value of `initial-mapped-area` property.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct InitialMappedArea {
	effective_address: u64,
	physical_address: u64,
	size: u32,
}

impl<'dtb> DeserializeProperty<'dtb> for InitialMappedArea {
	fn deserialize(blob_prop: Property<'dtb>, cx: NodeContext<'_>) -> Result<Self> {
		let mut bytes = <&[u32]>::deserialize(blob_prop, cx)?;
		if bytes.len() != 5 {
			return Err(Error::UnsuitableProperty);
		}
		Ok(Self {
			effective_address: util::parse_cells(&mut bytes, 2).unwrap() as u64,
			physical_address: util::parse_cells(&mut bytes, 2).unwrap() as u64,
			size: util::parse_cells(&mut bytes, 1).unwrap() as u32,
		})
	}
}

/// Property value that can be either 1 or 2 cells.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct SmallU64(pub u64);

impl<'dtb> DeserializeProperty<'dtb> for SmallU64 {
	fn deserialize(blob_prop: Property<'dtb>, _cx: NodeContext<'_>) -> Result<Self> {
		let value = blob_prop.value();
		if let Ok(arr) = value.try_into() {
			Ok(Self(u32::from_be_bytes(arr) as u64))
		} else if let Ok(arr) = value.try_into() {
			Ok(Self(u64::from_be_bytes(arr)))
		} else {
			Err(Error::UnsuitableProperty)
		}
	}
}

/// Zero-sized type that fails if the property value isn't `"memory"`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DeviceTypeMemory;

impl<'dtb> DeserializeProperty<'dtb> for DeviceTypeMemory {
	fn deserialize(blob_prop: Property<'dtb>, _cx: NodeContext<'_>) -> Result<Self> {
		if blob_prop.value() == b"memory\0" {
			Ok(Self)
		} else {
			Err(Error::InvalidDeviceType)
		}
	}
}

/// Zero-sized type that fails if the property value isn't `"cpu"`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DeviceTypeCpu;

impl<'dtb> DeserializeProperty<'dtb> for DeviceTypeCpu {
	fn deserialize(blob_prop: Property<'dtb>, _cx: NodeContext<'_>) -> Result<Self> {
		if blob_prop.value() == b"cpu\0" {
			Ok(Self)
		} else {
			Err(Error::InvalidDeviceType)
		}
	}
}
