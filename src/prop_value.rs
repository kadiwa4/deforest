//! Types representing property values.

use crate::{blob::Property, util, Cells, DeserializeProperty, Error, NodeContext, Result};
use core::iter::FusedIterator;

use ascii::AsciiStr;
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

/// Iterator over the strings contained in the property's value.
///
/// Fused (see [`core::iter::FusedIterator`]).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Strings<'dtb> {
	value: &'dtb [u8],
}

impl<'dtb> Strings<'dtb> {
	/// Empty iterator. Cannot be obtained from deserializing a property.
	pub const EMPTY: Self = Self { value: &[] };

	/// Creates a new iterator over the strings contained in the value.
	///
	/// Returns `None` if the value does not end in a null byte.
	pub fn new(value: &'dtb [u8]) -> Option<Self> {
		matches!(value, [.., 0]).then_some(Self { value })
	}
}

impl<'dtb> DeserializeProperty<'dtb> for Strings<'dtb> {
	fn deserialize(blob_prop: Property<'dtb>, _cx: NodeContext<'_>) -> Result<Self> {
		Self::new(blob_prop.value()).ok_or(Error::UnsuitableProperty)
	}
}

impl<'dtb> FallibleIterator for Strings<'dtb> {
	type Item = &'dtb str;
	type Error = Error;

	fn next(&mut self) -> Result<Option<Self::Item>, Self::Error> {
		let Some(idx) = self.value.iter().position(|&b| b == 0) else { return Ok(None) };
		let bytes = &self.value[..idx];
		self.value = &self.value[idx + 1..];
		let bytes = AsciiStr::from_ascii(bytes).map_err(|_| Error::UnsuitableProperty)?;
		Ok(Some(bytes.as_str()))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		if self.value.is_empty() {
			(0, Some(0))
		} else {
			(1, Some(self.value.len()))
		}
	}
}

impl<'dtb> DoubleEndedFallibleIterator for Strings<'dtb> {
	fn next_back(&mut self) -> Result<Option<Self::Item>, Self::Error> {
		let [value @ .., _] = self.value else { return Ok(None) };
		let idx = value.iter().rposition(|&b| b == 0).map_or(0, |i| i + 1);
		self.value = &self.value[..idx];
		let bytes = AsciiStr::from_ascii(&value[idx..]).map_err(|_| Error::UnsuitableProperty)?;
		Ok(Some(bytes.as_str()))
	}
}

impl Default for Strings<'static> {
	fn default() -> Self {
		Self::EMPTY
	}
}

/// Iterator over the _(address, length)_ pairs of `reg`'s value.
#[derive(Clone, Debug)]
pub struct Reg<'dtb> {
	value: &'dtb [u32],
	address_cells: Cells,
	size_cells: Cells,
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
		let length = util::parse_cells_back(&mut self.value, self.size_cells)?;
		let address = util::parse_cells_back(&mut self.value, self.address_cells).unwrap();
		Some(RegBlock(address, length))
	}
}

impl ExactSizeIterator for Reg<'_> {}
impl FusedIterator for Reg<'_> {}

/// _(address, length)_ pair contained in [`Reg`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RegBlock(pub u128, pub u128);

impl RegBlock {
	/// Parses an element of a `reg` property.
	///
	/// Returns something only if the length of the value is a multiple of 4 and
	/// none of the cell counts are bigger than 16 bytes each. The 16-byte limit
	/// is not part of the spec. The fields each default to 0 if zero cells are
	/// to be parsed.
	pub fn parse(bytes: &mut &[u32], address_cells: Cells, size_cells: Cells) -> Option<Self> {
		let address = util::parse_cells(bytes, address_cells)?;
		let length = util::parse_cells(bytes, size_cells)?;
		Some(Self(address, length))
	}
}

/// Iterator over the _(child-bus-address, parent-bus-address, length)_ triplets of `ranges`' value.
#[derive(Clone, Debug, Default)]
pub struct Ranges<'dtb> {
	value: &'dtb [u32],
	address_cells: Cells,
	size_cells: Cells,
}

impl<'dtb> Ranges<'dtb> {
	/// Creates a new iterator over the _(address, length)_ pairs of the value.
	pub fn new(value: &'dtb [u32], address_cells: Cells, size_cells: Cells) -> Result<Self> {
		if address_cells > 4 || size_cells > 4 {
			return Err(Error::TooManyCells);
		}
		if value.len() % (address_cells * 2 + size_cells) as usize != 0 {
			return Err(Error::UnsuitableProperty);
		}

		Ok(Self {
			value,
			address_cells,
			size_cells,
		})
	}
}

impl<'dtb> DeserializeProperty<'dtb> for Ranges<'dtb> {
	fn deserialize(blob_prop: Property<'dtb>, cx: NodeContext<'_>) -> Result<Self> {
		if cx.address_cells > 4 || cx.size_cells > 4 {
			return Err(Error::TooManyCells);
		}
		let value = <&[u32]>::deserialize(blob_prop, cx)?;
		Self::new(value, cx.address_cells, cx.size_cells)
	}
}

impl Iterator for Ranges<'_> {
	type Item = RangesBlock;

	fn next(&mut self) -> Option<Self::Item> {
		RangesBlock::parse(&mut self.value, self.address_cells, self.size_cells)
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.value.len() / (self.address_cells * 2 + self.size_cells) as usize;
		(len, Some(len))
	}

	fn nth(&mut self, n: usize) -> Option<RangesBlock> {
		let idx = usize::checked_mul(n, (self.address_cells * 2 + self.size_cells) as usize)?;
		self.value = self.value.get(idx..)?;
		self.next()
	}
}

impl DoubleEndedIterator for Ranges<'_> {
	fn next_back(&mut self) -> Option<Self::Item> {
		let length = util::parse_cells_back(&mut self.value, self.size_cells)?;
		let parent_bus_address =
			util::parse_cells_back(&mut self.value, self.address_cells).unwrap();
		let child_bus_address =
			util::parse_cells_back(&mut self.value, self.address_cells).unwrap();
		Some(RangesBlock(child_bus_address, parent_bus_address, length))
	}
}

impl ExactSizeIterator for Ranges<'_> {}
impl FusedIterator for Ranges<'_> {}

/// _(child-bus-address, parent-bus-address, length)_ triplets in [`Ranges`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RangesBlock(pub u128, pub u128, pub u128);

impl RangesBlock {
	/// Parses an element of a `ranges` property.
	///
	/// Returns something only if the length of the value is a multiple of 4 and
	/// none of the cell counts are bigger than 16 bytes each. The 16-byte limit
	/// is not part of the spec. The fields each default to 0 if zero cells are
	/// to be parsed.
	pub fn parse(bytes: &mut &[u32], address_cells: Cells, size_cells: Cells) -> Option<Self> {
		let child_bus_address = util::parse_cells(bytes, address_cells)?;
		let parent_bus_address = util::parse_cells(bytes, address_cells)?;
		let length = util::parse_cells(bytes, size_cells)?;
		Some(Self(child_bus_address, parent_bus_address, length))
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
