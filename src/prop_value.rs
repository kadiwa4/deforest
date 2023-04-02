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
	fn deserialize(blob_prop: Property<'dtb>, cx: &NodeContext) -> Result<Self> {
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
	fn deserialize(blob_prop: Property<'dtb>, cx: &NodeContext) -> Result<Self> {
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
#[derive(Clone, Debug)]
pub struct Strings<'dtb> {
	value: &'dtb [u8],
}

impl<'dtb> Strings<'dtb> {
	pub const EMPTY: Self = Self { value: &[] };

	pub fn new(value: &'dtb [u8]) -> Option<Self> {
		matches!(value, [.., 0]).then_some(Self { value })
	}
}

impl<'dtb> DeserializeProperty<'dtb> for Strings<'dtb> {
	fn deserialize(blob_prop: Property<'dtb>, _cx: &NodeContext) -> Result<Self> {
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
pub struct Reg<'dtb> {
	value: &'dtb [u32],
	address_cells: Cells,
	size_cells: Cells,
}

impl<'dtb> Reg<'dtb> {
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
	fn deserialize(blob_prop: Property<'dtb>, cx: &NodeContext) -> Result<Self> {
		if cx.address_cells > 4 || cx.size_cells > 4 {
			return Err(Error::TooManyCells);
		}
		let value = blob_prop.value_u32().ok_or(Error::UnsuitableProperty)?;
		Self::new(value, cx.address_cells, cx.size_cells)
	}
}

impl Iterator for Reg<'_> {
	type Item = (u128, u128);

	fn next(&mut self) -> Option<Self::Item> {
		let address = util::parse_cells(&mut self.value, self.address_cells)?;
		let length = util::parse_cells(&mut self.value, self.size_cells).unwrap();
		Some((address, length))
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.value.len() / (self.address_cells + self.size_cells) as usize;
		(len, Some(len))
	}
}

impl DoubleEndedIterator for Reg<'_> {
	fn next_back(&mut self) -> Option<Self::Item> {
		let length = util::parse_cells_back(&mut self.value, self.size_cells)?;
		let address = util::parse_cells_back(&mut self.value, self.address_cells).unwrap();
		Some((address, length))
	}
}

impl ExactSizeIterator for Reg<'_> {}
impl FusedIterator for Reg<'_> {}
