//! Higher level of abstraction. This is very incomplete; consider creating your
//! own types instead.

use crate::{
	blob::{self, Cursor, Devicetree},
	prop_value::{self, RangesIter},
	Cells, DeserializeNode, DeserializeProperty, Error, NodeContext, Result,
};

/// A devicetree node representing some sort of device, meaning it has a
/// `compatible` property.
#[derive(Clone, Debug)]
pub struct Device<'dtb> {
	node_name: &'dtb str,
	content_cursor: Cursor,
	parent_address_cells: Cells,
	parent_size_cells: Cells,
	address_cells: Cells,
	size_cells: Cells,
	phandle: Option<u32>,
	compatible: prop_value::Strings<'dtb>,
	status: prop_value::Status<'dtb>,
	reg: Option<&'dtb [u32]>,
	ranges: Option<&'dtb [u32]>,
}

impl<'dtb> Device<'dtb> {
	pub fn node_name(&self) -> &'dtb str {
		self.node_name
	}

	pub fn content_cursor(&self) -> Cursor {
		self.content_cursor
	}

	pub fn blob_node(&self, dt: &'dtb Devicetree) -> blob::Node<'dtb> {
		blob::Node {
			dt,
			name: self.node_name.as_bytes(),
			contents: self.content_cursor,
		}
	}

	pub fn address_cells(&self) -> Cells {
		self.address_cells
	}

	pub fn size_cells(&self) -> Cells {
		self.size_cells
	}

	pub fn phandle(&self) -> Option<u32> {
		self.phandle
	}

	pub fn compatible(&self) -> prop_value::Strings<'dtb> {
		self.compatible.clone()
	}

	pub fn status(&self) -> prop_value::Status<'dtb> {
		self.status
	}

	pub fn reg(&self) -> Option<prop_value::Reg<'dtb>> {
		self.reg.map(|value| prop_value::Reg {
			value,
			address_cells: self.parent_address_cells,
			size_cells: self.parent_size_cells,
		})
	}

	pub fn ranges(&self) -> Option<RangesIter<'dtb>> {
		self.ranges.map(|value| RangesIter {
			value,
			child_address_cells: self.address_cells,
			address_cells: self.parent_address_cells,
			child_size_cells: self.size_cells,
		})
	}
}

impl<'dtb> DeserializeNode<'dtb> for Device<'dtb> {
	fn deserialize(blob_node: &blob::Node<'dtb>, cx: NodeContext<'_>) -> Result<(Self, Cursor)> {
		let mut this = Self {
			node_name: blob_node.name()?,
			content_cursor: blob_node.contents,
			parent_address_cells: cx.address_cells,
			parent_size_cells: cx.size_cells,
			address_cells: 0,
			size_cells: 0,
			phandle: None,
			compatible: prop_value::Strings::EMPTY,
			status: prop_value::Status::Ok,
			reg: None,
			ranges: None,
		};
		let mut compatible = None;
		let (child_cx, cursor) = cx.deserialize_node(
			blob_node,
			|name, prop| {
				match name {
					"phandle" => this.phandle = Some(u32::deserialize(prop, cx)?),
					"compatible" => compatible = Some(prop_value::Strings::deserialize(prop, cx)?),
					"status" => this.status = prop_value::Status::deserialize(prop, cx)?,
					"reg" => this.reg = Some(prop_value::Reg::deserialize(prop, cx)?.value),
					"ranges" => this.reg = Some(<&[u32]>::deserialize(prop, cx)?),
					_ => (),
				};
				Ok(())
			},
			|node, _, cursor| {
				*cursor = node.end_cursor()?;
				Ok(())
			},
		)?;
		this.compatible = compatible.ok_or(Error::UnsuitableNode)?;
		if let Some(value) = this.ranges {
			RangesIter::new(
				value,
				child_cx.address_cells,
				cx.address_cells,
				child_cx.size_cells,
			)?;
		}
		this.address_cells = child_cx.address_cells;
		this.size_cells = child_cx.size_cells;
		Ok((this, cursor))
	}
}
