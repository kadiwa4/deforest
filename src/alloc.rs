//! Features needing memory allocation.

use core::{
	iter::Map,
	mem::{size_of, size_of_val},
	slice,
};
use std_alloc::{boxed::Box, string::String, vec::Vec};

use fallible_iterator::FallibleIterator;

use crate::{
	blob::{self, Cursor, Devicetree, Item, Node, Property},
	prop_value::{self, RegBlock},
	DeserializeNode, DeserializeProperty, NodeContext, Path, PushDeserializedNode, ReserveEntry,
	Result,
};

/// Starting point for constructing a [`Devicetree`] yourself.
#[derive(Clone, Default)]
#[non_exhaustive]
pub struct DevicetreeBuilder<'a> {
	/// Defaults to 0.
	pub boot_core_id: u32,
	/// Defaults to an empty slice.
	pub reserve_entries: &'a [ReserveEntry],
	/// Mandatory.
	pub struct_blob: Option<&'a [u32]>,
	/// Mandatory.
	pub strings_blob: Option<&'a [u8]>,
}

impl DevicetreeBuilder<'_> {
	/// Constructs the devicetree. Returns `None` if it is too large.
	pub fn build(&self) -> Option<Box<Devicetree>> {
		const HEADER_SIZE_ALIGN_RATIO: usize = blob::HEADER_SIZE / blob::DTB_ALIGN;

		let struct_blob = self.struct_blob.expect("builder has no struct blob");
		let strings_blob = self.strings_blob.expect("builder has no strings blob");

		let struct_offset =
			blob::HEADER_SIZE + size_of_val(self.reserve_entries) + size_of::<ReserveEntry>();
		let strings_offset = struct_offset + size_of_val(struct_blob);
		let size = strings_offset + strings_blob.len();

		let capacity = (size + blob::DTB_ALIGN - 1) / blob::DTB_ALIGN;
		let size = u32::try_from(size).ok()?;

		let mut blob: Vec<u64> = Vec::with_capacity(capacity);
		blob.extend::<[u64; HEADER_SIZE_ALIGN_RATIO]>(zerocopy::transmute!(blob::Header {
			magic: blob::DTB_MAGIC,
			totalsize: size.to_be(),
			off_dt_struct: (struct_offset as u32).to_be(),
			off_dt_strings: (strings_offset as u32).to_be(),
			off_mem_rsvmap: (blob::HEADER_SIZE as u32).to_be(),
			version: 17_u32.to_be(),
			last_comp_version: blob::LAST_COMPATIBLE_VERSION.to_be(),
			boot_cpuid_phys: self.boot_core_id.to_be(),
			size_dt_strings: (strings_blob.len() as u32).to_be(),
			size_dt_struct: (size_of_val(struct_blob) as u32).to_be(),
		}));
		blob.extend(self.reserve_entries.iter().flat_map(
			|e| -> [u64; blob::RESERVE_ENTRY_SIZE_ALIGN_RATIO] {
				zerocopy::transmute!(blob::RawReserveEntry {
					address: e.address.to_be(),
					size: e.size.to_be(),
				})
			},
		));
		unsafe {
			*blob.as_mut_ptr().add(capacity - 1) = 0;
		}
		blob.extend([0; blob::RESERVE_ENTRY_SIZE_ALIGN_RATIO]);

		unsafe {
			let ptr = blob.as_mut_ptr() as *mut u8;
			core::ptr::copy_nonoverlapping(
				struct_blob.as_ptr(),
				ptr.add(struct_offset) as *mut u32,
				struct_blob.len(),
			);
			core::ptr::copy_nonoverlapping(
				strings_blob.as_ptr(),
				ptr.add(strings_offset),
				strings_blob.len(),
			);
			blob.set_len(capacity);
		}

		Some(unsafe { Devicetree::from_box_unchecked(blob.into_boxed_slice()) })
	}
}

impl Path for [String] {
	type ComponentsIter<'a> = Map<slice::Iter<'a, String>, fn(&String) -> &str>
		where
			Self: 'a;

	fn as_components(&self) -> Result<Self::ComponentsIter<'_>> {
		Ok(self.iter().map(String::as_str))
	}
}

impl<const N: usize> Path for [String; N] {
	type ComponentsIter<'a> = Map<slice::Iter<'a, String>, fn(&String) -> &str>
		where
			Self: 'a;

	fn as_components(&self) -> Result<Self::ComponentsIter<'_>> {
		Ok(self.iter().map(String::as_str))
	}
}

impl<'dtb> DeserializeProperty<'dtb> for Vec<u8> {
	fn deserialize(blob_prop: Property<'dtb>, _cx: NodeContext<'_>) -> Result<Self> {
		Ok(blob_prop.value().to_vec())
	}
}

impl<'dtb> DeserializeProperty<'dtb> for Box<[u8]> {
	fn deserialize(blob_prop: Property<'dtb>, _cx: NodeContext<'_>) -> Result<Self> {
		Ok(blob_prop.value().into())
	}
}

impl<'dtb> DeserializeProperty<'dtb> for Vec<u32> {
	fn deserialize(blob_prop: Property<'dtb>, cx: NodeContext<'_>) -> Result<Self> {
		<&[u32]>::deserialize(blob_prop, cx).map(<[u32]>::to_vec)
	}
}

impl<'dtb> DeserializeProperty<'dtb> for Box<[u32]> {
	fn deserialize(blob_prop: Property<'dtb>, cx: NodeContext<'_>) -> Result<Self> {
		<&[u32]>::deserialize(blob_prop, cx).map(Box::from)
	}
}

impl<'dtb> DeserializeProperty<'dtb> for String {
	fn deserialize(blob_prop: Property<'dtb>, cx: NodeContext<'_>) -> Result<Self> {
		<&str>::deserialize(blob_prop, cx).map(String::from)
	}
}

impl<'dtb> DeserializeProperty<'dtb> for Box<str> {
	fn deserialize(blob_prop: Property<'dtb>, cx: NodeContext<'_>) -> Result<Self> {
		<&str>::deserialize(blob_prop, cx).map(Box::from)
	}
}

impl<'dtb> DeserializeProperty<'dtb> for Vec<&'dtb str> {
	fn deserialize(blob_prop: Property<'dtb>, cx: NodeContext<'_>) -> Result<Self> {
		prop_value::Strings::deserialize(blob_prop, cx)?.collect()
	}
}

impl<'dtb> DeserializeProperty<'dtb> for Vec<String> {
	fn deserialize(blob_prop: Property<'dtb>, cx: NodeContext<'_>) -> Result<Self> {
		prop_value::Strings::deserialize(blob_prop, cx)?
			.map(|s| Ok(s.into()))
			.collect()
	}
}

impl<'dtb> DeserializeProperty<'dtb> for Vec<Box<str>> {
	fn deserialize(blob_prop: Property<'dtb>, cx: NodeContext<'_>) -> Result<Self> {
		prop_value::Strings::deserialize(blob_prop, cx)?
			.map(|s| Ok(s.into()))
			.collect()
	}
}

impl<'dtb> DeserializeProperty<'dtb> for Box<[&'dtb str]> {
	fn deserialize(blob_prop: Property<'dtb>, cx: NodeContext<'_>) -> Result<Self> {
		<Vec<&str>>::deserialize(blob_prop, cx).map(Vec::into_boxed_slice)
	}
}

impl<'dtb> DeserializeProperty<'dtb> for Box<[String]> {
	fn deserialize(blob_prop: Property<'dtb>, cx: NodeContext<'_>) -> Result<Self> {
		<Vec<String>>::deserialize(blob_prop, cx).map(Vec::into_boxed_slice)
	}
}

impl<'dtb> DeserializeProperty<'dtb> for Box<[Box<str>]> {
	fn deserialize(blob_prop: Property<'dtb>, cx: NodeContext<'_>) -> Result<Self> {
		<Vec<Box<str>>>::deserialize(blob_prop, cx).map(Vec::into_boxed_slice)
	}
}

impl<'dtb> DeserializeProperty<'dtb> for Vec<RegBlock> {
	fn deserialize(blob_prop: Property<'dtb>, cx: NodeContext<'_>) -> Result<Self> {
		prop_value::Reg::deserialize(blob_prop, cx).map(Vec::from_iter)
	}
}

impl<'dtb> DeserializeProperty<'dtb> for Box<[RegBlock]> {
	fn deserialize(blob_prop: Property<'dtb>, cx: NodeContext<'_>) -> Result<Self> {
		prop_value::Reg::deserialize(blob_prop, cx).map(Box::from_iter)
	}
}

impl<'dtb> DeserializeNode<'dtb> for Vec<Item<'dtb>> {
	fn deserialize(blob_node: &Node<'dtb>, _cx: NodeContext<'_>) -> Result<(Self, Cursor)> {
		let mut items = blob_node.items();
		Ok(((&mut items).collect::<Vec<_>>()?, items.cursor))
	}
}

impl<'dtb> DeserializeNode<'dtb> for Box<[Item<'dtb>]> {
	fn deserialize(blob_node: &Node<'dtb>, _cx: NodeContext<'_>) -> Result<(Self, Cursor)> {
		let mut items = blob_node.items();
		Ok(((&mut items).collect::<Box<[_]>>()?, items.cursor))
	}
}

impl<'dtb, A: DeserializeNode<'dtb>> PushDeserializedNode<'dtb> for Vec<A> {
	type Node = A;

	fn push_node(&mut self, node: Self::Node, _cx: NodeContext<'_>) -> Result<()> {
		self.push(node);
		Ok(())
	}
}
