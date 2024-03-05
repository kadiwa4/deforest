//! Features depending on memory allocation.

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
	DeserializeNode, DeserializeProperty, Error, MemReserveEntry, NodeContext, Path,
	PushDeserializedNode, Result,
};

/// Starting point for constructing a [`Devicetree`] yourself.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct DevicetreeBuilder<'a> {
	/// Defaults to 0.
	pub boot_core_id: u32,
	/// Defaults to an empty slice.
	pub mem_reserve_entries: &'a [MemReserveEntry],
	/// Blob of the struct block.
	pub struct_blob: &'a [u32],
	/// Blob of the strings block.
	pub strings_blob: &'a [u8],
}

impl<'a> DevicetreeBuilder<'a> {
	/// Constructs a new builder.
	pub const fn new(struct_blob: &'a [u32], strings_blob: &'a [u8]) -> Self {
		Self {
			boot_core_id: 0,
			mem_reserve_entries: &[],
			struct_blob,
			strings_blob,
		}
	}

	/// Constructs the devicetree.
	///
	/// # Errors
	/// Throws [`Error::DevicetreeTooLarge`] or runs out of memory if it is too
	/// large.
	pub fn build(&self) -> Result<Box<Devicetree>> {
		let struct_offset = blob::Header::SIZE
			+ size_of_val(self.mem_reserve_entries)
			+ size_of::<MemReserveEntry>();
		let strings_offset = struct_offset + size_of_val(self.struct_blob);
		let size = strings_offset + self.strings_blob.len();

		let capacity = (size + blob::DTB_OPTIMAL_ALIGN - 1) / blob::DTB_OPTIMAL_ALIGN;
		let size = u32::try_from(size).ok().ok_or(Error::DevicetreeTooLarge)?;

		let mut blob: Vec<u64> = Vec::with_capacity(capacity);
		blob.extend::<[u64; blob::Header::SIZE / blob::DTB_OPTIMAL_ALIGN]>(zerocopy::transmute!(
			blob::Header {
				magic: blob::DTB_MAGIC,
				totalsize: size.to_be(),
				off_dt_struct: (struct_offset as u32).to_be(),
				off_dt_strings: (strings_offset as u32).to_be(),
				off_mem_rsvmap: (blob::Header::SIZE as u32).to_be(),
				version: 17_u32.to_be(),
				last_comp_version: blob::LAST_COMPATIBLE_VERSION.to_be(),
				boot_cpuid_phys: self.boot_core_id.to_be(),
				size_dt_strings: (self.strings_blob.len() as u32).to_be(),
				size_dt_struct: (size_of_val(self.struct_blob) as u32).to_be(),
			}
		));
		blob.extend(self.mem_reserve_entries.iter().flat_map(
			|e| -> [u64; blob::RawReserveEntry::FIELD_COUNT] {
				zerocopy::transmute!(blob::RawReserveEntry {
					address: e.address.to_be(),
					size: e.size.to_be(),
				})
			},
		));
		unsafe {
			blob.as_mut_ptr().add(capacity - 1).write(0);
		}
		blob.extend([0; blob::RawReserveEntry::FIELD_COUNT]);

		// Safety: after all of the requested capacity is filled with data, len can be set to the capacity.
		// the constructed Devicetree would pass all of the checks, so we can skip them
		unsafe {
			let ptr = blob.as_mut_ptr() as *mut u8;
			core::ptr::copy_nonoverlapping(
				self.struct_blob.as_ptr(),
				ptr.add(struct_offset) as *mut u32,
				self.struct_blob.len(),
			);
			core::ptr::copy_nonoverlapping(
				self.strings_blob.as_ptr(),
				ptr.add(strings_offset),
				self.strings_blob.len(),
			);
			blob.set_len(capacity);

			Ok(Devicetree::from_box_unchecked(blob.into_boxed_slice()))
		}
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
		<&[u32]>::deserialize(blob_prop, cx).map(Self::from)
	}
}

impl<'dtb> DeserializeProperty<'dtb> for String {
	fn deserialize(blob_prop: Property<'dtb>, cx: NodeContext<'_>) -> Result<Self> {
		<&str>::deserialize(blob_prop, cx).map(Self::from)
	}
}

impl<'dtb> DeserializeProperty<'dtb> for Box<str> {
	fn deserialize(blob_prop: Property<'dtb>, cx: NodeContext<'_>) -> Result<Self> {
		<&str>::deserialize(blob_prop, cx).map(Self::from)
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
		prop_value::Reg::deserialize(blob_prop, cx).map(Self::from_iter)
	}
}

impl<'dtb> DeserializeProperty<'dtb> for Box<[RegBlock]> {
	fn deserialize(blob_prop: Property<'dtb>, cx: NodeContext<'_>) -> Result<Self> {
		prop_value::Reg::deserialize(blob_prop, cx).map(Self::from_iter)
	}
}

impl<'dtb> DeserializeNode<'dtb> for Vec<Item<'dtb>> {
	fn deserialize(blob_node: &Node<'dtb>, _cx: NodeContext<'_>) -> Result<(Self, Cursor)> {
		let mut items = blob_node.items();
		Ok(((&mut items).collect::<Self>()?, items.cursor))
	}
}

impl<'dtb> DeserializeNode<'dtb> for Box<[Item<'dtb>]> {
	fn deserialize(blob_node: &Node<'dtb>, _cx: NodeContext<'_>) -> Result<(Self, Cursor)> {
		let mut items = blob_node.items();
		Ok(((&mut items).collect::<Self>()?, items.cursor))
	}
}

impl<'dtb, T: DeserializeNode<'dtb>> PushDeserializedNode<'dtb> for Vec<T> {
	type Node = T;

	fn push_node(&mut self, node: Self::Node, _cx: NodeContext<'_>) -> Result<()> {
		self.push(node);
		Ok(())
	}
}
