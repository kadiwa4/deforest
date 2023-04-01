use devicetree::{
	blob::{Cursor, CursorRange},
	prop_value, DeserializeNode,
};

#[derive(Default, DeserializeNode)]
struct RootNode<'dtb> {
	address_cells: prop_value::AddressCells,
	size_cells: prop_value::SizeCells,
	model: &'dtb str,
	compatible: prop_value::Strings<'dtb>,
	serial_number: Option<&'dtb str>,
	chassis_type: Option<&'dtb str>,
	#[dt_child]
	aliases: Option<Cursor>,
	#[dt_children]
	memory: CursorRange<'dtb>,
	#[dt_child]
	reserved_memory: Option<ReservedMemoryNode<'dtb>>,
	#[dt_child]
	chosen: Option<ChosenNode<'dtb>>,
	#[dt_child]
	cpus: Option<CpusNode<'dtb>>,

	#[dt_child]
	soc: Option<Cursor>,
}

#[derive(Default, DeserializeNode)]
struct MemoryNode<'dtb> {
	device_type: &'dtb str,
	reg: Option<prop_value::Reg<'dtb>>,
	initial_mapped_area: Option<&'dtb [u32]>,
	hotpluggable: Option<()>,
}

#[derive(Default, DeserializeNode)]
struct ReservedMemoryNode<'dtb> {
	address_cells: prop_value::AddressCells,
	size_cells: prop_value::SizeCells,
	ranges: &'dtb [u32],
}

#[derive(Default, DeserializeNode)]
struct ReservedMemoryChild<'dtb> {
	reg: Option<prop_value::Reg<'dtb>>,
	size: Option<&'dtb [u32]>,
	alignment: Option<&'dtb [u32]>,
	alloc_ranges: Option<&'dtb [u32]>,
	compatible: Option<prop_value::Strings<'dtb>>,
	no_map: Option<()>,
	reusable: Option<()>,
}

#[derive(Default, DeserializeNode)]
struct ChosenNode<'dtb> {
	bootargs: Option<&'dtb str>,
	stdout_path: Option<&'dtb str>,
	stdin_path: Option<&'dtb str>,
}

#[derive(Default, DeserializeNode)]
struct CpusNode<'dtb> {
	address_cells: prop_value::AddressCells,
	size_cells: prop_value::SizeCells,
	#[dt_children]
	cpu: CursorRange<'dtb>,
}

#[derive(Default, DeserializeNode)]
struct CpuNode<'dtb> {
	device_type: &'dtb str,
	reg: Option<prop_value::Reg<'dtb>>,
	clock_frequency: &'dtb [u32],
	timebase_frequency: &'dtb [u32],
	status: Option<&'dtb str>,
	enable_method: Option<prop_value::Strings<'dtb>>,
	cpu_release_addr: Option<u64>,
	// // power ISA properties
	// power_isa_version: Option<&'dtb str>,
	// cache_op_block_size: Option<u32>,
	// reservation_granule_size: Option<u32>,
	// mmu_type: Option<&'dtb str>,

	// // power ISA translate look-aside buffer properties
	// tlb_split: Option<()>,
	// tlb_size: Option<u32>,
	// tlb_sets: Option<u32>,
	// d_tlb_size: Option<u32>,
	// d_tlb_sets: Option<u32>,
	// i_tlb_size: Option<u32>,
	// i_tlb_sets: Option<u32>,

	// // power ISA cache properties
	// cache_unified: Option<()>,
	// cache_size: Option<u32>,
	// cache_sets: Option<u32>,
	// cache_block_size: Option<u32>,
	// cache_line_size: Option<u32>,
	// i_cache_size: Option<u32>,
	// i_cache_sets: Option<u32>,
	// i_cache_block_size: Option<u32>,
	// i_cache_line_size: Option<u32>,
	// d_cache_size: Option<u32>,
	// d_cache_sets: Option<u32>,
	// d_cache_block_size: Option<u32>,
	// d_cache_line_size: Option<u32>,
	// next_level_cache: Option<Phandle>,
}

// #[derive(Default, DeserializeNode)]
// struct MlAndSharedCacheNode<'dtb> {
// 	compatible: &'dtb str,
// 	cache_level: u32,
// }
