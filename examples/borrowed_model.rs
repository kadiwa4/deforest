use deforest::{
	blob::{node::NamedRange, Cursor},
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
	#[dt(child)]
	aliases: Option<Cursor>,
	#[dt(children)]
	memory: NamedRange<'dtb>,
	#[dt(child)]
	reserved_memory: Option<ReservedMemoryNode<'dtb>>,
	#[dt(child)]
	chosen: Option<ChosenNode<'dtb>>,
	#[dt(child)]
	cpus: Option<CpusNode<'dtb>>,
}

#[derive(Default, DeserializeNode)]
struct MemoryNode<'dtb> {
	device_type: Option<prop_value::DeviceTypeMemory>,
	reg: Option<prop_value::Reg<'dtb>>,
	initial_mapped_area: Option<prop_value::InitialMappedArea>,
	hotpluggable: bool,
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
	no_map: bool,
	reusable: bool,
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
	#[dt(children)]
	cpu: NamedRange<'dtb>,
}

#[derive(Default, DeserializeNode)]
struct CpuNode<'dtb> {
	device_type: Option<prop_value::DeviceTypeCpu>,
	reg: Option<prop_value::Reg<'dtb>>,
	clock_frequency: prop_value::SmallU64,
	timebase_frequency: prop_value::SmallU64,
	status: Option<&'dtb str>,
	enable_method: Option<prop_value::Strings<'dtb>>,
	cpu_release_addr: Option<u64>,
	// // power ISA properties
	// power_isa_version: Option<&'dtb str>,
	// cache_op_block_size: Option<u32>,
	// reservation_granule_size: Option<u32>,
	// mmu_type: Option<&'dtb str>,

	// // power ISA translate look-aside buffer properties
	// tlb_split: bool,
	// tlb_size: Option<u32>,
	// tlb_sets: Option<u32>,
	// d_tlb_size: Option<u32>,
	// d_tlb_sets: Option<u32>,
	// i_tlb_size: Option<u32>,
	// i_tlb_sets: Option<u32>,

	// // power ISA cache properties
	// cache_unified: bool,
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
