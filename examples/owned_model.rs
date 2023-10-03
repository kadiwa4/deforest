use devicetree::{
	blob::Cursor,
	prop_value::{self, RegBlock},
	DeserializeNode,
};

#[derive(Debug, Default, DeserializeNode)]
struct RootNode {
	address_cells: prop_value::AddressCells,
	size_cells: prop_value::SizeCells,
	model: String,
	compatible: Vec<String>,
	serial_number: Option<String>,
	chassis_type: Option<String>,
	#[dt(child)]
	aliases: Option<Cursor>,
	#[dt(children)]
	memory: Vec<MemoryNode>,
	#[dt(child)]
	reserved_memory: Option<ReservedMemoryNode>,
	#[dt(child)]
	chosen: Option<ChosenNode>,
	#[dt(child)]
	cpus: Option<CpusNode>,

	#[dt(children(rest))]
	rest: Vec<Cursor>,
}

#[derive(Debug, Default, DeserializeNode)]
struct MemoryNode {
	device_type: Option<prop_value::DeviceTypeMemory>,
	reg: Option<Vec<RegBlock>>,
	initial_mapped_area: Option<prop_value::InitialMappedArea>,
	hotpluggable: bool,
}

#[derive(Debug, Default, DeserializeNode)]
struct ReservedMemoryNode {
	address_cells: prop_value::AddressCells,
	size_cells: prop_value::SizeCells,
	ranges: Vec<u32>,
}

#[derive(Debug, Default, DeserializeNode)]
struct ReservedMemoryChild {
	reg: Option<Vec<RegBlock>>,
	size: Option<Vec<u32>>,
	alignment: Option<Vec<u32>>,
	alloc_ranges: Option<Vec<u32>>,
	compatible: Option<Vec<String>>,
	no_map: bool,
	reusable: bool,
}

#[derive(Debug, Default, DeserializeNode)]
struct ChosenNode {
	bootargs: Option<String>,
	stdout_path: Option<String>,
	stdin_path: Option<String>,
}

#[derive(Debug, Default, DeserializeNode)]
struct CpusNode {
	address_cells: prop_value::AddressCells,
	size_cells: prop_value::SizeCells,
	#[dt(children)]
	cpu: Vec<CpuNode>,
}

#[derive(Debug, Default, DeserializeNode)]
struct CpuNode {
	device_type: Option<prop_value::DeviceTypeCpu>,
	reg: Option<Vec<RegBlock>>,
	clock_frequency: prop_value::SmallU64,
	timebase_frequency: prop_value::SmallU64,
	status: Option<String>,
	enable_method: Option<Vec<String>>,
	cpu_release_addr: Option<u64>,
	// // power ISA properties
	// power_isa_version: Option<String>,
	// cache_op_block_size: Option<u32>,
	// reservation_granule_size: Option<u32>,
	// mmu_type: Option<String>,

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

// #[derive(Debug, Default, DeserializeNode)]
// struct MlAndSharedCacheNode {
// 	compatible: String,
// 	cache_level: u32,
// }

#[test]
fn deserialize() {
	const UNALIGNED_BLOB: &[u8] = include_bytes!("../tests/tree.dtb");

	let dt = devicetree::blob::Devicetree::from_unaligned(UNALIGNED_BLOB).unwrap();
	let root_node: RootNode = dt.parse_root().unwrap();
	let cpus = root_node.cpus.unwrap().cpu;
	assert_eq!(cpus.len(), 4);
	assert!(cpus.iter().all(|c| c.device_type.is_some()));
	assert!(root_node.memory[0].device_type.is_some());
}
