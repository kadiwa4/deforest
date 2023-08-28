use std::sync::OnceLock;

use devicetree::{
	alloc::DevicetreeBuilder,
	blob::{Cursor, Devicetree},
	fallible_iterator::FallibleIterator,
	prop_value::{self, RegBlock},
	DeserializeNode, DeserializeProperty, NodeContext,
};

const UNALIGNED_BLOB: &[u8] = include_bytes!("tree.dtb");
const FORMATTED: &str = include_str!("formatted.txt");

static DT: OnceLock<Box<Devicetree>> = OnceLock::new();

fn dt() -> &'static Devicetree {
	DT.get_or_init(|| Devicetree::from_unaligned(UNALIGNED_BLOB).unwrap())
}

#[test]
fn print() {
	let root_node = dt().root_node().unwrap();
	let formatted = format!("{root_node}\n");
	// std::fs::write("tests/formatted.txt", &formatted).unwrap();
	assert_eq!(formatted, FORMATTED);
}

#[test]
fn cpu_count() {
	let root_node = dt().root_node().unwrap();
	let cpus = root_node.get_child_strict("cpus").unwrap().unwrap();

	let cpus = cpus
		.children()
		.filter(|n| n.split_name().map(|(n, _)| n == "cpu"));
	let count = cpus.count().unwrap();
	assert_eq!(count, 4);
}

#[test]
fn paths() {
	const PATH0: &[&str] = &["soc", "rng"];
	const PATH1: &[&str; 3] = &["soc", "gpio@7e200000", "i2c0"];
	const PATH2: &str = "/soc/leds/act";

	let dt = dt();

	let root_node = dt.root_node().unwrap();
	let soc_node = root_node.get_child_strict("soc").unwrap().unwrap();
	let address_cells = soc_node.get_property("#address-cells").unwrap().unwrap();
	let prop_value::AddressCells(address_cells) = address_cells.contextless_parse().unwrap();
	let size_cells = soc_node.get_property("#size-cells").unwrap().unwrap();
	let prop_value::SizeCells(size_cells) = size_cells.contextless_parse().unwrap();

	let node0 = dt.get_node(PATH0).unwrap().unwrap();
	let prop0 = node0.get_property("reg").unwrap().unwrap();
	let mut cx = NodeContext::default();
	cx.address_cells = address_cells;
	cx.size_cells = size_cells;

	assert_eq!(
		prop_value::Reg::deserialize(prop0, cx)
			.unwrap()
			.collect::<Vec<_>>(),
		[RegBlock(0x7e104000, 0x10)]
	);

	let node1 = dt.get_node_strict(PATH1).unwrap().unwrap();
	let prop1 = node1.get_property("phandle").unwrap().unwrap();
	assert_eq!(prop1.value(), [0, 0, 0, 0x0a]);

	let node2 = dt.get_node_strict(PATH2).unwrap().unwrap();
	let prop2 = node2.get_property("label").unwrap().unwrap();
	assert_eq!(prop2.contextless_parse::<&str>(), Ok("led0"));
}

#[test]
fn multiple_children() {
	let clocks_node = dt().get_node_strict(&["clocks"]).unwrap().unwrap();
	let clock_cnt = clocks_node.get_children("clock").count().unwrap();
	assert_eq!(clock_cnt, 7);
	let iter = clocks_node.children().unwrap().filter_map(|n| {
		n.get_property("clock-output-names")
			.unwrap()
			.map(|p| p.contextless_parse::<&str>().unwrap())
	});
	assert_eq!(
		iter.collect::<Vec<_>>(),
		["core", "mmc", "uart0_pclk", "apb_pclk", "pwm", "osc"]
	);

	let mut iter = clocks_node
		.get_children("thermal")
		.iterator()
		.map(|res| res.unwrap());
	assert!(iter.next().is_none());
}

#[test]
fn derive_self_fields() {
	#[derive(Default, DeserializeNode)]
	struct DmaNode<'dtb> {
		#[dt_self(start_cursor)]
		start_cursor: Option<Cursor>,
		#[dt_self(name)]
		name: &'dtb str,
		#[dt_self(unit_address)]
		unit_address: Option<String>,
	}

	let dma_node = dt().get_node(&["soc", "dma"]).unwrap().unwrap();
	let cursor = dma_node.start_cursor();
	let dma_node = DmaNode::deserialize(&dma_node, NodeContext::default())
		.unwrap()
		.0;
	assert_eq!(dma_node.start_cursor, Some(cursor));
	assert_eq!(dma_node.name, "dma@7e007000");
	assert_eq!(dma_node.unit_address.unwrap(), "7e007000");
}

#[test]
fn build() {
	let original = dt();
	let mut builder = DevicetreeBuilder::default();
	builder.boot_core_id = original.boot_core_id();
	let reserve_entries: Vec<_> = original.reserve_entries().unwrap().collect().unwrap();
	builder.reserve_entries = &reserve_entries;
	builder.struct_blob = Some(original.struct_blob());
	builder.strings_blob = Some(original.strings_blob());
	let clone = builder.build().unwrap();
	assert_eq!(original.blob(), clone.blob());
}
