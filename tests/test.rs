use devicetree::{
	blob::{Devicetree, Node, Property},
	fallible_iterator::FallibleIterator,
	prop_value, DeserializeProperty, NodeContext,
};

const UNALIGNED_BLOB: &[u8] = include_bytes!("tree.dtb");
const FORMATTED: &str = include_str!("formatted.txt");

thread_local! {
	static BLOB: Vec<u64> = {
		// Devicetree::from_unaligned should be used here, but it might not be available
		assert_eq!(UNALIGNED_BLOB.len() % 8, 0);
		let mut aligned_blob: Vec<u64> = Vec::with_capacity(UNALIGNED_BLOB.len() / 8);
		unsafe {
			core::ptr::copy_nonoverlapping(
				UNALIGNED_BLOB.as_ptr(),
				aligned_blob.as_mut_ptr() as *mut u8,
				UNALIGNED_BLOB.len(),
			);
			aligned_blob.set_len(UNALIGNED_BLOB.len() / 8);
		}

		aligned_blob
	};
}

#[test]
fn print() {
	BLOB.with(|blob| {
		let dt = Devicetree::from_slice(blob).unwrap();
		let root = dt.root_node().unwrap();
		let formatted = format!("{root}\n");
		std::fs::write("tests/formatted.txt", &formatted).unwrap();
		assert_eq!(formatted, FORMATTED);
	});
}

#[test]
fn cpu_count() {
	BLOB.with(|blob| {
		let dt = Devicetree::from_slice(blob).unwrap();
		let root = dt.root_node().unwrap();
		let cpus = root
			.children()
			.find_by_name(|n| n == "cpus")
			.unwrap()
			.unwrap();

		let cpus = cpus
			.children()
			.filter(|n| n.split_name().map(|(n, _)| n == "cpu"));
		let count = cpus.count().unwrap();
		assert_eq!(count, 4);
	});
}

#[test]
fn paths() {
	fn get_property<'dtb>(node: &Node<'dtb>, name: &str) -> Option<Property<'dtb>> {
		node.properties().find_by_name(|n| n == name).unwrap()
	}

	const PATH0: &[&str] = &["soc", "rng"];
	const PATH1: &[&str] = &["soc", "gpio@7e200000", "i2c0"];
	const PATH2: &str = "/soc/leds/act";

	BLOB.with(|blob| {
		let dt = Devicetree::from_slice(blob).unwrap();

		let soc_node = dt
			.root_node()
			.unwrap()
			.children()
			.find_by_name(|n| n == "soc")
			.unwrap()
			.unwrap();
		let address_cells = get_property(&soc_node, "#address-cells").unwrap();
		let prop_value::AddressCells(address_cells) = address_cells.contextless_parse().unwrap();
		let size_cells = get_property(&soc_node, "#size-cells").unwrap();
		let prop_value::SizeCells(size_cells) = size_cells.contextless_parse().unwrap();

		let node0 = dt.get_node(PATH0).unwrap().unwrap();
		let prop0 = get_property(&node0, "reg").unwrap();
		let mut cx = NodeContext::default();
		cx.address_cells = address_cells;
		cx.size_cells = size_cells;

		assert_eq!(
			prop_value::Reg::deserialize(prop0, &cx)
				.unwrap()
				.collect::<Vec<_>>(),
			[(0x7e104000, 0x10)]
		);

		let node1 = dt.get_node_strict(PATH1).unwrap().unwrap();
		let prop1 = get_property(&node1, "phandle").unwrap();
		assert_eq!(*prop1.value(), [0, 0, 0, 0x0a]);

		let node2 = dt.get_node_strict(PATH2).unwrap().unwrap();
		let prop2 = get_property(&node2, "label").unwrap();
		assert_eq!(prop2.contextless_parse::<&str>(), Ok("led0"));
	});
}
