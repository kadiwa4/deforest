use devicetree::{
	blob::{CursorRange, Devicetree},
	fallible_iterator::FallibleIterator,
	prop_value::{self, RegBlock},
	DeserializeProperty, NodeContext,
};
use std::iter;

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
		let root_node = dt.root_node().unwrap();
		let formatted = format!("{root_node}\n");
		// std::fs::write("tests/formatted.txt", &formatted).unwrap();
		assert_eq!(formatted, FORMATTED);
	});
}

#[test]
fn cpu_count() {
	BLOB.with(|blob| {
		let dt = Devicetree::from_slice(blob).unwrap();
		let root_node = dt.root_node().unwrap();
		let cpus = root_node.get_child_strict("cpus").unwrap().unwrap();

		let cpus = cpus
			.children()
			.filter(|n| n.split_name().map(|(n, _)| n == "cpu"));
		let count = cpus.count().unwrap();
		assert_eq!(count, 4);
	});
}

#[test]
fn paths() {
	const PATH0: &[&str] = &["soc", "rng"];
	const PATH1: &[&str; 3] = &["soc", "gpio@7e200000", "i2c0"];
	const PATH2: &str = "/soc/leds/act";

	BLOB.with(|blob| {
		let dt = Devicetree::from_slice(blob).unwrap();

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
	});
}

#[test]
fn multiple_children() {
	BLOB.with(|blob| {
		let dt = Devicetree::from_slice(blob).unwrap();

		let clocks_node = dt.get_node_strict(&["clocks"]).unwrap().unwrap();
		let range: CursorRange<'_> = clocks_node
			.get_children("clock")
			.iterator()
			.map(|res| res.unwrap())
			.collect();
		assert!(!range.is_single());
		let mut iter = dt.nodes_in_range(range);
		let iter = iter::from_fn(|| {
			iter.walk_next(|n| Ok((n.clone(), n.end_cursor()?)))
				.unwrap()
		})
		.filter_map(|n| {
			n.get_property("clock-output-names")
				.unwrap()
				.map(|p| p.contextless_parse::<&str>().unwrap())
		});
		assert_eq!(
			iter.collect::<Vec<_>>(),
			["core", "mmc", "uart0_pclk", "apb_pclk", "pwm", "osc"]
		);

		let range: CursorRange<'_> = clocks_node
			.get_children("thermal")
			.iterator()
			.map(|res| res.unwrap())
			.collect();
		assert_eq!(range, CursorRange::EMPTY);
	})
}
