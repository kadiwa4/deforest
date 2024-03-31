use std::{fmt::Debug, ptr::NonNull, sync::OnceLock};

use deforest::{
	alloc::DevicetreeBuilder,
	blob::Devicetree,
	fallible_iterator::FallibleIterator,
	prop_value::{self, RegBlock},
	BlobError, DeserializeProperty, Error, NodeContext,
};
use zerocopy::{AsBytes, FromBytes, FromZeroes};

const UNALIGNED_BLOB: &[u8] = include_bytes!("tree.dtb");
const FORMATTED: &str = include_str!("formatted.txt");

macro_rules! assert_matches {
    ($left:expr, $($pattern:pat_param)|+ $(if $guard:expr)?) => {
        match $left {
            $( $pattern )|+ $( if $guard )? => {}
            ref left_val => assert_matches_failed(
				left_val,
				stringify!($($pattern)|+ $(if $guard)?),
			),
        }
    };
}

#[track_caller]
fn assert_matches_failed<T: ?Sized + Debug>(left: &T, right: &str) -> ! {
	panic!(
		"\
assertion `left matches right` failed
left: {left:?}
right: {right}"
	);
}

#[derive(AsBytes, FromBytes, FromZeroes)]
#[repr(C)]
struct Header {
	magic: [u8; 4],
	totalsize: u32,
	off_dt_struct: u32,
	off_dt_strings: u32,
	off_mem_rsvmap: u32,
	version: u32,
	last_comp_version: u32,
	boot_cpuid_phys: u32,
	size_dt_strings: u32,
	size_dt_struct: u32,
}

impl Header {
	const EMPTY: Self = Self {
		magic: deforest::blob::DTB_MAGIC,
		totalsize: 0x48_u32.to_be(),
		off_dt_struct: 0x38_u32.to_be(),
		off_dt_strings: 0x48_u32.to_be(),
		off_mem_rsvmap: 0x28_u32.to_be(),
		version: 17_u32.to_be(),
		last_comp_version: 16_u32.to_be(),
		boot_cpuid_phys: 0,
		size_dt_strings: 0,
		size_dt_struct: 0x10_u32.to_be(),
	};
}

/// Zero-initialized header followed by an empty mem-reserve array and these
/// struct tokens:
///
/// ```text
/// BeginNode { c"" }, EndNode, End
/// ```
const EMPTY_BUF: [u64; 9] = [
	0,
	0,
	0,
	0,
	0,
	0,
	0,
	0x0000_0001_0000_0000_u64.to_be(),
	0x0000_0002_0000_0009_u64.to_be(),
];

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
fn header() {
	let dt = dt();
	assert_eq!(dt.exact_size(), 0x2f3c);
	assert_eq!(dt.version(), 0x11);
	assert_eq!(dt.last_comp_version(), 0x10);
	assert_eq!(dt.boot_core_id(), 0);

	assert_eq!(dt.mem_reserve_entries().unwrap().count().unwrap(), 0);
}

#[test]
fn get_blob() {
	let dt = dt();
	assert_eq!(dt.blob().as_bytes(), dt.blob_u8());
	assert_eq!(dt.blob_u32().as_bytes(), dt.blob_u8());
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
	let dt = dt();

	let root_node = dt.root_node().unwrap();
	assert_eq!(
		dt.get_node("/").unwrap().unwrap().source_name().unwrap(),
		"/"
	);
	assert_eq!(
		dt.get_node_strict("/")
			.unwrap()
			.unwrap()
			.source_name()
			.unwrap(),
		"/"
	);
	assert_eq!(
		dt.get_node::<[&str]>(&[])
			.unwrap()
			.unwrap()
			.source_name()
			.unwrap(),
		"/"
	);
	assert_eq!(
		dt.get_node_strict::<[&str]>(&[])
			.unwrap()
			.unwrap()
			.source_name()
			.unwrap(),
		"/"
	);

	assert_matches!(dt.get_node(&["leds"]).unwrap(), None);
	assert_matches!(dt.get_node_strict(&["leds"]).unwrap(), None);

	let soc_node = root_node.get_child_strict("soc").unwrap().unwrap();
	assert_matches!(soc_node.get_property("status").unwrap(), None);

	let address_cells = soc_node.get_property("#address-cells").unwrap().unwrap();
	let prop_value::AddressCells(address_cells) = address_cells.contextless_parse().unwrap();
	let size_cells = soc_node.get_property("#size-cells").unwrap().unwrap();
	let prop_value::SizeCells(size_cells) = size_cells.contextless_parse().unwrap();

	let node0 = dt.get_node(&["soc", "rng"]).unwrap().unwrap();
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

	let node1 = dt
		.get_node_strict(&["soc", "gpio@7e200000", "i2c0"])
		.unwrap()
		.unwrap();
	let prop1 = node1.get_property("phandle").unwrap().unwrap();
	assert_eq!(prop1.value(), [0, 0, 0, 0x0a]);

	let node2 = dt.get_node_strict("/soc/leds/act").unwrap().unwrap();
	let prop2 = node2.get_property("label").unwrap().unwrap();
	assert_eq!(prop2.contextless_parse::<&str>(), Ok("led0"));
}

#[test]
fn err_paths() {
	let dt = dt();

	assert_matches!(dt.get_node(""), Err(Error::InvalidPath));
	assert_matches!(dt.get_node_strict(""), Err(Error::InvalidPath));
	assert_matches!(dt.get_node(&["/"]), Ok(None));
	assert_matches!(dt.get_node_strict(&["/"]), Ok(None));
	assert_matches!(dt.get_node(&[""]), Ok(None));
	assert_matches!(dt.get_node_strict(&[""]), Ok(None));
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
	assert_matches!(iter.next(), None);
}

#[test]
fn build() {
	let original = dt();
	let mut builder = DevicetreeBuilder::new(original.struct_blob(), original.strings_blob());
	builder.boot_core_id = original.boot_core_id();
	let mem_reserve_entries: Vec<_> = original.mem_reserve_entries().unwrap().collect().unwrap();
	builder.mem_reserve_entries = &mem_reserve_entries;
	let clone = builder.build().unwrap();
	assert_eq!(original.blob(), clone.blob());
}

#[test]
#[cfg_attr(miri, ignore)] // miri warns on pointer provenance violations
fn from_ptr() {
	let original = dt();
	let from_ptr = unsafe { Devicetree::from_ptr(NonNull::from(original.blob()).cast()) }.unwrap();
	assert_eq!(original.blob().len(), from_ptr.blob().len());
}

macro_rules! blob {
	{
		buf: $buf_init:expr,
		header: { $($field:ident: $val:expr),* $(,)? } $(,)?
	} => {{
		let mut buf = $buf_init;
		let header = Header::mut_from_prefix(buf.as_bytes_mut()).unwrap();
		*header = Header { $($field: $val,)* ..Header::EMPTY };
		buf
	}};
}

fn all_safe_ctors_return(blob: &[u64], err: Option<BlobError>) {
	assert_eq!(Devicetree::from_slice(blob).err(), err);
	assert_eq!(Devicetree::from_unaligned(blob.as_bytes()).err(), err);
	assert_eq!(Devicetree::from_vec(blob.to_vec()).err(), err);
}

fn all_ctors_return(blob: &[u64], err: Option<BlobError>) {
	#[cfg(not(miri))]
	assert_eq!(
		unsafe { Devicetree::from_ptr(NonNull::from(blob).cast()) }.err(),
		err
	);
	all_safe_ctors_return(blob, err);
}

#[test]
fn empty() {
	all_safe_ctors_return(&[], Some(BlobError::UnexpectedEnd));
	all_safe_ctors_return(&[0], Some(BlobError::UnexpectedEnd));

	let valid_empty = blob! { buf: EMPTY_BUF, header: {} };
	all_safe_ctors_return(&valid_empty, None);
	let dt = Devicetree::from_slice(&valid_empty).unwrap();
	assert_matches!(dt.root_node().unwrap().items().next().unwrap(), None);
}

#[test]
fn err_invalid_header() {
	all_ctors_return(
		&blob! {
			buf: EMPTY_BUF,
			header: { magic: [0; 4], last_comp_version: 0x11 },
		},
		Some(BlobError::NoMagicSignature),
	);
	all_ctors_return(
		&blob! {
			buf: EMPTY_BUF,
			header: { last_comp_version: 0x11 },
		},
		Some(BlobError::IncompatibleVersion),
	);
	all_safe_ctors_return(
		&blob! { buf: EMPTY_BUF, header: {} }[..5],
		Some(BlobError::InvalidTotalsize),
	);
	all_ctors_return(
		&blob! {
			buf: EMPTY_BUF,
			header: { totalsize: 0x20_u32.to_be() },
		},
		Some(BlobError::InvalidTotalsize),
	);
}

#[test]
fn err_invalid_blocks() {
	// struct
	all_ctors_return(
		&blob! {
			buf: EMPTY_BUF,
			header: { off_dt_struct: 0x3a_u32.to_be(), size_dt_struct: 8_u32.to_be() },
		},
		Some(BlobError::UnalignedBlock),
	);
	all_ctors_return(
		&blob! {
			buf: EMPTY_BUF,
			header: { size_dt_struct: 0x0e_u32.to_be() },
		},
		Some(BlobError::UnalignedBlock),
	);
	all_ctors_return(
		&blob! {
			buf: EMPTY_BUF,
			header: { off_dt_struct: 0x40_u32.to_be() },
		},
		Some(BlobError::BlockOutOfBounds),
	);
	all_ctors_return(
		&blob! {
			buf: EMPTY_BUF,
			header: { size_dt_struct: 0x18_u32.to_be() },
		},
		Some(BlobError::BlockOutOfBounds),
	);
	all_ctors_return(
		&blob! {
			buf: EMPTY_BUF,
			header: { off_dt_struct: 0x8000_0038_u32.to_be(), size_dt_struct: 0x8000_0010_u32.to_be() },
		},
		Some(BlobError::BlockOutOfBounds),
	);

	// strings
	all_ctors_return(
		&blob! {
			buf: EMPTY_BUF,
			header: { off_dt_strings: 0x49_u32.to_be() },
		},
		Some(BlobError::BlockOutOfBounds),
	);
	all_ctors_return(
		&blob! {
			buf: EMPTY_BUF,
			header: { size_dt_strings: 1_u32.to_be() },
		},
		Some(BlobError::BlockOutOfBounds),
	);
	all_ctors_return(
		&blob! {
			buf: EMPTY_BUF,
			header: { off_dt_strings: 0x8000_0048_u32.to_be(), size_dt_strings: 0x8000_0000_u32.to_be() },
		},
		Some(BlobError::BlockOutOfBounds),
	);

	// mem reservation
	assert_matches!(
		Devicetree::from_slice(&blob! {
			buf: EMPTY_BUF,
			header: { off_mem_rsvmap: 0x2c_u32.to_be() },
		})
		.unwrap()
		.mem_reserve_entries(),
		Err(BlobError::UnalignedBlock)
	);
	assert_matches!(
		Devicetree::from_slice(&blob! {
			buf: EMPTY_BUF,
			header: { off_mem_rsvmap: 0x8000_0028_u32.to_be() },
		})
		.unwrap()
		.mem_reserve_entries(),
		Err(BlobError::BlockOutOfBounds)
	);
}

#[cfg(feature = "derive")]
mod derive {
	use super::*;
	use deforest::{blob::Cursor, DeserializeNode};

	#[test]
	fn parse_root() {
		#[derive(Default, DeserializeNode)]
		struct RootNode<'dtb> {
			#[dt(name)]
			name: &'dtb str,
			model: &'dtb str,
			#[dt(child)]
			chosen: Option<ChosenNode<'dtb>>,
		}

		#[derive(Default, DeserializeNode)]
		struct ChosenNode<'dtb> {
			bootargs: &'dtb str,
		}

		let dt = dt();
		let root_blob_node = dt.root_node().unwrap();
		let root_node0: RootNode<'_> = dt.parse_root().unwrap();
		let (root_node1, _) =
			RootNode::deserialize(&root_blob_node, NodeContext::default()).unwrap();
		assert_eq!(root_node0.name, "");
		assert_eq!(root_node0.model, "Raspberry Pi 2 Model B");
		assert_eq!(root_node1.chosen.unwrap().bootargs, "");
	}

	#[test]
	fn self_fields() {
		#[derive(Default, DeserializeNode)]
		struct DmaNode<'dtb> {
			#[dt(start_cursor)]
			start_cursor: Option<Cursor>,
			#[dt(name)]
			name: &'dtb str,
			#[dt(unit_address)]
			unit_address: Option<String>,
		}

		let dma_node = dt().get_node(&["soc", "dma"]).unwrap().unwrap();
		let cursor = dma_node.start_cursor();
		let (dma_node, _) = DmaNode::deserialize(&dma_node, NodeContext::default()).unwrap();
		assert_eq!(dma_node.start_cursor, Some(cursor));
		assert_eq!(dma_node.name, "dma@7e007000");
		assert_eq!(dma_node.unit_address.unwrap(), "7e007000");
	}

	#[test]
	fn parse_reg_value() {
		#[derive(Default, DeserializeNode)]
		struct SocNode<'dtb> {
			#[dt(child)]
			spi: SpiNode<'dtb>,
		}

		#[derive(Default, DeserializeNode)]
		struct SpiNode<'dtb> {
			reg: prop_value::Reg<'dtb>,
		}

		let soc_node = dt().get_node_strict(&["soc"]).unwrap().unwrap();
		let (soc_node, _) = SocNode::deserialize(&soc_node, NodeContext::default()).unwrap();
		let mut reg = soc_node.spi.reg;
		assert_eq!(reg.next(), Some(RegBlock(0x7e20_4000, 0x1000)));
		assert!(reg.next().is_none());
	}
}
