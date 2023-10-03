# Rust crate `deforest`

Efficient `#![no_std]` parser for devicetree blobs compliant (hopefully) with version 0.4 of [the specification][spec].

This is in an early stage of development. Use [`fdt-rs`](https://lib.rs/crates/fdt-rs) instead.

The crate tries to be efficient by avoiding allocations (it can be used without `alloc`), but I have no realistic benchmarks and the interface isn't the most ergonomic.

[spec]: https://www.devicetree.org/specifications

## Competitor crates
- [`device_tree`](https://github.com/mbr/device_tree-rs)
- [`devicetree`](https://github.com/duanyu-yu/DeviceTree)
- [`devicetree-tool`](https://github.com/michael2012z/devicetree-tool) (not very similar in what it's trying to achieve)
- [`dtb`](https://github.com/ababo/dtb)
- [`dtb_parser`](https://github.com/d3ara1n/dtb_parser)
- [`dtb-walker`](https://github.com/YdrMaster/dtb-walker)
- [`fdt`](https://github.com/repnop/fdt)
- [`fdt-rs`](https://github.com/rs-embedded/fdt-rs)
- [`serde-device-tree`](https://github.com/rustsbi/serde-device-tree)

Some things I didn't like about some of them (I never intentionally searched for UB in any of the crates):

device_tree:
- depends on `std`

devicetree:
- is nightly-only
- is somewhat slow
- has UB (`static mut` [here](https://github.com/duanyu-yu/DeviceTree/blob/main/src/tree/node.rs#L27))
- can't do simple things like getting a property's raw value (unless it's a string list)

devicetree-tool:
- depends on `std`
- no error handling, always panics
- prints a ton of debug output to stdout with no way to disable it, making it unbearably slow

dtb:
- very little abstraction
- has a small case of UB (pointer [here](https://github.com/ababo/dtb/blob/master/src/reader.rs#L314) might not point to a valid `Header`)

dtb_parser: doesn't work

dtb-walker:
- interface for "walking" is not great
- has UB (alignment isn't checked [here](https://github.com/YdrMaster/dtb-walker/blob/main/src/lib.rs#L103); unchecked operation [here](https://github.com/YdrMaster/dtb-walker/blob/main/src/str.rs#L47))
- little error handling
- doesn't support `#cells` values greater than what `usize` allows
