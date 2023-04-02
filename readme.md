# Rust crate `devicetree`

[Devicetree specification](https://www.devicetree.org/specifications/)

This is in an early stage of development.
The crate tries to be efficient by avoiding allocations (it can be used without `alloc`), but I have no benchmarks and the interface isn't the most ergonomic. It also has `unsafe` code scattered across the entire codebase.

Competitor crates:
- [`device_tree`](https://github.com/mbr/device_tree-rs)
- another crate called [`devicetree`](https://github.com/duanyu-yu/DeviceTree)
- [`devicetree-tool`](https://github.com/michael2012z/devicetree-tool) (not very similar in what it's trying to achieve)
- [`dtb`](https://github.com/ababo/dtb)
- [`dtb_parser`](https://github.com/d3ara1n/dtb_parser)
- [`dtb-walker`](https://github.com/YdrMaster/dtb-walker)
- [`fdt`](https://github.com/repnop/fdt)
- [`fdt-rs`](https://github.com/rs-embedded/fdt-rs)
- [`serde-device-tree`](https://github.com/rustsbi/serde-device-tree)
