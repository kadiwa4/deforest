# Rust crate `devicetree`

[Devicetree specification](https://www.devicetree.org/specifications/)

This is in an early stage of development.
The crate tries to be efficient by avoiding allocations, but I have no benchmarks and the interface isn't the most ergonomic. It also has `unsafe` code scattered across the entire codebase.
