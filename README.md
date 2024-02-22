# Rust crate `deforest`

Efficient `#![no_std]` parser for devicetree blobs compliant (hopefully) with version 0.4 of [the specification][spec].

The crate tries to be efficient by avoiding allocations (it can be used without `alloc`) and only iterating over nodes once, but I have no realistic benchmarks.
On the downside, the interface isn't the most ergonomic.

[spec]: https://www.devicetree.org/specifications

## Alternatives
- [`fdt-rs`](https://github.com/rs-embedded/fdt-rs): can even build an index to interact with DTBs faster
- [`fdt`](https://github.com/repnop/fdt): comes with extra types for a couple of common nodes

## License
This project is licensed under the MIT license ([LICENSE-MIT](LICENSE-MIT) or
https://opensource.org/license/mit/).
