[![crates.io](https://img.shields.io/crates/v/rustsat-batsat?style=for-the-badge&logo=rust)](https://crates.io/crates/rustsat-batsat)
[![docs.rs](https://img.shields.io/docsrs/rustsat-batsat?style=for-the-badge&logo=docsdotrs)](https://docs.rs/rustsat-batsat)
[![License](https://img.shields.io/crates/l/rustsat-batsat?style=for-the-badge)](../LICENSE)

<!-- cargo-rdme start -->

# rustsat-batsat - Interface to the BatSat SAT Solver for RustSAT

Interface to the [BatSat](https://github.com/c-cube/batsat) incremental SAT-Solver to be used with the [RustSAT](https://github.com/chrjabs/rustsat) library.

BatSat is fully implemented in Rust which has advantages in restricted compilation scenarios like WebAssembly.

# BatSat Version

The version of BatSat in this crate is Version 0.6.0.

## Minimum Supported Rust Version (MSRV)

Currently, the MSRV is 1.76.0, the plan is to always support an MSRV that is at least a year
old.

Bumps in the MSRV will _not_ be considered breaking changes. If you need a specific MSRV, make
sure to pin a precise version of RustSAT.

<!-- cargo-rdme end -->
