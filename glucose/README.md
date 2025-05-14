[![crates.io](https://img.shields.io/crates/v/rustsat-glucose?style=for-the-badge&logo=rust)](https://crates.io/crates/rustsat-glucose)
[![docs.rs](https://img.shields.io/docsrs/rustsat-glucose?style=for-the-badge&logo=docsdotrs)](https://docs.rs/rustsat-glucose)
[![License](https://img.shields.io/crates/l/rustsat-glucose?style=for-the-badge)](../LICENSE)

<!-- cargo-rdme start -->

# rustsat-glucose - Interface to the Glucose SAT Solver for RustSAT

The Glucose SAT solver to be used with the [RustSAT](https://github.com/chrjabs/rustsat) library.

## Features

- `debug`: if this feature is enables, the Cpp library will be built with debug and check functionality if the Rust project is built in debug mode
- `quiet`: disable all glucose-internal printing to `stdout` during solving (on by default)

## Glucose Version

The version of Glucose in this crate is Version 4.2.1.
The used Cpp source can be found
[here](https://github.com/chrjabs/rustsat/tree/main/glucose/cppsrc).

## Minimum Supported Rust Version (MSRV)

Currently, the MSRV is 1.76.0, the plan is to always support an MSRV that is at least a year
old.

Bumps in the MSRV will _not_ be considered breaking changes. If you need a specific MSRV, make
sure to pin a precise version of RustSAT.

<!-- cargo-rdme end -->
