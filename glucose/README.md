[![Check & Test](https://github.com/chrjabs/rustsat/actions/workflows/glucose.yml/badge.svg)](https://github.com/chrjabs/rustsat/actions/workflows/glucose.yml)
[![crates.io](https://img.shields.io/crates/v/rustsat-glucose)](https://crates.io/crates/rustsat-glucose)
[![docs.rs](https://img.shields.io/docsrs/rustsat-glucose)](https://docs.rs/rustsat-glucose)
[![License](https://img.shields.io/crates/l/rustsat-glucose)](../LICENSE)

<!-- cargo-rdme start -->

# rustsat-glucose - Interface to the Glucose SAT Solver for RustSAT

The Glucose SAT solver to be used with the [RustSAT](https://github.com/chrjabs/rustsat) library.

## Features

- `debug`: if this feature is enables, the Cpp library will be built with debug and check functionality if the Rust project is built in debug mode
- `quiet`: disable all glucose-internal printing to `stdout` during solving (on by default)

## Glucose Version

The version of Glucose in this crate is Version 4.2.1.
The used Cpp source repository can be found [here](https://github.com/chrjabs/glucose4).

<!-- cargo-rdme end -->
