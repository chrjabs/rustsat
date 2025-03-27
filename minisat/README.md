[![crates.io](https://img.shields.io/crates/v/rustsat-minisat)](https://crates.io/crates/rustsat-minisat)
[![docs.rs](https://img.shields.io/docsrs/rustsat-minisat)](https://docs.rs/rustsat-minisat)
[![License](https://img.shields.io/crates/l/rustsat-minisat)](../LICENSE)

<!-- cargo-rdme start -->

# rustsat-minisat - Interface to the Minisat SAT Solver for RustSAT

The Minisat SAT solver to be used with the [RustSAT](https://github.com/chrjabs/rustsat) library.

## Features

- `debug`: if this feature is enables, the Cpp library will be built with debug and check functionality if the Rust project is built in debug mode
- `quiet`: disable all glucose-internal printing to `stdout` during solving (on by default)

## Minisat Version

The version of Minisat in this crate is Version 2.2.0.
The used Cpp source repository can be found [here](https://github.com/chrjabs/minisat).

<!-- cargo-rdme end -->
