[![Build & Test](https://github.com/chrjabs/rustsat/actions/workflows/rustsat.yml/badge.svg)](https://github.com/chrjabs/rustsat/actions/workflows/rustsat.yml)
[![crates.io](https://img.shields.io/crates/v/rustsat)](https://crates.io/crates/rustsat)
[![docs.rs](https://img.shields.io/docsrs/rustsat)](https://docs.rs/rustsat)
[![PyPI](https://img.shields.io/pypi/v/rustsat)](https://pypi.org/project/rustsat)
[![License](https://img.shields.io/crates/l/rustsat)](./LICENSE)

<!-- cargo-rdme start -->

# rustsat - A Comprehensive SAT Library for Rust

`rustsat` is a collection of interfaces and utilities for working with the boolean satisfiability problem in Rust.
This library aims to provide implementations of elements commonly used in the development of software in the area of satisfiability solving.
The focus of the library is to provide as much ease of use without giving up on performance.

## Example

```rust
let mut instance: SatInstance = SatInstance::new();
let l1 = instance.new_lit();
let l2 = instance.new_lit();
instance.add_binary(l1, l2);
instance.add_binary(!l1, l2);
instance.add_unit(l1);
let mut solver = rustsat_minisat::core::Minisat::default();
solver.add_cnf(instance.as_cnf().0).unwrap();
let res = solver.solve().unwrap();
assert_eq!(res, SolverResult::Sat);
let sol = solver.full_solution().unwrap();
assert_eq!(sol[l1.var()], TernaryVal::True);
assert_eq!(sol[l2.var()], TernaryVal::True);
```

## Crates

The RustSAT project is split up into multiple crates that are all contained in [this repository](https://github.com/chrjabs/rustsat/).
These are the crates the project consists of:

| Crate | Description |
| --- | --- |
| `rustsat` | The main library, containing basic types, traits, encodings, parsers, and more. |
| `rustsat-tools` | A collection of small helpful tools based on RustSAT that can be installed as binaries. For a list of available tools, see [this directory](https://github.com/chrjabs/rustsat/tree/main/tools/src/bin) with short descriptions of the tools in the headers of the files. |
| `rustsat-<satsolver>` | Interfaces to SAT solvers that can be used alongside `rustsat`. Currently interfaces are available for `cadical`, `kissat`, `glucose`, and `minisat`. |

## Installation

To use the RustSAT library as a dependency in your project, simply run `cargo add rustsat`.
To use an SAT solver interface in your project, run `cargo add rustsat-<satsolver>`.
Typically, the version of the SAT solver can be selected via crate features, refer to the documentation of the respective SAT solver crate for details.

To install the binary tools in `rustsat-tools` run `cargo install rustsat-tools`.

## Features

| Feature name | Description |
| --- | --- |
| `internals` | Make some internal data structures for e.g. encodings public. This is useful when basing a more complex encoding on the `rustsat` implementation of another encoding. Note that the internal API might change between releases. |
| `fxhash` | Use the faster firefox hash function from `rustc-hash` in `rustsat`. |
| `ipasir` | Include and link the IPASIR solver interface. |
| `optimization` | Include optimization (MaxSAT) data structures etc. |
| `multiopt` | Include data structures etc. for multi-objective optimization. |
| `compression` | Enable parsing and writing compressed input. |
| `bench` | Enable benchmark tests. Behind feature flag since it requires unstable Rust. |
| `rand` | Enable randomization features. (Shuffling clauses etc.) |

## Examples

For example usage refer to the small example tools in the [`rustsat-tools`
crate](https://crates.io/crates/rustsat_tools) at `tools/src/bin`. For a bigger
example you can look at this [multi-objective optimization
solver](https://github.com/chrjabs/scuttle).

For an example of how to use the C-API, see `rustsat/examples/capi*.cpp`.
Similarly, for an example of using the Python API, see `rustsat/examples/pyapi*.py`.

<!-- cargo-rdme end -->
