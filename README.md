[![crates.io](https://img.shields.io/crates/v/rustsat?style=for-the-badge&logo=rust)](https://crates.io/crates/rustsat)
[![docs.rs](https://img.shields.io/docsrs/rustsat?style=for-the-badge&logo=docsdotrs)](https://docs.rs/rustsat)
[![Coveralls](https://img.shields.io/coverallsCoverage/github/chrjabs/rustsat?style=for-the-badge&logo=coveralls)](https://coveralls.io/github/chrjabs/rustsat)
[![PyPI](https://img.shields.io/pypi/v/rustsat?style=for-the-badge&logo=pypi&logoColor=%23ffffff)](https://pypi.org/project/rustsat)
[![License](https://img.shields.io/crates/l/rustsat?style=for-the-badge)](./LICENSE)

<!-- cargo-rdme start -->

# RustSAT - A Comprehensive SAT Library for Rust

RustSAT is a collection of interfaces and utilities for working with the boolean satisfiability problem in Rust.
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
solver.add_cnf(instance.into_cnf().0).unwrap();
let res = solver.solve().unwrap();
assert_eq!(res, SolverResult::Sat);
let sol = solver.full_solution().unwrap();
assert_eq!(sol[l1.var()], TernaryVal::True);
assert_eq!(sol[l2.var()], TernaryVal::True);
```

## Crates

The RustSAT project is split up into multiple crates that are all contained in [this repository](https://github.com/chrjabs/rustsat/).
The general architecture is illustrated in [this architecture
diagram](https://github.com/chrjabs/rustsat/blob/main/docs/architecture.png).
These are the crates the project consists of:

| Crate | Description |
| --- | --- |
| `rustsat` | The main library, containing basic types, traits, encodings, parsers, and more. |
| `rustsat-tools` | A collection of small helpful tools based on RustSAT that can be installed as binaries. For a list of available tools, see [this directory](https://github.com/chrjabs/rustsat/tree/main/tools/src/bin) with short descriptions of the tools in the headers of the files. |
| `rustsat-<satsolver>` | Interfaces to SAT solvers that can be used alongside RustSAT. Currently interfaces are available for `cadical`, `kissat`, `glucose`, and `minisat`. |
| `rustsat-ipasir` | [IPASIR](https://github.com/biotomas/ipasir) bindings to use any compliant solver with RustSAT. |
| `pigeons` | A library for writing [VeriPB](https://gitlab.com/MIAOresearch/software/VeriPB) proofs. Used by RustSAT with the `proof-logging` feature. |

## Comparison to Other Libraries

For a basic comparison of RustSAT to other libraries, you can have a look at [this benchmark
repository](https://github.com/chrjabs/rustsat-benchmarks/) and the [RustSAT tool
paper](https://media.christophjabs.info/papers/Jabs2025RustsatLibrarySat.pdf).

## Citing

If you use RustSAT in your research, please cite the following system description paper.

```bibtex
@inproceedings{Jabs2025RustsatLibrarySat,
  title       = {{RustSAT}: {A} Library For {SAT} Solving in Rust},
  author      = {Jabs, Christoph},
  booktitle   = {28th International Conference on Theory and Applications of Satisfiability
  Testing ({SAT} 2025)},
  editor      = {Berg, Jeremias and Nordstr{\"o}m, Jakob},
  year        = {2025},
  volume      = {341},
  publisher   = {Schloss Dagstuhl---Leibniz-Zentrum f{\"{u}}r Informatik},
  series      = {Leibniz International Proceedings in Informatics ({LIPIcs})},
  pages       = {24:1--24:13},
  doi         = {10.4230/LIPIcs.SAT.2025.24},
  eprint      = {2505.15221},
}
```

## Installation

To use the RustSAT library as a dependency in your project, simply run `cargo add rustsat`.
To use an SAT solver interface in your project, run `cargo add rustsat-<satsolver>`.
Typically, the version of the SAT solver can be selected via crate features, refer to the documentation of the respective SAT solver crate for details.

To install the binary tools in `rustsat-tools` run `cargo install rustsat-tools`.

## Features

| Feature name | Description |
| --- | --- |
| `optimization` | Include optimization (MaxSAT) data structures etc. |
| `multiopt` | Include data structures etc. for multi-objective optimization. |
| `compression` | Enable parsing and writing compressed input. |
| `fxhash` | Use the faster firefox hash function from `rustc-hash` in RustSAT. |
| `rand` | Enable randomization features. (Shuffling clauses etc.) |
| `ipasir-display` | Changes `Display` trait for `Lit` and `Var` types to follow IPASIR variables indexing. |
| `serde` | Add implementations for [`serde::Serialize`](https://docs.rs/serde/latest/serde/trait.Serialize.html) and [`serde::Deserialize`](https://docs.rs/serde/latest/serde/trait.Deserialize.html) for many library types |
| `proof-logging` | Add proof logging / certification support to constraint encodings |
| `verbose-proofs` | Make the generated proofs (see `proof-logging`) more verbose, for debugging and testing |
| `bench` | Enable benchmark tests. Behind feature flag since it requires unstable Rust. |
| `internals` | Make some internal data structures for e.g. encodings public. This is useful when basing a more complex encoding on the RustSAT implementation of another encoding. Note that the internal API might change between releases. |

## Examples

For example usage refer to the small example tools in the [`rustsat-tools`
crate](https://crates.io/crates/rustsat_tools) at `tools/src/bin`. For a bigger
example you can look at this [multi-objective optimization
solver](https://github.com/chrjabs/scuttle).

## Minimum Supported Rust Version (MSRV)

Currently, the MSRV of RustSAT is 1.76.0, the plan is to always support an MSRV that is at
least a year old.

Bumps in the MSRV will _not_ be considered breaking changes. If you need a specific MSRV, make
sure to pin a precise version of RustSAT.

<!-- cargo-rdme end -->

## Main Branch Documentation

The API documentation of the main branch can be found
[here](https://christophjabs.info/rustsat/main/rustsat/).

## Python Bindings

This library also comes with experimental Python bindings to use its encodings
from Python. The Python bindings are available at
[PyPI](https://pypi.org/project/rustsat/). For more details see the [Python API
documentation](https://christophjabs.info/rustsat/pyapi/).

## Contributing

We are welcoming contributions in the form of pull requests and suggestions.
Kindly make sure to read
[`CONTRIBUTING.md`](https://github.com/chrjabs/rustsat/blob/main/CONTRIBUTING.md)
first.
