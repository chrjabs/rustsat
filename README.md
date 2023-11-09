# rustsat - A Comprehensive SAT Library for Rust

`rustsat` is a collection of interfaces and utilities for working with the boolean satisfiability problem in Rust.
This library aims to provide implementations of elements commonly used in the development on software in the area of satisfiability solving.
The focus of the library is to provide as much ease of use without giving up on performance.

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

For example useage refer to the small example tools in the [`rustsat-tools`
crate](https://crates.io/crates/rustsat_tools) at `tools/src/bin`. For a bigger
example you can look at this [multi-objective optimization
solver](https://github.com/chrjabs/scuttle).

For an example of how to use the C-API, see `rustsat/examples/capi*.cpp`.

## Versions

Note that at the current state of development, releases of RustSAT are _not_ following semantic versioning, meaning the API can _change_ between minor releases.
For a more detailed changelog including all patch versions, see [GitHub Releases](https://github.com/chrjabs/rustsat/releases).

### Version 0.3.x

- Alternative totalizer implementation based on a totalizer database
- Dynamic polynomial watchdog encoing
- Changes to public API: changed some vectores to slices
- Changed internal variable/literal representation from `usize` to `u32`

### Version 0.2.x

Solver interfaces factored out into seperate crates.
See detailed changes in [GitHub Releases](https://github.com/chrjabs/rustsat/releases).

### Version 0.1.2

Updated initial version with working dependencies

### Version 0.1.0 and 0.1.1

Yanked because of dependencies that don't exist anymore
