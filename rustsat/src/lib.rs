//! # rustsat - A Comprehensive SAT Solving Library
//!
//! `rustsat` is a collection of interfaces and utilities for working with the
//! boolean satisfiability problem in Rust.
//!
//! ## Features
//!
//! | Feature name | Description |
//! | --- | --- |
//! | `internals` | Make some internal data structures for e.g. encodings public. This is useful when basing a more complex encoding on the `rustsat` implementation of another encoding. Note that the internal API might change between releases. |
//! | `fxhash` | Use the faster firefox hash function from `rustc-hash` in `rustsat`. |
//! | `ipasir` | Include and link the IPASIR solver interface. |
//! | `optimization` | Include optimization (MaxSAT) data structures etc. |
//! | `multiopt` | Include data structures etc. for multi-objective optimization. |
//! | `compression` | Enable parsing and writing compressed input. |
//! | `rand` | Enable randomization features. (Shuffling clauses etc.) |

pub mod encodings;
pub mod instances;
pub mod solvers;
pub mod types;

mod utils;
