//! # C-API For RustSAT
//!
//! In the C-API, literals are represented as IPASIR literals.
//!
//! This is the C-API for RustSAT. Currently this API is very minimal and not the focus of this
//! project. For now, only the API of certain encodings is available.
//!
//! For the API itself, see `rustsat.h`. To use RustSAT from an external project, build this crate
//! with the following command in the root of this repository:
//!
//! ```bash
//! RUSTFLAGS="--print=native-static-libs" cargo --release -p rustsat-capi
//! ```
//!
//! Then link against `librustsat_capi.a` (produced by `cargo` in `target/release`).
//! If you run into undefined symbols when linking to `librustsat_capi.a`, check the output of the
//! build command for a line starting with `note: native-static-libs:` and make sure that these
//! libraries are included when linking the final project.
//!
//! For some more pointers for how to use the C-API, the
//! [tests](https://github.com/chrjabs/rustsat/tree/main/capi/tests) might be a good starting
//! point.
#![warn(clippy::pedantic)]
#![expect(clippy::module_name_repetitions)]

pub mod encodings;
