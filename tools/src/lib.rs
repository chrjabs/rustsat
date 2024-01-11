//! # rustsat-tools - Tools for and with the RustSAT Library
//!
//! This crate contains tools for and built on the RustSAT library.

pub mod utils;

pub mod encodings {
    //! # Encodings for Encoding Generators

    pub mod clustering;
    pub mod knapsack;
}

#[cfg(feature = "cadical")]
pub type Solver = rustsat_cadical::CaDiCaL<'static, 'static>;
#[cfg(all(not(feature = "cadical"), feature = "minisat"))]
pub type Solver = rustsat_minisat::core::Minisat;
