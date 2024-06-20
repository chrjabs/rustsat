//! # rustsat-tools - Tools for and with the RustSAT Library
//!
//! This crate contains tools for and built on the RustSAT library.

mod parsing;
pub mod utils;

pub mod encodings {
    //! # Encodings for Encoding Generators

    pub mod assignment;
    pub mod facilitylocation;
    pub mod knapsack;

    pub mod cnf {
        //! # CNF Encodings

        pub mod clustering;
        pub mod knapsack;
    }

    pub mod pb {
        //! PB Encodings

        pub mod assignment;
        pub mod facilitylocation;
        pub mod knapsack;
    }
}

#[cfg(feature = "cadical")]
pub type Solver = rustsat_cadical::CaDiCaL<'static, 'static>;
#[cfg(all(not(feature = "cadical"), feature = "minisat"))]
pub type Solver = rustsat_minisat::core::Minisat;
