//! # rustsat-minisat - Interface to the Minisat SAT Solver for RustSAT
//!
//! The Minisat SAT solver to be used with the [RustSAT](https://github.com/chrjabs/rustsat) library.
//!
//! ## Features
//!
//! - `debug`: if this feature is enables, the C++ library will be built with debug and check functionality if the Rust project is built in debug mode
//!
//! ## Minisat Version
//!
//! The version of minisat in this crate is Version 2.2.0.
//! The used C++ source repository can be found [here](https://github.com/chrjabs/minisat).

use rustsat::{solvers::SolverState, types::Lit};
use std::fmt;

pub mod simp;

pub mod core;

#[derive(Debug, PartialEq, Eq, Default)]
enum InternalSolverState {
    #[default]
    Configuring,
    Input,
    Sat,
    Unsat(Vec<Lit>),
}

impl InternalSolverState {
    fn to_external(&self) -> SolverState {
        match self {
            InternalSolverState::Configuring => SolverState::Configuring,
            InternalSolverState::Input => SolverState::Input,
            InternalSolverState::Sat => SolverState::Sat,
            InternalSolverState::Unsat(_) => SolverState::Unsat,
        }
    }
}

/// Possible Minisat limits
#[derive(Debug)]
pub enum Limit {
    /// No limits
    None,
    /// A limit on the number of conflicts
    Conflicts(i64),
    /// A limit on the number of propagations
    Propagations(i64),
}

impl fmt::Display for Limit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Limit::None => write!(f, "none"),
            Limit::Conflicts(val) => write!(f, "conflicts ({})", val),
            Limit::Propagations(val) => write!(f, "propagations ({})", val),
        }
    }
}
