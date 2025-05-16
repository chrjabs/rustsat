//! # rustsat-minisat - Interface to the Minisat SAT Solver for RustSAT
//!
//! The Minisat SAT solver to be used with the [RustSAT](https://github.com/chrjabs/rustsat) library.
//!
//! ## Features
//!
//! - `debug`: if this feature is enables, the Cpp library will be built with debug and check functionality if the Rust project is built in debug mode
//! - `quiet`: disable all glucose-internal printing to `stdout` during solving (on by default)
//!
//! ## Minisat Version
//!
//! The version of Minisat in this crate is Version 2.2.0.
//! The used Cpp source can be found
//! [here](https://github.com/chrjabs/rustsat/tree/main/minisat/cppsrc).
//!
//! ## Minimum Supported Rust Version (MSRV)
//!
//! Currently, the MSRV is 1.76.0, the plan is to always support an MSRV that is at least a year
//! old.
//!
//! Bumps in the MSRV will _not_ be considered breaking changes. If you need a specific MSRV, make
//! sure to pin a precise version of RustSAT.

#![warn(clippy::pedantic)]
#![warn(missing_docs)]
#![warn(missing_debug_implementations)]

use rustsat::{solvers::SolverState, types::Var};
use std::{ffi::c_int, fmt};
use thiserror::Error;

pub mod core;
pub mod simp;

/// Fatal error returned if the Minisat API returns an invalid value
#[derive(Error, Clone, Copy, PartialEq, Eq, Debug)]
#[error("minisat c-api returned an invalid value: {api_call} -> {value}")]
pub struct InvalidApiReturn {
    api_call: &'static str,
    value: c_int,
}

/// Error returned if a provided assumption variable was eliminated in preprocessing by the solver
///
/// Minisat does not support assumptions over eliminated variables. To prevent this, variables that
/// will be used as assumptions can be frozen via [`rustsat::solvers::FreezeVar`]
#[derive(Error, Clone, Copy, PartialEq, Eq, Debug)]
#[error("assumption variable {0} has been eliminated by minisat simplification")]
pub struct AssumpEliminated(Var);

#[derive(Debug, PartialEq, Eq, Default)]
enum InternalSolverState {
    #[default]
    Configuring,
    Input,
    Sat,
    Unsat(bool),
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
#[derive(Debug, Clone, Copy)]
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
            Limit::Conflicts(val) => write!(f, "conflicts ({val})"),
            Limit::Propagations(val) => write!(f, "propagations ({val})"),
        }
    }
}

macro_rules! handle_oom {
    ($val:expr) => {{
        let val = $val;
        if val == $crate::ffi::OUT_OF_MEM {
            return anyhow::Context::context(
                Err(rustsat::OutOfMemory::ExternalApi),
                "minisat out of memory",
            );
        }
        val
    }};
}
pub(crate) use handle_oom;

pub(crate) mod ffi {
    #![allow(non_upper_case_globals)]
    #![allow(non_camel_case_types)]
    #![allow(non_snake_case)]

    use std::os::raw::c_void;

    use rustsat::types::Lit;

    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

    impl From<Lit> for c_Lit {
        fn from(value: Lit) -> Self {
            unsafe { std::mem::transmute::<Lit, c_Lit>(value) }
        }
    }

    pub extern "C" fn rustsat_minisat_collect_lits(vec: *mut c_void, lit: c_Lit) {
        let vec = vec.cast::<Vec<Lit>>();
        unsafe { (*vec).push(std::mem::transmute::<c_Lit, Lit>(lit)) };
    }
}
