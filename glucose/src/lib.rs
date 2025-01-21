//! # rustsat-glucose - Interface to the Glucose SAT Solver for RustSAT
//!
//! The Glucose SAT solver to be used with the [RustSAT](https://github.com/chrjabs/rustsat) library.
//!
//! ## Features
//!
//! - `debug`: if this feature is enables, the Cpp library will be built with debug and check functionality if the Rust project is built in debug mode
//! - `quiet`: disable all glucose-internal printing to `stdout` during solving (on by default)
//!
//! ## Glucose Version
//!
//! The version of Glucose in this crate is Version 4.2.1.
//! The used Cpp source repository can be found [here](https://github.com/chrjabs/glucose4).

#![warn(clippy::pedantic)]
#![warn(missing_docs)]

use rustsat::{
    solvers::SolverState,
    types::{Lit, Var},
};
use std::{ffi::c_int, fmt};
use thiserror::Error;

pub mod core;
pub mod simp;

/// Fatal error returned if the Glucose API returns an invalid value
#[derive(Error, Clone, Copy, PartialEq, Eq, Debug)]
#[error("glucose c-api returned an invalid value: {api_call} -> {value}")]
pub struct InvalidApiReturn {
    api_call: &'static str,
    value: c_int,
}

/// Error returned if a provided assumption variable was eliminated in preprocessing by the solver
///
/// Glucose does not support assumptions over eliminated variables. To prevent this, variables that
/// will be used as assumptions can be frozen via [`rustsat::solvers::FreezeVar`]
#[derive(Error, Clone, Copy, PartialEq, Eq, Debug)]
#[error("assumption variable {0} has been eliminated by glucose simplification")]
pub struct AssumpEliminated(Var);

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

/// Possible Glucose limits
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
                "glucose out of memory",
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

    use std::os::raw::{c_int, c_void};

    use rustsat::types::Lit;

    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

    pub extern "C" fn rustsat_glucose_collect_lits(vec: *mut c_void, lit: c_int) {
        let vec = vec.cast::<Vec<Lit>>();
        let lit = Lit::from_ipasir(lit).expect("got invalid IPASIR lit from Glucose");
        unsafe { (*vec).push(lit) };
    }
}
