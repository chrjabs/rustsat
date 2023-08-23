//! # Minisat Solver Interface
//!
//! Interface to the [Minisat](https://github.com/niklasso/minisat) incremental
//! SAT solver.

use std::fmt;

mod simp;
pub use simp::MinisatSimp;

mod core;
pub use self::core::MinisatCore;

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
