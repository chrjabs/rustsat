//! # Glucose 4 Solver Interface
//!
//! Interface to the [Glucose
//! 4](https://www.labri.fr/perso/lsimon/research/glucose/#glucose-4.2.1)
//! incremental SAT solver.

use std::fmt;

mod simp;
pub use simp::GlucoseSimp4;

mod core;
pub use self::core::GlucoseCore4;

/// Possible Glucose limits
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
