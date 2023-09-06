//! # Encodings for Common Constraint Types to CNF
//!
//! CNF encodings for cardinality and pseudo-boolean constraints.

pub mod am1;
pub mod card;
pub mod pb;

mod nodedb;

/// Errors from encodings
#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    /// Encode was not called before using the encoding
    NotEncoded,
    /// The requested encoding is unsatisfiable
    Unsat,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::NotEncoded => write!(f, "not encoded to enforce bound"),
            Error::Unsat => write!(f, "encoding is unsat"),
        }
    }
}

/// Trait for encodings that track statistics.
pub trait EncodeStats {
    /// Gets the number of clauses in the encoding
    fn n_clauses(&self) -> usize;

    /// Gets the number of variables in the encoding
    fn n_vars(&self) -> usize;
}
