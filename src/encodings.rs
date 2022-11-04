//! # Encodings for Common Constraint Types to CNF
//!
//! CNF encodings for cardinality and pseudo-boolean constraints.

pub mod card;
pub mod pb;

/// Errors from encodings
#[derive(Debug, PartialEq, Eq)]
pub enum EncodingError {
    /// Encode was not called before using the encoding
    NotEncoded,
    /// The requested encoding is unsatisfiable
    Unsat,
    /// The limits for the encoding are invalid
    InvalidLimits,
}

/// Trait for encodings that track statistics.
pub trait EncodeStats {
    /// Gets the number of clauses in the encoding
    fn n_clauses(&self) -> usize;

    /// Gets the number of variables in the encoding
    fn n_vars(&self) -> usize;
}
