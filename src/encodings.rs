//! # Encodings for Common Constraint Types to CNF
//!
//! CNF encodings for cardinality and pseudo-boolean constraints.

pub mod card;
pub mod pb;

/// Possible bound types for cardinality constraints
pub enum BoundType {
    /// Can only enforce lower bounds
    LB,
    /// Can only enforce upper bounds
    UB,
    /// Can enforce both lower and upper bounds
    BOTH,
}

/// Errors from encodings
#[derive(Debug, PartialEq)]
pub enum EncodingError {
    /// The encoding type does not support a function
    NoTypeSupport,
    /// The encoding object was constructed without support for a function
    NoObjectSupport,
    /// Encode was not called before using the encoding
    NotEncoded,
    /// The requested encoding is unsatisfiable
    Unsat,
}
