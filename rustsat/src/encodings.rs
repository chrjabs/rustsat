//! # Encodings for Common Constraint Types to CNF
//!
//! CNF encodings for cardinality and pseudo-boolean constraints.

pub mod am1;
pub mod atomics;
pub mod card;
pub mod pb;

/// Trait for collecting clauses. Mainly used when generating encodings and implemented by
/// [`instances::Cnf`], and solvers.
pub trait CollectClauses: Extend<crate::types::Clause> {
    /// Gets the number of clauses in the collection
    fn n_clauses(&self) -> usize;
}

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
    fn n_vars(&self) -> u32;
}

#[path = "encodings/nodedb.rs"]
mod nodedbimpl;

// Module defined inline to be able to dynamically change visibility
// (non-inline modules in proc macro input are unstable)
#[cfg_attr(feature = "internals", visibility::make(pub))]
mod nodedb {
    //! # Node Database Functionality For Universal Tree-Like Encodings
    //!
    //! Encodings with a tree-like structure where each node contains a sorted
    //! version of its childrens' literals. The leafs are input literals.
    //!
    //! This is used as the basis for the dynamic polynomial watchdog encoding.
    //! (Note that the DPW encoding is not technically tree-like since it might
    //! share substructures, but close enough.)

    pub use super::nodedbimpl::{NodeById, NodeCon, NodeId, NodeLike};
}
