//! # Encodings for Common Constraint Types to CNF
//!
//! CNF encodings for cardinality and pseudo-boolean constraints.

use thiserror::Error;

use crate::types::Lit;

pub mod am1;
pub mod atomics;
pub mod card;
pub mod pb;

/// Trait for collecting clauses. Mainly used when generating encodings and implemented by
/// [`crate::instances::Cnf`], and solvers.
pub trait CollectClauses: Extend<crate::types::Clause> {
    /// Gets the number of clauses in the collection
    fn n_clauses(&self) -> usize;
}

/// Errors from encodings
#[derive(Error, Debug, PartialEq, Eq)]
pub enum Error {
    /// Encode was not called before using the encoding
    #[error("not encoded to enforce bound")]
    NotEncoded,
    /// The requested encoding is unsatisfiable
    #[error("encoding is unsat")]
    Unsat,
}

#[cfg(feature = "pyapi")]
impl From<Error> for pyo3::PyErr {
    fn from(value: Error) -> Self {
        match value {
            Error::NotEncoded => {
                pyo3::exceptions::PyRuntimeError::new_err("not encoded to enforce bound")
            }
            Error::Unsat => pyo3::exceptions::PyValueError::new_err("encoding is unsat"),
        }
    }
}

/// Trait for encodings that track statistics.
pub trait EncodeStats {
    /// Gets the number of clauses in the encoding
    fn n_clauses(&self) -> usize;

    /// Gets the number of auxiliary variables in the encoding
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

/// Iterate over encoding inputs
pub trait IterInputs {
    type Iter<'a>: Iterator<Item = Lit>
    where
        Self: 'a;
    /// Gets an iterator over copies of the input literals
    fn iter(&self) -> Self::Iter<'_>;
}

/// Iterate over weighted encoding inputs
pub trait IterWeightedInputs {
    type Iter<'a>: Iterator<Item = (Lit, usize)>
    where
        Self: 'a;
    /// Gets an iterator over copies of the input literals
    fn iter(&self) -> Self::Iter<'_>;
}
