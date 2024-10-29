//! # Encodings for Common Constraint Types to CNF
//!
//! CNF encodings for cardinality and pseudo-boolean constraints.

use thiserror::Error;

use crate::types::{Clause, Lit};

pub mod am1;
pub mod atomics;
pub mod card;
pub mod pb;

/// Trait for collecting clauses. Mainly used when generating encodings and implemented by
/// [`crate::instances::Cnf`], and solvers.
pub trait CollectClauses {
    /// Gets the number of clauses in the collection
    fn n_clauses(&self) -> usize;
    /// Extends the clause collector with an iterator of clauses
    ///
    /// # Errors
    ///
    /// If the collector runs out of memory, return an [`crate::OutOfMemory`] error.
    fn extend_clauses<T>(&mut self, cl_iter: T) -> Result<(), crate::OutOfMemory>
    where
        T: IntoIterator<Item = Clause>;
    /// Adds one clause to the collector
    ///
    /// # Errors
    ///
    /// If the collector runs out of memory, return an [`crate::OutOfMemory`] error.
    fn add_clause(&mut self, cl: Clause) -> Result<(), crate::OutOfMemory> {
        self.extend_clauses([cl])
    }
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
#[cfg_attr(docsrs, doc(cfg(feature = "internals")))]
mod nodedb {
    //! # Node Database Functionality For Universal Tree-Like Encodings
    //!
    //! Encodings with a tree-like structure where each node contains a sorted
    //! version of its children's literals. The leafs are input literals.
    //!
    //! This is used as the basis for the dynamic polynomial watchdog encoding.
    //! (Note that the DPW encoding is not technically tree-like since it might
    //! share substructures, but close enough.)

    pub use super::nodedbimpl::{NodeById, NodeCon, NodeId, NodeLike};
}

/// Iterate over encoding inputs
pub trait IterInputs {
    /// The iterator type
    type Iter<'a>: Iterator<Item = Lit>
    where
        Self: 'a;
    /// Gets an iterator over copies of the input literals
    fn iter(&self) -> Self::Iter<'_>;
}

/// Iterate over weighted encoding inputs
pub trait IterWeightedInputs {
    /// The iterator type
    type Iter<'a>: Iterator<Item = (Lit, usize)>
    where
        Self: 'a;
    /// Gets an iterator over copies of the input literals
    fn iter(&self) -> Self::Iter<'_>;
}
