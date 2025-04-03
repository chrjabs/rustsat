//! # Encodings for Common Constraint Types to CNF
//!
//! CNF encodings for cardinality and pseudo-boolean constraints.

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

/// Usage error for operations where the encoding would first have to be built
#[derive(thiserror::Error, Debug, PartialEq, Eq, Clone, Copy)]
#[error("the encoding is not built for this operation")]
pub struct NotEncoded;

/// Usage errors for methods enforcing a bound
#[derive(thiserror::Error, Debug, PartialEq, Eq, Clone, Copy)]
pub enum EnforceError {
    /// Encode was not called before using the encoding
    #[error("not encoded to enforce bound")]
    NotEncoded,
    /// The requested encoding is unsatisfiable
    #[error("encoding is unsat")]
    Unsat,
}

impl From<NotEncoded> for EnforceError {
    fn from(_: NotEncoded) -> Self {
        EnforceError::NotEncoded
    }
}

/// Error type for encoding a constraint
#[derive(thiserror::Error, Debug, PartialEq, Eq)]
pub enum ConstraintEncodingError {
    /// The constraint is unsatisfiable
    #[error("constraint is unsat")]
    Unsat,
    /// Building the constraint encoding ran out of memory
    #[error("out of memory error: {0}")]
    OutOfMemory(#[from] crate::OutOfMemory),
}

/// Marker trait for "monotone" incremental encodings, i.e., encodings for which enforcing `sum <=
/// k` (as hard clauses) does not conflict with enforcing `sum <= k - x` later.
///
/// The [`pb::DynamicPolyWatchdog`] is a notable exception to this, because of its tare variables.
pub trait Monotone {}

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
    //! version of its children's literals. The leaves are input literals.
    //!
    //! This is used as the basis for the dynamic polynomial watchdog encoding.
    //! (Note that the DPW encoding is not technically tree-like since it might
    //! share substructures, but close enough.)

    pub use super::nodedbimpl::{NodeById, NodeCon, NodeId, NodeLike};
}

#[path = "encodings/totdb.rs"]
mod totdbimpl;

// Module defined inline to be able to dynamically change visibility
// (non-inline modules in proc macro input are unstable)
#[cfg_attr(feature = "internals", visibility::make(pub))]
#[cfg_attr(docsrs, doc(cfg(feature = "internals")))]
mod totdb {
    //! # Totalizer Database
    pub(crate) use super::totdbimpl::LitData;
    pub use super::totdbimpl::{AssignIter, Db, GeneralNode, Node, Semantics, UnitNode};

    #[cfg(feature = "proof-logging")]
    pub use super::totdbimpl::cert;
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

#[cfg(feature = "proof-logging")]
pub mod cert {
    //! # Certified Constraint Encodings

    use crate::types::Clause;

    /// Trait for collecting clauses including their [`pigeons::AbsConstraintId`] in a proof
    ///
    /// The default implementation of this trait simply ignores the proof log IDs
    pub trait CollectClauses: super::CollectClauses {
        /// Extends the collector with an iterator of clauses and proof log IDs
        ///
        /// # Errors
        ///
        /// If the collector runs out of memory, return an [`crate::OutOfMemory`] error.
        fn extend_cert_clauses<T>(&mut self, cl_iter: T) -> Result<(), crate::OutOfMemory>
        where
            T: IntoIterator<Item = (Clause, pigeons::AbsConstraintId)>,
        {
            self.extend_clauses(cl_iter.into_iter().map(|(cl, _)| cl))
        }
        /// Adds one clause and proof log ID to the collector
        ///
        /// # Errors
        ///
        /// If the collector runs out of memory, return an [`crate::OutOfMemory`] error.
        fn add_cert_clause(
            &mut self,
            cl: Clause,
            id: pigeons::AbsConstraintId,
        ) -> Result<(), crate::OutOfMemory> {
            self.extend_cert_clauses([(cl, id)])
        }
    }

    /// Error type for building a certified encoding
    #[derive(thiserror::Error, Debug)]
    pub enum EncodingError {
        /// Building the encoding ran out of memory
        #[error("out of memory error: {0}")]
        OutOfMemory(#[from] crate::OutOfMemory),
        /// Writing the proof failed
        #[error("writing the proof failed: {0}")]
        Proof(#[from] std::io::Error),
    }

    /// Error type for encoding a constraint with proof logging
    #[derive(thiserror::Error, Debug)]
    pub enum ConstraintEncodingError {
        /// The constraint is unsatisfiable
        #[error("constraint is unsat")]
        Unsat,
        /// Building the constraint encoding ran out of memory
        #[error("out of memory error: {0}")]
        OutOfMemory(#[from] crate::OutOfMemory),
        /// Writing the proof failed
        #[error("writing the proof failed: {0}")]
        Proof(#[from] std::io::Error),
    }

    impl From<EncodingError> for ConstraintEncodingError {
        fn from(value: EncodingError) -> Self {
            match value {
                EncodingError::OutOfMemory(error) => error.into(),
                EncodingError::Proof(error) => error.into(),
            }
        }
    }
}
