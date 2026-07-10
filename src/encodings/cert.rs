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
