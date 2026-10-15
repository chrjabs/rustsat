//! # Certified CNF Encodings for At-Most-One Constraints

/// Trait for all certified at-most-1 encodings
pub trait Encode: super::Encode {
    /// Encodes and enforces the at-most-1 constraint, given the constraint ID
    ///
    /// # Errors
    ///
    /// If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
    fn encode_cert<Col, W>(
        &mut self,
        id: pigeons::AbsConstraintId,
        collector: &mut Col,
        var_manager: &mut dyn crate::instances::ManageVars,
        proof: &mut pigeons::Proof<W>,
    ) -> Result<(), crate::encodings::cert::EncodingError>
    where
        Col: crate::encodings::cert::CollectClauses,
        W: std::io::Write;
}
