//! # Certified CNF Encodings for Cardinality Constraints

use std::ops::RangeBounds;

use crate::{encodings::CollectCertClauses, instances::ManageVars};

/// Trait for certified cardinality encodings that allow upper bounding of the form `sum of lits <=
/// ub`
pub trait BoundUpper: super::Encode + super::BoundUpper {
    /// Lazily builds the certified cardinality encoding to enable upper bounds in a given range.
    /// `var_manager` is the variable manager to use for tracking new variables. A specific
    /// encoding might ignore the lower or upper end of the range. The derivation of the encoding
    /// is written to the given `proof`.
    ///
    /// # Errors
    ///
    /// - If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
    /// - If writing the proof fails, returns [`std::io::Error`]
    fn encode_ub_cert<Col, R, W>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pidgeons::Proof<W>,
    ) -> anyhow::Result<()>
    where
        Col: CollectCertClauses,
        R: RangeBounds<usize>,
        W: std::io::Write;
}

/// Trait for certified cardinality encodings that allow lower bounding of the form `sum of lits >=
/// lb`
pub trait BoundLower: super::Encode + super::BoundLower {
    /// Lazily builds the certified cardinality encoding to enable lower bounds in a given range.
    /// `var_manager` is the variable manager to use for tracking new variables. A specific
    /// encoding might ignore the lower or upper end of the range. The derivation of the encoding
    /// is written to the given `proof`.
    ///
    /// # Errors
    ///
    /// - If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
    /// - If writing the proof fails, returns [`std::io::Error`]
    fn encode_lb_cert<Col, R, W>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pidgeons::Proof<W>,
    ) -> anyhow::Result<()>
    where
        Col: CollectCertClauses,
        R: RangeBounds<usize>,
        W: std::io::Write;
}

/// Trait for certified cardinality encodings that allow upper and lower bounding
pub trait BoundBoth: BoundUpper + BoundLower {
    /// Lazily builds the certified cardinality encoding to enable both bounds in a given range.
    /// `var_manager` is the variable manager to use for tracking new variables. A specific
    /// encoding might ignore the lower or upper end of the range. The derivation of the encoding
    /// is written to the given `proof`.
    ///
    /// # Errors
    ///
    /// - If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
    /// - If writing the proof fails, returns [`std::io::Error`]
    fn encode_both_cert<Col, R, W>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pidgeons::Proof<W>,
    ) -> anyhow::Result<()>
    where
        Col: CollectCertClauses,
        R: RangeBounds<usize> + Clone,
        W: std::io::Write,
    {
        self.encode_ub_cert(range.clone(), collector, var_manager, proof)?;
        self.encode_lb_cert(range, collector, var_manager, proof)?;
        Ok(())
    }
}

/// Default implementation of [`BoundBoth`] for every encoding that does upper
/// and lower bounding
impl<CE> BoundBoth for CE where CE: BoundUpper + BoundLower {}

/// Trait for incremental certified cardinality encodings that allow upper bounding of the form
/// `sum of lits <= ub`
pub trait BoundUpperIncremental: BoundUpper + super::EncodeIncremental {
    /// Lazily builds the _change in_ the certified cardinality encoding to enable upper bounds in
    /// a given range. A change might be added literals or changed bounds. `var_manager` is the
    /// variable manager to use for tracking new variables. A specific encoding might ignore the
    /// lower or upper end of the range. The derivation of the encoding is written to the given
    /// `proof`.
    ///
    /// # Errors
    ///
    /// - If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
    /// - If writing the proof fails, returns [`std::io::Error`]
    fn encode_ub_change_cert<Col, R, W>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pidgeons::Proof<W>,
    ) -> anyhow::Result<()>
    where
        Col: CollectCertClauses,
        R: RangeBounds<usize>,
        W: std::io::Write;
}

/// Trait for incremental certified cardinality encodings that allow lower bounding of the form
/// `sum of lits >= lb`
pub trait BoundLowerIncremental: BoundLower + super::EncodeIncremental {
    /// Lazily builds the _change in_ the certified cardinality encoding to enable upper bounds in
    /// a given range. A change might be added literals or changed bounds. `var_manager` is the
    /// variable manager to use for tracking new variables. A specific encoding might ignore the
    /// lower or upper end of the range. The derivation of the encoding is written to the given
    /// `proof`.
    ///
    /// # Errors
    ///
    /// - If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
    /// - If writing the proof fails, returns [`std::io::Error`]
    fn encode_lb_change_cert<Col, R, W>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pidgeons::Proof<W>,
    ) -> anyhow::Result<()>
    where
        Col: CollectCertClauses,
        R: RangeBounds<usize>,
        W: std::io::Write;
}

/// Trait for incremental cardinality encodings that allow upper and lower bounding
pub trait BoundBothIncremental: BoundUpperIncremental + BoundLowerIncremental {
    /// Lazily builds the _change in_ the certified cardinality encoding to enable both bounds in a
    /// given range. `var_manager` is the variable manager to use for tracking new variables. A
    /// specific encoding might ignore the lower or upper end of the range. The derivation of the
    /// encoding is written to the given `proof`.
    ///
    /// # Errors
    ///
    /// - If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
    /// - If writing the proof fails, returns [`std::io::Error`]
    fn encode_both_change_cert<Col, R, W>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pidgeons::Proof<W>,
    ) -> anyhow::Result<()>
    where
        Col: CollectCertClauses,
        R: RangeBounds<usize> + Clone,
        W: std::io::Write,
    {
        self.encode_ub_change_cert(range.clone(), collector, var_manager, proof)?;
        self.encode_lb_change_cert(range, collector, var_manager, proof)?;
        Ok(())
    }
}

/// Default implementation of [`BoundBothIncremental`] for every encoding that
/// does incremental upper and lower bounding
impl<CE> BoundBothIncremental for CE where CE: BoundUpperIncremental + BoundLowerIncremental {}
