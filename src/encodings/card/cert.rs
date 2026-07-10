//! # Certified CNF Encodings for Cardinality Constraints

use crate::encodings::cert::CollectClauses;
use crate::encodings::cert::ConstraintEncodingError;
use crate::encodings::cert::EncodingError;
use crate::instances::ManageVars;
use crate::types::constraints::CardConstraint;
use crate::types::constraints::CardEqConstr;
use crate::types::constraints::CardLbConstr;
use crate::types::constraints::CardUbConstr;
use crate::types::Lit;

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
    /// If the clause collector runs out of memory, or writing the proof fails
    fn encode_ub_cert<Col, R, W>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
    ) -> Result<(), EncodingError>
    where
        Col: CollectClauses,
        R: std::ops::RangeBounds<usize>,
        W: std::io::Write;

    /// Encodes an upper bound cardinality constraint to CNF with proof logging
    ///
    /// # Errors
    ///
    /// If the clause collector runs out of memory, or writing the proof fails
    fn encode_ub_constr_cert<Col, W>(
        constr: (CardUbConstr, pigeons::AbsConstraintId),
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
    ) -> Result<(), EncodingError>
    where
        Col: CollectClauses,
        W: std::io::Write,
        Self: FromIterator<Lit> + Sized;
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
    /// If the clause collector runs out of memory, or writing the proof fails
    fn encode_lb_cert<Col, R, W>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
    ) -> Result<(), EncodingError>
    where
        Col: CollectClauses,
        R: std::ops::RangeBounds<usize>,
        W: std::io::Write;

    /// Encodes a lower bound cardinality constraint to CNF with proof logging
    ///
    /// # Errors
    ///
    /// If the clause collector runs out of memory, writing the proof fails, or the constraint is
    /// unsatisfiable
    fn encode_lb_constr_cert<Col, W>(
        constr: (CardLbConstr, pigeons::AbsConstraintId),
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
    ) -> Result<(), ConstraintEncodingError>
    where
        Col: CollectClauses,
        W: std::io::Write,
        Self: FromIterator<Lit> + Sized;
}

/// Trait for certified cardinality encodings that allow upper and lower bounding
pub trait BoundBoth: BoundUpper + BoundLower + super::BoundBoth {
    /// Lazily builds the certified cardinality encoding to enable both bounds in a given range.
    /// `var_manager` is the variable manager to use for tracking new variables. A specific
    /// encoding might ignore the lower or upper end of the range. The derivation of the encoding
    /// is written to the given `proof`.
    ///
    /// # Errors
    ///
    /// If the clause collector runs out of memory, or writing the proof fails
    fn encode_both_cert<Col, R, W>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
    ) -> Result<(), EncodingError>
    where
        Col: CollectClauses,
        R: std::ops::RangeBounds<usize> + Clone,
        W: std::io::Write,
    {
        self.encode_ub_cert(range.clone(), collector, var_manager, proof)?;
        self.encode_lb_cert(range, collector, var_manager, proof)?;
        Ok(())
    }

    /// Encodes an equality cardinality constraint to CNF with proof logging
    ///
    /// # Errors
    ///
    /// If the clause collector runs out of memory, writing the proof fails, or the constraint is
    /// unsatisfiable
    fn encode_eq_constr_cert<Col, W>(
        constr: (CardEqConstr, pigeons::AbsConstraintId),
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
    ) -> Result<(), ConstraintEncodingError>
    where
        Col: CollectClauses,
        W: std::io::Write,
        Self: FromIterator<Lit> + Sized,
    {
        // Assume the two constraints have ID as given and +1
        let (constr, id) = constr;
        let (lb_c, ub_c) = constr.split();
        Self::encode_ub_constr_cert((ub_c, id + 1), collector, var_manager, proof)?;
        Self::encode_lb_constr_cert((lb_c, id), collector, var_manager, proof)?;
        Ok(())
    }

    /// Encodes any cardinality constraint to CNF with proof logging
    ///
    /// # Errors
    ///
    /// If the clause collector runs out of memory, writing the proof fails, or the constraint is
    /// unsatisfiable
    fn encode_constr_cert<Col, W>(
        constr: (CardConstraint, pigeons::AbsConstraintId),
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
    ) -> Result<(), ConstraintEncodingError>
    where
        Col: CollectClauses,
        W: std::io::Write,
        Self: FromIterator<Lit> + Sized,
    {
        let (constr, id) = constr;
        match constr {
            CardConstraint::Ub(constr) => {
                Self::encode_ub_constr_cert((constr, id), collector, var_manager, proof)?;
                Ok(())
            }
            CardConstraint::Lb(constr) => {
                Self::encode_lb_constr_cert((constr, id), collector, var_manager, proof)
            }
            CardConstraint::Eq(constr) => {
                Self::encode_eq_constr_cert((constr, id), collector, var_manager, proof)
            }
        }
    }
}

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
    /// If the clause collector runs out of memory, or writing the proof fails
    fn encode_ub_change_cert<Col, R, W>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
    ) -> Result<(), EncodingError>
    where
        Col: CollectClauses,
        R: std::ops::RangeBounds<usize>,
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
    /// If the clause collector runs out of memory, or writing the proof fails
    fn encode_lb_change_cert<Col, R, W>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
    ) -> Result<(), EncodingError>
    where
        Col: CollectClauses,
        R: std::ops::RangeBounds<usize>,
        W: std::io::Write;
}

/// Trait for incremental cardinality encodings that allow upper and lower bounding
pub trait BoundBothIncremental: BoundUpperIncremental + BoundLowerIncremental + BoundBoth {
    /// Lazily builds the _change in_ the certified cardinality encoding to enable both bounds in a
    /// given range. `var_manager` is the variable manager to use for tracking new variables. A
    /// specific encoding might ignore the lower or upper end of the range. The derivation of the
    /// encoding is written to the given `proof`.
    ///
    /// # Errors
    ///
    /// If the clause collector runs out of memory, or writing the proof fails
    fn encode_both_change_cert<Col, R, W>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
    ) -> Result<(), EncodingError>
    where
        Col: CollectClauses,
        R: std::ops::RangeBounds<usize> + Clone,
        W: std::io::Write,
    {
        self.encode_ub_change_cert(range.clone(), collector, var_manager, proof)?;
        self.encode_lb_change_cert(range, collector, var_manager, proof)?;
        Ok(())
    }
}

/// The default upper bound encoding. For now this is a [`super::Totalizer`].
pub type DefUpperBounding = super::Totalizer;
/// The default lower bound encoding. For now this is a [`super::Totalizer`].
pub type DefLowerBounding = super::Totalizer;
/// The default encoding for both bounds. For now this is a [`super::Totalizer`].
pub type DefBothBounding = super::Totalizer;
/// The default incremental upper bound encoding. For now this is a [`super::Totalizer`].
pub type DefIncUpperBounding = super::Totalizer;
/// The default incremental lower bound encoding. For now this is a [`super::Totalizer`].
pub type DefIncLowerBounding = super::Totalizer;
/// The default incremental encoding for both bounds. For now this is a [`super::Totalizer`].
pub type DefIncBothBounding = super::Totalizer;

/// Constructs a default upper bounding cardinality encoding.
#[must_use]
pub fn new_default_ub() -> impl BoundUpper {
    DefUpperBounding::default()
}

/// Constructs a default lower bounding cardinality encoding.
#[must_use]
pub fn new_default_lb() -> impl BoundLower {
    DefLowerBounding::default()
}

/// Constructs a default double bounding cardinality encoding.
#[must_use]
pub fn new_default_both() -> impl BoundBoth {
    DefBothBounding::default()
}

/// Constructs a default incremental upper bounding cardinality encoding.
#[must_use]
pub fn new_default_inc_ub() -> impl BoundUpperIncremental {
    DefIncUpperBounding::default()
}

/// Constructs a default incremental lower bounding cardinality encoding.
#[must_use]
pub fn new_default_inc_lb() -> impl BoundLower {
    DefIncLowerBounding::default()
}

/// Constructs a default incremental double bounding cardinality encoding.
#[must_use]
pub fn new_default_inc_both() -> impl BoundBoth {
    DefIncBothBounding::default()
}

/// A default encoder for any cardinality constraint. This uses a
/// [`DefBothBounding`] to encode non-trivial constraints.
///
/// # Errors
///
/// If the clause collector runs out of memory, or writing the proof fails
pub fn default_encode_cardinality_constraint<Col: CollectClauses, W: std::io::Write>(
    constr: (CardConstraint, pigeons::AbsConstraintId),
    collector: &mut Col,
    var_manager: &mut dyn ManageVars,
    proof: &mut pigeons::Proof<W>,
) -> Result<(), EncodingError> {
    encode_cardinality_constraint::<DefBothBounding, Col, W>(constr, collector, var_manager, proof)
}

/// An encoder for any cardinality constraint with an encoding of choice
///
/// # Errors
///
/// If the clause collector runs out of memory, or writing the proof fails
pub fn encode_cardinality_constraint<
    CE: BoundBoth + FromIterator<Lit>,
    Col: CollectClauses,
    W: std::io::Write,
>(
    constr: (CardConstraint, pigeons::AbsConstraintId),
    collector: &mut Col,
    var_manager: &mut dyn ManageVars,
    proof: &mut pigeons::Proof<W>,
) -> Result<(), EncodingError> {
    let (constr, mut id) = constr;
    if constr.is_tautology() {
        return Ok(());
    }
    if constr.is_unsat() {
        let empty = crate::clause![];
        let unsat_id = proof.reverse_unit_prop(&empty, [id.into()])?;
        collector.add_cert_clause(empty, unsat_id)?;
        return Ok(());
    }
    if constr.is_positive_assignment() {
        for lit in constr.into_lits() {
            let unit = crate::clause![lit];
            let unit_id = proof.reverse_unit_prop(&unit, [id.into()])?;
            collector.add_cert_clause(unit, unit_id)?;
        }
        return Ok(());
    }
    if constr.is_negative_assignment() {
        if matches!(constr, CardConstraint::Eq(_)) {
            id += 1;
        }
        for lit in constr.into_lits() {
            let unit = crate::clause![!lit];
            let unit_id = proof.reverse_unit_prop(&unit, [id.into()])?;
            collector.add_cert_clause(unit, unit_id)?;
        }
        return Ok(());
    }
    if constr.is_clause() {
        let clause = crate::utils::unreachable_err!(constr.into_clause());
        let cl_id = proof.reverse_unit_prop(&clause, [id.into()])?;
        collector.add_cert_clause(clause, cl_id)?;
        return Ok(());
    }
    match CE::encode_constr_cert((constr, id), collector, var_manager, proof) {
        Ok(()) => Ok(()),
        Err(ConstraintEncodingError::OutOfMemory(err)) => Err(err.into()),
        Err(ConstraintEncodingError::Proof(err)) => Err(err.into()),
        Err(ConstraintEncodingError::Unsat) => unreachable!(),
    }
}
