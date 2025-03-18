//! # Certified CNF Encodings for Pseudo-Boolean Constraints

use std::ops::RangeBounds;

use pigeons::AbsConstraintId;

use crate::{
    clause,
    encodings::{card, CollectCertClauses},
    instances::ManageVars,
    types::{
        constraints::{PbConstraint, PbEqConstr, PbLbConstr, PbUbConstr},
        Lit,
    },
    utils::unreachable_err,
};

use super::{simulators, DbGte};

/// Trait for certified PB encodings that allow upper bounding of the form `sum of lits <=
/// ub`
pub trait BoundUpper: super::Encode + super::BoundUpper {
    /// Lazily builds the certified PB encoding to enable upper bounds in a given range.
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
        proof: &mut pigeons::Proof<W>,
    ) -> anyhow::Result<()>
    where
        Col: CollectCertClauses,
        R: RangeBounds<usize>,
        W: std::io::Write;

    /// Encodes an upper bound pseudo-boolean constraint to CNF with proof logging
    ///
    /// # Errors
    ///
    /// - Either an [`super::Error`] or [`crate::OutOfMemory`]
    /// - [`std::io::Error`] if writing the proof fails
    fn encode_ub_constr_cert<Col, W>(
        constr: (PbUbConstr, AbsConstraintId),
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
    ) -> anyhow::Result<()>
    where
        Col: CollectCertClauses,
        W: std::io::Write,
        Self: FromIterator<(Lit, usize)> + Sized;
}

/// Trait for certified PB encodings that allow lower bounding of the form `sum of lits >=
/// lb`
pub trait BoundLower: super::Encode + super::BoundLower {
    /// Lazily builds the certified PB encoding to enable lower bounds in a given range.
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
        proof: &mut pigeons::Proof<W>,
    ) -> anyhow::Result<()>
    where
        Col: CollectCertClauses,
        R: RangeBounds<usize>,
        W: std::io::Write;

    /// Encodes a lower bound pseudo-boolean constraint to CNF with proof logging
    ///
    /// # Errors
    ///
    /// - Either an [`super::Error`] or [`crate::OutOfMemory`]
    /// - [`std::io::Error`] if writing the proof fails
    fn encode_lb_constr_cert<Col, W>(
        constr: (PbLbConstr, AbsConstraintId),
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
    ) -> anyhow::Result<()>
    where
        Col: CollectCertClauses,
        W: std::io::Write,
        Self: FromIterator<(Lit, usize)> + Sized;
}

/// Trait for certified PB encodings that allow upper and lower bounding
pub trait BoundBoth: BoundUpper + BoundLower + super::BoundBoth {
    /// Lazily builds the certified PB encoding to enable both bounds in a given range.
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
        proof: &mut pigeons::Proof<W>,
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

    /// Encodes an equality pseudo-boolean constraint to CNF with proof logging
    ///
    /// # Errors
    ///
    /// - Either an [`super::Error`] or [`crate::OutOfMemory`]
    /// - [`std::io::Error`] if writing the proof fails
    fn encode_eq_constr_cert<Col, W>(
        constr: (PbEqConstr, AbsConstraintId),
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
    ) -> anyhow::Result<()>
    where
        Col: CollectCertClauses,
        W: std::io::Write,
        Self: FromIterator<(Lit, usize)> + Sized,
    {
        // Assume the two constraints have ID as given and +1
        let (constr, id) = constr;
        let (lb_c, ub_c) = constr.split();
        Self::encode_lb_constr_cert((lb_c, id), collector, var_manager, proof)?;
        Self::encode_ub_constr_cert((ub_c, id + 1), collector, var_manager, proof)?;
        Ok(())
    }

    /// Encodes any pseudo-boolean constraint to CNF with proof logging
    ///
    /// # Errors
    ///
    /// - Either an [`super::Error`] or [`crate::OutOfMemory`]
    /// - [`std::io::Error`] if writing the proof fails
    fn encode_constr_cert<Col, W>(
        constr: (PbConstraint, AbsConstraintId),
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
    ) -> anyhow::Result<()>
    where
        Col: CollectCertClauses,
        W: std::io::Write,
        Self: FromIterator<(Lit, usize)> + Sized,
    {
        let (constr, id) = constr;
        match constr {
            PbConstraint::Ub(constr) => {
                Self::encode_ub_constr_cert((constr, id), collector, var_manager, proof)
            }
            PbConstraint::Lb(constr) => {
                Self::encode_lb_constr_cert((constr, id), collector, var_manager, proof)
            }
            PbConstraint::Eq(constr) => {
                Self::encode_eq_constr_cert((constr, id), collector, var_manager, proof)
            }
        }
    }
}

/// Trait for incremental certified PB encodings that allow upper bounding of the form
/// `sum of lits <= ub`
pub trait BoundUpperIncremental: BoundUpper + super::EncodeIncremental {
    /// Lazily builds the _change in_ the certified PB encoding to enable upper bounds in
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
        proof: &mut pigeons::Proof<W>,
    ) -> anyhow::Result<()>
    where
        Col: CollectCertClauses,
        R: RangeBounds<usize>,
        W: std::io::Write;
}

/// Trait for incremental certified PB encodings that allow lower bounding of the form
/// `sum of lits >= lb`
pub trait BoundLowerIncremental: BoundLower + super::EncodeIncremental {
    /// Lazily builds the _change in_ the certified PB encoding to enable upper bounds in
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
        proof: &mut pigeons::Proof<W>,
    ) -> anyhow::Result<()>
    where
        Col: CollectCertClauses,
        R: RangeBounds<usize>,
        W: std::io::Write;
}

/// Trait for incremental PB encodings that allow upper and lower bounding
pub trait BoundBothIncremental: BoundUpperIncremental + BoundLowerIncremental + BoundBoth {
    /// Lazily builds the _change in_ the certified PB encoding to enable both bounds in a
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
        proof: &mut pigeons::Proof<W>,
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

/// The default upper bound encoding. For now this is a [`DbGte`].
pub type DefUpperBounding = DbGte;
/// The default lower bound encoding. For now this is an inverted [`DbGte`].
pub type DefLowerBounding = simulators::Inverted<DbGte>;
/// The default encoding for both bounds. For now this is a doubled [`DbGte`].
pub type DefBothBounding = simulators::Double<DbGte, simulators::Inverted<DbGte>>;
/// The default incremental upper bound encoding. For now this is a [`DbGte`].
pub type DefIncUpperBounding = DbGte;
/// The default incremental lower bound encoding. For now this is an inverted [`DbGte`].
pub type DefIncLowerBounding = simulators::Inverted<DbGte>;
/// The default incremental encoding for both bounds. For now this is a doubled [`DbGte`].
pub type DefIncBothBounding = simulators::Double<DbGte, simulators::Inverted<DbGte>>;

/// Constructs a default upper bounding pseudo-boolean encoding.
#[must_use]
pub fn new_default_ub() -> impl BoundUpper + Extend<(Lit, usize)> {
    DefUpperBounding::default()
}

/// Constructs a default lower bounding pseudo-boolean encoding.
#[must_use]
pub fn new_default_lb() -> impl BoundLower + Extend<(Lit, usize)> {
    DefLowerBounding::default()
}

/// Constructs a default double bounding pseudo-boolean encoding.
#[must_use]
pub fn new_default_both() -> impl BoundBoth + Extend<(Lit, usize)> {
    DefBothBounding::default()
}

/// Constructs a default incremental upper bounding pseudo-boolean encoding.
#[must_use]
pub fn new_default_inc_ub() -> impl BoundUpperIncremental + Extend<(Lit, usize)> {
    DefIncUpperBounding::default()
}

/// Constructs a default incremental lower bounding pseudo-boolean encoding.
#[must_use]
pub fn new_default_inc_lb() -> impl BoundLower + Extend<(Lit, usize)> {
    DefIncLowerBounding::default()
}

/// Constructs a default incremental double bounding pseudo-boolean encoding.
#[must_use]
pub fn new_default_inc_both() -> impl BoundBoth + Extend<(Lit, usize)> {
    DefIncBothBounding::default()
}

/// A default encoder for any pseudo-boolean constraint. This uses a
/// [`DefBothBounding`] to encode true pseudo-boolean constraints and
/// [`card::cert::default_encode_cardinality_constraint`] for cardinality constraints.
///
/// # Errors
///
/// - If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
/// - If writing the proof fails, returns [`std::io::Error`]
pub fn default_encode_pb_constraint<Col: CollectCertClauses, W: std::io::Write>(
    constr: (PbConstraint, AbsConstraintId),
    collector: &mut Col,
    var_manager: &mut dyn ManageVars,
    proof: &mut pigeons::Proof<W>,
) -> anyhow::Result<()> {
    encode_pb_constraint::<DefBothBounding, Col, W>(constr, collector, var_manager, proof)
}

/// An encoder for any pseudo-boolean constraint with an encoding of choice
///
/// # Errors
///
/// If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
pub fn encode_pb_constraint<
    PBE: BoundBoth + FromIterator<(Lit, usize)>,
    Col: CollectCertClauses,
    W: std::io::Write,
>(
    constr: (PbConstraint, AbsConstraintId),
    collector: &mut Col,
    var_manager: &mut dyn ManageVars,
    proof: &mut pigeons::Proof<W>,
) -> anyhow::Result<()> {
    let (constr, mut id) = constr;
    if constr.is_tautology() {
        return Ok(());
    }
    if constr.is_unsat() {
        let empty = clause![];
        let unsat_id = proof.reverse_unit_prop(&empty, [id.into()])?;
        collector.add_cert_clause(empty, unsat_id)?;
        return Ok(());
    }
    if constr.is_positive_assignment() {
        for (lit, _) in constr.into_lits() {
            let unit = clause![lit];
            let unit_id = proof.reverse_unit_prop(&unit, [id.into()])?;
            collector.add_cert_clause(unit, unit_id)?;
        }
        return Ok(());
    }
    if constr.is_negative_assignment() {
        if matches!(constr, PbConstraint::Eq(_)) {
            id += 1;
        }
        for (lit, _) in constr.into_lits() {
            let unit = clause![!lit];
            let unit_id = proof.reverse_unit_prop(&unit, [id.into()])?;
            collector.add_cert_clause(unit, unit_id)?;
        }
        return Ok(());
    }
    if constr.is_clause() {
        let clause = unreachable_err!(constr.into_clause());
        let cl_id = proof.reverse_unit_prop(&clause, [id.into()])?;
        collector.add_cert_clause(clause, cl_id)?;
        return Ok(());
    }
    if constr.is_card() {
        let card = unreachable_err!(constr.into_card_constr());
        return card::cert::default_encode_cardinality_constraint(
            (card, id),
            collector,
            var_manager,
            proof,
        );
    }
    PBE::encode_constr_cert((constr, id), collector, var_manager, proof)
}
