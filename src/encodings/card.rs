//! # CNF Encodings for Cardinality Constraints
//!
//! The module contains implementations of CNF encodings for cardinality
//! constraints. It defines traits for (non-)incremental cardinality constraints
//! and encodings implementing these traits.
//!
//! ## Example Usage
//!
//! ```
//! # use rustsat::{
//! #     clause,
//! #     encodings::card::{BoundBoth, DefIncBothBounding, Encode},
//! #     instances::{BasicVarManager, Cnf, ManageVars},
//! #     lit, solvers, var,
//! # };
//! #
//! let mut var_manager = BasicVarManager::default();
//! var_manager.increase_next_free(var![4]);
//!
//! let mut enc = DefIncBothBounding::from(vec![lit![0], lit![1], lit![2], lit![3]]);
//! let mut encoding = Cnf::new();
//! enc.encode_both(3..=3, &mut encoding, &mut var_manager);
//! ```
//!
//! When using cardinality and pseudo-boolean encodings at the same time, it is
//! recommended to import only the modules or rename the traits, e.g., `use
//! card::Encode as EncodeCard`.

use std::{
    cmp,
    ops::{Bound, Range, RangeBounds},
};

use super::{CollectClauses, Error};
use crate::{
    clause,
    instances::ManageVars,
    types::{
        constraints::{CardConstraint, CardEqConstr, CardLbConstr, CardUbConstr},
        Clause, Lit,
    },
    utils::unreachable_err,
};

pub mod totalizer;
pub use totalizer::Totalizer;

pub mod simulators;

pub mod dbtotalizer;
pub use dbtotalizer::DbTotalizer;

/// Trait for all cardinality encodings of form `sum of lits <> rhs`
pub trait Encode {
    /// Gets the number of input literals in the encoding
    fn n_lits(&self) -> usize;
}

/// Trait for cardinality encodings that allow upper bounding of the form `sum
/// of lits <= ub`
pub trait BoundUpper: Encode {
    /// Lazily builds the cardinality encoding to enable upper bounds in a given
    /// range. `var_manager` is the variable manager to use for tracking new
    /// variables. A specific encoding might ignore the lower or upper end of
    /// the range.
    ///
    /// # Errors
    ///
    /// If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
    fn encode_ub<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
        R: RangeBounds<usize>;
    /// Returns assumptions/units for enforcing an upper bound (`sum of lits <=
    /// ub`). Make sure that [`BoundUpper::encode_ub`] has been called
    /// adequately and nothing has been called afterwards.
    ///
    /// # Errors
    ///
    /// Returns [`Error::NotEncoded`] if [`BoundUpper::encode_ub`] has not been called
    /// adequately before.
    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, Error>;
    /// Encodes an upper bound cardinality constraint to CNF
    ///
    /// # Errors
    ///
    /// Either an [`enum@Error`] or [`crate::OutOfMemory`]
    fn encode_ub_constr<Col>(
        constr: CardUbConstr,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> anyhow::Result<()>
    where
        Col: CollectClauses,
        Self: FromIterator<Lit> + Sized,
    {
        let (lits, ub) = constr.decompose();
        let mut enc = Self::from_iter(lits);
        enc.encode_ub(ub..=ub, collector, var_manager)?;
        collector.extend_clauses(
            enc.enforce_ub(ub)
                .unwrap()
                .into_iter()
                .map(|unit| clause![unit]),
        )?;
        Ok(())
    }
}

/// Trait for cardinality encodings that allow upper bounding of the form `sum
/// of lits <= ub`
pub trait BoundLower: Encode {
    /// Lazily builds the cardinality encoding to enable lower bounds in a given
    /// range. `var_manager` is the variable manager to use for tracking new
    /// variables. A specific encoding might ignore the lower or upper end of
    /// the range.
    ///
    /// # Errors
    ///
    /// If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
    fn encode_lb<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
        R: RangeBounds<usize>;
    /// Returns assumptions/units for enforcing a lower bound (`sum of lits >=
    /// lb`). Make sure that [`BoundLower::encode_lb`] has been called
    /// adequately and nothing has been added afterwards.
    ///
    /// # Errors
    ///
    /// - [`Error::NotEncoded`] if [`BoundLower::encode_lb`] has not been called adequately
    /// - [`Error::Unsat`] if `lb` is higher than the number of literals in the encoding
    fn enforce_lb(&self, lb: usize) -> Result<Vec<Lit>, Error>;
    /// Encodes a lower bound cardinality constraint to CNF
    ///
    /// # Errors
    ///
    /// Either an [`enum@Error`] or [`crate::OutOfMemory`]
    fn encode_lb_constr<Col>(
        constr: CardLbConstr,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> anyhow::Result<()>
    where
        Col: CollectClauses,
        Self: FromIterator<Lit> + Sized,
    {
        let (lits, lb) = constr.decompose();
        let mut enc = Self::from_iter(lits);
        enc.encode_lb(lb..=lb, collector, var_manager)?;
        collector.extend_clauses(
            enc.enforce_lb(lb)
                .unwrap()
                .into_iter()
                .map(|unit| clause![unit]),
        )?;
        Ok(())
    }
}

/// Trait for cardinality encodings that allow upper and lower bounding
pub trait BoundBoth: BoundUpper + BoundLower {
    /// Lazily builds the cardinality encoding to enable both bounds in a given
    /// range. `var_manager` is the variable manager to use for tracking new
    /// variables. A specific encoding might ignore the lower or upper end of
    /// the range.
    ///
    /// # Errors
    ///
    /// If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
    fn encode_both<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
        R: RangeBounds<usize> + Clone,
    {
        self.encode_ub(range.clone(), collector, var_manager)?;
        self.encode_lb(range, collector, var_manager)?;
        Ok(())
    }
    /// Returns assumptions for enforcing an equality (`sum of lits = b`) or an
    /// error if the encoding does not support one of the two required bound
    /// types. Make sure the adequate `encode_x` methods have been called before
    /// this method and nothing has been added afterwards.
    ///
    /// # Errors
    ///
    /// - [`Error::NotEncoded`] if not adequately encoded
    /// - [`Error::Unsat`] if `b` is higher than the number of literals in the encoding
    fn enforce_eq(&self, b: usize) -> Result<Vec<Lit>, Error> {
        let mut assumps = self.enforce_ub(b)?;
        assumps.extend(self.enforce_lb(b)?);
        Ok(assumps)
    }
    /// Encodes an equality cardinality constraint to CNF
    ///
    /// # Errors
    ///
    /// Either an [`enum@Error`] or [`crate::OutOfMemory`]
    fn encode_eq_constr<Col>(
        constr: CardEqConstr,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> anyhow::Result<()>
    where
        Col: CollectClauses,
        Self: FromIterator<Lit> + Sized,
    {
        let (lits, b) = constr.decompose();
        let mut enc = Self::from_iter(lits);
        enc.encode_both(b..=b, collector, var_manager)?;
        collector.extend_clauses(
            enc.enforce_eq(b)
                .unwrap()
                .into_iter()
                .map(|unit| clause![unit]),
        )?;
        Ok(())
    }
    /// Encodes any cardinality constraint to CNF
    ///
    /// # Errors
    ///
    /// Either an [`enum@Error`] or [`crate::OutOfMemory`]
    fn encode_constr<Col>(
        constr: CardConstraint,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> anyhow::Result<()>
    where
        Col: CollectClauses,
        Self: FromIterator<Lit> + Sized,
    {
        match constr {
            CardConstraint::Ub(constr) => Self::encode_ub_constr(constr, collector, var_manager),
            CardConstraint::Lb(constr) => Self::encode_lb_constr(constr, collector, var_manager),
            CardConstraint::Eq(constr) => Self::encode_eq_constr(constr, collector, var_manager),
        }
    }
}

/// Default implementation of [`BoundBoth`] for every encoding that does upper
/// and lower bounding
impl<CE> BoundBoth for CE where CE: BoundUpper + BoundLower {}

/// Trait for all cardinality encodings of form `sum of lits <> rhs`
pub trait EncodeIncremental: Encode {
    /// Reserves all variables this encoding might need
    fn reserve(&mut self, var_manager: &mut dyn ManageVars);
}

/// Trait for incremental cardinality encodings that allow upper bounding of the
/// form `sum of lits <= ub`
pub trait BoundUpperIncremental: BoundUpper + EncodeIncremental {
    /// Lazily builds the _change in_ cardinality encoding to enable upper
    /// bounds in a given range. A change might be added literals or changed
    /// bounds. `var_manager` is the variable manager to use for tracking new
    /// variables. A specific encoding might ignore the lower or upper end of
    /// the range.
    ///
    /// # Errors
    ///
    /// If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
    fn encode_ub_change<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
        R: RangeBounds<usize>;
}

/// Trait for incremental cardinality encodings that allow upper bounding of the
/// form `sum of lits <= ub`
pub trait BoundLowerIncremental: BoundLower + EncodeIncremental {
    /// Lazily builds the _change in_ cardinality encoding to enable lower
    /// bounds in a given range. `var_manager` is the variable manager to use
    /// for tracking new variables. A specific encoding might ignore the lower
    /// or upper end of the range.
    ///
    /// # Errors
    ///
    /// If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
    fn encode_lb_change<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
        R: RangeBounds<usize>;
}

/// Trait for incremental cardinality encodings that allow upper and lower bounding
pub trait BoundBothIncremental: BoundUpperIncremental + BoundLowerIncremental {
    /// Lazily builds the _change in_ cardinality encoding to enable both bounds
    /// in a given range. `var_manager` is the variable manager to use for
    /// tracking new variables. A specific encoding might ignore the lower or
    /// upper end of the range.
    ///
    /// # Errors
    ///
    /// If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
    fn encode_both_change<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
        R: RangeBounds<usize> + Clone,
    {
        self.encode_ub_change(range.clone(), collector, var_manager)?;
        self.encode_lb_change(range, collector, var_manager)
    }
}

/// Default implementation of [`BoundBothIncremental`] for every encoding that
/// does incremental upper and lower bounding
impl<CE> BoundBothIncremental for CE where CE: BoundUpperIncremental + BoundLowerIncremental {}

/// The default upper bound encoding. For now this is a [`Totalizer`].
pub type DefUpperBounding = Totalizer;
/// The default lower bound encoding. For now this is a [`Totalizer`].
pub type DefLowerBounding = Totalizer;
/// The default encoding for both bounds. For now this is a [`Totalizer`].
pub type DefBothBounding = Totalizer;
/// The default incremental upper bound encoding. For now this is a [`Totalizer`].
pub type DefIncUpperBounding = Totalizer;
/// The default incremental lower bound encoding. For now this is a [`Totalizer`].
pub type DefIncLowerBounding = Totalizer;
/// The default incremental encoding for both bounds. For now this is a [`Totalizer`].
pub type DefIncBothBounding = Totalizer;

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
/// If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
pub fn default_encode_cardinality_constraint<Col: CollectClauses>(
    constr: CardConstraint,
    collector: &mut Col,
    var_manager: &mut dyn ManageVars,
) -> Result<(), crate::OutOfMemory> {
    encode_cardinality_constraint::<DefBothBounding, Col>(constr, collector, var_manager)
}

/// An encoder for any cardinality constraint with an encoding of choice
///
/// # Errors
///
/// If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
pub fn encode_cardinality_constraint<CE: BoundBoth + FromIterator<Lit>, Col: CollectClauses>(
    constr: CardConstraint,
    collector: &mut Col,
    var_manager: &mut dyn ManageVars,
) -> Result<(), crate::OutOfMemory> {
    if constr.is_tautology() {
        return Ok(());
    }
    if constr.is_unsat() {
        return collector.add_clause(Clause::new());
    }
    if constr.is_positive_assignment() {
        return collector.extend_clauses(constr.into_lits().into_iter().map(|lit| clause![lit]));
    }
    if constr.is_negative_assignment() {
        return collector.extend_clauses(constr.into_lits().into_iter().map(|lit| clause![!lit]));
    }
    if constr.is_clause() {
        return collector.add_clause(unreachable_err!(constr.into_clause()));
    }
    match CE::encode_constr(constr, collector, var_manager) {
        Ok(()) => Ok(()),
        Err(err) => Err(unreachable_err!(err.downcast::<crate::OutOfMemory>())),
    }
}

fn prepare_ub_range<Enc: Encode, R: RangeBounds<usize>>(enc: &Enc, range: R) -> Range<usize> {
    (match range.start_bound() {
        Bound::Included(b) => *b,
        Bound::Excluded(b) => b + 1,
        Bound::Unbounded => 0,
    })..match range.end_bound() {
        Bound::Included(b) => cmp::min(b + 1, enc.n_lits()),
        Bound::Excluded(b) => cmp::min(*b, enc.n_lits()),
        Bound::Unbounded => enc.n_lits(),
    }
}

fn prepare_lb_range<Enc: Encode, R: RangeBounds<usize>>(enc: &Enc, range: R) -> Range<usize> {
    (match range.start_bound() {
        Bound::Included(b) => cmp::max(*b, 1),
        Bound::Excluded(b) => cmp::max(b + 1, 1),
        Bound::Unbounded => 1,
    })..match range.end_bound() {
        Bound::Included(b) => cmp::min(b + 1, enc.n_lits() + 1),
        Bound::Excluded(b) => cmp::min(*b, enc.n_lits() + 1),
        Bound::Unbounded => enc.n_lits() + 1,
    }
}
