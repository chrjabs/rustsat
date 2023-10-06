//! # CNF Encodings for Pseudo-Boolean Constraints
//!
//! The module contains implementations of CNF encodings for pseudo-boolean
//! constraints. It defines traits for (non-)incremental PB constraints and
//! encodings implementing these traits.
//!
//! ## Example Useage
//!
//! ```
//! use rustsat::{
//!     clause,
//!     encodings::pb::{BoundBoth, DefIncBothBounding, Encode},
//!     instances::{BasicVarManager, Cnf, ManageVars},
//!     lit, solvers, var,
//!     types::RsHashMap,
//! };
//!
//! let mut var_manager = BasicVarManager::default();
//! var_manager.increase_next_free(var![4]);
//!
//! let mut lits = RsHashMap::default();
//! lits.insert(lit![0], 4);
//! lits.insert(lit![1], 2);
//! lits.insert(lit![2], 2);
//! lits.insert(lit![3], 6);
//! let mut enc = DefIncBothBounding::from(lits);
//! let mut encoding = Cnf::new();
//! enc.encode_both(4..=4, &mut encoding, &mut var_manager);
//! ```
//!
//! When using cardinality and pseudo-boolean encodings at the same time, it is
//! recommended to import only the modules or rename the traits, e.g., `use
//! card::Encode as EncodePB`.

use std::{
    cmp,
    ops::{Bound, Range, RangeBounds},
};

use super::{card, CollectClauses, Error};
use crate::{
    clause,
    instances::ManageVars,
    types::{
        constraints::{PBConstraint, PBEQConstr, PBLBConstr, PBUBConstr},
        Clause, Lit,
    },
};

pub mod gte;
pub use gte::GeneralizedTotalizer;

pub mod simulators;
pub type InvertedGeneralizedTotalizer = simulators::Inverted<GeneralizedTotalizer>;
pub type DoubleGeneralizedTotalizer =
    simulators::Double<GeneralizedTotalizer, InvertedGeneralizedTotalizer>;

pub mod dpw;
pub use dpw::DynamicPolyWatchdog;

pub mod dbgte;
pub use dbgte::DbGte;

/// Trait for all pseudo-boolean encodings of form `weighted sum of lits <> rhs`
pub trait Encode {
    /// Get the sum of weights in the encoding
    fn weight_sum(&self) -> usize;
    /// Gets the next higher value possible to be achieved by the weighted sum.
    /// Might simply return `val + 1` if no stronger value can be inferred.
    fn next_higher(&self, val: usize) -> usize {
        val + 1
    }
    /// Gets the next lower value possible to be achieved by the weighted sum.
    /// Might simply return `val - 1` if no stronger value can be inferred.
    fn next_lower(&self, val: usize) -> usize {
        val - 1
    }
}

/// Trait for pseudo-boolean encodings that allow upper bounding of the form `sum
/// of lits <= ub`
pub trait BoundUpper: Encode {
    /// Lazily builds the pseudo-boolean encoding to enable upper bounds within
    /// a given range. `var_manager` is the variable manager to use for tracking
    /// new variables. A specific encoding might ignore the upper or lower end
    /// of the range.
    fn encode_ub<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) where
        Col: CollectClauses,
        R: RangeBounds<usize>;
    /// Returns assumptions/units for enforcing an upper bound (`weighted sum of
    /// lits <= ub`). Make sure that [`BoundUpper::encode_ub`] has been called
    /// adequately and nothing has been called afterwards, otherwise
    /// [`Error::NotEncoded`] will be returned.
    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, Error>;
    /// Encodes an upper bound pseudo-boolean constraint to CNF
    fn encode_ub_constr<Col>(
        constr: PBUBConstr,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), Error>
    where
        Col: CollectClauses,
        Self: FromIterator<(Lit, usize)> + Sized,
    {
        let (lits, ub) = constr.decompose();
        let ub = if ub < 0 {
            return Err(Error::Unsat);
        } else {
            ub as usize
        };
        let mut enc = Self::from_iter(lits);
        enc.encode_ub(ub..ub + 1, collector, var_manager);
        collector.extend(
            enc.enforce_ub(ub)
                .unwrap()
                .into_iter()
                .map(|unit| clause![unit]),
        );
        Ok(())
    }
    /// Gets the next smaller upper bound value that can be _easily_ encoded. This
    /// is used for coarse convergence, e.g., with the [`DynamicPolyWatchdog`]
    /// encoding.
    fn coarse_ub(&self, ub: usize) -> usize {
        ub
    }
}

/// Trait for pseudo-boolean encodings that allow upper bounding of the form `sum
/// of lits <= ub`
pub trait BoundLower: Encode {
    /// Lazily builds the pseudo-boolean encoding to enable lower bounds in a
    /// given range. `var_manager` is the variable manager to use for tracking
    /// new variables. A specific encoding might ignore the upper or lower end
    /// of the range.
    fn encode_lb<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) where
        Col: CollectClauses,
        R: RangeBounds<usize>;
    /// Returns assumptions/units for enforcing a lower bound (`sum of lits >=
    /// lb`). Make sure that [`BoundLower::encode_lb`] has been called
    /// adequately and nothing has been added afterwards, otherwise
    /// [`Error::NotEncoded`] will be returned. If `lb` is higher than
    /// the weighted sum of literals in the encoding, [`Error::Unsat`]
    /// is returned.
    fn enforce_lb(&self, lb: usize) -> Result<Vec<Lit>, Error>;
    /// Encodes a lower bound pseudo-boolean constraint to CNF
    fn encode_lb_constr<Col>(
        constr: PBLBConstr,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), Error>
    where
        Col: CollectClauses,
        Self: FromIterator<(Lit, usize)> + Sized,
    {
        let (lits, lb) = constr.decompose();
        let lb = if lb < 0 {
            return Ok(()); // tautology
        } else {
            lb as usize
        };
        let mut enc = Self::from_iter(lits);
        enc.encode_lb(lb..lb + 1, collector, var_manager);
        collector.extend(
            enc.enforce_lb(lb)
                .unwrap()
                .into_iter()
                .map(|unit| clause![unit]),
        );
        Ok(())
    }
    /// Gets the next greater lower bound value that can be _easily_ encoded. This
    /// is used for coarse convergence.
    fn coarse_lb(&self, lb: usize) -> usize {
        lb
    }
}

/// Trait for pseudo-boolean encodings that allow upper and lower bounding
pub trait BoundBoth: BoundUpper + BoundLower {
    /// Lazily builds the pseudo-boolean encoding to enable both bounds in a
    /// given range. `var_manager` is the variable manager to use for tracking
    /// new variables. A specific encoding might ignore the upper or lower end
    /// of the range.
    fn encode_both<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) where
        Col: CollectClauses,
        R: RangeBounds<usize> + Clone,
    {
        self.encode_ub(range.clone(), collector, var_manager);
        self.encode_lb(range, collector, var_manager);
    }
    /// Returns assumptions for enforcing an equality (`sum of lits = b`) or an
    /// error if the encoding does not support one of the two required bound
    /// types. Make sure the adequate `encode_x` methods have been called before
    /// this method and nothing has been added afterwards, otherwise
    /// [`Error::NotEncoded`] will be returned. If `b` is higher than
    /// the number of literals in the encoding, [`Error::Unsat`] is
    /// returned.
    fn enforce_eq(&self, b: usize) -> Result<Vec<Lit>, Error> {
        let mut assumps = self.enforce_ub(b)?;
        assumps.extend(self.enforce_lb(b)?);
        Ok(assumps)
    }
    /// Encodes an equality pseudo-boolean constraint to CNF
    fn encode_eq_constr<Col>(
        constr: PBEQConstr,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), Error>
    where
        Col: CollectClauses,
        Self: FromIterator<(Lit, usize)> + Sized,
    {
        let (lits, b) = constr.decompose();
        let b = if b < 0 {
            return Err(Error::Unsat);
        } else {
            b as usize
        };
        let mut enc = Self::from_iter(lits);
        enc.encode_both(b..b + 1, collector, var_manager);
        collector.extend(
            enc.enforce_eq(b)
                .unwrap()
                .into_iter()
                .map(|unit| clause![unit]),
        );
        Ok(())
    }
    /// Encodes any pseudo-boolean constraint to CNF
    fn encode_constr<Col>(
        constr: PBConstraint,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), Error>
    where
        Col: CollectClauses,
        Self: FromIterator<(Lit, usize)> + Sized,
    {
        match constr {
            PBConstraint::UB(constr) => Self::encode_ub_constr(constr, collector, var_manager),
            PBConstraint::LB(constr) => Self::encode_lb_constr(constr, collector, var_manager),
            PBConstraint::EQ(constr) => Self::encode_eq_constr(constr, collector, var_manager),
        }
    }
}

/// Default implementation of [`BoundBoth`] for every encoding that does upper
/// and lower bounding
impl<PBE> BoundBoth for PBE where PBE: BoundUpper + BoundLower {}

/// Trait for all pseudo-boolean encodings of form `sum of lits <> rhs`
pub trait EncodeIncremental: Encode {
    /// Reserves all variables this encoding might need
    fn reserve(&mut self, var_manager: &mut dyn ManageVars);
}

/// Trait for incremental pseudo-boolean encodings that allow upper bounding of the
/// form `sum of lits <= ub`
pub trait BoundUpperIncremental: BoundUpper + EncodeIncremental {
    /// Lazily builds the _change in_ pseudo-boolean encoding to enable upper
    /// bounds from within the range. A change might be added literals or
    /// changed bounds. `var_manager` is the variable manager to use for
    /// tracking new variables. A specific encoding might ignore the lower or
    /// upper end of the range.
    fn encode_ub_change<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) where
        Col: CollectClauses,
        R: RangeBounds<usize>;
}

/// Trait for incremental pseudo-boolean encodings that allow upper bounding of the
/// form `sum of lits <= ub`
pub trait BoundLowerIncremental: BoundLower + EncodeIncremental {
    /// Lazily builds the _change in_ pseudo-boolean encoding to enable lower
    /// bounds within the range. `var_manager` is the variable manager to use
    /// for tracking new variables. A specific encoding might ignore the lower
    /// or upper end of the range.
    fn encode_lb_change<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) where
        Col: CollectClauses,
        R: RangeBounds<usize>;
}

/// Trait for incremental pseudo-boolean encodings that allow upper and lower bounding
pub trait BoundBothIncremental: BoundUpperIncremental + BoundLowerIncremental {
    /// Lazily builds the _change in_ pseudo-boolean encoding to enable both
    /// bounds from `min_b` to `max_b`. `var_manager` is the variable manager to
    /// use for tracking new variables. A specific encoding might ignore the
    /// lower or upper end of the range.
    fn encode_both_change<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) where
        Col: CollectClauses,
        R: RangeBounds<usize> + Clone,
    {
        self.encode_ub_change(range.clone(), collector, var_manager);
        self.encode_lb_change(range, collector, var_manager);
    }
}

/// Default implementation of [`BoundBothIncremental`] for every encoding that
/// does incremental upper and lower bounding
impl<PBE> BoundBothIncremental for PBE where PBE: BoundUpperIncremental + BoundLowerIncremental {}

/// The default upper bound encoding. For now this is a [`GeneralizedTotalizer`].
pub type DefUpperBounding = GeneralizedTotalizer;
/// The default lower bound encoding. For now this is a [`InvertedGeneralizedTotalizer`].
pub type DefLowerBounding = InvertedGeneralizedTotalizer;
/// The default encoding for both bounds. For now this is a [`DoubleGeneralizedTotalizer`].
pub type DefBothBounding = DoubleGeneralizedTotalizer;
/// The default incremental upper bound encoding. For now this is a [`GeneralizedTotalizer`].
pub type DefIncUpperBounding = GeneralizedTotalizer;
/// The default incremental lower bound encoding. For now this is a [`InvertedGeneralizedTotalizer`].
pub type DefIncLowerBounding = InvertedGeneralizedTotalizer;
/// The default incremental encoding for both bounds. For now this is a [`DoubleGeneralizedTotalizer`].
pub type DefIncBothBounding = DoubleGeneralizedTotalizer;

/// Constructs a default upper bounding pseudo-boolean encoding.
pub fn new_default_ub() -> impl BoundUpper + Extend<(Lit, usize)> {
    DefUpperBounding::default()
}

/// Constructs a default lower bounding pseudo-boolean encoding.
pub fn new_default_lb() -> impl BoundLower + Extend<(Lit, usize)> {
    DefLowerBounding::default()
}

/// Constructs a default double bounding pseudo-boolean encoding.
pub fn new_default_both() -> impl BoundBoth + Extend<(Lit, usize)> {
    DefBothBounding::default()
}

/// Constructs a default incremental upper bounding pseudo-boolean encoding.
pub fn new_default_inc_ub() -> impl BoundUpperIncremental + Extend<(Lit, usize)> {
    DefIncUpperBounding::default()
}

/// Constructs a default incremental lower bounding pseudo-boolean encoding.
pub fn new_default_inc_lb() -> impl BoundLower + Extend<(Lit, usize)> {
    DefIncLowerBounding::default()
}

/// Constructs a default incremental double bounding pseudo-boolean encoding.
pub fn new_default_inc_both() -> impl BoundBoth + Extend<(Lit, usize)> {
    DefIncBothBounding::default()
}

/// A default encoder for any pseudo-boolean constraint. This uses a
/// [`DefBothBounding`] to encode true pseudo-boolean constraints and
/// [`card::default_encode_cardinality_constraint`] for cardinality constraints.
pub fn default_encode_pb_constraint<Col: CollectClauses>(
    constr: PBConstraint,
    collector: &mut Col,
    var_manager: &mut dyn ManageVars,
) {
    encode_pb_constraint::<DefBothBounding, Col>(constr, collector, var_manager)
}

/// An encoder for any pseudo-boolean constraint with an encoding of choice
pub fn encode_pb_constraint<PBE: BoundBoth + FromIterator<(Lit, usize)>, Col: CollectClauses>(
    constr: PBConstraint,
    collector: &mut Col,
    var_manager: &mut dyn ManageVars,
) {
    if constr.is_tautology() {
        return;
    }
    if constr.is_unsat() {
        collector.extend([Clause::new()]);
        return;
    }
    if constr.is_positive_assignment() {
        collector.extend(constr.into_lits().into_iter().map(|(lit, _)| clause![lit]));
        return;
    }
    if constr.is_negative_assignment() {
        collector.extend(constr.into_lits().into_iter().map(|(lit, _)| clause![!lit]));
        return;
    }
    if constr.is_clause() {
        collector.extend([constr.as_clause().unwrap()]);
        return;
    }
    if constr.is_card() {
        let card = constr.as_card_constr().unwrap();
        return card::default_encode_cardinality_constraint(card, collector, var_manager);
    }
    PBE::encode_constr(constr, collector, var_manager).unwrap()
}

fn prepare_ub_range<Enc: Encode, R: RangeBounds<usize>>(enc: &Enc, range: R) -> Range<usize> {
    (match range.start_bound() {
        Bound::Included(b) => *b,
        Bound::Excluded(b) => b + 1,
        Bound::Unbounded => 0,
    })..match range.end_bound() {
        Bound::Included(b) => cmp::min(b + 1, enc.weight_sum()),
        Bound::Excluded(b) => cmp::min(*b, enc.weight_sum()),
        Bound::Unbounded => enc.weight_sum(),
    }
}

fn prepare_lb_range<Enc: Encode, R: RangeBounds<usize>>(enc: &Enc, range: R) -> Range<usize> {
    (match range.start_bound() {
        Bound::Included(b) => cmp::max(*b, 1),
        Bound::Excluded(b) => cmp::max(b + 1, 1),
        Bound::Unbounded => 1,
    })..match range.end_bound() {
        Bound::Included(b) => cmp::min(b + 1, enc.weight_sum() + 1),
        Bound::Excluded(b) => cmp::min(*b, enc.weight_sum() + 1),
        Bound::Unbounded => enc.weight_sum() + 1,
    }
}
