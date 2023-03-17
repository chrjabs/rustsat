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
//!     encodings::{pb, pb::{BoundBoth, Encode}},
//!     instances::{BasicVarManager, ManageVars},
//!     lit, solvers,
//!     solvers::{SolverResult, Solve, SolveIncremental},
//!     types::{Clause, Lit, Var, RsHashMap},
//!     var,
//! };
//!
//! let mut solver = solvers::new_default_inc_solver();
//! solver.add_clause(clause![lit![0], lit![1], lit![2], lit![3]]);
//! let mut var_manager = BasicVarManager::default();
//! var_manager.increase_next_free(var![4]);
//!
//! let mut enc = pb::new_default_inc_both();
//! let mut lits = RsHashMap::default();
//! lits.insert(lit![0], 4);
//! lits.insert(lit![1], 2);
//! lits.insert(lit![2], 2);
//! lits.insert(lit![3], 6);
//! enc.extend(lits);
//! solver.add_cnf(enc.encode_both(4..5, &mut var_manager));
//!
//! let mut assumps = enc.enforce_eq(4).unwrap();
//! assumps.extend(vec![!lit![0], lit![1], lit![2], !lit![3]]);
//! let res = solver.solve_assumps(assumps).unwrap();
//! assert_eq!(res, SolverResult::Sat);
//!
//! let mut assumps = enc.enforce_eq(4).unwrap();
//! assumps.extend(vec![!lit![0], !lit![1], lit![2], lit![3]]);
//! let res = solver.solve_assumps(assumps).unwrap();
//! assert_eq!(res, SolverResult::Unsat);
//! ```
//!
//! When using cardinality and pseudo-boolean encodings at the same time, it is
//! recommended to import only the modules or rename the traits, e.g., `use
//! card::Encode as EncodePB`.

use std::ops::Range;

use super::{card, Error};
use crate::{
    instances::{Cnf, ManageVars},
    types::{
        constraints::{PBConstraint, PBEQConstr, PBLBConstr, PBUBConstr},
        Clause, Lit, RsHashMap,
    },
};

pub mod gte;
pub use gte::GeneralizedTotalizer;
pub mod simulators;
pub type InvertedGeneralizedTotalizer = simulators::Inverted<GeneralizedTotalizer>;
pub type DoubleGeneralizedTotalizer =
    simulators::Double<GeneralizedTotalizer, InvertedGeneralizedTotalizer>;

/// Trait for all pseudo-boolean encodings of form `weighted sum of lits <> rhs`
pub trait Encode:
    Default + From<RsHashMap<Lit, usize>> + FromIterator<(Lit, usize)> + Extend<(Lit, usize)>
{
    type Iter<'a>: Iterator<Item = (Lit, usize)>
    where
        Self: 'a;
    /// Gets an iterator over copies of the input literals
    fn iter(&self) -> Self::Iter<'_>;
    /// Get the sum of weights in the encoding
    fn weight_sum(&self) -> usize;
}

/// Trait for pseudo-boolean encodings that allow upper bounding of the form `sum
/// of lits <= ub`
pub trait BoundUpper: Encode {
    /// Lazily builds the pseudo-boolean encoding to enable upper bounds within
    /// a given range. `var_manager` is the variable manager to use for tracking
    /// new variables. A specific encoding might ignore the upper or lower end
    /// of the range.
    fn encode_ub(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> Cnf;
    /// Returns assumptions/units for enforcing an upper bound (`weighted sum of
    /// lits <= ub`). Make sure that [`BoundUpper::encode_ub`] has been called
    /// adequately and nothing has been called afterwards, otherwise
    /// [`Error::NotEncoded`] will be returned.
    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, Error>;
    /// Encodes an upper bound pseudo-boolean constraint to CNF
    fn encode_ub_constr(constr: PBUBConstr, var_manager: &mut dyn ManageVars) -> Result<Cnf, Error>
    where
        Self: Sized,
    {
        let mut enc = Self::default();
        let (lits, ub) = constr.decompose();
        let ub = if ub < 0 {
            return Err(Error::Unsat);
        } else {
            ub as usize
        };
        enc.extend(lits);
        let mut cnf = enc.encode_ub(ub..ub + 1, var_manager);
        enc.enforce_ub(ub)
            .unwrap()
            .into_iter()
            .for_each(|unit| cnf.add_unit(unit));
        Ok(cnf)
    }
}

/// Trait for pseudo-boolean encodings that allow upper bounding of the form `sum
/// of lits <= ub`
pub trait BoundLower: Encode {
    /// Lazily builds the pseudo-boolean encoding to enable lower bounds in a
    /// given range. `var_manager` is the variable manager to use for tracking
    /// new variables. A specific encoding might ignore the upper or lower end
    /// of the range.
    fn encode_lb(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> Cnf;
    /// Returns assumptions/units for enforcing a lower bound (`sum of lits >=
    /// lb`). Make sure that [`BoundLower::encode_lb`] has been called
    /// adequately and nothing has been added afterwards, otherwise
    /// [`Error::NotEncoded`] will be returned. If `lb` is higher than
    /// the weighted sum of literals in the encoding, [`Error::Unsat`]
    /// is returned.
    fn enforce_lb(&self, lb: usize) -> Result<Vec<Lit>, Error>;
    /// Encodes a lower bound pseudo-boolean constraint to CNF
    fn encode_lb_constr(constr: PBLBConstr, var_manager: &mut dyn ManageVars) -> Result<Cnf, Error>
    where
        Self: Sized,
    {
        let mut enc = Self::default();
        let (lits, lb) = constr.decompose();
        let lb = if lb < 0 {
            return Ok(Cnf::new()); // tautology
        } else {
            lb as usize
        };
        enc.extend(lits);
        let mut cnf = enc.encode_lb(lb..lb + 1, var_manager);
        enc.enforce_lb(lb)
            .unwrap()
            .into_iter()
            .for_each(|unit| cnf.add_unit(unit));
        Ok(cnf)
    }
}

/// Trait for pseudo-boolean encodings that allow upper and lower bounding
pub trait BoundBoth: BoundUpper + BoundLower {
    /// Lazily builds the pseudo-boolean encoding to enable both bounds in a
    /// given range. `var_manager` is the variable manager to use for tracking
    /// new variables. A specific encoding might ignore the upper or lower end
    /// of the range.
    fn encode_both(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> Cnf {
        let cnf = self.encode_ub(range.clone(), var_manager);
        cnf.join(self.encode_lb(range, var_manager))
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
    fn encode_eq_constr(constr: PBEQConstr, var_manager: &mut dyn ManageVars) -> Result<Cnf, Error>
    where
        Self: Sized,
    {
        let mut enc = Self::default();
        let (lits, b) = constr.decompose();
        let b = if b < 0 {
            return Err(Error::Unsat);
        } else {
            b as usize
        };
        enc.extend(lits);
        let mut cnf = enc.encode_both(b..b + 1, var_manager);
        enc.enforce_eq(b)
            .unwrap()
            .into_iter()
            .for_each(|unit| cnf.add_unit(unit));
        Ok(cnf)
    }
    /// Encodes any pseudo-boolean constraint to CNF
    fn encode_constr(constr: PBConstraint, var_manager: &mut dyn ManageVars) -> Result<Cnf, Error>
    where
        Self: Sized,
    {
        match constr {
            PBConstraint::UB(constr) => Self::encode_ub_constr(constr, var_manager),
            PBConstraint::LB(constr) => Self::encode_lb_constr(constr, var_manager),
            PBConstraint::EQ(constr) => Self::encode_eq_constr(constr, var_manager),
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
    fn encode_ub_change(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> Cnf;
}

/// Trait for incremental pseudo-boolean encodings that allow upper bounding of the
/// form `sum of lits <= ub`
pub trait BoundLowerIncremental: BoundLower + EncodeIncremental {
    /// Lazily builds the _change in_ pseudo-boolean encoding to enable lower
    /// bounds within the range. `var_manager` is the variable manager to use
    /// for tracking new variables. A specific encoding might ignore the lower
    /// or upper end of the range.
    fn encode_lb_change(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> Cnf;
}

/// Trait for incremental pseudo-boolean encodings that allow upper and lower bounding
pub trait BoundBothIncremental: BoundUpperIncremental + BoundLowerIncremental {
    /// Lazily builds the _change in_ pseudo-boolean encoding to enable both
    /// bounds from `min_b` to `max_b`. `var_manager` is the variable manager to
    /// use for tracking new variables. A specific encoding might ignore the
    /// lower or upper end of the range.
    fn encode_both_change(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> Cnf {
        let cnf = self.encode_ub_change(range.clone(), var_manager);
        cnf.join(self.encode_lb_change(range, var_manager))
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
pub fn new_default_ub() -> impl BoundUpper {
    DefUpperBounding::default()
}

/// Constructs a default lower bounding pseudo-boolean encoding.
pub fn new_default_lb() -> impl BoundLower {
    DefLowerBounding::default()
}

/// Constructs a default double bounding pseudo-boolean encoding.
pub fn new_default_both() -> impl BoundBoth {
    DefBothBounding::default()
}

/// Constructs a default incremental upper bounding pseudo-boolean encoding.
pub fn new_default_inc_ub() -> impl BoundUpperIncremental {
    DefIncUpperBounding::default()
}

/// Constructs a default incremental lower bounding pseudo-boolean encoding.
pub fn new_default_inc_lb() -> impl BoundLower {
    DefIncLowerBounding::default()
}

/// Constructs a default incremental double bounding pseudo-boolean encoding.
pub fn new_default_inc_both() -> impl BoundBoth {
    DefIncBothBounding::default()
}

/// A default encoder for any pseudo-boolean constraint. This uses a
/// [`DefBothBounding`] to encode true pseudo-boolean constraints and
/// [`card::default_encode_cardinality_constraint`] for cardinality constraints.
pub fn default_encode_pb_constraint(constr: PBConstraint, var_manager: &mut dyn ManageVars) -> Cnf {
    encode_pb_constraint::<DefBothBounding>(constr, var_manager)
}

/// An encoder for any pseudo-boolean constraint with an encoding of choice
pub fn encode_pb_constraint<PBE: BoundBoth>(
    constr: PBConstraint,
    var_manager: &mut dyn ManageVars,
) -> Cnf {
    if constr.is_tautology() {
        return Cnf::new();
    }
    if constr.is_unsat() {
        let mut cnf = Cnf::new();
        cnf.add_clause(Clause::new());
        return cnf;
    }
    if constr.is_assignment() {
        let mut cnf = Cnf::new();
        let lits = constr.into_lits();
        lits.into_iter().for_each(|(l, _)| cnf.add_unit(l));
        return cnf;
    }
    if constr.is_card() {
        let card = constr.as_card_constr().unwrap();
        return card::default_encode_cardinality_constraint(card, var_manager);
    }
    PBE::encode_constr(constr, var_manager).unwrap()
}
