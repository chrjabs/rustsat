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
//!     encodings::{pb, pb::{BothB, Encode}},
//!     instances::{BasicVarManager, ManageVars},
//!     lit, solvers,
//!     solvers::{SolverResult, Solve, IncrementalSolve},
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
//! solver.add_cnf(enc.encode_both(4, 4, &mut var_manager).unwrap());
//!
//! let mut assumps = enc.enforce_eq(4).unwrap();
//! assumps.extend(vec![!lit![0], lit![1], lit![2], !lit![3]]);
//! let res = solver.solve_assumps(assumps).unwrap();
//! assert_eq!(res, SolverResult::SAT);
//!
//! let mut assumps = enc.enforce_eq(4).unwrap();
//! assumps.extend(vec![!lit![0], !lit![1], lit![2], lit![3]]);
//! let res = solver.solve_assumps(assumps).unwrap();
//! assert_eq!(res, SolverResult::UNSAT);
//! ```
//!
//! When using cardinality and pseudo-boolean encodings at the same time, it is
//! recommended to import only the modules or rename the traits, e.g., `use
//! card::Encode as EncodePB`.

use super::{card, EncodingError};
use crate::{
    instances::{ManageVars, CNF},
    types::{
        constraints::{PBConstraint, PBEQConstr, PBLBConstr, PBUBConstr},
        Clause, Lit, RsHashMap,
    },
};

mod gte;
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
pub trait UB: Encode {
    /// Lazily builds the pseudo-boolean encoding to enable upper bounds from
    /// `min_ub` to `max_ub`. `var_manager` is the variable manager to use for
    /// tracking new variables. A specific encoding might ignore `min_ub` or
    /// `max_ub`. Returns [`EncodingError::InvalidLimits`] if the bounds are
    /// invalid.
    fn encode_ub(
        &mut self,
        min_ub: usize,
        max_ub: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError>;
    /// Returns assumptions/units for enforcing an upper bound (`weighted sum of
    /// lits <= ub`). Make sure that [`UBPB::encode_ub`] has been called
    /// adequately and nothing has been called afterwards, otherwise
    /// [`EncodingError::NotEncoded`] will be returned.
    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, EncodingError>;
    /// Encodes an upper bound pseudo-boolean constraint to CNF
    fn encode_ub_constr(
        constr: PBUBConstr,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError>
    where
        Self: Sized,
    {
        let mut enc = Self::default();
        let (lits, ub) = constr.decompose();
        let ub = if ub < 0 {
            return Err(EncodingError::Unsat);
        } else {
            ub as usize
        };
        enc.extend(lits);
        let mut cnf = enc.encode_ub(ub, ub, var_manager)?;
        enc.enforce_ub(ub)
            .unwrap()
            .into_iter()
            .for_each(|unit| cnf.add_unit(unit));
        Ok(cnf)
    }
}

/// Trait for pseudo-boolean encodings that allow upper bounding of the form `sum
/// of lits <= ub`
pub trait LB: Encode {
    /// Lazily builds the pseudo-boolean encoding to enable lower bounds from
    /// `min_lb` to `max_lb`. `var_manager` is the variable manager to use for
    /// tracking new variables. A specific encoding might ignore `min_lb` or
    /// `max_lb`. Returns [`EncodingError::InvalidLimits`] if the bounds are
    /// invalid.
    fn encode_lb(
        &mut self,
        min_lb: usize,
        max_lb: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError>;
    /// Returns assumptions/units for enforcing a lower bound (`sum of lits >=
    /// lb`). Make sure that [`LBPB::encode_lb`] has been called adequately and
    /// nothing has been added afterwards, otherwise
    /// [`EncodingError::NotEncoded`] will be returned. If `lb` is higher than
    /// the weighted sum of literals in the encoding, [`EncodingError::Unsat`]
    /// is returned.
    fn enforce_lb(&self, lb: usize) -> Result<Vec<Lit>, EncodingError>;
    /// Encodes a lower bound pseudo-boolean constraint to CNF
    fn encode_lb_constr(
        constr: PBLBConstr,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError>
    where
        Self: Sized,
    {
        let mut enc = Self::default();
        let (lits, lb) = constr.decompose();
        let lb = if lb < 0 {
            return Ok(CNF::new()); // tautology
        } else {
            lb as usize
        };
        enc.extend(lits);
        let mut cnf = enc.encode_lb(lb, lb, var_manager)?;
        enc.enforce_lb(lb)
            .unwrap()
            .into_iter()
            .for_each(|unit| cnf.add_unit(unit));
        Ok(cnf)
    }
}

/// Trait for pseudo-boolean encodings that allow upper and lower bounding
pub trait BothB: UB + LB {
    /// Lazily builds the pseudo-boolean encoding to enable both bounds from
    /// `min_b` to `max_b`. `var_manager` is the variable manager to use for
    /// tracking new variables. A specific encoding might ignore `min_lb` or
    /// `max_lb`. Returns [`EncodingError::InvalidLimits`] if the bounds are
    /// invalid.
    fn encode_both(
        &mut self,
        min_b: usize,
        max_b: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError> {
        let mut cnf = self.encode_ub(min_b, max_b, var_manager)?;
        cnf.extend(self.encode_lb(min_b, max_b, var_manager)?);
        Ok(cnf)
    }
    /// Returns assumptions for enforcing an equality (`sum of lits = b`) or an
    /// error if the encoding does not support one of the two required bound
    /// types. Make sure the adequate `encode_x` methods have been called before
    /// this method and nothing has been added afterwards, otherwise
    /// [`EncodingError::NotEncoded`] will be returned. If `b` is higher than
    /// the number of literals in the encoding, [`EncodingError::Unsat`] is
    /// returned.
    fn enforce_eq(&self, b: usize) -> Result<Vec<Lit>, EncodingError> {
        let mut assumps = self.enforce_ub(b)?;
        assumps.extend(self.enforce_lb(b)?);
        Ok(assumps)
    }
    /// Encodes an equality pseudo-boolean constraint to CNF
    fn encode_eq_constr(
        constr: PBEQConstr,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError>
    where
        Self: Sized,
    {
        let mut enc = Self::default();
        let (lits, b) = constr.decompose();
        let b = if b < 0 {
            return Err(EncodingError::Unsat);
        } else {
            b as usize
        };
        enc.extend(lits);
        let mut cnf = enc.encode_both(b, b, var_manager)?;
        enc.enforce_eq(b)
            .unwrap()
            .into_iter()
            .for_each(|unit| cnf.add_unit(unit));
        Ok(cnf)
    }
    /// Encodes any pseudo-boolean constraint to CNF
    fn encode_constr(
        constr: PBConstraint,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError>
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

/// Default implementation of [`BothBPB`] for every encoding that does upper
/// and lower bounding
impl<PBE> BothB for PBE where PBE: UB + LB {}

/// Trait for all pseudo-boolean encodings of form `sum of lits <> rhs`
pub trait IncEncode: Encode {
    /// Reserves all variables this encoding might need
    fn reserve(&mut self, var_manager: &mut dyn ManageVars);
}

/// Trait for incremental pseudo-boolean encodings that allow upper bounding of the
/// form `sum of lits <= ub`
pub trait IncUB: UB + IncEncode {
    /// Lazily builds the _change in_ pseudo-boolean encoding to enable upper
    /// bounds from `min_ub` to `max_ub`. A change might be added literals or
    /// changed bounds. `var_manager` is the variable manager to use for
    /// tracking new variables. A specific encoding might ignore `min_ub` or
    /// `max_ub`. Returns [`EncodingError::InvalidLimits`] if the bounds are
    /// invalid.
    fn encode_ub_change(
        &mut self,
        min_ub: usize,
        max_ub: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError>;
}

/// Trait for incremental pseudo-boolean encodings that allow upper bounding of the
/// form `sum of lits <= ub`
pub trait IncLB: LB + IncEncode {
    /// Lazily builds the _change in_ pseudo-boolean encoding to enable lower
    /// bounds from `min_lb` to `max_lb`. `var_manager` is the variable manager
    /// to use for tracking new variables. A specific encoding might ignore
    /// `min_lb` or `max_lb`. Returns [`EncodingError::InvalidLimits`] if the
    /// bounds are invalid.
    fn encode_lb_change(
        &mut self,
        min_lb: usize,
        max_lb: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError>;
}

/// Trait for incremental pseudo-boolean encodings that allow upper and lower bounding
pub trait IncBothB: IncUB + IncLB {
    /// Lazily builds the _change in_ pseudo-boolean encoding to enable both bounds
    /// from `min_b` to `max_b`. `var_manager` is the variable manager to use
    /// for tracking new variables. A specific encoding might ignore `min_lb` or
    /// `max_lb`. Returns [`EncodingError::InvalidLimits`] if the bounds are
    /// invalid.
    fn encode_both_change(
        &mut self,
        min_b: usize,
        max_b: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError> {
        let mut cnf = self.encode_ub_change(min_b, max_b, var_manager)?;
        cnf.extend(self.encode_lb_change(min_b, max_b, var_manager)?);
        Ok(cnf)
    }
}

/// Default implementation of [`IncBothBPB`] for every encoding that does
/// incremental upper and lower bounding
impl<PBE> IncBothB for PBE where PBE: IncUB + IncLB {}

/// The default upper bound encoding. For now this is a [`GeneralizedTotalizer`].
pub type DefUB = GeneralizedTotalizer;
/// The default lower bound encoding. For now this is a [`InvertedGeneralizedTotalizer`].
pub type DefLB = InvertedGeneralizedTotalizer;
/// The default encoding for both bounds. For now this is a [`DoubleGeneralizedTotalizer`].
pub type DefBothB = DoubleGeneralizedTotalizer;
/// The default incremental upper bound encoding. For now this is a [`GeneralizedTotalizer`].
pub type DefIncUB = GeneralizedTotalizer;
/// The default incremental lower bound encoding. For now this is a [`InvertedGeneralizedTotalizer`].
pub type DefIncLB = InvertedGeneralizedTotalizer;
/// The default incremental encoding for both bounds. For now this is a [`DoubleGeneralizedTotalizer`].
pub type DefIncBothB = DoubleGeneralizedTotalizer;

/// Constructs a default upper bounding pseudo-boolean encoding.
pub fn new_default_ub() -> impl UB {
    DefUB::default()
}

/// Constructs a default lower bounding pseudo-boolean encoding.
pub fn new_default_lb() -> impl LB {
    DefLB::default()
}

/// Constructs a default double bounding pseudo-boolean encoding.
pub fn new_default_both() -> impl BothB {
    DefBothB::default()
}

/// Constructs a default incremental upper bounding pseudo-boolean encoding.
pub fn new_default_inc_ub() -> impl IncUB {
    DefIncUB::default()
}

/// Constructs a default incremental lower bounding pseudo-boolean encoding.
pub fn new_default_inc_lb() -> impl LB {
    DefIncLB::default()
}

/// Constructs a default incremental double bounding pseudo-boolean encoding.
pub fn new_default_inc_both() -> impl BothB {
    DefIncBothB::default()
}

/// A default encoder for any pseudo-boolean constraint. This uses a
/// [`DefBothB`] to encode true pseudo-boolean constraints and
/// [`card::default_encode_cardinality_constraint`] for cardinality constraints.
pub fn default_encode_pb_constraint(constr: PBConstraint, var_manager: &mut dyn ManageVars) -> CNF {
    if constr.is_tautology() {
        return CNF::new();
    }
    if constr.is_unsat() {
        let mut cnf = CNF::new();
        cnf.add_clause(Clause::new());
        return cnf;
    }
    if constr.is_assignment() {
        let mut cnf = CNF::new();
        let lits = constr.into_lits();
        lits.into_iter().for_each(|(l, _)| cnf.add_unit(l));
        return cnf;
    }
    if constr.is_card() {
        let card = constr.as_card_constr().unwrap();
        return card::default_encode_cardinality_constraint(card, var_manager);
    }
    DefBothB::encode_constr(constr, var_manager).unwrap()
}
