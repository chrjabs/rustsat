//! # CNF Encodings for Cardinality Constraints
//!
//! The module contains implementations of CNF encodings for cardinality
//! constraints. It defines traits for (non-)incremental cardinality constraints
//! and encodings implementing these traits.
//!
//! ## Example Useage
//!
//! ```
//! use rustsat::{
//!     clause,
//!     encodings::{card, card::{BothBCard, EncodeCard}},
//!     instances::{BasicVarManager, ManageVars},
//!     lit, solvers,
//!     solvers::{SolverResult, Solve, IncrementalSolve},
//!     types::{Clause, Lit, Var},
//!     var,
//! };
//!
//! let mut solver = solvers::new_default_inc_solver();
//! solver.add_clause(clause![lit![0], lit![1], lit![2], lit![3]]);
//! let mut var_manager = BasicVarManager::new();
//! var_manager.increase_next_free(var![4]);
//!
//! let mut enc = card::new_default_inc_both();
//! enc.add(vec![lit![0], lit![1], lit![2], lit![3]]);
//! solver.add_cnf(enc.encode_both(3, 3, &mut var_manager).unwrap());
//!
//! let mut assumps = enc.enforce_eq(3).unwrap();
//! assumps.extend(vec![lit![0], lit![1], lit![2], !lit![3]]);
//! let res = solver.solve_assumps(assumps).unwrap();
//! assert_eq!(res, SolverResult::SAT);
//!
//! let mut assumps = enc.enforce_eq(3).unwrap();
//! assumps.extend(vec![!lit![0], !lit![1], lit![2], lit![3]]);
//! let res = solver.solve_assumps(assumps).unwrap();
//! assert_eq!(res, SolverResult::UNSAT);
//! ```

use super::EncodingError;
use crate::{
    instances::{ManageVars, CNF},
    types::{
        constraints::{CardConstraint, CardEQConstr, CardLBConstr, CardUBConstr},
        Clause, Lit,
    },
};

mod totalizer;
pub use totalizer::Totalizer;
pub mod simulators;

/// Trait for all cardinality encodings of form `sum of lits <> rhs`
pub trait EncodeCard {
    type Iter<'a>: Iterator<Item = Lit> where Self: 'a;
    /// Constructs a new cardinality encoding
    fn new() -> Self
    where
        Self: Sized;
    /// Constructs a new cardinality encoding from input
    /// literals.
    fn new_from_lits<I>(lits: I) -> Self
    where
        Self: Sized,
        I: Iterator<Item = Lit>,
    {
        let lits = lits.collect();
        let mut ce = Self::new();
        ce.add(lits);
        ce
    }
    /// Adds new literals to the cardinality encoding
    fn add(&mut self, lits: Vec<Lit>);
    /// Gets an iterator over copies of the input literals
    fn iter<'a>(&'a self) -> Self::Iter<'a>;
    /// Gets the number of literals in the encoding
    fn n_lits(&self) -> usize;
}

/// Trait for cardinality encodings that allow upper bounding of the form `sum
/// of lits <= ub`
pub trait UBCard: EncodeCard {
    /// Lazily builds the cardinality encoding to enable upper bounds from
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
    /// Returns assumptions/units for enforcing an upper bound (`sum of lits <=
    /// ub`). Make sure that [`UBCard::encode_ub`] has been called adequately
    /// and nothing has been called afterwards, otherwise
    /// [`EncodingError::NotEncoded`] will be returned.
    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, EncodingError>;
    /// Encodes an upper bound cardinality constraint to CNF
    fn encode_ub_constr(
        constr: CardUBConstr,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError>
    where
        Self: Sized,
    {
        let mut enc = Self::new();
        let (lits, ub) = constr.decompose();
        enc.add(lits);
        let mut cnf = enc.encode_ub(ub, ub, var_manager)?;
        enc.enforce_ub(ub)
            .unwrap()
            .into_iter()
            .for_each(|unit| cnf.add_unit(unit));
        Ok(cnf)
    }
}

/// Trait for cardinality encodings that allow upper bounding of the form `sum
/// of lits <= ub`
pub trait LBCard: EncodeCard {
    /// Lazily builds the cardinality encoding to enable lower bounds from
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
    /// lb`). Make sure that [`LBCard::encode_lb`] has been called adequately
    /// and nothing has been added afterwards, otherwise
    /// [`EncodingError::NotEncoded`] will be returned. If `lb` is higher than
    /// the number of literals in the encoding, [`EncodingError::Unsat`] is
    /// returned.
    fn enforce_lb(&self, lb: usize) -> Result<Vec<Lit>, EncodingError>;
    /// Encodes a lower bound cardinality constraint to CNF
    fn encode_lb_constr(
        constr: CardLBConstr,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError>
    where
        Self: Sized,
    {
        let mut enc = Self::new();
        let (lits, lb) = constr.decompose();
        enc.add(lits);
        let mut cnf = enc.encode_lb(lb, lb, var_manager)?;
        enc.enforce_lb(lb)
            .unwrap()
            .into_iter()
            .for_each(|unit| cnf.add_unit(unit));
        Ok(cnf)
    }
}

/// Trait for cardinality encodings that allow upper and lower bounding
pub trait BothBCard: UBCard + LBCard {
    /// Lazily builds the cardinality encoding to enable both bounds from
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
    /// Encodes an equality cardinality constraint to CNF
    fn encode_eq_constr(
        constr: CardEQConstr,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError>
    where
        Self: Sized,
    {
        let mut enc = Self::new();
        let (lits, b) = constr.decompose();
        enc.add(lits);
        let mut cnf = enc.encode_both(b, b, var_manager)?;
        enc.enforce_eq(b)
            .unwrap()
            .into_iter()
            .for_each(|unit| cnf.add_unit(unit));
        Ok(cnf)
    }
    /// Encodes any cardinality constraint to CNF
    fn encode_constr(
        constr: CardConstraint,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError>
    where
        Self: Sized,
    {
        match constr {
            CardConstraint::UB(constr) => Self::encode_ub_constr(constr, var_manager),
            CardConstraint::LB(constr) => Self::encode_lb_constr(constr, var_manager),
            CardConstraint::EQ(constr) => Self::encode_eq_constr(constr, var_manager),
        }
    }
}

/// Default implementation of [`BothBCard`] for every encoding that does upper
/// and lower bounding
impl<CE> BothBCard for CE where CE: UBCard + LBCard {}

/// Trait for all cardinality encodings of form `sum of lits <> rhs`
pub trait IncEncodeCard: EncodeCard {
    /// Constructs a new cardinality encoding that reserves all variables on the
    /// first call to an encode method
    fn new_reserving() -> Self
    where
        Self: Sized;
    /// Constructs a new cardinality encoding that reserves all variables on the
    /// first call to an encode method from input literals.
    fn new_reserving_from_lits<I>(lits: I) -> Self
    where
        Self: Sized,
        I: Iterator<Item = Lit>,
    {
        let lits = lits.collect();
        let mut ce = Self::new_reserving();
        ce.add(lits);
        ce
    }
}

/// Trait for incremental cardinality encodings that allow upper bounding of the
/// form `sum of lits <= ub`
pub trait IncUBCard: UBCard + IncEncodeCard {
    /// Lazily builds the _change in_ cardinality encoding to enable upper
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

/// Trait for incremental cardinality encodings that allow upper bounding of the
/// form `sum of lits <= ub`
pub trait IncLBCard: LBCard + IncEncodeCard {
    /// Lazily builds the _change in_ cardinality encoding to enable lower
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

/// Trait for incremental cardinality encodings that allow upper and lower bounding
pub trait IncBothBCard: IncUBCard + IncLBCard {
    /// Lazily builds the _change in_ cardinality encoding to enable both bounds
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

/// Default implementation of [`IncBothBCard`] for every encoding that does
/// incremental upper and lower bounding
impl<CE> IncBothBCard for CE where CE: IncUBCard + IncLBCard {}

/// Constructs a default upper bounding cardinality encoding. For now this is a
/// [`Totalizer`]
pub fn new_default_ub() -> impl UBCard {
    Totalizer::new()
}

/// Constructs a default lower bounding cardinality encoding. For now this is a
/// [`Totalizer`]
pub fn new_default_lb() -> impl LBCard {
    Totalizer::new()
}

/// Constructs a default double bounding cardinality encoding. For now this is a
/// [`Totalizer`]
pub fn new_default_both() -> impl BothBCard {
    Totalizer::new()
}

/// Constructs a default incremental upper bounding cardinality encoding. For
/// now this is a [`Totalizer`]
pub fn new_default_inc_ub() -> impl IncUBCard {
    Totalizer::new()
}

/// Constructs a default incremental lower bounding cardinality encoding. For
/// now this is a [`Totalizer`]
pub fn new_default_inc_lb() -> impl LBCard {
    Totalizer::new()
}

/// Constructs a default incremental double bounding cardinality encoding. For
/// now this is a [`Totalizer`]
pub fn new_default_inc_both() -> impl BothBCard {
    Totalizer::new()
}

/// A default encoder for any cardinality constraint.
/// This uses a [`Totalizer`] to encode non-trivial constraints.
pub fn default_encode_cardinality_constraint(
    constr: CardConstraint,
    var_manager: &mut dyn ManageVars,
) -> CNF {
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
        lits.into_iter().for_each(|l| cnf.add_unit(l));
        return cnf;
    }
    if constr.is_clause() {
        let mut cnf = CNF::new();
        cnf.add_clause(constr.into_clause().unwrap());
        return cnf;
    }
    Totalizer::encode_constr(constr, var_manager).unwrap()
}
