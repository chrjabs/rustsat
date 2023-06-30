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
//!     encodings::{card, card::{BoundBoth, Encode}},
//!     instances::{BasicVarManager, ManageVars},
//!     lit, solvers,
//!     solvers::{SolverResult, Solve, SolveIncremental},
//!     types::{Clause, Lit, Var},
//!     var,
//! };
//!
//! let mut solver = solvers::new_default_inc_solver();
//! solver.add_clause(clause![lit![0], lit![1], lit![2], lit![3]]);
//! let mut var_manager = BasicVarManager::default();
//! var_manager.increase_next_free(var![4]);
//!
//! let mut enc = card::new_default_inc_both();
//! enc.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
//! solver.add_cnf(enc.encode_both(3..4, &mut var_manager));
//!
//! let mut assumps = enc.enforce_eq(3).unwrap();
//! assumps.extend(vec![lit![0], lit![1], lit![2], !lit![3]]);
//! let res = solver.solve_assumps(assumps).unwrap();
//! assert_eq!(res, SolverResult::Sat);
//!
//! let mut assumps = enc.enforce_eq(3).unwrap();
//! assumps.extend(vec![!lit![0], !lit![1], lit![2], lit![3]]);
//! let res = solver.solve_assumps(assumps).unwrap();
//! assert_eq!(res, SolverResult::Unsat);
//! ```
//!
//! When using cardinality and pseudo-boolean encodings at the same time, it is
//! recommended to import only the modules or rename the traits, e.g., `use
//! card::Encode as EncodeCard`.

use std::ops::Range;

use super::Error;
use crate::{
    instances::{Cnf, ManageVars},
    types::{
        constraints::{CardConstraint, CardEQConstr, CardLBConstr, CardUBConstr},
        Clause, Lit,
    },
};

pub mod totalizer;
pub use totalizer::Totalizer;
pub mod simulators;

/// Trait for all cardinality encodings of form `sum of lits <> rhs`
pub trait Encode: Default + From<Vec<Lit>> + FromIterator<Lit> + Extend<Lit> {
    type Iter<'a>: Iterator<Item = Lit>
    where
        Self: 'a;
    /// Gets an iterator over copies of the input literals
    fn iter(&self) -> Self::Iter<'_>;
    /// Gets the number of literals in the encoding
    fn n_lits(&self) -> usize;
}

/// Trait for cardinality encodings that allow upper bounding of the form `sum
/// of lits <= ub`
pub trait BoundUpper: Encode {
    /// Lazily builds the cardinality encoding to enable upper bounds in a given
    /// range. `var_manager` is the variable manager to use for tracking new
    /// variables. A specific encoding might ignore the lower or upper end of
    /// the range.
    fn encode_ub(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> Cnf;
    /// Returns assumptions/units for enforcing an upper bound (`sum of lits <=
    /// ub`). Make sure that [`BoundUpper::encode_ub`] has been called
    /// adequately and nothing has been called afterwards, otherwise
    /// [`Error::NotEncoded`] will be returned.
    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, Error>;
    /// Encodes an upper bound cardinality constraint to CNF
    fn encode_ub_constr(
        constr: CardUBConstr,
        var_manager: &mut dyn ManageVars,
    ) -> Result<Cnf, Error>
    where
        Self: Sized,
    {
        let mut enc = Self::default();
        let (lits, ub) = constr.decompose();
        enc.extend(lits);
        let mut cnf = enc.encode_ub(ub..ub + 1, var_manager);
        enc.enforce_ub(ub)
            .unwrap()
            .into_iter()
            .for_each(|unit| cnf.add_unit(unit));
        Ok(cnf)
    }
}

/// Trait for cardinality encodings that allow upper bounding of the form `sum
/// of lits <= ub`
pub trait BoundLower: Encode {
    /// Lazily builds the cardinality encoding to enable lower bounds in a given
    /// range. `var_manager` is the variable manager to use for tracking new
    /// variables. A specific encoding might ignore the lower or upper end of
    /// the range.
    fn encode_lb(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> Cnf;
    /// Returns assumptions/units for enforcing a lower bound (`sum of lits >=
    /// lb`). Make sure that [`BoundLower::encode_lb`] has been called
    /// adequately and nothing has been added afterwards, otherwise
    /// [`Error::NotEncoded`] will be returned. If `lb` is higher than
    /// the number of literals in the encoding, [`Error::Unsat`] is
    /// returned.
    fn enforce_lb(&self, lb: usize) -> Result<Vec<Lit>, Error>;
    /// Encodes a lower bound cardinality constraint to CNF
    fn encode_lb_constr(
        constr: CardLBConstr,
        var_manager: &mut dyn ManageVars,
    ) -> Result<Cnf, Error>
    where
        Self: Sized,
    {
        let mut enc = Self::default();
        let (lits, lb) = constr.decompose();
        enc.extend(lits);
        let mut cnf = enc.encode_lb(lb..lb + 1, var_manager);
        enc.enforce_lb(lb)
            .unwrap()
            .into_iter()
            .for_each(|unit| cnf.add_unit(unit));
        Ok(cnf)
    }
}

/// Trait for cardinality encodings that allow upper and lower bounding
pub trait BoundBoth: BoundUpper + BoundLower {
    /// Lazily builds the cardinality encoding to enable both bounds in a given
    /// range. `var_manager` is the variable manager to use for tracking new
    /// variables. A specific encoding might ignore the lower or upper end of
    /// the range.
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
    /// Encodes an equality cardinality constraint to CNF
    fn encode_eq_constr(
        constr: CardEQConstr,
        var_manager: &mut dyn ManageVars,
    ) -> Result<Cnf, Error>
    where
        Self: Sized,
    {
        let mut enc = Self::default();
        let (lits, b) = constr.decompose();
        enc.extend(lits);
        let mut cnf = enc.encode_both(b..b + 1, var_manager);
        enc.enforce_eq(b)
            .unwrap()
            .into_iter()
            .for_each(|unit| cnf.add_unit(unit));
        Ok(cnf)
    }
    /// Encodes any cardinality constraint to CNF
    fn encode_constr(constr: CardConstraint, var_manager: &mut dyn ManageVars) -> Result<Cnf, Error>
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
    fn encode_ub_change(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> Cnf;
}

/// Trait for incremental cardinality encodings that allow upper bounding of the
/// form `sum of lits <= ub`
pub trait BoundLowerIncremental: BoundLower + EncodeIncremental {
    /// Lazily builds the _change in_ cardinality encoding to enable lower
    /// bounds in a given range. `var_manager` is the variable manager to use
    /// for tracking new variables. A specific encoding might ignore the lower
    /// or upper end of the range.
    fn encode_lb_change(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> Cnf;
}

/// Trait for incremental cardinality encodings that allow upper and lower bounding
pub trait BoundBothIncremental: BoundUpperIncremental + BoundLowerIncremental {
    /// Lazily builds the _change in_ cardinality encoding to enable both bounds
    /// in a given range. `var_manager` is the variable manager to use for
    /// tracking new variables. A specific encoding might ignore the lower or
    /// upper end of the range.
    fn encode_both_change(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> Cnf {
        let cnf = self.encode_ub_change(range.clone(), var_manager);
        cnf.join(self.encode_lb_change(range, var_manager))
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
pub fn new_default_ub() -> impl BoundUpper {
    DefUpperBounding::default()
}

/// Constructs a default lower bounding cardinality encoding.
pub fn new_default_lb() -> impl BoundLower {
    DefLowerBounding::default()
}

/// Constructs a default double bounding cardinality encoding.
pub fn new_default_both() -> impl BoundBoth {
    DefBothBounding::default()
}

/// Constructs a default incremental upper bounding cardinality encoding.
pub fn new_default_inc_ub() -> impl BoundUpperIncremental {
    DefIncUpperBounding::default()
}

/// Constructs a default incremental lower bounding cardinality encoding.
pub fn new_default_inc_lb() -> impl BoundLower {
    DefIncLowerBounding::default()
}

/// Constructs a default incremental double bounding cardinality encoding.
pub fn new_default_inc_both() -> impl BoundBoth {
    DefIncBothBounding::default()
}

/// A default encoder for any cardinality constraint. This uses a
/// [`DefBothBounding`] to encode non-trivial constraints.
pub fn default_encode_cardinality_constraint(
    constr: CardConstraint,
    var_manager: &mut dyn ManageVars,
) -> Cnf {
    encode_cardinality_constraint::<DefBothBounding>(constr, var_manager)
}

/// An encoder for any cardinality constraint with an encoding of choice
pub fn encode_cardinality_constraint<CE: BoundBoth>(
    constr: CardConstraint,
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
        lits.into_iter().for_each(|l| cnf.add_unit(l));
        return cnf;
    }
    if constr.is_clause() {
        let mut cnf = Cnf::new();
        cnf.add_clause(constr.as_clause().unwrap());
        return cnf;
    }
    CE::encode_constr(constr, var_manager).unwrap()
}
