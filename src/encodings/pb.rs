//! # CNF Encodings for Pseudo-Boolean Constraints
//!
//! The module contains implementations of CNF encodings for pseudo-boolean
//! constraints. It defines traits for (non-)incremental PB constraints and
//! encodings implementing these traits.

use super::EncodingError;
use crate::{
    instances::{ManageVars, CNF},
    types::Lit,
};
use std::collections::HashMap;

mod gte;
pub use gte::GeneralizedTotalizer;
pub use gte::InvertedGeneralizedTotalizer;
pub use gte::DoubleGeneralizedTotalizer;

/// Trait for all pseudo-boolean encodings of form `weighted sum of lits <> rhs`
pub trait EncodePB {
    /// Constructs a new cardinality encoding
    fn new() -> Self
    where
        Self: Sized;
    /// Constructs a new cardinality encoding from input
    /// literals.
    fn new_from_lits<I>(lits: I) -> Self
    where
        Self: Sized,
        I: Iterator<Item = (Lit, usize)>,
    {
        let lits = lits.collect();
        let mut ce = Self::new();
        ce.add(lits);
        ce
    }
    /// Adds new literals to the cardinality encoding
    fn add(&mut self, lits: HashMap<Lit, usize>);
}

/// Trait for pseudo-boolean encodings that allow upper bounding of the form `sum
/// of lits <= ub`
pub trait UBPB: EncodePB {
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
}

/// Trait for pseudo-boolean encodings that allow upper bounding of the form `sum
/// of lits <= ub`
pub trait LBPB: EncodePB {
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
}

/// Trait for pseudo-boolean encodings that allow upper and lower bounding
pub trait BothBPB: UBPB + LBPB {
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
}

/// Trait for all pseudo-boolean encodings of form `sum of lits <> rhs`
pub trait IncEncodePB: EncodePB {
    /// Constructs a new pseudo-boolean encoding that reserves all variables on the
    /// first call to an encode method
    fn new_reserving() -> Self
    where
        Self: Sized;
    /// Constructs a new pseudo-boolean encoding that reserves all variables on the
    /// first call to an encode method from input literals.
    fn new_reserving_from_lits<I>(lits: I) -> Self
    where
        Self: Sized,
        I: Iterator<Item = (Lit, usize)>,
    {
        let lits = lits.collect();
        let mut ce = Self::new();
        ce.add(lits);
        ce
    }
}

/// Trait for incremental pseudo-boolean encodings that allow upper bounding of the
/// form `sum of lits <= ub`
pub trait IncUBPB: UBPB + IncEncodePB {
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
pub trait IncLBPB: LBPB + IncEncodePB {
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
pub trait IncBothBPB: IncUBPB + IncLBPB + BothBPB {
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
