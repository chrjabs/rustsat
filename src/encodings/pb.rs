//! # Pseudo-Boolean Encodings for Cardinality Constraints
//!
//! The module contains implementations of CNF encodings for pseudo-boolean
//! constraints. It defines traits for (non-)incremental PB constraints and
//! encodings implementing these traits.

use super::{BoundType, EncodingError};
use crate::{
    instances::{ManageVars, CNF},
    types::Lit,
};
use std::collections::HashMap;

pub trait EncodePB: Sized {
    /// Constructs a new pseudo boolean encoding. If the given bound type is not
    /// supported by the implementing type, it returns
    /// [`EncodingError::NoTypeSupport`].
    fn new(bound_type: BoundType) -> Result<Self, EncodingError>;
    /// Constructs a new pseudo boolean encoding from input literals. If the
    /// given bound type is not supported by the implementing type, it returns
    /// [`EncodingError::NoTypeSupport`].
    fn new_from_lits<PBE: EncodePB>(
        lits: HashMap<Lit, usize>,
        bound_type: BoundType,
    ) -> Result<PBE, EncodingError> {
        let mut pbe = PBE::new(bound_type)?;
        pbe.add(lits);
        Ok(pbe)
    }
    /// Adds new literals or weight to literals in the PB constraint
    fn add(&mut self, lits: HashMap<Lit, usize>);
    /// Encodes the PB constraint with a maximum right hand side of `max_rhs`
    /// over all literals in the object. `var_manager` is the variable manager to use for tracking new variables.
    fn encode<VM: ManageVars>(&mut self, max_rhs: usize, var_manager: &mut VM) -> CNF;
    /// Returns assumptions for enforcing an upper bound (`weighted sum of lits
    /// <= ub`) or an error if the encoding does not support upper bounding.
    /// Make sure that nothing was added to the encoding between the last call
    /// to [`EncodePB::encode`] and this method, otherwise
    /// [`super::EncodingError::NotEncoded`] will be returned.
    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, EncodingError>;
    /// Returns assumptions for enforcing a lower bound (`weighted sum of lits
    /// >= lb`) or an error if the encoding does not support lower bounding.
    /// Make sure that nothing was added to the encoding between the last call
    /// to [`EncodePB::encode`] and this method, otherwise
    /// [`super::EncodingError::NotEncoded`] will be returned.
    fn enforce_lb(&self, lb: usize) -> Result<Vec<Lit>, EncodingError>;
    /// Returns assumptions for enforcing an equality (`weighted sum of lits =
    /// b`) or an error if the encoding does not support one of the two required
    /// bound types. Make sure that nothing was added to the encoding between
    /// the last call to [`EncodePB::encode`] and this method, otherwise
    /// [`super::EncodingError::NotEncoded`] will be returned.
    fn enforce_eq(&self, b: usize) -> Result<Vec<Lit>, EncodingError> {
        let mut assumps = self.enforce_ub(b)?;
        assumps.extend(self.enforce_lb(b)?);
        Ok(assumps)
    }
}

pub trait IncEncodePB: EncodePB {
    /// Constructs a new pseudo boolean encoding that reserves all variables on
    /// the first call to an encode method. If the given bound type is not
    /// supported by the implementing type, it returns
    /// [`EncodingError::NoTypeSupport`].
    fn new_reserving(bound_type: BoundType) -> Result<Self, EncodingError>;
    /// Constructs a new pseudo boolean encoding that reserves all variables on
    /// the first call to an encode method from input literals. If the given
    /// bound type is not supported by the implementing type, it returns
    /// [`EncodingError::NoTypeSupport`].
    fn new_from_lits<IPBE: IncEncodePB>(
        lits: HashMap<Lit, usize>,
        bound_type: BoundType,
    ) -> Result<IPBE, EncodingError> {
        let mut pbe = IPBE::new_reserving(bound_type)?;
        pbe.add(lits);
        Ok(pbe)
    }
    /// Encodes a change in the cardinality encoding.
    /// A change can be added literals, or increased `max_rhs`.
    fn encode_change<VM: ManageVars>(&mut self, max_rhs: usize, var_manager: &mut VM) -> CNF;
}
