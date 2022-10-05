//! # Pseudo-Boolean Encodings for Cardinality Constraints
//!
//! The module contains implementations of CNF encodings for pseudo-boolean
//! constraints. It defines traits for (non-)incremental PB constraints and
//! encodings implementing these traits.

use crate::{
    instances::{ManageVars, CNF},
    types::Lit,
};
use std::collections::HashMap;

pub trait EncodePB {
    /// Adds new literals or weight to literals in the PB constraint
    fn add(&mut self, lits: HashMap<Lit, u64>);
    /// Encodes the PB constraint with a maximum right hand side of `max_rhs`
    /// over all literals in the object. `var_manager` is the variable manager to use for tracking new variables.
    fn encode<VM: ManageVars>(&mut self, max_rhs: u64, var_manager: VM) -> CNF;
    /// Returns assumptions for enforcing an upper bound
    fn enforce_ub(&self, ub: u64) -> Vec<Lit>;
    /// Returns assumptions for enforcing a lower bound
    fn enforce_lb(&self, lb: u64) -> Vec<Lit>;
}

pub trait IncEncodePB: EncodePB {
    /// Encodes a change in the cardinality encoding.
    /// A change can be added literals, or increased `max_rhs`.
    fn encode_change<VM: ManageVars>(&mut self, max_rhs: u64, var_manager: VM) -> CNF;
}
