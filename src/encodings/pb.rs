//! # Pseudo-Boolean Encodings for Cardinality Constraints
//!
//! The module contains implementations of CNF encodings for pseudo-boolean
//! constraints. It defines traits for (non-)incremental PB constraints and
//! encodings implementing these traits.

use std::collections::HashMap;
use crate::{instances::SatInstance, types::Lit};

pub trait EncodePB {
    /// Adds new literals or weight to literals in the PB constraint
    fn add(&mut self, lits: HashMap<Lit, u64>);
    /// Encodes the PB constraint with a maximum right hand side of `max_rhs`
    /// over all literals in the object. `next_idx` gives the next free variable
    /// index. `next_idx` is ignored if smaller than the internal next free
    /// counter.
    fn encode(&mut self, max_rhs: u64, next_idx: usize) -> SatInstance;
    /// Returns assumptions for enforcing an upper bound
    fn enforce_ub(&self, ub: u64) -> Vec<Lit>;
    /// Returns assumptions for enforcing a lower bound
    fn enforce_lb(&self, lb: u64) -> Vec<Lit>;
}

pub trait IncEncodePB: EncodePB {
    /// Encodes a change in the cardinality encoding.
    /// A change can be added literals, or increased `max_rhs`.
    fn encode_change(&mut self, max_rhs: u64, next_idx: usize) -> SatInstance;
}
