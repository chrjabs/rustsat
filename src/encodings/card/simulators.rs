//! # Cardinality Encoding Simulators
//!
//! This module contains generic code to simulate cardinality encodings from
//! other cardinality encodings. This can for example be used to simulate lower
//! bounding with an encoding that only natively support upper bounding by
//! negating the input literals.

use std::ops::{Not, Range};

use super::{Encode, IncEncode, IncLB, IncUB, LB, UB};
use crate::{
    encodings::{EncodeStats, EncodingError},
    instances::{ManageVars, CNF},
    types::Lit,
};

/// Simulator type that builds a cardinality encoding of type `CE` over the
/// negated input literals in order to simulate the other bound type
#[derive(Default)]
pub struct Inverted<CE>
where
    CE: Encode + 'static,
{
    card_enc: CE,
    n_lits: usize,
}

impl<CE> Inverted<CE>
where
    CE: Encode + 'static,
{
    fn convert_encoding_range(&self, range: Range<usize>) -> Range<usize> {
        let min = if self.n_lits > (range.end - 1) {
            self.n_lits - (range.end - 1)
        } else {
            0
        };
        let max = if self.n_lits > range.start {
            self.n_lits - range.start + 1
        } else {
            0
        };
        min..max
    }
}

impl<CE> From<Vec<Lit>> for Inverted<CE>
where
    CE: Encode + 'static,
{
    fn from(lits: Vec<Lit>) -> Self {
        let n = lits.len();
        let lits: Vec<Lit> = lits.into_iter().map(Lit::not).collect();
        Self {
            card_enc: CE::from(lits),
            n_lits: n,
        }
    }
}

impl<CE> FromIterator<Lit> for Inverted<CE>
where
    CE: Encode + 'static,
{
    fn from_iter<T: IntoIterator<Item = Lit>>(iter: T) -> Self {
        let lits: Vec<Lit> = iter.into_iter().collect();
        Self::from(lits)
    }
}

impl<CE> Extend<Lit> for Inverted<CE>
where
    CE: Encode + 'static,
{
    fn extend<T: IntoIterator<Item = Lit>>(&mut self, iter: T) {
        let lits: Vec<Lit> = iter.into_iter().map(Lit::not).collect();
        self.n_lits += lits.len();
        self.card_enc.extend(lits)
    }
}

impl<CE> Encode for Inverted<CE>
where
    CE: Encode,
{
    type Iter<'a> = InvertedIter<CE::Iter<'a>>;

    fn iter(&self) -> Self::Iter<'_> {
        self.card_enc.iter().map(Lit::not)
    }

    fn n_lits(&self) -> usize {
        self.n_lits
    }
}

impl<CE> IncEncode for Inverted<CE>
where
    CE: IncEncode,
{
    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        self.card_enc.reserve(var_manager)
    }
}

impl<CE> UB for Inverted<CE>
where
    CE: LB,
{
    fn encode_ub(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> CNF {
        self.card_enc
            .encode_lb(self.convert_encoding_range(range), var_manager)
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, EncodingError> {
        let lb = if self.n_lits > ub {
            self.n_lits - ub
        } else {
            return Ok(vec![]);
        };
        self.card_enc.enforce_lb(lb)
    }
}

impl<CE> LB for Inverted<CE>
where
    CE: UB,
{
    fn encode_lb(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> CNF {
        self.card_enc
            .encode_ub(self.convert_encoding_range(range), var_manager)
    }

    fn enforce_lb(&self, lb: usize) -> Result<Vec<Lit>, EncodingError> {
        let ub = if self.n_lits > lb {
            self.n_lits - lb
        } else {
            return Err(EncodingError::Unsat);
        };
        self.card_enc.enforce_ub(ub)
    }
}

impl<CE> IncUB for Inverted<CE>
where
    CE: IncLB,
{
    fn encode_ub_change(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> CNF {
        self.card_enc
            .encode_lb_change(self.convert_encoding_range(range), var_manager)
    }
}

impl<CE> IncLB for Inverted<CE>
where
    CE: IncUB,
{
    fn encode_lb_change(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> CNF {
        self.card_enc
            .encode_ub_change(self.convert_encoding_range(range), var_manager)
    }
}

impl<CE> EncodeStats for Inverted<CE>
where
    CE: Encode + EncodeStats,
{
    fn n_clauses(&self) -> usize {
        self.card_enc.n_clauses()
    }

    fn n_vars(&self) -> usize {
        self.card_enc.n_vars()
    }
}

type InvertedIter<ICE> = std::iter::Map<ICE, fn(Lit) -> Lit>;

/// Simulator type that builds a combined cardinality encoding supporting both
/// bounds from two individual cardinality encodings supporting each bound
/// separately
#[derive(Default)]
pub struct Double<UBE, LBE>
where
    UBE: UB + 'static,
    LBE: LB + 'static,
{
    ub_enc: UBE,
    lb_enc: LBE,
}

impl<UBE, LBE> From<Vec<Lit>> for Double<UBE, LBE>
where
    UBE: UB + 'static,
    LBE: LB + 'static,
{
    fn from(lits: Vec<Lit>) -> Self {
        Self {
            ub_enc: UBE::from(lits.clone()),
            lb_enc: LBE::from(lits),
        }
    }
}

impl<UBE, LBE> FromIterator<Lit> for Double<UBE, LBE>
where
    UBE: UB + 'static,
    LBE: LB + 'static,
{
    fn from_iter<T: IntoIterator<Item = Lit>>(iter: T) -> Self {
        let lits: Vec<Lit> = iter.into_iter().collect();
        Self::from(lits)
    }
}

impl<UBE, LBE> Extend<Lit> for Double<UBE, LBE>
where
    UBE: UB + 'static,
    LBE: LB + 'static,
{
    fn extend<T: IntoIterator<Item = Lit>>(&mut self, iter: T) {
        let lits: Vec<Lit> = iter.into_iter().collect();
        self.ub_enc.extend(lits.clone());
        self.lb_enc.extend(lits)
    }
}

impl<UBE, LBE> Encode for Double<UBE, LBE>
where
    UBE: UB,
    LBE: LB,
{
    type Iter<'a> = UBE::Iter<'a>;

    fn iter(&self) -> Self::Iter<'_> {
        self.ub_enc.iter()
    }

    fn n_lits(&self) -> usize {
        self.ub_enc.n_lits()
    }
}

impl<UBE, LBE> IncEncode for Double<UBE, LBE>
where
    UBE: IncUB,
    LBE: IncLB,
{
    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        self.ub_enc.reserve(var_manager);
        self.lb_enc.reserve(var_manager)
    }
}

impl<UBE, LBE> UB for Double<UBE, LBE>
where
    UBE: UB,
    LBE: LB,
{
    fn encode_ub(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> CNF {
        self.ub_enc.encode_ub(range, var_manager)
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, EncodingError> {
        self.ub_enc.enforce_ub(ub)
    }
}

impl<UBE, LBE> LB for Double<UBE, LBE>
where
    UBE: UB,
    LBE: LB,
{
    fn encode_lb(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> CNF {
        self.lb_enc.encode_lb(range, var_manager)
    }

    fn enforce_lb(&self, lb: usize) -> Result<Vec<Lit>, EncodingError> {
        self.lb_enc.enforce_lb(lb)
    }
}

impl<UBE, LBE> IncUB for Double<UBE, LBE>
where
    UBE: IncUB,
    LBE: IncLB,
{
    fn encode_ub_change(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> CNF {
        self.ub_enc.encode_ub_change(range, var_manager)
    }
}

impl<UBE, LBE> IncLB for Double<UBE, LBE>
where
    UBE: IncUB,
    LBE: IncLB,
{
    fn encode_lb_change(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> CNF {
        self.lb_enc.encode_lb_change(range, var_manager)
    }
}

impl<UBE, LBE> EncodeStats for Double<UBE, LBE>
where
    UBE: EncodeStats + UB,
    LBE: EncodeStats + LB,
{
    fn n_clauses(&self) -> usize {
        self.ub_enc.n_clauses() + self.lb_enc.n_clauses()
    }

    fn n_vars(&self) -> usize {
        self.ub_enc.n_vars() + self.lb_enc.n_vars()
    }
}
