//! # Pseudo-Boolean Encoding Simulators
//!
//! This module contains generic code to simulate pseudo-boolean encodings from
//! other pseudo-boolean encodings as well as cardinality encodings. This can
//! for example be used to simulate lower bounding with an encoding that only
//! natively support upper bounding by negating the input literals. A
//! pseudo-boolean encoding can also be simulated by a cardinality encoding
//! where literals are added multiple times.

use std::ops::Range;

use super::{Encode, IncEncode, IncLB, IncUB, LB, UB};
use crate::{
    encodings::{card, EncodeStats, EncodingError},
    instances::{ManageVars, CNF},
    types::{Lit, RsHashMap},
};

/// Simulator type that builds a pseudo-boolean encoding of type `PBE` over the
/// negated input literals in order to simulate the other bound type
#[derive(Default)]
pub struct Inverted<PBE>
where
    PBE: Encode + 'static,
{
    pb_enc: PBE,
    weight_sum: usize,
}

impl<PBE> Inverted<PBE>
where
    PBE: Encode + 'static,
{
    fn convert_encoding_range(&self, range: Range<usize>) -> Range<usize> {
        let min = if self.weight_sum > (range.end - 1) {
            self.weight_sum - (range.end - 1)
        } else {
            0
        };
        let max = if self.weight_sum > range.start {
            self.weight_sum - range.start + 1
        } else {
            0
        };
        min..max
    }
}

impl<PBE> From<RsHashMap<Lit, usize>> for Inverted<PBE>
where
    PBE: Encode + 'static,
{
    fn from(lits: RsHashMap<Lit, usize>) -> Self {
        let ws = lits.iter().fold(0, |ws, (_, w)| ws + w);
        let lits: RsHashMap<Lit, usize> = lits.into_iter().map(|(l, w)| (!l, w)).collect();
        Self {
            pb_enc: PBE::from(lits),
            weight_sum: ws,
        }
    }
}

impl<PBE> FromIterator<(Lit, usize)> for Inverted<PBE>
where
    PBE: Encode + 'static,
{
    fn from_iter<T: IntoIterator<Item = (Lit, usize)>>(iter: T) -> Self {
        let lits: RsHashMap<Lit, usize> = iter.into_iter().collect();
        Self::from(lits)
    }
}

impl<PBE> Extend<(Lit, usize)> for Inverted<PBE>
where
    PBE: Encode + 'static,
{
    fn extend<T: IntoIterator<Item = (Lit, usize)>>(&mut self, iter: T) {
        let lits: RsHashMap<Lit, usize> = iter.into_iter().map(|(l, w)| (!l, w)).collect();
        let ws = lits.iter().fold(0, |ws, (_, w)| ws + w);
        self.pb_enc.extend(lits);
        self.weight_sum += ws;
    }
}

impl<PBE> Encode for Inverted<PBE>
where
    PBE: Encode,
{
    type Iter<'a> = InvertedIter<PBE::Iter<'a>>;

    fn iter(&self) -> Self::Iter<'_> {
        self.pb_enc.iter().map(negate_weighted)
    }

    fn weight_sum(&self) -> usize {
        self.weight_sum
    }
}

impl<PBE> IncEncode for Inverted<PBE>
where
    PBE: IncEncode,
{
    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        self.pb_enc.reserve(var_manager)
    }
}

impl<PBE> UB for Inverted<PBE>
where
    PBE: LB,
{
    fn encode_ub(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> CNF {
        self.pb_enc
            .encode_lb(self.convert_encoding_range(range), var_manager)
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, EncodingError> {
        let lb = if self.weight_sum > ub {
            self.weight_sum - ub
        } else {
            return Ok(vec![]);
        };
        self.pb_enc.enforce_lb(lb)
    }
}

impl<PBE> LB for Inverted<PBE>
where
    PBE: UB,
{
    fn encode_lb(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> CNF {
        self.pb_enc
            .encode_ub(self.convert_encoding_range(range), var_manager)
    }

    fn enforce_lb(&self, lb: usize) -> Result<Vec<Lit>, EncodingError> {
        let ub = if self.weight_sum > lb {
            self.weight_sum - lb
        } else {
            return Err(EncodingError::Unsat);
        };
        self.pb_enc.enforce_ub(ub)
    }
}

impl<PBE> IncUB for Inverted<PBE>
where
    PBE: IncLB,
{
    fn encode_ub_change(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> CNF {
        self.pb_enc
            .encode_lb_change(self.convert_encoding_range(range), var_manager)
    }
}

impl<PBE> IncLB for Inverted<PBE>
where
    PBE: IncUB,
{
    fn encode_lb_change(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> CNF {
        self.pb_enc
            .encode_ub_change(self.convert_encoding_range(range), var_manager)
    }
}

impl<PBE> EncodeStats for Inverted<PBE>
where
    PBE: Encode + EncodeStats,
{
    fn n_clauses(&self) -> usize {
        self.pb_enc.n_clauses()
    }

    fn n_vars(&self) -> usize {
        self.pb_enc.n_vars()
    }
}

fn negate_weighted(weighted_lit: (Lit, usize)) -> (Lit, usize) {
    (!weighted_lit.0, weighted_lit.1)
}
type InvertedIter<IPBE> = std::iter::Map<IPBE, fn((Lit, usize)) -> (Lit, usize)>;

/// Simulator type that builds a combined pseudo-boolean encoding supporting
/// both bounds from two individual pseudo-boolean encodings supporting each
/// bound separately
#[derive(Default)]
pub struct Double<UBE, LBE>
where
    UBE: UB + 'static,
    LBE: LB + 'static,
{
    ub_enc: UBE,
    lb_enc: LBE,
}

impl<UBE, LBE> From<RsHashMap<Lit, usize>> for Double<UBE, LBE>
where
    UBE: UB + 'static,
    LBE: LB + 'static,
{
    fn from(lits: RsHashMap<Lit, usize>) -> Self {
        Self {
            ub_enc: UBE::from(lits.clone()),
            lb_enc: LBE::from(lits),
        }
    }
}

impl<UBE, LBE> FromIterator<(Lit, usize)> for Double<UBE, LBE>
where
    UBE: UB + 'static,
    LBE: LB + 'static,
{
    fn from_iter<T: IntoIterator<Item = (Lit, usize)>>(iter: T) -> Self {
        let lits: RsHashMap<Lit, usize> = iter.into_iter().collect();
        Self::from(lits)
    }
}

impl<UBE, LBE> Extend<(Lit, usize)> for Double<UBE, LBE>
where
    UBE: UB + 'static,
    LBE: LB + 'static,
{
    fn extend<T: IntoIterator<Item = (Lit, usize)>>(&mut self, iter: T) {
        let lits: RsHashMap<Lit, usize> = iter.into_iter().collect();
        self.ub_enc.extend(lits.clone());
        self.lb_enc.extend(lits);
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

    fn weight_sum(&self) -> usize {
        self.ub_enc.weight_sum()
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

/// Simulator type that mimics a pseudo-boolean encoding based on a cardinality
/// encoding that literals are added to multiple times
#[derive(Default)]
pub struct Card<CE>
where
    CE: card::Encode + 'static,
{
    card_enc: CE,
}

impl<CE> From<RsHashMap<Lit, usize>> for Card<CE>
where
    CE: card::Encode + 'static,
{
    fn from(lits: RsHashMap<Lit, usize>) -> Self {
        Self::from_iter(lits)
    }
}

impl<CE> FromIterator<(Lit, usize)> for Card<CE>
where
    CE: card::Encode + 'static,
{
    fn from_iter<T: IntoIterator<Item = (Lit, usize)>>(iter: T) -> Self {
        let mut mult_lits = vec![];
        iter.into_iter().for_each(|(l, w)| {
            mult_lits.resize(mult_lits.len() + w, l);
        });
        Self {
            card_enc: CE::from(mult_lits),
        }
    }
}

impl<CE> Extend<(Lit, usize)> for Card<CE>
where
    CE: card::Encode + 'static,
{
    fn extend<T: IntoIterator<Item = (Lit, usize)>>(&mut self, iter: T) {
        let mut mult_lits = vec![];
        iter.into_iter().for_each(|(l, w)| {
            mult_lits.resize(mult_lits.len() + w, l);
        });
        self.card_enc.extend(mult_lits)
    }
}

impl<CE> Encode for Card<CE>
where
    CE: card::Encode,
{
    type Iter<'a> = CardIter<CE::Iter<'a>>;

    fn iter(&self) -> Self::Iter<'_> {
        self.card_enc.iter().map(add_unit_weight)
    }

    fn weight_sum(&self) -> usize {
        self.card_enc.n_lits()
    }
}

impl<CE> IncEncode for Card<CE>
where
    CE: card::IncEncode,
{
    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        self.card_enc.reserve(var_manager)
    }
}

impl<CE> UB for Card<CE>
where
    CE: card::UB,
{
    fn encode_ub(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> CNF {
        self.card_enc.encode_ub(range, var_manager)
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, EncodingError> {
        self.card_enc.enforce_ub(ub)
    }
}

impl<CE> LB for Card<CE>
where
    CE: card::LB,
{
    fn encode_lb(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> CNF {
        self.card_enc.encode_lb(range, var_manager)
    }

    fn enforce_lb(&self, lb: usize) -> Result<Vec<Lit>, EncodingError> {
        self.card_enc.enforce_lb(lb)
    }
}

impl<CE> IncUB for Card<CE>
where
    CE: card::IncUB,
{
    fn encode_ub_change(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> CNF {
        self.card_enc.encode_ub_change(range, var_manager)
    }
}

impl<CE> IncLB for Card<CE>
where
    CE: card::IncLB,
{
    fn encode_lb_change(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> CNF {
        self.card_enc.encode_lb_change(range, var_manager)
    }
}

fn add_unit_weight(lit: Lit) -> (Lit, usize) {
    (lit, 1)
}
type CardIter<ICE> = std::iter::Map<ICE, fn(Lit) -> (Lit, usize)>;
