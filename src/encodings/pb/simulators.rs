//! # Pseudo-Boolean Encoding Simulators
//!
//! This module contains generic code to simulate pseudo-boolean encodings from
//! other pseudo-boolean encodings as well as cardinality encodings. This can
//! for example be used to simulate lower bounding with an encoding that only
//! natively support upper bounding by negating the input literals. A
//! pseudo-boolean encoding can also be simulated by a cardinality encoding
//! where literals are added multiple times.

use super::{Encode, IncEncode, IncLB, IncUB, LB, UB};
use crate::{
    encodings::{card, EncodeStats, EncodingError},
    instances::{ManageVars, CNF},
    types::{Lit, RsHashMap},
};

/// Simulator type that builds a pseudo-boolean encoding of type `PBE` over the
/// negated input literals in order to simulate the other bound type
pub struct Inverted<PBE>
where
    PBE: Encode + 'static,
{
    pb_enc: PBE,
    weight_sum: usize,
}

impl<PBE> Encode for Inverted<PBE>
where
    PBE: Encode,
{
    type Iter<'a> = InvertedIter<PBE::Iter<'a>>;

    fn new() -> Self
    where
        Self: Sized,
    {
        Inverted {
            pb_enc: PBE::new(),
            weight_sum: 0,
        }
    }

    fn add(&mut self, lits: RsHashMap<Lit, usize>) {
        let mut neg_lits = RsHashMap::default();
        lits.iter().for_each(|(&l, &w)| {
            self.weight_sum += w;
            neg_lits.insert(!l, w);
        });
        self.pb_enc.add(neg_lits)
    }

    fn iter<'a>(&'a self) -> Self::Iter<'a> {
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
    fn new_reserving() -> Self
    where
        Self: Sized,
    {
        Inverted {
            pb_enc: PBE::new_reserving(),
            weight_sum: 0,
        }
    }
}

impl<PBE> UB for Inverted<PBE>
where
    PBE: LB,
{
    fn encode_ub(
        &mut self,
        min_ub: usize,
        max_ub: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError> {
        let min_lb = if self.weight_sum > max_ub {
            self.weight_sum - max_ub
        } else {
            0
        };
        let max_lb = if self.weight_sum > min_ub {
            self.weight_sum - min_ub
        } else {
            0
        };
        self.pb_enc.encode_lb(min_lb, max_lb, var_manager)
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
    fn encode_lb(
        &mut self,
        min_lb: usize,
        max_lb: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError> {
        let min_ub = if self.weight_sum > max_lb {
            self.weight_sum - max_lb
        } else {
            0
        };
        let max_ub = if self.weight_sum > min_lb {
            self.weight_sum - min_lb
        } else {
            0
        };
        self.pb_enc.encode_ub(min_ub, max_ub, var_manager)
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
    fn encode_ub_change(
        &mut self,
        min_ub: usize,
        max_ub: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError> {
        let min_lb = if self.weight_sum > max_ub {
            self.weight_sum - max_ub
        } else {
            0
        };
        let max_lb = if self.weight_sum > min_ub {
            self.weight_sum - min_ub
        } else {
            0
        };
        self.pb_enc.encode_lb_change(min_lb, max_lb, var_manager)
    }
}

impl<PBE> IncLB for Inverted<PBE>
where
    PBE: IncUB,
{
    fn encode_lb_change(
        &mut self,
        min_lb: usize,
        max_lb: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError> {
        let min_ub = if self.weight_sum > max_lb {
            self.weight_sum - max_lb
        } else {
            0
        };
        let max_ub = if self.weight_sum > min_lb {
            self.weight_sum - min_lb
        } else {
            0
        };
        self.pb_enc.encode_ub_change(min_ub, max_ub, var_manager)
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
pub struct Double<UBE, LBE>
where
    UBE: UB + 'static,
    LBE: LB + 'static,
{
    ub_enc: UBE,
    lb_enc: LBE,
}

impl<UBE, LBE> Encode for Double<UBE, LBE>
where
    UBE: UB,
    LBE: LB,
{
    type Iter<'a> = UBE::Iter<'a>;

    fn new() -> Self
    where
        Self: Sized,
    {
        Double {
            ub_enc: UBE::new(),
            lb_enc: LBE::new(),
        }
    }

    fn add(&mut self, lits: RsHashMap<Lit, usize>) {
        self.ub_enc.add(lits.clone());
        self.lb_enc.add(lits);
    }

    fn iter<'a>(&'a self) -> Self::Iter<'a> {
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
    fn new_reserving() -> Self
    where
        Self: Sized,
    {
        Double {
            ub_enc: UBE::new_reserving(),
            lb_enc: LBE::new_reserving(),
        }
    }
}

impl<UBE, LBE> UB for Double<UBE, LBE>
where
    UBE: UB,
    LBE: LB,
{
    fn encode_ub(
        &mut self,
        min_ub: usize,
        max_ub: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError> {
        self.ub_enc.encode_ub(min_ub, max_ub, var_manager)
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
    fn encode_lb(
        &mut self,
        min_lb: usize,
        max_lb: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError> {
        self.lb_enc.encode_lb(min_lb, max_lb, var_manager)
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
    fn encode_ub_change(
        &mut self,
        min_ub: usize,
        max_ub: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError> {
        self.ub_enc.encode_ub_change(min_ub, max_ub, var_manager)
    }
}

impl<UBE, LBE> IncLB for Double<UBE, LBE>
where
    UBE: IncUB,
    LBE: IncLB,
{
    fn encode_lb_change(
        &mut self,
        min_lb: usize,
        max_lb: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError> {
        self.lb_enc.encode_lb_change(min_lb, max_lb, var_manager)
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
pub struct Card<CE>
where
    CE: card::Encode + 'static,
{
    card_enc: CE,
}

impl<CE> Encode for Card<CE>
where
    CE: card::Encode,
{
    type Iter<'a> = CardIter<CE::Iter<'a>>;

    fn new() -> Self
    where
        Self: Sized,
    {
        Card {
            card_enc: CE::new(),
        }
    }

    fn add(&mut self, lits: RsHashMap<Lit, usize>) {
        let mut lit_vec = vec![];
        lits.iter().for_each(|(&l, &w)| {
            for _ in 0..w {
                lit_vec.push(l)
            }
        });
        self.card_enc.add(lit_vec)
    }

    fn iter<'a>(&'a self) -> Self::Iter<'a> {
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
    fn new_reserving() -> Self
    where
        Self: Sized,
    {
        Card {
            card_enc: CE::new_reserving(),
        }
    }
}

impl<CE> UB for Card<CE>
where
    CE: card::UB,
{
    fn encode_ub(
        &mut self,
        min_ub: usize,
        max_ub: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError> {
        self.card_enc.encode_ub(min_ub, max_ub, var_manager)
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, EncodingError> {
        self.card_enc.enforce_ub(ub)
    }
}

impl<CE> LB for Card<CE>
where
    CE: card::LB,
{
    fn encode_lb(
        &mut self,
        min_lb: usize,
        max_lb: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError> {
        self.card_enc.encode_lb(min_lb, max_lb, var_manager)
    }

    fn enforce_lb(&self, lb: usize) -> Result<Vec<Lit>, EncodingError> {
        self.card_enc.enforce_lb(lb)
    }
}

impl<CE> IncUB for Card<CE>
where
    CE: card::IncUB,
{
    fn encode_ub_change(
        &mut self,
        min_ub: usize,
        max_ub: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError> {
        self.card_enc.encode_ub_change(min_ub, max_ub, var_manager)
    }
}

impl<CE> IncLB for Card<CE>
where
    CE: card::IncLB,
{
    fn encode_lb_change(
        &mut self,
        min_lb: usize,
        max_lb: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError> {
        self.card_enc.encode_lb_change(min_lb, max_lb, var_manager)
    }
}

fn add_unit_weight(lit: Lit) -> (Lit, usize) {
    (lit, 1)
}
type CardIter<ICE> = std::iter::Map<ICE, fn(Lit) -> (Lit, usize)>;
