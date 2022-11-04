//! # Pseudo-Boolean Encoding Simulators
//!
//! This module contains generic code to simulate pseudo-boolean encodings from
//! other pseudo-boolean encodings as well as cardinality encodings. This can
//! for example be used to simulate lower bounding with an encoding that only
//! natively support upper bounding by negating the input literals. A
//! pseudo-boolean encoding can also be simulated by a cardinality encoding
//! where literals are added multiple times.

use super::{EncodePB, IncEncodePB, IncLBPB, IncUBPB, IterPBEncoding, LBPB, UBPB};
use crate::{
    encodings::{
        card::{EncodeCard, IncEncodeCard, IncLBCard, IncUBCard, IterCardEncoding, LBCard, UBCard},
        EncodeStats, EncodingError,
    },
    instances::{ManageVars, CNF},
    types::{Lit, RsHashMap},
};
use std::marker::PhantomData;

/// Simulator type that builds a pseudo-boolean encoding of type `PBE` over the
/// negated input literals in order to simulate the other bound type
pub struct InvertedPB<'a, PBE>
where
    PBE: EncodePB<'a>,
{
    pb_enc: PBE,
    weight_sum: usize,
    phantom: PhantomData<&'a PBE>,
}

impl<'a, PBE> EncodePB<'a> for InvertedPB<'a, PBE>
where
    PBE: EncodePB<'a>,
{
    type Iter = InvertedIter<'a, PBE::Iter>;

    fn new() -> Self
    where
        Self: Sized,
    {
        InvertedPB {
            pb_enc: PBE::new(),
            weight_sum: 0,
            phantom: PhantomData,
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

    fn iter(&'a self) -> Self::Iter {
        self.pb_enc.iter().map(negate_weighted)
    }

    fn weight_sum(&self) -> usize {
        self.weight_sum
    }
}

impl<'a, PBE> IncEncodePB<'a> for InvertedPB<'a, PBE>
where
    PBE: IncEncodePB<'a>,
{
    fn new_reserving() -> Self
    where
        Self: Sized,
    {
        InvertedPB {
            pb_enc: PBE::new_reserving(),
            weight_sum: 0,
            phantom: PhantomData,
        }
    }
}

impl<'a, PBE> UBPB<'a> for InvertedPB<'a, PBE>
where
    PBE: LBPB<'a>,
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

impl<'a, PBE> LBPB<'a> for InvertedPB<'a, PBE>
where
    PBE: UBPB<'a>,
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

impl<'a, PBE> IncUBPB<'a> for InvertedPB<'a, PBE>
where
    PBE: IncLBPB<'a>,
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

impl<'a, PBE> IncLBPB<'a> for InvertedPB<'a, PBE>
where
    PBE: IncUBPB<'a>,
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

impl<'a, PBE> EncodeStats for InvertedPB<'a, PBE>
where
    PBE: EncodePB<'a> + EncodeStats,
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
type InvertedIter<'a, IPBE> = std::iter::Map<IPBE, fn((Lit, usize)) -> (Lit, usize)>;
impl<'a, IPBE> IterPBEncoding<'a> for InvertedIter<'a, IPBE> where IPBE: IterPBEncoding<'a> {}

/// Simulator type that builds a combined pseudo-boolean encoding supporting
/// both bounds from two individual pseudo-boolean encodings supporting each
/// bound separately
pub struct DoublePB<'a, UB, LB>
where
    UB: UBPB<'a>,
    LB: LBPB<'a>,
{
    ub_enc: UB,
    lb_enc: LB,
    phantom: PhantomData<&'a UB>,
}

impl<'a, UB, LB> EncodePB<'a> for DoublePB<'a, UB, LB>
where
    UB: UBPB<'a>,
    LB: LBPB<'a>,
{
    type Iter = UB::Iter;

    fn new() -> Self
    where
        Self: Sized,
    {
        DoublePB {
            ub_enc: UB::new(),
            lb_enc: LB::new(),
            phantom: PhantomData,
        }
    }

    fn add(&mut self, lits: RsHashMap<Lit, usize>) {
        self.ub_enc.add(lits.clone());
        self.lb_enc.add(lits);
    }

    fn iter(&'a self) -> Self::Iter {
        self.ub_enc.iter()
    }

    fn weight_sum(&self) -> usize {
        self.ub_enc.weight_sum()
    }
}

impl<'a, UB, LB> IncEncodePB<'a> for DoublePB<'a, UB, LB>
where
    UB: IncUBPB<'a>,
    LB: IncLBPB<'a>,
{
    fn new_reserving() -> Self
    where
        Self: Sized,
    {
        DoublePB {
            ub_enc: UB::new_reserving(),
            lb_enc: LB::new_reserving(),
            phantom: PhantomData,
        }
    }
}

impl<'a, UB, LB> UBPB<'a> for DoublePB<'a, UB, LB>
where
    UB: UBPB<'a>,
    LB: LBPB<'a>,
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

impl<'a, UB, LB> LBPB<'a> for DoublePB<'a, UB, LB>
where
    UB: UBPB<'a>,
    LB: LBPB<'a>,
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

impl<'a, UB, LB> IncUBPB<'a> for DoublePB<'a, UB, LB>
where
    UB: IncUBPB<'a>,
    LB: IncLBPB<'a>,
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

impl<'a, UB, LB> IncLBPB<'a> for DoublePB<'a, UB, LB>
where
    UB: IncUBPB<'a>,
    LB: IncLBPB<'a>,
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

impl<'a, UB, LB> EncodeStats for DoublePB<'a, UB, LB>
where
    UB: EncodeStats + UBPB<'a>,
    LB: EncodeStats + LBPB<'a>,
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
pub struct CardPB<'a, CE>
where
    CE: EncodeCard<'a>,
{
    card_enc: CE,
    phantom: PhantomData<&'a CE>,
}

impl<'a, CE> EncodePB<'a> for CardPB<'a, CE>
where
    CE: EncodeCard<'a>,
{
    type Iter = CardIter<'a, CE::Iter>;

    fn new() -> Self
    where
        Self: Sized,
    {
        CardPB {
            card_enc: CE::new(),
            phantom: PhantomData,
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

    fn iter(&'a self) -> Self::Iter {
        self.card_enc.iter().map(add_unit_weight)
    }

    fn weight_sum(&self) -> usize {
        self.card_enc.n_lits()
    }
}

impl<'a, CE> IncEncodePB<'a> for CardPB<'a, CE>
where
    CE: IncEncodeCard<'a>,
{
    fn new_reserving() -> Self
    where
        Self: Sized,
    {
        CardPB {
            card_enc: CE::new_reserving(),
            phantom: PhantomData,
        }
    }
}

impl<'a, CE> UBPB<'a> for CardPB<'a, CE>
where
    CE: UBCard<'a>,
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

impl<'a, CE> LBPB<'a> for CardPB<'a, CE>
where
    CE: LBCard<'a>,
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

impl<'a, CE> IncUBPB<'a> for CardPB<'a, CE>
where
    CE: IncUBCard<'a>,
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

impl<'a, CE> IncLBPB<'a> for CardPB<'a, CE>
where
    CE: IncLBCard<'a>,
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
type CardIter<'a, ICE> = std::iter::Map<ICE, fn(Lit) -> (Lit, usize)>;
impl<'a, ICE> IterPBEncoding<'a> for CardIter<'a, ICE> where ICE: IterCardEncoding<'a> {}
