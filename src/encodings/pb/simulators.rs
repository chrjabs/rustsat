//! # Pseudo-Boolean Encoding Simulators
//!
//! This module contains generic code to simulate pseudo-boolean encodings from
//! other pseudo-boolean encodings as well as cardinality encodings. This can
//! for example be used to simulate lower bounding with an encoding that only
//! natively support upper bounding by negating the input literals. A
//! pseudo-boolean encoding can also be simulated by a cardinality encoding
//! where literals are added multiple times.

use super::{BothBPB, EncodePB, IncBothBPB, IncEncodePB, IncLBPB, IncUBPB, LBPB, UBPB};
use crate::{
    encodings::{
        card::{
            BothBCard, EncodeCard, IncBothBCard, IncEncodeCard, IncLBCard, IncUBCard, LBCard,
            UBCard,
        },
        EncodeStats, EncodingError,
    },
    instances::{ManageVars, CNF},
    types::{Lit, RsHashMap},
};

/// Simulator type that builds a pseudo-boolean encoding of type `PBE` over the
/// negated input literals in order to simulate the other bound type
pub struct InvertedPB<PBE>
where
    PBE: EncodePB,
{
    pb_enc: PBE,
    total_weight: usize,
}

impl<CE> EncodePB for InvertedPB<CE>
where
    CE: EncodePB,
{
    fn new() -> Self
    where
        Self: Sized,
    {
        InvertedPB {
            pb_enc: CE::new(),
            total_weight: 0,
        }
    }

    fn add(&mut self, lits: RsHashMap<Lit, usize>) {
        let mut neg_lits = RsHashMap::default();
        lits.iter().for_each(|(&l, &w)| {
            self.total_weight += w;
            neg_lits.insert(!l, w);
        });
        self.pb_enc.add(neg_lits)
    }
}

impl<CE> IncEncodePB for InvertedPB<CE>
where
    CE: IncEncodePB,
{
    fn new_reserving() -> Self
    where
        Self: Sized,
    {
        InvertedPB {
            pb_enc: CE::new_reserving(),
            total_weight: 0,
        }
    }
}

impl<CE> UBPB for InvertedPB<CE>
where
    CE: LBPB,
{
    fn encode_ub(
        &mut self,
        min_ub: usize,
        max_ub: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError> {
        let min_lb = if self.total_weight > max_ub {
            self.total_weight - max_ub
        } else {
            0
        };
        let max_lb = if self.total_weight > min_ub {
            self.total_weight - min_ub
        } else {
            0
        };
        self.pb_enc.encode_lb(min_lb, max_lb, var_manager)
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, EncodingError> {
        let lb = if self.total_weight > ub {
            self.total_weight - ub
        } else {
            return Ok(vec![]);
        };
        self.pb_enc.enforce_lb(lb)
    }
}

impl<CE> LBPB for InvertedPB<CE>
where
    CE: UBPB,
{
    fn encode_lb(
        &mut self,
        min_lb: usize,
        max_lb: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError> {
        let min_ub = if self.total_weight > max_lb {
            self.total_weight - max_lb
        } else {
            0
        };
        let max_ub = if self.total_weight > min_lb {
            self.total_weight - min_lb
        } else {
            0
        };
        self.pb_enc.encode_ub(min_ub, max_ub, var_manager)
    }

    fn enforce_lb(&self, lb: usize) -> Result<Vec<Lit>, EncodingError> {
        let ub = if self.total_weight > lb {
            self.total_weight - lb
        } else {
            return Err(EncodingError::Unsat);
        };
        self.pb_enc.enforce_ub(ub)
    }
}

impl<CE> IncUBPB for InvertedPB<CE>
where
    CE: IncLBPB,
{
    fn encode_ub_change(
        &mut self,
        min_ub: usize,
        max_ub: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError> {
        let min_lb = if self.total_weight > max_ub {
            self.total_weight - max_ub
        } else {
            0
        };
        let max_lb = if self.total_weight > min_ub {
            self.total_weight - min_ub
        } else {
            0
        };
        self.pb_enc.encode_lb_change(min_lb, max_lb, var_manager)
    }
}

impl<CE> IncLBPB for InvertedPB<CE>
where
    CE: IncUBPB,
{
    fn encode_lb_change(
        &mut self,
        min_lb: usize,
        max_lb: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError> {
        let min_ub = if self.total_weight > max_lb {
            self.total_weight - max_lb
        } else {
            0
        };
        let max_ub = if self.total_weight > min_lb {
            self.total_weight - min_lb
        } else {
            0
        };
        self.pb_enc.encode_ub_change(min_ub, max_ub, var_manager)
    }
}

impl<CE> EncodeStats for InvertedPB<CE>
where
    CE: EncodePB + EncodeStats,
{
    fn n_clauses(&self) -> usize {
        self.pb_enc.n_clauses()
    }

    fn n_vars(&self) -> usize {
        self.pb_enc.n_vars()
    }
}

/// Simulator type that builds a combined pseudo-boolean encoding supporting
/// both bounds from two individual pseudo-boolean encodings supporting each
/// bound separately
pub struct DoublePB<UB, LB>
where
    UB: UBPB,
    LB: LBPB,
{
    ub_enc: UB,
    lb_enc: LB,
}

impl<UB, LB> EncodePB for DoublePB<UB, LB>
where
    UB: UBPB,
    LB: LBPB,
{
    fn new() -> Self
    where
        Self: Sized,
    {
        DoublePB {
            ub_enc: UB::new(),
            lb_enc: LB::new(),
        }
    }

    fn add(&mut self, lits: RsHashMap<Lit, usize>) {
        self.ub_enc.add(lits.clone());
        self.lb_enc.add(lits);
    }
}

impl<UB, LB> IncEncodePB for DoublePB<UB, LB>
where
    UB: IncUBPB,
    LB: IncLBPB,
{
    fn new_reserving() -> Self
    where
        Self: Sized,
    {
        DoublePB {
            ub_enc: UB::new_reserving(),
            lb_enc: LB::new_reserving(),
        }
    }
}

impl<UB, LB> UBPB for DoublePB<UB, LB>
where
    UB: UBPB,
    LB: LBPB,
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

impl<UB, LB> LBPB for DoublePB<UB, LB>
where
    UB: UBPB,
    LB: LBPB,
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

impl<UB, LB> IncUBPB for DoublePB<UB, LB>
where
    UB: IncUBPB,
    LB: IncLBPB,
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

impl<UB, LB> IncLBPB for DoublePB<UB, LB>
where
    UB: IncUBPB,
    LB: IncLBPB,
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

impl<UB, LB> BothBPB for DoublePB<UB, LB>
where
    UB: UBPB,
    LB: LBPB,
{
}

impl<UB, LB> IncBothBPB for DoublePB<UB, LB>
where
    UB: IncUBPB,
    LB: IncLBPB,
{
}

impl<UB, LB> EncodeStats for DoublePB<UB, LB>
where
    UB: EncodeStats + UBPB,
    LB: EncodeStats + LBPB,
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
pub struct CardPB<CE>
where
    CE: EncodeCard,
{
    card_enc: CE,
}

impl<CE> EncodePB for CardPB<CE>
where
    CE: EncodeCard,
{
    fn new() -> Self
    where
        Self: Sized,
    {
        CardPB {
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
}

impl<CE> IncEncodePB for CardPB<CE>
where
    CE: IncEncodeCard,
{
    fn new_reserving() -> Self
    where
        Self: Sized,
    {
        CardPB {
            card_enc: CE::new_reserving(),
        }
    }
}

impl<CE> UBPB for CardPB<CE>
where
    CE: UBCard,
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

impl<CE> LBPB for CardPB<CE>
where
    CE: LBCard,
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

impl<CE> IncUBPB for CardPB<CE>
where
    CE: IncUBCard,
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

impl<CE> IncLBPB for CardPB<CE>
where
    CE: IncLBCard,
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

impl<CE> BothBPB for CardPB<CE> where CE: BothBCard {}

impl<CE> IncBothBPB for CardPB<CE> where CE: IncBothBCard {}
