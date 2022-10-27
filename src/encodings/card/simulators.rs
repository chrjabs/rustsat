//! # Cardinality Encoding Simulators
//!
//! This module contains generic code to simulate cardinality encodings from
//! other cardinality encodings. This can for example be used to simulate lower
//! bounding with an encoding that only natively support upper bounding by
//! negating the input literals.

use super::{
    BothBCard, EncodeCard, IncBothBCard, IncEncodeCard, IncLBCard, IncUBCard, LBCard, UBCard,
};
use crate::{
    encodings::{EncodeStats, EncodingError},
    instances::{ManageVars, CNF},
    types::Lit,
};

/// Simulator type that builds a cardinality encoding of type `CE` over the
/// negated input literals in order to simulate the other bound type
pub struct InvertedCard<CE>
where
    CE: EncodeCard,
{
    card_enc: CE,
    n_lits: usize,
}

impl<CE> EncodeCard for InvertedCard<CE>
where
    CE: EncodeCard,
{
    fn new() -> Self
    where
        Self: Sized,
    {
        InvertedCard {
            card_enc: CE::new(),
            n_lits: 0,
        }
    }

    fn add(&mut self, mut lits: Vec<Lit>) {
        self.n_lits += lits.len();
        lits.iter_mut().for_each(|l| *l = !*l);
        self.card_enc.add(lits)
    }
}

impl<CE> IncEncodeCard for InvertedCard<CE>
where
    CE: IncEncodeCard,
{
    fn new_reserving() -> Self
    where
        Self: Sized,
    {
        InvertedCard {
            card_enc: CE::new_reserving(),
            n_lits: 0,
        }
    }
}

impl<CE> UBCard for InvertedCard<CE>
where
    CE: LBCard,
{
    fn encode_ub(
        &mut self,
        min_ub: usize,
        max_ub: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError> {
        let min_lb = if self.n_lits > max_ub {
            self.n_lits - max_ub
        } else {
            0
        };
        let max_lb = if self.n_lits > min_ub {
            self.n_lits - min_ub
        } else {
            0
        };
        self.card_enc.encode_lb(min_lb, max_lb, var_manager)
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

impl<CE> LBCard for InvertedCard<CE>
where
    CE: UBCard,
{
    fn encode_lb(
        &mut self,
        min_lb: usize,
        max_lb: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError> {
        let min_ub = if self.n_lits > max_lb {
            self.n_lits - max_lb
        } else {
            0
        };
        let max_ub = if self.n_lits > min_lb {
            self.n_lits - min_lb
        } else {
            0
        };
        self.card_enc.encode_ub(min_ub, max_ub, var_manager)
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

impl<CE> IncUBCard for InvertedCard<CE>
where
    CE: IncLBCard,
{
    fn encode_ub_change(
        &mut self,
        min_ub: usize,
        max_ub: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError> {
        let min_lb = if self.n_lits > max_ub {
            self.n_lits - max_ub
        } else {
            0
        };
        let max_lb = if self.n_lits > min_ub {
            self.n_lits - min_ub
        } else {
            0
        };
        self.card_enc.encode_lb_change(min_lb, max_lb, var_manager)
    }
}

impl<CE> IncLBCard for InvertedCard<CE>
where
    CE: IncUBCard,
{
    fn encode_lb_change(
        &mut self,
        min_lb: usize,
        max_lb: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError> {
        let min_ub = if self.n_lits > max_lb {
            self.n_lits - max_lb
        } else {
            0
        };
        let max_ub = if self.n_lits > min_lb {
            self.n_lits - min_lb
        } else {
            0
        };
        self.card_enc.encode_ub_change(min_ub, max_ub, var_manager)
    }
}

impl<CE> EncodeStats for InvertedCard<CE>
where
    CE: EncodeCard + EncodeStats,
{
    fn n_clauses(&self) -> usize {
        self.card_enc.n_clauses()
    }

    fn n_vars(&self) -> usize {
        self.card_enc.n_vars()
    }
}

/// Simulator type that builds a combined cardinality encoding supporting both
/// bounds from two individual cardinality encodings supporting each bound
/// separately
pub struct DoubleCard<UB, LB>
where
    UB: UBCard,
    LB: LBCard,
{
    ub_enc: UB,
    lb_enc: LB,
}

impl<UB, LB> EncodeCard for DoubleCard<UB, LB>
where
    UB: UBCard,
    LB: LBCard,
{
    fn new() -> Self
    where
        Self: Sized,
    {
        DoubleCard {
            ub_enc: UB::new(),
            lb_enc: LB::new(),
        }
    }

    fn add(&mut self, lits: Vec<Lit>) {
        self.ub_enc.add(lits.clone());
        self.lb_enc.add(lits);
    }
}

impl<UB, LB> IncEncodeCard for DoubleCard<UB, LB>
where
    UB: IncUBCard,
    LB: IncLBCard,
{
    fn new_reserving() -> Self
    where
        Self: Sized,
    {
        DoubleCard {
            ub_enc: UB::new_reserving(),
            lb_enc: LB::new_reserving(),
        }
    }
}

impl<UB, LB> UBCard for DoubleCard<UB, LB>
where
    UB: UBCard,
    LB: LBCard,
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

impl<UB, LB> LBCard for DoubleCard<UB, LB>
where
    UB: UBCard,
    LB: LBCard,
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

impl<UB, LB> IncUBCard for DoubleCard<UB, LB>
where
    UB: IncUBCard,
    LB: IncLBCard,
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

impl<UB, LB> IncLBCard for DoubleCard<UB, LB>
where
    UB: IncUBCard,
    LB: IncLBCard,
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

impl<UB, LB> BothBCard for DoubleCard<UB, LB>
where
    UB: UBCard,
    LB: LBCard,
{
}

impl<UB, LB> IncBothBCard for DoubleCard<UB, LB>
where
    UB: IncUBCard,
    LB: IncLBCard,
{
}

impl<UB, LB> EncodeStats for DoubleCard<UB, LB>
where
    UB: EncodeStats + UBCard,
    LB: EncodeStats + LBCard,
{
    fn n_clauses(&self) -> usize {
        self.ub_enc.n_clauses() + self.lb_enc.n_clauses()
    }

    fn n_vars(&self) -> usize {
        self.ub_enc.n_vars() + self.lb_enc.n_vars()
    }
}
