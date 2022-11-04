//! # Cardinality Encoding Simulators
//!
//! This module contains generic code to simulate cardinality encodings from
//! other cardinality encodings. This can for example be used to simulate lower
//! bounding with an encoding that only natively support upper bounding by
//! negating the input literals.

use std::{marker::PhantomData, ops::Not};

use super::{EncodeCard, IncEncodeCard, IncLBCard, IncUBCard, IterCardEncoding, LBCard, UBCard};
use crate::{
    encodings::{EncodeStats, EncodingError},
    instances::{ManageVars, CNF},
    types::Lit,
};

/// Simulator type that builds a cardinality encoding of type `CE` over the
/// negated input literals in order to simulate the other bound type
pub struct InvertedCard<'a, CE>
where
    CE: EncodeCard<'a>,
{
    card_enc: CE,
    n_lits: usize,
    phantom: PhantomData<&'a CE>,
}

impl<'a, CE> EncodeCard<'a> for InvertedCard<'a, CE>
where
    CE: EncodeCard<'a>,
{
    type Iter = InvertedIter<'a, CE::Iter>;

    fn new() -> Self
    where
        Self: Sized,
    {
        InvertedCard {
            card_enc: CE::new(),
            n_lits: 0,
            phantom: PhantomData,
        }
    }

    fn add(&mut self, mut lits: Vec<Lit>) {
        self.n_lits += lits.len();
        lits.iter_mut().for_each(|l| *l = !*l);
        self.card_enc.add(lits)
    }

    fn iter(&'a self) -> Self::Iter {
        self.card_enc.iter().map(Lit::not)
    }

    fn n_lits(&self) -> usize {
        self.n_lits
    }
}

impl<'a, CE> IncEncodeCard<'a> for InvertedCard<'a, CE>
where
    CE: IncEncodeCard<'a>,
{
    fn new_reserving() -> Self
    where
        Self: Sized,
    {
        InvertedCard {
            card_enc: CE::new_reserving(),
            n_lits: 0,
            phantom: PhantomData,
        }
    }
}

impl<'a, CE> UBCard<'a> for InvertedCard<'a, CE>
where
    CE: LBCard<'a>,
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

impl<'a, CE> LBCard<'a> for InvertedCard<'a, CE>
where
    CE: UBCard<'a>,
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

impl<'a, CE> IncUBCard<'a> for InvertedCard<'a, CE>
where
    CE: IncLBCard<'a>,
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

impl<'a, CE> IncLBCard<'a> for InvertedCard<'a, CE>
where
    CE: IncUBCard<'a>,
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

impl<'a, CE> EncodeStats for InvertedCard<'a, CE>
where
    CE: EncodeCard<'a> + EncodeStats,
{
    fn n_clauses(&self) -> usize {
        self.card_enc.n_clauses()
    }

    fn n_vars(&self) -> usize {
        self.card_enc.n_vars()
    }
}

type InvertedIter<'a, ICE> = std::iter::Map<ICE, fn(Lit) -> Lit>;
impl<'a, ICE> IterCardEncoding<'a> for InvertedIter<'a, ICE> where ICE: IterCardEncoding<'a> {}

/// Simulator type that builds a combined cardinality encoding supporting both
/// bounds from two individual cardinality encodings supporting each bound
/// separately
pub struct DoubleCard<'a, UB, LB>
where
    UB: UBCard<'a>,
    LB: LBCard<'a>,
{
    ub_enc: UB,
    lb_enc: LB,
    phantom: PhantomData<&'a UB>,
}

impl<'a, UB, LB> EncodeCard<'a> for DoubleCard<'a, UB, LB>
where
    UB: UBCard<'a>,
    LB: LBCard<'a>,
{
    type Iter = UB::Iter;

    fn new() -> Self
    where
        Self: Sized,
    {
        DoubleCard {
            ub_enc: UB::new(),
            lb_enc: LB::new(),
            phantom: PhantomData,
        }
    }

    fn add(&mut self, lits: Vec<Lit>) {
        self.ub_enc.add(lits.clone());
        self.lb_enc.add(lits);
    }

    fn iter(&'a self) -> Self::Iter {
        self.ub_enc.iter()
    }

    fn n_lits(&self) -> usize {
        self.ub_enc.n_lits()
    }
}

impl<'a, UB, LB> IncEncodeCard<'a> for DoubleCard<'a, UB, LB>
where
    UB: IncUBCard<'a>,
    LB: IncLBCard<'a>,
{
    fn new_reserving() -> Self
    where
        Self: Sized,
    {
        DoubleCard {
            ub_enc: UB::new_reserving(),
            lb_enc: LB::new_reserving(),
            phantom: PhantomData,
        }
    }
}

impl<'a, UB, LB> UBCard<'a> for DoubleCard<'a, UB, LB>
where
    UB: UBCard<'a>,
    LB: LBCard<'a>,
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

impl<'a, UB, LB> LBCard<'a> for DoubleCard<'a, UB, LB>
where
    UB: UBCard<'a>,
    LB: LBCard<'a>,
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

impl<'a, UB, LB> IncUBCard<'a> for DoubleCard<'a, UB, LB>
where
    UB: IncUBCard<'a>,
    LB: IncLBCard<'a>,
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

impl<'a, UB, LB> IncLBCard<'a> for DoubleCard<'a, UB, LB>
where
    UB: IncUBCard<'a>,
    LB: IncLBCard<'a>,
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

impl<'a, UB, LB> EncodeStats for DoubleCard<'a, UB, LB>
where
    UB: EncodeStats + UBCard<'a>,
    LB: EncodeStats + LBCard<'a>,
{
    fn n_clauses(&self) -> usize {
        self.ub_enc.n_clauses() + self.lb_enc.n_clauses()
    }

    fn n_vars(&self) -> usize {
        self.ub_enc.n_vars() + self.lb_enc.n_vars()
    }
}
