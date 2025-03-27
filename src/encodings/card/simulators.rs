//! # Cardinality Encoding Simulators
//!
//! This module contains generic code to simulate cardinality encodings from
//! other cardinality encodings. This can for example be used to simulate lower
//! bounding with an encoding that only natively support upper bounding by
//! negating the input literals.

use std::ops::{Not, Range, RangeBounds};

use super::{
    BoundLower, BoundLowerIncremental, BoundUpper, BoundUpperIncremental, Encode, EncodeIncremental,
};
use crate::{
    encodings::{CollectClauses, EncodeStats, Error, IterInputs},
    instances::ManageVars,
    types::Lit,
};

/// Simulator type that builds a cardinality encoding of type `CE` over the
/// negated input literals in order to simulate the other bound type
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Inverted<CE>
where
    CE: Encode + 'static,
{
    card_enc: CE,
    n_lits: usize,
}

impl<CE> Default for Inverted<CE>
where
    CE: Encode + Default,
{
    fn default() -> Self {
        Self {
            card_enc: Default::default(),
            n_lits: Default::default(),
        }
    }
}

impl<CE> Inverted<CE>
where
    CE: Encode + 'static,
{
    fn convert_encoding_range(&self, range: Range<usize>) -> Range<usize> {
        let min = self.n_lits() - (range.end - 1);
        let max = if self.n_lits() >= range.start {
            self.n_lits() - range.start + 1
        } else {
            0
        };
        min..max
    }
}

impl<CE> From<Vec<Lit>> for Inverted<CE>
where
    CE: Encode + From<Vec<Lit>> + 'static,
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
    CE: Encode + From<Vec<Lit>> + 'static,
{
    fn from_iter<T: IntoIterator<Item = Lit>>(iter: T) -> Self {
        let lits: Vec<Lit> = iter.into_iter().collect();
        Self::from(lits)
    }
}

impl<CE> Extend<Lit> for Inverted<CE>
where
    CE: Encode + Extend<Lit> + 'static,
{
    fn extend<T: IntoIterator<Item = Lit>>(&mut self, iter: T) {
        let lits: Vec<Lit> = iter.into_iter().map(Lit::not).collect();
        self.n_lits += lits.len();
        self.card_enc.extend(lits);
    }
}

impl<CE> Encode for Inverted<CE>
where
    CE: Encode,
{
    fn n_lits(&self) -> usize {
        self.n_lits
    }
}

impl<CE> IterInputs for Inverted<CE>
where
    CE: Encode + IterInputs,
{
    type Iter<'a> = InvertedIter<CE::Iter<'a>>;

    fn iter(&self) -> Self::Iter<'_> {
        self.card_enc.iter().map(Lit::not)
    }
}

impl<CE> EncodeIncremental for Inverted<CE>
where
    CE: EncodeIncremental,
{
    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        self.card_enc.reserve(var_manager);
    }
}

impl<CE> BoundUpper for Inverted<CE>
where
    CE: BoundLower,
{
    fn encode_ub<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
        R: RangeBounds<usize>,
    {
        self.card_enc.encode_lb(
            self.convert_encoding_range(super::prepare_ub_range(self, range)),
            collector,
            var_manager,
        )
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, Error> {
        let lb = if self.n_lits > ub {
            self.n_lits - ub
        } else {
            return Ok(vec![]);
        };
        self.card_enc.enforce_lb(lb)
    }
}

impl<CE> BoundLower for Inverted<CE>
where
    CE: BoundUpper,
{
    fn encode_lb<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
        R: RangeBounds<usize>,
    {
        self.card_enc.encode_ub(
            self.convert_encoding_range(super::prepare_lb_range(self, range)),
            collector,
            var_manager,
        )
    }

    fn enforce_lb(&self, lb: usize) -> Result<Vec<Lit>, Error> {
        let ub = if self.n_lits >= lb {
            self.n_lits - lb
        } else {
            return Err(Error::Unsat);
        };
        self.card_enc.enforce_ub(ub)
    }
}

impl<CE> BoundUpperIncremental for Inverted<CE>
where
    CE: BoundLowerIncremental,
{
    fn encode_ub_change<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
        R: RangeBounds<usize>,
    {
        self.card_enc.encode_lb_change(
            self.convert_encoding_range(super::prepare_ub_range(self, range)),
            collector,
            var_manager,
        )
    }
}

impl<CE> BoundLowerIncremental for Inverted<CE>
where
    CE: BoundUpperIncremental,
{
    fn encode_lb_change<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
        R: RangeBounds<usize>,
    {
        self.card_enc.encode_ub_change(
            self.convert_encoding_range(super::prepare_lb_range(self, range)),
            collector,
            var_manager,
        )
    }
}

impl<CE> EncodeStats for Inverted<CE>
where
    CE: Encode + EncodeStats,
{
    fn n_clauses(&self) -> usize {
        self.card_enc.n_clauses()
    }

    fn n_vars(&self) -> u32 {
        self.card_enc.n_vars()
    }
}

type InvertedIter<ICE> = std::iter::Map<ICE, fn(Lit) -> Lit>;

/// Simulator type that builds a combined cardinality encoding supporting both
/// bounds from two individual cardinality encodings supporting each bound
/// separately
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Double<UBE, LBE>
where
    UBE: BoundUpper + 'static,
    LBE: BoundLower + 'static,
{
    ub_enc: UBE,
    lb_enc: LBE,
}

impl<UBE, LBE> Default for Double<UBE, LBE>
where
    UBE: BoundUpper + Default + 'static,
    LBE: BoundLower + Default + 'static,
{
    fn default() -> Self {
        Self {
            ub_enc: Default::default(),
            lb_enc: Default::default(),
        }
    }
}

impl<UBE, LBE> From<Vec<Lit>> for Double<UBE, LBE>
where
    UBE: BoundUpper + From<Vec<Lit>> + 'static,
    LBE: BoundLower + From<Vec<Lit>> + 'static,
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
    UBE: BoundUpper + From<Vec<Lit>> + 'static,
    LBE: BoundLower + From<Vec<Lit>> + 'static,
{
    fn from_iter<T: IntoIterator<Item = Lit>>(iter: T) -> Self {
        let lits: Vec<Lit> = iter.into_iter().collect();
        Self::from(lits)
    }
}

impl<UBE, LBE> Extend<Lit> for Double<UBE, LBE>
where
    UBE: BoundUpper + Extend<Lit> + 'static,
    LBE: BoundLower + Extend<Lit> + 'static,
{
    fn extend<T: IntoIterator<Item = Lit>>(&mut self, iter: T) {
        let lits: Vec<Lit> = iter.into_iter().collect();
        self.ub_enc.extend(lits.clone());
        self.lb_enc.extend(lits);
    }
}

impl<UBE, LBE> Encode for Double<UBE, LBE>
where
    UBE: BoundUpper,
    LBE: BoundLower,
{
    fn n_lits(&self) -> usize {
        self.ub_enc.n_lits()
    }
}

impl<UBE, LBE> IterInputs for Double<UBE, LBE>
where
    UBE: BoundUpper + IterInputs,
    LBE: BoundLower,
{
    type Iter<'a> = UBE::Iter<'a>;

    fn iter(&self) -> Self::Iter<'_> {
        self.ub_enc.iter()
    }
}

impl<UBE, LBE> EncodeIncremental for Double<UBE, LBE>
where
    UBE: BoundUpperIncremental,
    LBE: BoundLowerIncremental,
{
    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        self.ub_enc.reserve(var_manager);
        self.lb_enc.reserve(var_manager);
    }
}

impl<UBE, LBE> BoundUpper for Double<UBE, LBE>
where
    UBE: BoundUpper,
    LBE: BoundLower,
{
    fn encode_ub<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
        R: RangeBounds<usize>,
    {
        self.ub_enc.encode_ub(range, collector, var_manager)
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, Error> {
        self.ub_enc.enforce_ub(ub)
    }
}

impl<UBE, LBE> BoundLower for Double<UBE, LBE>
where
    UBE: BoundUpper,
    LBE: BoundLower,
{
    fn encode_lb<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
        R: RangeBounds<usize>,
    {
        self.lb_enc.encode_lb(range, collector, var_manager)
    }

    fn enforce_lb(&self, lb: usize) -> Result<Vec<Lit>, Error> {
        self.lb_enc.enforce_lb(lb)
    }
}

impl<UBE, LBE> BoundUpperIncremental for Double<UBE, LBE>
where
    UBE: BoundUpperIncremental,
    LBE: BoundLowerIncremental,
{
    fn encode_ub_change<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
        R: RangeBounds<usize>,
    {
        self.ub_enc.encode_ub_change(range, collector, var_manager)
    }
}

impl<UBE, LBE> BoundLowerIncremental for Double<UBE, LBE>
where
    UBE: BoundUpperIncremental,
    LBE: BoundLowerIncremental,
{
    fn encode_lb_change<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
        R: RangeBounds<usize>,
    {
        self.lb_enc.encode_lb_change(range, collector, var_manager)
    }
}

impl<UBE, LBE> EncodeStats for Double<UBE, LBE>
where
    UBE: EncodeStats + BoundUpper,
    LBE: EncodeStats + BoundLower,
{
    fn n_clauses(&self) -> usize {
        self.ub_enc.n_clauses() + self.lb_enc.n_clauses()
    }

    fn n_vars(&self) -> u32 {
        self.ub_enc.n_vars() + self.lb_enc.n_vars()
    }
}
