//! # PB Encodings from [`pindakaas`]

use pindakaas::bool_linear::PosCoeff;

use crate::{
    encodings::{pb::Encode, pindakaas::ReifClauseDb},
    instances::ManageVars,
    types::{Lit, RsHashMap},
};

/// Encoder type that allows using pseudo-Boolean encoders from the [`pindakaas`] crate in the same
/// way as RustSAT at-most-one encodings.
///
/// Since [`pindakaas`] encoders do not support reification, the entire encoding is
/// conditionallized on a fresh variable, which is then returned as the enforcing assumption.
#[derive(Debug)]
pub struct Encoder<Enc> {
    marker: std::marker::PhantomData<Enc>,
    lit_buffer: Vec<(Lit, usize)>,
    weight_sum: usize,
    reifications: RsHashMap<usize, Lit>,
}

impl<Enc> From<Vec<(Lit, usize)>> for Encoder<Enc> {
    fn from(value: Vec<(Lit, usize)>) -> Self {
        let weight_sum = value.iter().map(|(_, cf)| *cf).sum();
        Self {
            marker: std::marker::PhantomData,
            lit_buffer: value,
            weight_sum,
            reifications: RsHashMap::default(),
        }
    }
}

impl<Enc> FromIterator<(Lit, usize)> for Encoder<Enc> {
    fn from_iter<T: IntoIterator<Item = (Lit, usize)>>(iter: T) -> Self {
        let lit_buffer: Vec<_> = iter.into_iter().collect();
        Self::from(lit_buffer)
    }
}

impl<Enc> Encode for Encoder<Enc>
where
    Enc: pindakaas::Encoder<pindakaas::bool_linear::NormalizedBoolLinear> + Default,
{
    fn weight_sum(&self) -> usize {
        self.weight_sum
    }
}

impl<Enc> super::BoundUpper for Encoder<Enc>
where
    Enc: pindakaas::Encoder<pindakaas::bool_linear::NormalizedBoolLinear> + Default,
{
    fn encode_ub<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: crate::encodings::CollectClauses,
        R: std::ops::RangeBounds<usize>,
    {
        let lits: Vec<_> = self
            .lit_buffer
            .iter()
            .map(|&(lit, cf)| {
                (
                    pindakaas::Lit::from(lit),
                    PosCoeff::new(i64::try_from(cf).expect("coefficient exceeds `i64::MAX`")),
                )
            })
            .collect();
        for bound in super::prepare_ub_range(self, range) {
            let mut db = ReifClauseDb::new(collector, var_manager);
            let con = pindakaas::bool_linear::NormalizedBoolLinear::new(
                lits.clone(),
                pindakaas::bool_linear::LimitComp::LessEq,
                PosCoeff::new(i64::try_from(bound).expect("bound does not fit in `i64::MAX`")),
            );
            let enc = Enc::default();
            enc.encode(&mut db, &con)
                .expect("constraint does not contain any literals");
            self.reifications.insert(bound, db.reification());
        }
        Ok(())
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, crate::encodings::EnforceError> {
        if ub > self.weight_sum() {
            return Ok(vec![]);
        }
        let Some(&reification) = self.reifications.get(&ub) else {
            return Err(crate::encodings::EnforceError::NotEncoded);
        };
        Ok(vec![!reification])
    }
}
