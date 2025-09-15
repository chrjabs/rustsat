//! # Cardinality Encodings from [`pindakaas`]

use crate::{
    encodings::{card::Encode, pindakaas::ReifClauseDb},
    instances::ManageVars,
    types::Lit,
};

/// Encoder type that allows using cardinality encoders from the [`pindakaas`] crate in the same
/// way as RustSAT at-most-one encodings.
///
/// Since [`pindakaas`] encoders do not support reification, the entire encoding is
/// conditionallized on a fresh variable, which is then returned as the enforcing assumption.
#[derive(Debug)]
pub struct Encoder<Enc> {
    marker: std::marker::PhantomData<Enc>,
    lit_buffer: Vec<Lit>,
    reifications: Vec<Option<Lit>>,
}

impl<Enc> From<Vec<Lit>> for Encoder<Enc> {
    fn from(value: Vec<Lit>) -> Self {
        let n_lits = value.len();
        Self {
            marker: std::marker::PhantomData,
            lit_buffer: value,
            reifications: vec![None; n_lits],
        }
    }
}

impl<Enc> FromIterator<Lit> for Encoder<Enc> {
    fn from_iter<T: IntoIterator<Item = Lit>>(iter: T) -> Self {
        let lit_buffer: Vec<_> = iter.into_iter().collect();
        Self::from(lit_buffer)
    }
}

impl<Enc> Encode for Encoder<Enc>
where
    Enc: pindakaas::Encoder<pindakaas::cardinality::Cardinality> + Default,
{
    fn n_lits(&self) -> usize {
        self.lit_buffer.len()
    }
}

impl<Enc> super::BoundUpper for Encoder<Enc>
where
    Enc: pindakaas::Encoder<pindakaas::cardinality::Cardinality> + Default,
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
            .copied()
            .map(pindakaas::Lit::from)
            .collect();
        for bound in super::prepare_ub_range(self, range) {
            let mut db = ReifClauseDb::new(collector, var_manager);
            let con = pindakaas::cardinality::Cardinality::new(
                lits.clone(),
                pindakaas::bool_linear::LimitComp::LessEq,
                pindakaas::bool_linear::PosCoeff::new(
                    i64::try_from(bound).expect("bound does not fit in `i64::MAX`"),
                ),
            );
            let enc = Enc::default();
            enc.encode(&mut db, &con)
                .expect("constraint does not contain any literals");
            self.reifications[bound] = Some(db.reification());
        }
        Ok(())
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, crate::encodings::NotEncoded> {
        if ub > self.n_lits() {
            return Ok(vec![]);
        }
        let Some(reification) = self.reifications[ub] else {
            return Err(crate::encodings::NotEncoded);
        };
        Ok(vec![!reification])
    }
}
