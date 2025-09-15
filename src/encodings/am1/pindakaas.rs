//! # At-most-one Encodings from [`pindakaas`]

use crate::{encodings::pindakaas::ClauseDb, instances::ManageVars, types::Lit};

/// Encoder type that allows using at-most-one encoders from the [`pindakaas`] crate in the same
/// way as RustSAT at-most-one encodings
#[derive(Debug)]
pub struct Encoder<Enc> {
    marker: std::marker::PhantomData<Enc>,
    lit_buffer: Vec<Lit>,
}

impl<Enc> From<Vec<Lit>> for Encoder<Enc> {
    fn from(value: Vec<Lit>) -> Self {
        Self {
            marker: std::marker::PhantomData,
            lit_buffer: value,
        }
    }
}

impl<Enc> FromIterator<Lit> for Encoder<Enc> {
    fn from_iter<T: IntoIterator<Item = Lit>>(iter: T) -> Self {
        let lit_buffer: Vec<_> = iter.into_iter().collect();
        Self::from(lit_buffer)
    }
}

impl<Enc> super::Encode for Encoder<Enc>
where
    Enc: pindakaas::Encoder<pindakaas::cardinality_one::CardinalityOne> + Default,
{
    fn n_lits(&self) -> usize {
        self.lit_buffer.len()
    }

    fn encode<Col>(
        &mut self,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: super::CollectClauses,
    {
        let mut db = ClauseDb::new(collector, var_manager);
        let con = pindakaas::cardinality_one::CardinalityOne::new(
            self.lit_buffer
                .iter()
                .copied()
                .map(pindakaas::Lit::from)
                .collect(),
            pindakaas::bool_linear::LimitComp::LessEq,
        );
        let enc = Enc::default();
        enc.encode(&mut db, &con)
            .expect("constraint does not contain any literals");
        Ok(())
    }
}
