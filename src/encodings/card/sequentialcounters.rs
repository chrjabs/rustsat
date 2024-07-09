//! # Sequential Counters Encoding
//!
//! ## References
//!
//! - Carsten Sinz: _Towards an Optimal CNF Encoding of Boolean Cardinality Constraints_, CP 2005.

use std::{
    cmp,
    ops::{Range, RangeBounds},
    slice,
};

use crate::{
    clause,
    encodings::{atomics, CollectClauses, EncodeStats, IterInputs},
    instances::ManageVars,
    types::Lit,
};

use super::{
    BoundLower, BoundLowerIncremental, BoundUpper, BoundUpperIncremental, Encode,
    EncodeIncremental, Error,
};

#[derive(Debug, Default, Clone, Copy)]
struct BoundData {
    encoded: bool,
    out: Option<(Lit, bool)>,
}

/// Implementation of the sequential counters encoding
///
/// # References
///
/// - Carsten Sinz: _Towards an Optimal CNF Encoding of Boolean Cardinality Constraints_, CP 2005.
#[derive(Default)]
pub struct SequentialCounters {
    /// Input literals to the totalizer
    in_lits: Vec<Lit>,
    /// Index of the next literal in [`SequentialCounters::in_lits`] that is not in the encoding yet
    not_enc_idx: usize,
    /// The number of variables in the totalizer
    n_vars: u32,
    /// The number of clauses in the totalizer
    n_clauses: usize,
    /// The counter variables
    s_lits: Vec<Lit>,
    /// Encoding and output data for each bound
    bound_data: Vec<BoundData>,
}

impl SequentialCounters {
    #[must_use]
    fn s_lit(&self, i: usize, j: usize) -> Lit {
        debug_assert!(i < self.not_enc_idx - 1);
        debug_assert!(j < self.bound_data.len());
        self.s_lits[i * self.bound_data.len() + j]
    }

    fn reserve_vars(&mut self, n: usize, k: usize, var_manager: &mut dyn ManageVars) {
        debug_assert!(self.s_lits.len() < (n - 1) * k);
        let old_lits = self.s_lits.split_off(0);
        self.s_lits.reserve((n - 1) * k - self.s_lits.len());
        for i in 0..=self.not_enc_idx {
            // copy previously reserved vars
            self.s_lits.extend_from_slice(
                &old_lits[i * self.bound_data.len()..(i + 1) * self.bound_data.len()],
            );
            // add new vars
            self.s_lits
                .extend((self.bound_data.len()..k).map(|_| var_manager.new_lit()));
        }
    }

    fn encode<C: CollectClauses>(
        &mut self,
        bound: usize,
        collector: &mut C,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory> {
        debug_assert!(bound > self.bound_data.len());
        self.reserve_vars(self.in_lits.len(), bound, var_manager);
        let old_enc = self.not_enc_idx;
        let old_bound = self.bound_data.len();
        self.not_enc_idx = self.in_lits.len();
        self.bound_data.resize(bound - 1, Default::default());

        let s_lit = |i, j| self.s_lit(i, j);
        let in_lits = &self.in_lits;

        // Extend old part of encoding to new bound
        if old_bound == 0 {
            // Sinz p828: line 1 and 3
            collector
                .extend_clauses((0..old_enc - 1).map(|i| clause![!in_lits[i], s_lit(i, 0)]))?;
        }
        // Sinz p828: line 4
        collector.extend_clauses(
            (cmp::max(1, old_bound)..self.bound_data.len()).map(|j| clause![!s_lit(0, j)]),
        )?;
        // Sinz p828: line 5
        collector.extend_clauses((1..old_enc - 1).flat_map(|i| {
            (old_bound..self.bound_data.len()).map(move |j| {
                atomics::cube_impl_lit(&[in_lits[i], s_lit(i - 1, j - 1)], s_lit(i, j))
            })
        }))?;
        // Sinz p828: line 6
        collector.extend_clauses((1..old_enc - 1).flat_map(|i| {
            (old_bound..self.bound_data.len())
                .map(move |j| atomics::lit_impl_lit(s_lit(i - 1, j), s_lit(i, j)))
        }))?;

        // Extend to new variables
        // Sinz p828: line 5
        collector.extend_clauses((old_enc..self.not_enc_idx - 1).flat_map(|i| {
            (1..self.bound_data.len()).map(move |j| {
                atomics::cube_impl_lit(&[in_lits[i], s_lit(i - 1, j - 1)], s_lit(i, j))
            })
        }))?;
        // Sinz p828: line 6
        collector.extend_clauses((old_enc..self.not_enc_idx - 1).flat_map(|i| {
            (1..self.bound_data.len())
                .map(move |j| atomics::lit_impl_lit(s_lit(i - 1, j), s_lit(i, j)))
        }))?;

        for bnd in &mut self.bound_data[old_bound..] {
            bnd.encoded = true;
        }

        Ok(())
    }

    fn prepare_assump<C: CollectClauses>(
        &mut self,
        bound: usize,
        collector: &mut C,
        var_manager: &mut dyn ManageVars,
    ) -> Result<Lit, crate::OutOfMemory> {
        debug_assert!(bound <= self.bound_data.len());
        let lit = match &mut self.bound_data[bound - 1].out {
            None => {
                let lit = var_manager.new_lit();
                self.bound_data[bound - 1].out = Some((lit, true));
                lit
            }
            Some((lit, true)) => *lit,
            Some((lit, x)) => {
                *x = true;
                *lit
            }
        };
        // Sinz p828: line 7 and 8, but reified
        collector.extend_clauses((1..self.not_enc_idx).map(|i| {
            atomics::cube_impl_lit(&[self.in_lits[i], self.s_lit(i - 1, bound - 1)], lit)
        }))?;
        Ok(lit)
    }
}

impl Encode for SequentialCounters {
    fn n_lits(&self) -> usize {
        self.in_lits.len()
    }
}

impl IterInputs for SequentialCounters {
    type Iter<'a> = std::iter::Copied<std::slice::Iter<'a, Lit>>
    where
        Self: 'a;

    fn iter(&self) -> Self::Iter<'_> {
        self.in_lits.iter().copied()
    }
}

impl EncodeIncremental for SequentialCounters {
    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        self.reserve_vars(self.in_lits.len(), self.in_lits.len() - 1, var_manager);
        for bnd in &mut self.bound_data {
            bnd.out
                .get_or_insert_with(|| (var_manager.new_lit(), false));
        }
    }
}

impl BoundUpper for SequentialCounters {
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
        todo!()
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, Error> {
        todo!()
    }
}
