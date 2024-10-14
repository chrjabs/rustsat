//! # Commander At-Most-1 Encoding
//!
//! ## References
//!
//! - Will Klieber and Gihwon Kwon: _Efficient CNF Encoding for Selecting 1 from N Objects, CFV
//!   2007.

use std::marker::PhantomData;

use super::Encode;
use crate::{
    encodings::{atomics, CollectClauses, EncodeStats, IterInputs},
    instances::ManageVars,
    types::Lit,
};

/// Implementations of the commander at-most-1 encoding.
///
/// # Generics
///
/// - `Sub`: the sub encoding to use for each split
/// - `N`: the size of the splits
///
/// # References
///
/// - Will Klieber and Gihwon Kwon: _Efficient CNF Encoding for Selecting 1 from N Objects, CFV
///   2007.
#[derive(Default)]
pub struct Commander<const N: usize = 4, Sub = super::Pairwise> {
    /// Input literals
    in_lits: Vec<Lit>,
    /// The number of clauses in the encoding
    n_clauses: usize,
    /// The number of new variables in the encoding
    n_vars: u32,
    _phantom: PhantomData<Sub>,
}

impl<const N: usize, Sub> Encode for Commander<N, Sub>
where
    Sub: Encode + FromIterator<Lit> + From<Vec<Lit>>,
{
    fn n_lits(&self) -> usize {
        self.in_lits.len()
    }

    fn encode<Col>(
        &mut self,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
    {
        if self.in_lits.len() <= 1 {
            return Ok(());
        }
        let prev_clauses = collector.n_clauses();
        let prev_vars = var_manager.n_used();

        let n_splits = (self.in_lits.len() + N - 1) / N;

        let commanders: Vec<_> = (0..n_splits).map(|_| var_manager.new_lit()).collect();

        for (split, &commander) in commanders.iter().enumerate() {
            let lits = &self.in_lits[split * N..std::cmp::min(self.in_lits.len(), (split + 1) * N)];
            collector.extend_clauses(atomics::clause_impl_lit(lits, commander))?;
            let mut sub = lits.iter().copied().collect::<Sub>();
            sub.encode(collector, var_manager)?;
        }

        let mut sub = Sub::from(commanders);
        sub.encode(collector, var_manager)?;

        self.n_clauses = collector.n_clauses() - prev_clauses;
        self.n_vars += var_manager.n_used() - prev_vars;
        Ok(())
    }
}

impl<const N: usize, Sub> IterInputs for Commander<N, Sub> {
    type Iter<'a> = std::iter::Copied<std::slice::Iter<'a, Lit>> where Sub: 'a;

    fn iter(&self) -> Self::Iter<'_> {
        self.in_lits.iter().copied()
    }
}

impl<const N: usize, Sub> EncodeStats for Commander<N, Sub> {
    fn n_clauses(&self) -> usize {
        self.n_clauses
    }

    fn n_vars(&self) -> u32 {
        self.n_vars
    }
}

impl<const N: usize, Sub> From<Vec<Lit>> for Commander<N, Sub> {
    fn from(lits: Vec<Lit>) -> Self {
        Self {
            in_lits: lits,
            n_clauses: 0,
            n_vars: 0,
            _phantom: PhantomData,
        }
    }
}

impl<const N: usize, Sub> FromIterator<Lit> for Commander<N, Sub> {
    fn from_iter<T: IntoIterator<Item = Lit>>(iter: T) -> Self {
        Self {
            in_lits: Vec::from_iter(iter),
            n_clauses: 0,
            n_vars: 0,
            _phantom: PhantomData,
        }
    }
}

impl<const N: usize, Sub> Extend<Lit> for Commander<N, Sub> {
    fn extend<T: IntoIterator<Item = Lit>>(&mut self, iter: T) {
        self.in_lits.extend(iter);
    }
}
