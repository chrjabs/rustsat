//! # Bimander At-Most-1 Encoding
//!
//! ## References
//!
//! - Van-Hau Nguyen and Son Thay Mai: _A New Method to Encode the At-Most-One Constraint into SAT,
//!   SOICT 2015.

use std::marker::PhantomData;

use super::Encode;
use crate::{
    encodings::{atomics, CollectClauses, EncodeStats, IterInputs},
    instances::ManageVars,
    types::Lit,
    utils,
};

/// Implementation of the bimander at-most-1 encoding.
///
/// # Generics
///
/// - `Sub`: the sub encoding to use for each split
/// - `N`: the size of the splits
///
/// # References
///
/// - Van-Hau Nguyen and Son Thay Mai: _A New Method to Encode the At-Most-One Constraint into SAT,
///   SOICT 2015.
#[derive(Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Bimander<const N: usize = 4, Sub = super::Pairwise> {
    /// Input literals
    in_lits: Vec<Lit>,
    /// The number of clauses in the encoding
    n_clauses: usize,
    /// The number of new variables in the encoding
    n_vars: u32,
    _phantom: PhantomData<Sub>,
}

impl<const N: usize, Sub> Encode for Bimander<N, Sub>
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

        let n_splits = self.in_lits.len().div_ceil(N);
        let p = utils::digits(n_splits - 1, 2);

        let aux_vars: Vec<_> = (0..p).map(|_| var_manager.new_var()).collect();

        for split in 0..n_splits {
            let lits = &self.in_lits[split * N..std::cmp::min(self.in_lits.len(), (split + 1) * N)];
            for (k, aux) in aux_vars.iter().enumerate().take(p as usize) {
                let aux = aux.lit(split & (1 << k) == 0);
                collector.extend_clauses(atomics::clause_impl_lit(lits, aux))?;
            }
            let mut sub = lits.iter().copied().collect::<Sub>();
            sub.encode(collector, var_manager)?;
        }

        self.n_clauses = collector.n_clauses() - prev_clauses;
        self.n_vars += var_manager.n_used() - prev_vars;
        Ok(())
    }
}

impl<const N: usize, Sub> IterInputs for Bimander<N, Sub> {
    type Iter<'a>
        = std::iter::Copied<std::slice::Iter<'a, Lit>>
    where
        Sub: 'a;

    fn iter(&self) -> Self::Iter<'_> {
        self.in_lits.iter().copied()
    }
}

impl<const N: usize, Sub> EncodeStats for Bimander<N, Sub> {
    fn n_clauses(&self) -> usize {
        self.n_clauses
    }

    fn n_vars(&self) -> u32 {
        self.n_vars
    }
}

impl<const N: usize, Sub> From<Vec<Lit>> for Bimander<N, Sub> {
    fn from(lits: Vec<Lit>) -> Self {
        Self {
            in_lits: lits,
            n_clauses: 0,
            n_vars: 0,
            _phantom: PhantomData,
        }
    }
}

impl<const N: usize, Sub> FromIterator<Lit> for Bimander<N, Sub> {
    fn from_iter<T: IntoIterator<Item = Lit>>(iter: T) -> Self {
        Self {
            in_lits: Vec::from_iter(iter),
            n_clauses: 0,
            n_vars: 0,
            _phantom: PhantomData,
        }
    }
}

impl<const N: usize, Sub> Extend<Lit> for Bimander<N, Sub> {
    fn extend<T: IntoIterator<Item = Lit>>(&mut self, iter: T) {
        self.in_lits.extend(iter);
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        encodings::am1::Encode,
        instances::{BasicVarManager, Cnf, ManageVars},
        lit, var,
    };

    #[test]
    fn basic() {
        let mut enc: super::Bimander = [lit![0], lit![1], lit![2], lit![3]].into_iter().collect();
        let mut cnf = Cnf::new();
        let mut vm = BasicVarManager::from_next_free(var![4]);
        enc.encode(&mut cnf, &mut vm).unwrap();
        assert_eq!(vm.n_used(), 5);
        assert_eq!(cnf.len(), 10);
    }
}
