//! # 2-Product At-Most-1 Encoding
//!
//! ## References
//!
//! - Jingchao Chen: _A New SAT Encoding of the At-Most-One Constraint_, ModRef 2010.

use std::marker::PhantomData;

use super::Encode;
use crate::{
    encodings::{atomics, CollectClauses, EncodeStats, IterInputs},
    instances::ManageVars,
    types::Lit,
};

/// Implementations of the 2-product at-most-1 encoding.
///
/// # References
///
/// - Jingchao Chen: _A New SAT Encoding of the At-Most-One Constraint_, ModRef 2010.
#[derive(Default, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TwoProduct<Sub = super::Pairwise> {
    /// Input literals
    in_lits: Vec<Lit>,
    /// The number of clauses in the encoding
    n_clauses: usize,
    /// The number of new variables in the encoding
    n_vars: u32,
    _sub: PhantomData<Sub>,
}

impl<Sub> Encode for TwoProduct<Sub>
where
    Sub: Encode + From<Vec<Lit>>,
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

        // reserve row and column vars
        let mut p = 0;
        let mut aux_rows = vec![];
        while (p + 1) * (p + 1) <= self.in_lits.len() {
            aux_rows.push(var_manager.new_lit());
            p += 1;
        }
        let p = p;
        let aux_rows = aux_rows;
        let q = self.in_lits.len().div_ceil(p);
        let aux_cols: Vec<_> = (0..q).map(|_| var_manager.new_lit()).collect();

        // force row and column selectors
        collector.extend_clauses(self.in_lits.iter().enumerate().flat_map(|(idx, &lit)| {
            let row_idx = idx / q;
            let row_sel = aux_rows[row_idx];
            let col_idx = idx % q;
            let col_sel = aux_cols[col_idx];
            [
                atomics::lit_impl_lit(lit, row_sel),
                atomics::lit_impl_lit(lit, col_sel),
            ]
        }))?;

        // restrict rows and columns to one
        let mut row_sub = Sub::from(aux_rows);
        row_sub.encode(collector, var_manager)?;
        let mut col_sub = Sub::from(aux_cols);
        col_sub.encode(collector, var_manager)?;

        self.n_clauses = collector.n_clauses() - prev_clauses;
        self.n_vars += var_manager.n_used() - prev_vars;
        Ok(())
    }
}

impl<Sub> IterInputs for TwoProduct<Sub> {
    type Iter<'a>
        = std::iter::Copied<std::slice::Iter<'a, Lit>>
    where
        Sub: 'a;

    fn iter(&self) -> Self::Iter<'_> {
        self.in_lits.iter().copied()
    }
}

impl<Sub> EncodeStats for TwoProduct<Sub> {
    fn n_clauses(&self) -> usize {
        self.n_clauses
    }

    fn n_vars(&self) -> u32 {
        self.n_vars
    }
}

impl<Sub> From<Vec<Lit>> for TwoProduct<Sub> {
    fn from(lits: Vec<Lit>) -> Self {
        Self {
            in_lits: lits,
            n_clauses: 0,
            n_vars: 0,
            _sub: PhantomData,
        }
    }
}

impl<Sub> FromIterator<Lit> for TwoProduct<Sub> {
    fn from_iter<T: IntoIterator<Item = Lit>>(iter: T) -> Self {
        Self {
            in_lits: Vec::from_iter(iter),
            n_clauses: 0,
            n_vars: 0,
            _sub: PhantomData,
        }
    }
}

impl<Sub> Extend<Lit> for TwoProduct<Sub> {
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
        let mut enc: super::TwoProduct = [lit![0], lit![1], lit![2], lit![3]].into_iter().collect();
        let mut cnf = Cnf::new();
        let mut vm = BasicVarManager::from_next_free(var![4]);
        enc.encode(&mut cnf, &mut vm).unwrap();
        assert_eq!(vm.n_used(), 8);
        assert_eq!(cnf.len(), 10);
    }
}
