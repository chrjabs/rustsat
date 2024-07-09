//! # Bitwise At-Most-1 Encoding
//!
//! ## References
//!
//! - Steven D. Prestwich: _Negative Effects of Modeling Techniques on Search Performance_, in
//!   Trends in Constraint Programming 2007.

use super::Encode;
use crate::{
    encodings::{atomics, CollectClauses, EncodeStats, IterInputs},
    instances::ManageVars,
    types::Lit,
    utils,
};

/// Implementations of the bitwise at-most-1 encoding.
///
/// # References
///
/// - Steven D. Prestwich: _Negative Effects of Modeling Techniques on Search Performance_, in
///   Trends in Constraint Programming 2007.
#[derive(Default)]
pub struct Bitwise {
    /// Input literals
    in_lits: Vec<Lit>,
    /// The number of clauses in the encoding
    n_clauses: usize,
    /// The number of new variables in the encoding
    n_vars: u32,
}

impl Encode for Bitwise {
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

        let p = utils::digits(self.in_lits.len() - 1, 2);
        let aux_vars: Vec<_> = (0..p).map(|_| var_manager.new_var()).collect();

        let clause = |idx: usize, k: usize| {
            let aux = aux_vars[k].lit(idx & (1 << k) == 0);
            atomics::lit_impl_lit(self.in_lits[idx], aux)
        };
        collector.extend_clauses(
            (0..self.in_lits.len()).flat_map(|idx| (0..p as usize).map(move |k| clause(idx, k))),
        )?;

        self.n_clauses = collector.n_clauses() - prev_clauses;
        self.n_vars += p;
        Ok(())
    }
}

impl IterInputs for Bitwise {
    type Iter<'a> = std::iter::Copied<std::slice::Iter<'a, Lit>>;

    fn iter(&self) -> Self::Iter<'_> {
        self.in_lits.iter().copied()
    }
}

impl EncodeStats for Bitwise {
    fn n_clauses(&self) -> usize {
        self.n_clauses
    }

    fn n_vars(&self) -> u32 {
        self.n_vars
    }
}

impl From<Vec<Lit>> for Bitwise {
    fn from(lits: Vec<Lit>) -> Self {
        Self {
            in_lits: lits,
            n_clauses: 0,
            n_vars: 0,
        }
    }
}

impl FromIterator<Lit> for Bitwise {
    fn from_iter<T: IntoIterator<Item = Lit>>(iter: T) -> Self {
        Self {
            in_lits: Vec::from_iter(iter),
            n_clauses: 0,
            n_vars: 0,
        }
    }
}

impl Extend<Lit> for Bitwise {
    fn extend<T: IntoIterator<Item = Lit>>(&mut self, iter: T) {
        self.in_lits.extend(iter);
    }
}
