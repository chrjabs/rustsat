//! # Pairwise At-Most-1 Encoding
//!
//! ## References
//!
//! - Steven D. Prestwich: _CNF Encodings_, in Handbook of Satisfiability 2021.

use super::Encode;
use crate::{
    clause,
    encodings::{CollectClauses, EncodeStats, Error, IterInputs},
    instances::ManageVars,
    types::Lit,
};

/// Implementations of the pairwise at-most-1 encoding.
///
/// # References
///
/// - Steven D. Prestwich: _CNF Encodings_, in Handbook of Satisfiability 2021.
#[derive(Default)]
pub struct Pairwise {
    /// Input literals
    in_lits: Vec<Lit>,
    /// The number of clauses in the encoding
    n_clauses: usize,
}

impl Encode for Pairwise {
    fn n_lits(&self) -> usize {
        self.in_lits.len()
    }

    fn encode<Col>(
        &mut self,
        collector: &mut Col,
        _var_manager: &mut dyn ManageVars,
    ) -> Result<(), Error>
    where
        Col: CollectClauses,
    {
        let prev_clauses = collector.n_clauses();
        let lits = &self.in_lits;
        let clause_iter = (0..self.in_lits.len()).flat_map(|first| {
            (first + 1..self.in_lits.len()).map(move |second| clause![!lits[first], !lits[second]])
        });
        collector.extend(clause_iter);
        self.n_clauses = collector.n_clauses() - prev_clauses;
        Ok(())
    }
}

impl IterInputs for Pairwise {
    type Iter<'a> = std::iter::Copied<std::slice::Iter<'a, Lit>>;

    fn iter(&self) -> Self::Iter<'_> {
        self.in_lits.iter().copied()
    }
}

impl EncodeStats for Pairwise {
    fn n_clauses(&self) -> usize {
        self.n_clauses
    }

    fn n_vars(&self) -> u32 {
        0
    }
}

impl From<Vec<Lit>> for Pairwise {
    fn from(lits: Vec<Lit>) -> Self {
        Self {
            in_lits: lits,
            n_clauses: Default::default(),
        }
    }
}

impl FromIterator<Lit> for Pairwise {
    fn from_iter<T: IntoIterator<Item = Lit>>(iter: T) -> Self {
        Self {
            in_lits: Vec::from_iter(iter),
            n_clauses: Default::default(),
        }
    }
}

impl Extend<Lit> for Pairwise {
    fn extend<T: IntoIterator<Item = Lit>>(&mut self, iter: T) {
        self.in_lits.extend(iter)
    }
}
