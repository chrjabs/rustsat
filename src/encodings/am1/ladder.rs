//! # Ladder At-Most-1 Encoding
//!
//! ## References
//!
//! - Ian P. Gent and Peter Nightingale: _A new Encoding of AllDifferent into SAT_, ModRef 2004.

use super::Encode;
use crate::{
    encodings::{atomics, CollectClauses, EncodeStats, IterInputs},
    instances::ManageVars,
    lit,
    types::Lit,
};

/// Implementations of the ladder at-most-1 encoding.
///
/// # References
///
/// - Ian P. Gent and Peter Nightingale: _A new Encoding of AllDifferent into SAT_, ModRef 2004.
#[derive(Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Ladder {
    /// Input literals
    in_lits: Vec<Lit>,
    /// The number of clauses in the encoding
    n_clauses: usize,
    /// The number of new variables in the encoding
    n_vars: u32,
}

impl Encode for Ladder {
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

        let aux_lits: Vec<_> = (0..self.in_lits.len() - 1)
            .map(|_| var_manager.new_lit())
            .collect();
        // ladder validity clauses
        collector.extend_clauses(
            (0..self.in_lits.len() - 2)
                .map(|idx| atomics::lit_impl_lit(aux_lits[idx + 1], aux_lits[idx])),
        )?;
        // channelling clauses
        let mut buf = [lit![0], lit![0]];
        for idx in 0..self.in_lits.len() {
            let mut cube_len = 0;
            if idx > 0 {
                buf[cube_len] = aux_lits[idx - 1];
                cube_len += 1;
            }
            if idx < aux_lits.len() {
                buf[cube_len] = !aux_lits[idx];
                cube_len += 1;
            }
            let cube = &buf[0..cube_len];
            let lit = self.in_lits[idx];
            collector.extend_clauses(atomics::lit_impl_cube(lit, cube))?;
        }

        self.n_clauses = collector.n_clauses() - prev_clauses;
        self.n_vars += u32::try_from(self.in_lits.len())
            .expect("cannot handle more than `u32::MAX` variables")
            - 1;
        Ok(())
    }
}

impl IterInputs for Ladder {
    type Iter<'a> = std::iter::Copied<std::slice::Iter<'a, Lit>>;

    fn iter(&self) -> Self::Iter<'_> {
        self.in_lits.iter().copied()
    }
}

impl EncodeStats for Ladder {
    fn n_clauses(&self) -> usize {
        self.n_clauses
    }

    fn n_vars(&self) -> u32 {
        self.n_vars
    }
}

impl From<Vec<Lit>> for Ladder {
    fn from(lits: Vec<Lit>) -> Self {
        Self {
            in_lits: lits,
            n_clauses: 0,
            n_vars: 0,
        }
    }
}

impl FromIterator<Lit> for Ladder {
    fn from_iter<T: IntoIterator<Item = Lit>>(iter: T) -> Self {
        Self {
            in_lits: Vec::from_iter(iter),
            n_clauses: 0,
            n_vars: 0,
        }
    }
}

impl Extend<Lit> for Ladder {
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
        let mut enc: super::Ladder = [lit![0], lit![1], lit![2], lit![3]].into_iter().collect();
        let mut cnf = Cnf::new();
        let mut vm = BasicVarManager::from_next_free(var![4]);
        enc.encode(&mut cnf, &mut vm).unwrap();
        assert_eq!(vm.n_used(), 7);
        assert_eq!(cnf.len(), 8);
    }
}
