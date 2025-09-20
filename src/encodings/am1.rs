//! # CNF Encodings for At-Most-1 Constraints
//!
//! The module contains implementations of CNF encodings for at-most-1
//! constraints.
//!
//! ## Example Usage
//!
//! ```
//! # use rustsat::{
//! #     encodings::am1::{Def, Encode},
//! #     instances::{BasicVarManager, Cnf, ManageVars},
//! #     lit, var,
//! # };
//! #
//! let mut var_manager = BasicVarManager::default();
//! var_manager.increase_next_free(var![3]);
//!
//! let mut enc = Def::from(vec![lit![0], lit![1], lit![2]]);
//! let mut encoding = Cnf::new();
//! enc.encode(&mut encoding, &mut var_manager).unwrap();
//! ```

use std::ops::Neg;

use super::CollectClauses;
use crate::{
    clause,
    instances::ManageVars,
    types::{Clause, Lit},
};

mod pairwise;
pub use pairwise::Pairwise;

mod ladder;
pub use ladder::Ladder;

mod bitwise;
pub use bitwise::Bitwise;

mod commander;
pub use commander::Commander;

mod bimander;
pub use bimander::Bimander;

/// Trait for all at-most-1 encodings
pub trait Encode {
    /// Gets the number of literals in the encoding
    fn n_lits(&self) -> usize;
    /// Encodes and enforces the at-most-1 constraint
    ///
    /// # Errors
    ///
    /// If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
    fn encode<Col>(
        &mut self,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses;
}

/// The default at-most-1 encoding. For now this is a [`Pairwise`] encoding.
pub type Def = Pairwise;

/// Constructs a default at-most-1 encoding.
#[must_use]
pub fn new_default() -> impl Encode {
    Def::default()
}

/// Results of AM1 preprocessing
#[derive(Debug, PartialEq, Eq)]
struct Preprocessed {
    remaining: Vec<Lit>,
    units: Vec<Lit>,
}

impl Preprocessed {
    /// Preprocess the input literals to an AM1 constraint
    ///
    /// This does the following:
    /// - If there are duplicate literals, mark their negation as a unit
    /// - If there are literals and their negation, mark all other literals as a unit
    fn new(mut lits: Vec<Lit>) -> Self {
        let mut duplicate = vec![];
        let mut negated: Vec<Lit> = vec![];
        lits.sort_unstable();
        lits.dedup_by(|a, b| {
            // NOTE: a is removed, b remains
            if a == b {
                if !duplicate.last().is_some_and(|last| last == b) {
                    duplicate.push(*b);
                }
                return true;
            }
            if negated.last().is_some_and(|last| last.var() == a.var()) {
                duplicate.push(*a);
                return true;
            }
            if a.var() == b.var() {
                negated.push(*b);
                return true;
            }
            false
        });
        if negated.len() > 1 {
            // more than two negated pairs of the same variable make the constraint unsatisfiable
            return Preprocessed {
                remaining: vec![],
                units: vec![negated[0], !negated[0]],
            };
        }
        let mut dup_iter = duplicate.iter().peekable();
        let mut neg_iter = negated.iter().peekable();
        lits.retain(|&lit| {
            while dup_iter.peek().is_some_and(|&&dup| dup < lit) {
                dup_iter.next();
            }
            if let Some(&&dup) = dup_iter.peek() {
                if dup == lit {
                    return false;
                }
            }
            while neg_iter.peek().is_some_and(|&&dup| dup < lit) {
                neg_iter.next();
            }
            if let Some(&&neg) = neg_iter.peek() {
                if neg == lit {
                    return false;
                }
            }
            true
        });
        let mut units: Vec<_> = duplicate.into_iter().map(Lit::neg).collect();
        if !negated.is_empty() {
            units.extend(lits.into_iter().map(Lit::neg));
            return Preprocessed {
                remaining: vec![],
                units,
            };
        }
        Preprocessed {
            remaining: lits,
            units,
        }
    }

    fn units(&self) -> impl Iterator<Item = Clause> + '_ {
        self.units.iter().map(|&l| clause![l])
    }
}

#[cfg(test)]
mod tests {
    use crate::lit;

    #[test]
    fn preprocess_literals() {
        let lits = vec![lit![0], lit![1], lit![2], lit![3]];
        assert_eq!(
            super::Preprocessed::new(lits.clone()),
            super::Preprocessed {
                remaining: lits,
                units: vec![]
            }
        );

        let lits = vec![lit![0], lit![1], lit![0], lit![2], lit![3]];
        assert_eq!(
            super::Preprocessed::new(lits.clone()),
            super::Preprocessed {
                remaining: vec![lit![1], lit![2], lit![3]],
                units: vec![!lit![0]]
            }
        );

        let lits = vec![lit![0], lit![1], !lit![0], lit![2], lit![3]];
        assert_eq!(
            super::Preprocessed::new(lits.clone()),
            super::Preprocessed {
                remaining: vec![],
                units: vec![!lit![1], !lit![2], !lit![3]],
            }
        );

        let lits = vec![lit![0], lit![1], !lit![0], lit![2], !lit![1], lit![3]];
        assert_eq!(
            super::Preprocessed::new(lits.clone()),
            super::Preprocessed {
                remaining: vec![],
                units: vec![lit![0], !lit![0]],
            }
        );

        let lits = vec![lit![0], lit![1], lit![0], lit![2], !lit![1], lit![3]];
        assert_eq!(
            super::Preprocessed::new(lits.clone()),
            super::Preprocessed {
                remaining: vec![],
                units: vec![!lit![0], !lit![2], !lit![3]],
            }
        );

        let lits = vec![lit![0], !lit![0], !lit![0]];
        assert_eq!(
            super::Preprocessed::new(lits.clone()),
            super::Preprocessed {
                remaining: vec![],
                units: vec![lit![0]],
            }
        );
    }
}
