//! # CNF Encodings for At-Most-1 Constraints
//!
//! The module contains implementations of CNF encodings for at-most-1
//! constraints.
//!
//! ## Example Useage
//!
//! ```
//! use rustsat::{
//!     encodings::am1::{self, Encode},
//!     instances::{BasicVarManager, ManageVars},
//!     lit,
//!     types::{Lit, Var},
//!     var,
//! };
//!
//! let mut var_manager = BasicVarManager::default();
//! var_manager.increase_next_free(var![3]);
//!
//! let mut encoder = am1::new_default_am1();
//! encoder.extend(vec![lit![0], lit![1], lit![2]]);
//! let encoding = encoder.encode(&mut var_manager).unwrap();
//! ```

use super::Error;
use crate::{
    instances::{Cnf, ManageVars},
    types::Lit,
};

mod pairwise;
pub use pairwise::Pairwise;

/// Trait for all at-most-1 encodings
pub trait Encode: Default + From<Vec<Lit>> + FromIterator<Lit> + Extend<Lit> {
    type Iter<'a>: Iterator<Item = Lit>
    where
        Self: 'a;
    /// Gets an iterator over copies of the input literals
    fn iter(&self) -> Self::Iter<'_>;
    /// Gets the number of literals in the encoding
    fn n_lits(&self) -> usize;
    /// Encodes and enforces the at-most-1 constraint
    fn encode(&mut self, var_manager: &mut dyn ManageVars) -> Result<Cnf, Error>;
}

/// The default at-most-1 encoding. For now this is a [`Pairwise`] encoding.
pub type DefUB = Pairwise;

/// Constructs a default at-most-1 encoding.
pub fn new_default_am1() -> impl Encode {
    DefUB::default()
}
