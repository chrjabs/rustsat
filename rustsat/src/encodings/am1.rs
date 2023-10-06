//! # CNF Encodings for At-Most-1 Constraints
//!
//! The module contains implementations of CNF encodings for at-most-1
//! constraints.
//!
//! ## Example Useage
//!
//! ```
//! use rustsat::{
//!     encodings::am1::{Def, Encode},
//!     instances::{BasicVarManager, Cnf, ManageVars},
//!     lit, var,
//! };
//!
//! let mut var_manager = BasicVarManager::default();
//! var_manager.increase_next_free(var![3]);
//!
//! let mut enc = Def::from(vec![lit![0], lit![1], lit![2]]);
//! let mut encoding = Cnf::new();
//! enc.encode(&mut encoding, &mut var_manager).unwrap();
//! ```

use super::{CollectClauses, Error};
use crate::instances::ManageVars;

mod pairwise;
pub use pairwise::Pairwise;

/// Trait for all at-most-1 encodings
pub trait Encode {
    /// Gets the number of literals in the encoding
    fn n_lits(&self) -> usize;
    /// Encodes and enforces the at-most-1 constraint
    fn encode<Col>(
        &mut self,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), Error>
    where
        Col: CollectClauses;
}

/// The default at-most-1 encoding. For now this is a [`Pairwise`] encoding.
pub type Def = Pairwise;

/// Constructs a default at-most-1 encoding.
pub fn new_default_am1() -> impl Encode {
    Def::default()
}
