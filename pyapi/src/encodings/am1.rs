//! # Python API for RustSAT At-Most-One Encodings

use pyo3::prelude::*;

use rustsat::{
    encodings::{
        am1::{
            Bimander as RsBimander, Bitwise as RsBitwise, Commander as RsCommander, Encode,
            Ladder as RsLadder, Pairwise as RsPairwise,
        },
        EncodeStats,
    },
    instances::{BasicVarManager, Cnf as RsCnf},
    types::Lit as RsLit,
};

use crate::{
    handle_oom,
    instances::{Cnf, VarManager},
    types::Lit,
};

macro_rules! implement_pyapi {
    ($type:ty, $rstype:ty) => {
        impl From<$rstype> for $type {
            fn from(value: $rstype) -> Self {
                Self(value)
            }
        }

        impl From<$type> for $rstype {
            fn from(value: $type) -> Self {
                value.0
            }
        }

        #[pymethods]
        impl $type {
            #[new]
            fn new(lits: Vec<Lit>) -> Self {
                let lits: Vec<RsLit> = unsafe { std::mem::transmute(lits) };
                <$rstype>::from_iter(lits).into()
            }

            /// Gets the number of input literals in the encoding
            fn n_lits(&self) -> usize {
                self.0.n_lits()
            }

            /// Gets the number of clauses in the encoding
            fn n_clauses(&self) -> usize {
                self.0.n_clauses()
            }

            /// Gets the number of variables in the encoding
            fn n_vars(&self) -> u32 {
                self.0.n_vars()
            }

            /// Builds the encoding. New variables will be taken from `var_manager`.
            fn encode(&mut self, var_manager: &mut VarManager) -> PyResult<Cnf> {
                let mut cnf = RsCnf::new();
                let var_manager: &mut BasicVarManager = var_manager.into();
                handle_oom!(self.0.encode(&mut cnf, var_manager));
                Ok(cnf.into())
            }
        }
    };
}

/// Implementation of the bimander at-most-1 encoding.
///
/// The sub encoding is fixed to [`Pairwise`] and the size of the splits to 4.
///
/// # References
///
/// - Van-Hau Nguyen and Son Thay Mai: _A New Method to Encode the At-Most-One Constraint into SAT,
///   SOICT 2015.
#[pyclass]
#[repr(transparent)]
pub struct Bimander(RsBimander);

implement_pyapi!(Bimander, RsBimander);

/// Implementations of the bitwise at-most-1 encoding.
///
/// # References
///
/// - Steven D. Prestwich: _Negative Effects of Modeling Techniques on Search Performance_, in
///   Trends in Constraint Programming 2007.
#[pyclass]
#[repr(transparent)]
pub struct Bitwise(RsBitwise);

implement_pyapi!(Bitwise, RsBitwise);

/// Implementations of the commander at-most-1 encoding.
///
/// The encoding uses 4 splits and the pairwise encoding as the sub encoding.
///
/// # References
///
/// - Will Klieber and Gihwon Kwon: _Efficient CNF Encoding for Selecting 1 from N Objects, CFV
///   2007.
#[pyclass]
#[repr(transparent)]
pub struct Commander(RsCommander);

implement_pyapi!(Commander, RsCommander);

/// Implementations of the ladder at-most-1 encoding.
///
/// # References
///
/// - Ian P. Gent and Peter Nightingale: _A new Encoding of AllDifferent into SAT_, CP 2004.
#[pyclass]
#[repr(transparent)]
pub struct Ladder(RsLadder);

implement_pyapi!(Ladder, RsLadder);

/// Implementations of the pairwise at-most-1 encoding.
///
/// # References
///
/// - Steven D. Prestwich: _CNF Encodings_, in Handbook of Satisfiability 2021.
#[pyclass]
#[repr(transparent)]
pub struct Pairwise(RsPairwise);

implement_pyapi!(Pairwise, RsPairwise);
