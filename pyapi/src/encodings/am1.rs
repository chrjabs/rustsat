//! # Python API for RustSAT At-Most-One Encodings

use pyo3::prelude::*;
use rustsat::encodings::am1::Encode;
use rustsat::encodings::EncodeStats;

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
            #[pyo3(text_signature = "(lits = [])")]
            fn new(lits: Vec<crate::types::Lit>) -> Self {
                let lits: Vec<rustsat::types::Lit> = unsafe { std::mem::transmute(lits) };
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
            fn encode(
                &mut self,
                var_manager: &mut crate::instances::VarManager,
            ) -> PyResult<crate::instances::Cnf> {
                let mut cnf = rustsat::instances::Cnf::new();
                let var_manager: &mut rustsat::instances::BasicVarManager = var_manager.into();
                crate::handle_oom!(self.0.encode(&mut cnf, var_manager));
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
pub struct Bimander(rustsat::encodings::am1::Bimander);

implement_pyapi!(Bimander, rustsat::encodings::am1::Bimander);

/// Implementations of the bitwise at-most-1 encoding.
///
/// # References
///
/// - Steven D. Prestwich: _Negative Effects of Modeling Techniques on Search Performance_, in
///   Trends in Constraint Programming 2007.
#[pyclass]
#[repr(transparent)]
pub struct Bitwise(rustsat::encodings::am1::Bitwise);

implement_pyapi!(Bitwise, rustsat::encodings::am1::Bitwise);

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
pub struct Commander(rustsat::encodings::am1::Commander);

implement_pyapi!(Commander, rustsat::encodings::am1::Commander);

/// Implementations of the ladder at-most-1 encoding.
///
/// # References
///
/// - Ian P. Gent and Peter Nightingale: _A new Encoding of AllDifferent into SAT_, CP 2004.
#[pyclass]
#[repr(transparent)]
pub struct Ladder(rustsat::encodings::am1::Ladder);

implement_pyapi!(Ladder, rustsat::encodings::am1::Ladder);

/// Implementations of the pairwise at-most-1 encoding.
///
/// # References
///
/// - Steven D. Prestwich: _CNF Encodings_, in Handbook of Satisfiability 2021.
#[pyclass]
#[repr(transparent)]
pub struct Pairwise(rustsat::encodings::am1::Pairwise);

implement_pyapi!(Pairwise, rustsat::encodings::am1::Pairwise);
