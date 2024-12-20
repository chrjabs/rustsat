//! # Python API for RustSAT PB Encodings

use pyo3::prelude::*;

use rustsat::{
    encodings::{
        pb::{
            BinaryAdder as RsAdder, BoundBoth, BoundBothIncremental, BoundLower,
            BoundLowerIncremental, BoundUpper as PbBU, BoundUpperIncremental as PbBUI, DbGte,
            DynamicPolyWatchdog as RsDpw, Encode as PbEncode,
        },
        EncodeStats, Error,
    },
    instances::{BasicVarManager, Cnf as RsCnf},
    types::Lit as RsLit,
};

use crate::{
    handle_oom,
    instances::{Cnf, VarManager},
    types::Lit,
};

#[allow(clippy::needless_pass_by_value)]
fn convert_error(err: Error) -> PyErr {
    match err {
        Error::NotEncoded => {
            pyo3::exceptions::PyRuntimeError::new_err("not encoded to enforce bound")
        }
        Error::Unsat => pyo3::exceptions::PyValueError::new_err("encoding is unsat"),
    }
}

macro_rules! shared_pyapi {
    (derive_from, $type:ty, $rstype:ty) => {
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
    };
    (extend, $type:ty) => {
        #[pymethods]
        impl $type {
            /// Adds additional input literals to the encoding
            fn extend(&mut self, lits: Vec<(Lit, usize)>) {
                let lits: Vec<(RsLit, usize)> = unsafe { std::mem::transmute(lits) };
                self.0.extend(lits);
            }
        }
    };
    (base, $type:ty, $rstype:ty) => {
        #[pymethods]
        impl $type {
            #[new]
            fn new(lits: Vec<(Lit, usize)>) -> Self {
                let lits: Vec<(RsLit, usize)> = unsafe { std::mem::transmute(lits) };
                <$rstype>::from_iter(lits).into()
            }

            /// Gets the sum of weights in the encoding
            fn weight_sum(&self) -> usize {
                self.0.weight_sum()
            }

            /// Gets the number of clauses in the encoding
            fn n_clauses(&self) -> usize {
                self.0.n_clauses()
            }

            /// Gets the number of variables in the encoding
            fn n_vars(&self) -> u32 {
                self.0.n_vars()
            }
        }
    };
    (ub, $type:ty) => {
        #[pymethods]
        impl $type {
            /// Incrementally builds the encoding to that upper bounds in the range
            /// `min_ub..=max_ub` can be enforced. New variables will be taken from `var_manager`.
            fn encode_ub(
                &mut self,
                min_ub: usize,
                max_ub: usize,
                var_manager: &mut VarManager,
            ) -> PyResult<Cnf> {
                let mut cnf = RsCnf::new();
                let var_manager: &mut BasicVarManager = var_manager.into();
                handle_oom!(self
                    .0
                    .encode_ub_change(min_ub..=max_ub, &mut cnf, var_manager));
                Ok(cnf.into())
            }

            /// Gets assumptions to enforce the given upper bound. Make sure that the required
            /// encoding is built first.
            fn enforce_ub(&self, ub: usize) -> PyResult<Vec<Lit>> {
                let assumps: Vec<Lit> =
                    unsafe { std::mem::transmute(self.0.enforce_ub(ub).map_err(convert_error)?) };
                Ok(assumps)
            }
        }
    };
    (lb, $type:ty) => {
        #[pymethods]
        impl $type {
            /// Incrementally builds the encoding to that lower bounds in the range `min_lb..=max_lb`
            /// can be enforced. New variables will be taken from `var_manager`.
            fn encode_lb(
                &mut self,
                min_lb: usize,
                max_lb: usize,
                var_manager: &mut VarManager,
            ) -> PyResult<Cnf> {
                let mut cnf = RsCnf::new();
                let var_manager: &mut BasicVarManager = var_manager.into();
                handle_oom!(self
                    .0
                    .encode_lb_change(min_lb..=max_lb, &mut cnf, var_manager));
                Ok(cnf.into())
            }

            /// Gets assumptions to enforce the given lower bound. Make sure that the required encoding
            /// is built first.
            fn enforce_lb(&self, lb: usize) -> PyResult<Vec<Lit>> {
                let assumps = self.0.enforce_lb(lb).map_err(convert_error)?;
                Ok(assumps.into_iter().map(Into::into).collect())
            }
        }
    };
    (both, $type:ty) => {
        #[pymethods]
        impl $type {
            /// Incrementally builds the encoding to that both bounds in the range
            /// `min_bound..=max_bound` can be enforced. New variables will be taken from
            /// `var_manager`.
            fn encode_both(
                &mut self,
                min_bound: usize,
                max_bound: usize,
                var_manager: &mut VarManager,
            ) -> PyResult<Cnf> {
                let mut cnf = RsCnf::new();
                let var_manager: &mut BasicVarManager = var_manager.into();
                handle_oom!(self.0.encode_both_change(
                    min_bound..=max_bound,
                    &mut cnf,
                    var_manager
                ));
                Ok(cnf.into())
            }

            /// Gets assumptions to enforce the given equality bound. Make sure that the required
            /// encoding is built first.
            fn enforce_eq(&self, val: usize) -> PyResult<Vec<Lit>> {
                let assumps = self.0.enforce_eq(val).map_err(convert_error)?;
                Ok(assumps.into_iter().map(Into::into).collect())
            }
        }
    };
}

macro_rules! implement_pyapi {
    (ub, $type:ty, $rstype:ty) => {
        shared_pyapi!(derive_from, $type, $rstype);
        shared_pyapi!(base, $type, $rstype);
        shared_pyapi!(extend, $type);
        shared_pyapi!(ub, $type);
    };
    (ub_noextend, $type:ty, $rstype:ty) => {
        shared_pyapi!(derive_from, $type, $rstype);
        shared_pyapi!(base, $type, $rstype);
        shared_pyapi!(ub, $type);
    };
    (both, $type:ty, $rstype:ty) => {
        shared_pyapi!(derive_from, $type, $rstype);
        shared_pyapi!(base, $type, $rstype);
        shared_pyapi!(extend, $type);
        shared_pyapi!(ub, $type);
        shared_pyapi!(lb, $type);
        shared_pyapi!(both, $type);
    };
}

/// Implementation of the binary adder tree generalized totalizer encoding
/// \[1\]. The implementation is incremental. The implementation is recursive.
/// This encoding only support upper bounding. Lower bounding can be achieved by
/// negating the input literals. This is implemented in
/// [`super::simulators::Inverted`].
/// The implementation is based on a node database.
///
/// # References
///
/// - \[1\] Saurabh Joshi and Ruben Martins and Vasco Manquinho: _Generalized
///   Totalizer Encoding for Pseudo-Boolean Constraints_, CP 2015.
#[pyclass]
#[repr(transparent)]
pub struct GeneralizedTotalizer(DbGte);

implement_pyapi!(ub, GeneralizedTotalizer, DbGte);

/// Implementation of the dynamic polynomial watchdog (DPW) encoding \[1\].
///
/// **Note**:
/// This implementation of the  DPW encoding only supports incrementally
/// changing the bound, but not adding new input literals. Calling extend after
/// encoding resets the entire encoding and with the next encode and entirely
/// new encoding will be returned.
///
/// ## References
///
/// - \[1\] Tobias Paxian and Sven Reimer and Bernd Becker: _Dynamic Polynomial
///   Watchdog Encoding for Solving Weighted MaxSAT_, SAT 2018.
#[pyclass]
#[repr(transparent)]
pub struct DynamicPolyWatchdog(RsDpw);

implement_pyapi!(ub_noextend, DynamicPolyWatchdog, RsDpw);

/// Implementation of the binary adder encoding first described in \[1\].
/// The implementation follows the description in \[2\].
///
/// ## References
///
/// - \[1\] Joose P. Warners: _A linear-time transformation of linear inequalities into conjunctive
///     normal form_, Inf. Process. Lett. 1998.
/// - \[2\] Niklas Eén and Niklas Sörensson: _Translating Pseudo-Boolean Constraints into SAT_,
///     JSAT 2006.
#[pyclass]
#[repr(transparent)]
pub struct BinaryAdder(RsAdder);

implement_pyapi!(both, BinaryAdder, RsAdder);
