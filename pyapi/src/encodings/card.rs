//! # Python API for RustSAT Cardinality Encodings

use pyo3::prelude::*;

use rustsat::{
    encodings::{
        card::{
            BoundBoth, BoundBothIncremental, BoundLower, BoundLowerIncremental, BoundUpper,
            BoundUpperIncremental, Encode as CardEncode, Totalizer as RsTotalizer,
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

            /// Adds additional input literals to the encoding
            fn extend(&mut self, lits: Vec<Lit>) {
                let lits: Vec<RsLit> = unsafe { std::mem::transmute(lits) };
                self.0.extend(lits);
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

            /// Incrementally builds the encoding so that upper bounds in the range
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
                let assumps: Vec<Lit> = unsafe {
                    std::mem::transmute(self.0.enforce_ub(ub).map_err(|_| {
                        pyo3::exceptions::PyRuntimeError::new_err("not encoded to enforce bound")
                    })?)
                };
                Ok(assumps)
            }

            /// Incrementally builds the encoding so that lower bounds in the range
            /// `min_lb..=max_lb` can be enforced. New variables will be taken from `var_manager`.
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

            /// Gets assumptions to enforce the given upper bound. Make sure that the required
            /// encoding is built first.
            fn enforce_lb(&self, lb: usize) -> PyResult<Vec<Lit>> {
                let assumps: Vec<Lit> = unsafe {
                    std::mem::transmute(
                        self.0
                            .enforce_lb(lb)
                            .map_err(super::convert_enforce_error)?,
                    )
                };
                Ok(assumps)
            }

            /// Incrementally builds the encoding so that both bounds in the range
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
                let assumps: Vec<Lit> = unsafe {
                    std::mem::transmute(
                        self.0
                            .enforce_eq(val)
                            .map_err(super::convert_enforce_error)?,
                    )
                };
                Ok(assumps)
            }
        }
    };
}

/// Implementation of the binary adder tree totalizer encoding \[1\].
/// The implementation is incremental as extended in \[2\].
/// The implementation is based on a node database.
/// For now, this implementation only supports upper bounding.
///
/// # References
///
/// - \[1\] Olivier Bailleux and Yacine Boufkhad: _Efficient CNF Encoding of Boolean Cardinality Constraints_, CP 2003.
/// - \[2\] Ruben Martins and Saurabh Joshi and Vasco Manquinho and Ines Lynce: _Incremental Cardinality Constraints for MaxSAT_, CP 2014.
#[pyclass]
#[repr(transparent)]
pub struct Totalizer(RsTotalizer);

implement_pyapi!(Totalizer, RsTotalizer);
