//! # Python API for RustSAT Encodings

use pyo3::prelude::*;

use rustsat::{
    encodings::{
        card::{
            BoundUpper as CardBU, BoundUpperIncremental as CardBUI, DbTotalizer,
            Encode as CardEncode,
        },
        pb::{
            BoundUpper as PbBU, BoundUpperIncremental as PbBUI, DbGte,
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

fn convert_error(err: Error) -> PyErr {
    match err {
        Error::NotEncoded => {
            pyo3::exceptions::PyRuntimeError::new_err("not encoded to enforce bound")
        }
        Error::Unsat => pyo3::exceptions::PyValueError::new_err("encoding is unsat"),
    }
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
pub struct Totalizer(DbTotalizer);

impl From<DbTotalizer> for Totalizer {
    fn from(value: DbTotalizer) -> Self {
        Self(value)
    }
}

impl From<Totalizer> for DbTotalizer {
    fn from(value: Totalizer) -> Self {
        value.0
    }
}

#[pymethods]
impl Totalizer {
    #[new]
    fn new(lits: Vec<Lit>) -> Self {
        let lits: Vec<RsLit> = unsafe { std::mem::transmute(lits) };
        DbTotalizer::from_iter(lits).into()
    }

    /// Adds additional input literals to the totalizer
    fn extend(&mut self, lits: Vec<Lit>) {
        let lits: Vec<RsLit> = unsafe { std::mem::transmute(lits) };
        self.0.extend(lits)
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

    /// Incrementally builds the totalizer encoding to that upper bounds
    /// in the range `max_ub..=min_ub` can be enforced. New variables will
    /// be taken from `var_manager`.
    fn encode_ub(
        &mut self,
        max_ub: usize,
        min_ub: usize,
        var_manager: &mut VarManager,
    ) -> PyResult<Cnf> {
        let mut cnf = RsCnf::new();
        let var_manager: &mut BasicVarManager = var_manager.into();
        handle_oom!(self
            .0
            .encode_ub_change(max_ub..=min_ub, &mut cnf, var_manager));
        Ok(cnf.into())
    }

    /// Gets assumptions to enforce the given upper bound. Make sure that
    /// the required encoding is built first.
    fn enforce_ub(&self, ub: usize) -> PyResult<Vec<Lit>> {
        let assumps: Vec<Lit> =
            unsafe { std::mem::transmute(self.0.enforce_ub(ub).map_err(convert_error)?) };
        Ok(assumps)
    }
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

impl From<DbGte> for GeneralizedTotalizer {
    fn from(value: DbGte) -> Self {
        Self(value)
    }
}

impl From<GeneralizedTotalizer> for DbGte {
    fn from(value: GeneralizedTotalizer) -> Self {
        value.0
    }
}

#[pymethods]
impl GeneralizedTotalizer {
    #[new]
    fn new(lits: Vec<(Lit, usize)>) -> Self {
        let lits: Vec<(RsLit, usize)> = unsafe { std::mem::transmute(lits) };
        DbGte::from_iter(lits).into()
    }

    /// Adds additional input literals to the generalized totalizer
    fn extend(&mut self, lits: Vec<(Lit, usize)>) {
        let lits: Vec<(RsLit, usize)> = unsafe { std::mem::transmute(lits) };
        self.0.extend(lits)
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

    /// Incrementally builds the GTE encoding to that upper bounds
    /// in the range `max_ub..=min_ub` can be enforced. New variables will
    /// be taken from `var_manager`.
    fn encode_ub(
        &mut self,
        max_ub: usize,
        min_ub: usize,
        var_manager: &mut VarManager,
    ) -> PyResult<Cnf> {
        let mut cnf = RsCnf::new();
        let var_manager: &mut BasicVarManager = var_manager.into();
        handle_oom!(self
            .0
            .encode_ub_change(max_ub..=min_ub, &mut cnf, var_manager));
        Ok(cnf.into())
    }

    /// Gets assumptions to enforce the given upper bound. Make sure that
    /// the required encoding is built first.
    fn enforce_ub(&self, ub: usize) -> PyResult<Vec<Lit>> {
        let assumps = unsafe { std::mem::transmute(self.0.enforce_ub(ub).map_err(convert_error)?) };
        Ok(assumps)
    }
}

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

impl From<RsDpw> for DynamicPolyWatchdog {
    fn from(value: RsDpw) -> Self {
        Self(value)
    }
}

impl From<DynamicPolyWatchdog> for RsDpw {
    fn from(value: DynamicPolyWatchdog) -> Self {
        value.0
    }
}

#[pymethods]
impl DynamicPolyWatchdog {
    #[new]
    fn new(lits: Vec<(Lit, usize)>) -> Self {
        let lits: Vec<(RsLit, usize)> = unsafe { std::mem::transmute(lits) };
        RsDpw::from_iter(lits).into()
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

    /// Incrementally builds the DPW encoding to that upper bounds
    /// in the range `max_ub..=min_ub` can be enforced. New variables will
    /// be taken from `var_manager`.
    fn encode_ub(
        &mut self,
        max_ub: usize,
        min_ub: usize,
        var_manager: &mut VarManager,
    ) -> PyResult<Cnf> {
        let mut cnf = RsCnf::new();
        let var_manager: &mut BasicVarManager = var_manager.into();
        handle_oom!(self
            .0
            .encode_ub_change(max_ub..=min_ub, &mut cnf, var_manager));
        Ok(cnf.into())
    }

    /// Gets assumptions to enforce the given upper bound. Make sure that
    /// the required encoding is built first.
    fn enforce_ub(&self, ub: usize) -> PyResult<Vec<Lit>> {
        let assumps = self.0.enforce_ub(ub).map_err(convert_error)?;
        Ok(assumps.into_iter().map(|l| l.into()).collect())
    }
}
