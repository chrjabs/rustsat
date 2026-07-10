//! # Python API for RustSAT Instance Types

use pyo3::prelude::*;
use rustsat::instances::ManageVars;

/// Simple counting variable manager
#[pyclass]
#[repr(transparent)]
#[derive(Debug, PartialEq, Eq)]
pub struct VarManager(rustsat::instances::BasicVarManager);

impl From<rustsat::instances::BasicVarManager> for VarManager {
    fn from(value: rustsat::instances::BasicVarManager) -> Self {
        VarManager(value)
    }
}

impl From<VarManager> for rustsat::instances::BasicVarManager {
    fn from(value: VarManager) -> Self {
        value.0
    }
}

impl<'a> From<&'a VarManager> for &'a rustsat::instances::BasicVarManager {
    fn from(value: &'a VarManager) -> Self {
        &value.0
    }
}

impl<'a> From<&'a mut VarManager> for &'a mut rustsat::instances::BasicVarManager {
    fn from(value: &'a mut VarManager) -> Self {
        &mut value.0
    }
}

#[pymethods]
impl VarManager {
    /// Creates a new variable manager. Optionally marking `n_used` variables as already used.
    #[new]
    #[pyo3(text_signature = "(n_used = 0)")]
    fn new(n_used: u32) -> Self {
        rustsat::instances::BasicVarManager::from_next_free(rustsat::types::Var::new(n_used)).into()
    }

    /// Increases the number of variables marked as used
    fn increase_used(&mut self, n_used: u32) -> bool {
        self.0.increase_next_free(rustsat::types::Var::new(n_used))
    }

    /// Gets a new unused variable
    fn new_var(&mut self) -> u32 {
        let v = self.0.new_var();
        v.idx32() + 1
    }

    /// Gets the number of used variables
    fn n_used(&self) -> u32 {
        self.0.n_used()
    }
}

/// Simple type representing a CNF formula. Other than [`SatInstance<VM>`], this
/// type only supports clauses and does have an internal variable manager.
#[pyclass(sequence)]
#[derive(Debug, Eq, Default)]
pub struct Cnf {
    cnf: rustsat::instances::Cnf,
    modified: bool,
}

impl From<rustsat::instances::Cnf> for Cnf {
    fn from(value: rustsat::instances::Cnf) -> Self {
        Self {
            cnf: value,
            modified: false,
        }
    }
}

impl From<Cnf> for rustsat::instances::Cnf {
    fn from(value: Cnf) -> Self {
        value.cnf
    }
}

impl PartialEq for Cnf {
    fn eq(&self, other: &Self) -> bool {
        self.cnf == other.cnf
    }
}

#[pymethods]
impl Cnf {
    /// Adds a clause to the CNF
    #[inline]
    pub fn add_clause(&mut self, clause: &crate::types::Clause) {
        self.modified = true;
        self.cnf.add_clause(clause.inner().clone());
    }

    /// Adds a unit clause to the CNF
    pub fn add_unit(&mut self, unit: crate::types::Lit) {
        self.modified = true;
        self.cnf.add_clause(rustsat::clause![unit.into()]);
    }

    /// Adds a binary clause to the CNF
    pub fn add_binary(&mut self, lit1: crate::types::Lit, lit2: crate::types::Lit) {
        self.modified = true;
        self.cnf
            .add_clause(rustsat::types::Lit::from(lit1) | rustsat::types::Lit::from(lit2));
    }

    /// Adds a ternary clause to the CNF
    pub fn add_ternary(
        &mut self,
        lit1: crate::types::Lit,
        lit2: crate::types::Lit,
        lit3: crate::types::Lit,
    ) {
        self.modified = true;
        self.cnf.add_clause(
            rustsat::types::Lit::from(lit1)
                | rustsat::types::Lit::from(lit2)
                | rustsat::types::Lit::from(lit3),
        );
    }

    #[new]
    #[pyo3(text_signature = "(clauses = [])")]
    fn new(clauses: Vec<crate::types::Clause>) -> Self {
        clauses
            .into_iter()
            .map(Into::<rustsat::types::Clause>::into)
            .collect::<rustsat::instances::Cnf>()
            .into()
    }

    fn __repr__(&self) -> String {
        format!("{:?}", self.cnf)
    }

    fn __len__(&self) -> usize {
        self.cnf.len()
    }

    #[expect(clippy::cast_sign_loss)]
    #[expect(clippy::needless_pass_by_value)]
    fn __getitem__(
        &self,
        idx: Bound<'_, PyAny>,
    ) -> PyResult<crate::SingleOrList<crate::types::Clause>> {
        if let Ok(idx) = idx.extract::<i32>() {
            let idx: usize = idx.try_into().expect("got unexpected negative index");
            Ok(crate::SingleOrList::Single(self.cnf[idx].clone().into()))
        } else if let Ok(slice) = idx.cast::<pyo3::types::PySlice>() {
            let indices = slice.indices(self.__len__().try_into().unwrap())?;
            debug_assert!(indices.start >= 0);
            debug_assert!(indices.stop >= 0);
            debug_assert!(indices.step >= 0);
            Ok(crate::SingleOrList::List(
                (indices.start as usize..indices.stop as usize)
                    .step_by(indices.step as usize)
                    .map(|idx| self.cnf[idx].clone().into())
                    .collect(),
            ))
        } else {
            Err(pyo3::exceptions::PyTypeError::new_err("Unsupported type"))
        }
    }

    /// Adds an implication of form `a -> b`
    fn add_lit_impl_lit(&mut self, a: crate::types::Lit, b: crate::types::Lit) {
        self.modified = true;
        self.cnf.add_lit_impl_lit(a.into(), b.into());
    }

    /// Adds an implication of form `a -> (b1 | b2 | ... | bm)`
    fn add_lit_impl_clause(&mut self, a: crate::types::Lit, b: Vec<crate::types::Lit>) {
        self.modified = true;
        let b: Vec<rustsat::types::Lit> = unsafe { std::mem::transmute(b) };
        self.cnf.add_lit_impl_clause(a.into(), &b);
    }

    /// Adds an implication of form `a -> (b1 & b2 & ... & bm)`
    fn add_lit_impl_cube(&mut self, a: crate::types::Lit, b: Vec<crate::types::Lit>) {
        self.modified = true;
        let b: Vec<rustsat::types::Lit> = unsafe { std::mem::transmute(b) };
        self.cnf.add_lit_impl_cube(a.into(), &b);
    }

    /// Adds an implication of form `(a1 & a2 & ... & an) -> b`
    fn add_cube_impl_lit(&mut self, a: Vec<crate::types::Lit>, b: crate::types::Lit) {
        self.modified = true;
        let a: Vec<rustsat::types::Lit> = unsafe { std::mem::transmute(a) };
        self.cnf.add_cube_impl_lit(&a, b.into());
    }

    /// Adds an implication of form `(a1 | a2 | ... | an) -> b`
    fn add_clause_impl_lit(&mut self, a: Vec<crate::types::Lit>, b: crate::types::Lit) {
        self.modified = true;
        let a: Vec<rustsat::types::Lit> = unsafe { std::mem::transmute(a) };
        self.cnf.add_clause_impl_lit(&a, b.into());
    }

    /// Adds an implication of form `(a1 & a2 & ... & an) -> (b1 | b2 | ... | bm)`
    fn add_cube_impl_clause(&mut self, a: Vec<crate::types::Lit>, b: Vec<crate::types::Lit>) {
        self.modified = true;
        let a: Vec<rustsat::types::Lit> = unsafe { std::mem::transmute(a) };
        let b: Vec<rustsat::types::Lit> = unsafe { std::mem::transmute(b) };
        self.cnf.add_cube_impl_clause(&a, &b);
    }

    /// Adds an implication of form `(a1 | a2 | ... | an) -> (b1 | b2 | ... | bm)`
    fn add_clause_impl_clause(&mut self, a: Vec<crate::types::Lit>, b: Vec<crate::types::Lit>) {
        self.modified = true;
        let a: Vec<rustsat::types::Lit> = unsafe { std::mem::transmute(a) };
        let b: Vec<rustsat::types::Lit> = unsafe { std::mem::transmute(b) };
        self.cnf.add_clause_impl_clause(&a, &b);
    }

    /// Adds an implication of form `(a1 | a2 | ... | an) -> (b1 & b2 & ... & bm)`
    fn add_clause_impl_cube(&mut self, a: Vec<crate::types::Lit>, b: Vec<crate::types::Lit>) {
        self.modified = true;
        let a: Vec<rustsat::types::Lit> = unsafe { std::mem::transmute(a) };
        let b: Vec<rustsat::types::Lit> = unsafe { std::mem::transmute(b) };
        self.cnf.add_clause_impl_cube(&a, &b);
    }

    /// Adds an implication of form `(a1 & a2 & ... & an) -> (b1 & b2 & ... & bm)`
    fn add_cube_impl_cube(&mut self, a: Vec<crate::types::Lit>, b: Vec<crate::types::Lit>) {
        self.modified = true;
        let a: Vec<rustsat::types::Lit> = unsafe { std::mem::transmute(a) };
        let b: Vec<rustsat::types::Lit> = unsafe { std::mem::transmute(b) };
        self.cnf.add_cube_impl_cube(&a, &b);
    }

    fn __iter__(mut slf: PyRefMut<'_, Self>) -> CnfIter {
        slf.modified = false;
        CnfIter {
            cnf: slf.into(),
            index: 0,
        }
    }

    fn __eq__(&self, other: &Cnf) -> bool {
        self == other
    }

    fn __ne__(&self, other: &Cnf) -> bool {
        self != other
    }
}

#[pyclass]
struct CnfIter {
    cnf: Py<Cnf>,
    index: usize,
}

#[pymethods]
impl CnfIter {
    fn __iter__(slf: PyRef<'_, Self>) -> PyRef<'_, Self> {
        slf
    }

    fn __next__(mut slf: PyRefMut<'_, Self>) -> PyResult<Option<crate::types::Clause>> {
        if slf.cnf.borrow(slf.py()).modified {
            return Err(pyo3::exceptions::PyRuntimeError::new_err(
                "cnf modified during iteration",
            ));
        }
        if slf.index < slf.cnf.borrow(slf.py()).__len__() {
            slf.index += 1;
            return Ok(Some(
                slf.cnf.borrow(slf.py()).cnf[slf.index - 1].clone().into(),
            ));
        }
        Ok(None)
    }
}
