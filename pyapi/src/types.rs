//! # Python API for Basic RustSAT Types

use core::{ffi::c_int, fmt};

use pyo3::{
    exceptions::{PyIndexError, PyRuntimeError, PyValueError},
    prelude::*,
};

use rustsat::types::{Clause as RsClause, Lit as RsLit};

use crate::{SingleOrList, SliceOrInt};

/// Type representing literals, possibly negated boolean variables.
///
/// # Representation in Memory
///
/// Literal representation is `idx << 1` with the last bit representing
/// whether the literal is negated or not. This way the literal can directly
/// be used to index data structures with the two literals of a variable
/// being close together.
#[pyclass]
#[repr(transparent)]
#[derive(Hash, Eq, PartialEq, PartialOrd, Ord, Clone, Copy, Debug)]
pub struct Lit(RsLit);

impl From<RsLit> for Lit {
    fn from(value: RsLit) -> Self {
        Lit(value)
    }
}

impl From<Lit> for RsLit {
    fn from(value: Lit) -> Self {
        value.0
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[pymethods]
impl Lit {
    #[new]
    fn new(ipasir: c_int) -> PyResult<Self> {
        Ok(RsLit::from_ipasir(ipasir)
            .map_err(|_| PyValueError::new_err("invalid ipasir lit"))?
            .into())
    }

    fn __str__(&self) -> String {
        format!("{}", self)
    }

    fn __repr__(&self) -> String {
        format!("{}", self)
    }

    fn __neg__(&self) -> Lit {
        Lit(!self.0)
    }

    fn __richcmp__(&self, other: &Lit, op: pyo3::basic::CompareOp) -> bool {
        op.matches(self.cmp(other))
    }

    fn __hash__(&self) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        self.hash(&mut hasher);
        hasher.finish()
    }

    /// Gets the IPASIR/DIMACS representation of the literal
    #[allow(clippy::wrong_self_convention)]
    fn to_ipasir(&self) -> c_int {
        let negated = self.0.is_neg();
        let idx: c_int = (self.0.vidx() + 1)
            .try_into()
            .expect("variable index too high to fit in c_int");
        if negated {
            -idx
        } else {
            idx
        }
    }
}

/// Type representing a clause.
/// Wrapper around a std collection to allow for changing the data structure.
/// Optional clauses as sets will be included in the future.
#[pyclass]
#[derive(Eq, PartialOrd, Ord, Clone, Default)]
pub struct Clause {
    cl: RsClause,
    modified: bool,
}

impl From<RsClause> for Clause {
    fn from(value: RsClause) -> Self {
        Self {
            cl: value,
            modified: false,
        }
    }
}

impl From<Clause> for RsClause {
    fn from(value: Clause) -> Self {
        value.cl
    }
}

impl PartialEq for Clause {
    fn eq(&self, other: &Self) -> bool {
        self.cl == other.cl
    }
}

#[pymethods]
impl Clause {
    /// Checks if the clause is a unit clause
    #[inline]
    pub fn is_unit(&self) -> bool {
        self.cl.len() == 1
    }

    /// Checks if the clause is binary
    pub fn is_binary(&self) -> bool {
        self.cl.len() == 2
    }

    /// Adds a literal to the clause
    pub fn add(&mut self, lit: Lit) {
        self.modified = true;
        self.cl.add(lit.0)
    }

    /// Removes the first occurrence of a literal from the clause
    /// Returns true if an occurrence was found
    pub fn remove(&mut self, lit: &Lit) -> bool {
        self.modified = true;
        self.cl.remove(&lit.0)
    }

    /// Removes all occurrences of a literal from the clause
    pub fn remove_thorough(&mut self, lit: &Lit) -> bool {
        self.modified = true;
        self.cl.remove_thorough(&lit.0)
    }

    #[new]
    fn new(lits: Vec<Lit>) -> Self {
        let lits: Vec<RsLit> = unsafe { std::mem::transmute(lits) };
        RsClause::from_iter(lits).into()
    }

    fn __str__(&self) -> String {
        format!("{}", self.cl)
    }

    fn __repr__(&self) -> String {
        format!("{}", self.cl)
    }

    fn __len__(&self) -> usize {
        self.cl.len()
    }

    fn __getitem__(&self, idx: SliceOrInt) -> PyResult<SingleOrList<Lit>> {
        match idx {
            SliceOrInt::Slice(slice) => {
                let indices = slice.indices(self.__len__().try_into().unwrap())?;
                Ok(SingleOrList::List(
                    (indices.start as usize..indices.stop as usize)
                        .step_by(indices.step as usize)
                        .map(|idx| Lit(self.cl[idx]))
                        .collect(),
                ))
            }
            SliceOrInt::Int(idx) => {
                if idx.unsigned_abs() > self.__len__()
                    || idx >= 0 && idx.unsigned_abs() >= self.__len__()
                {
                    return Err(PyIndexError::new_err("out of bounds"));
                }
                let idx = if idx >= 0 {
                    idx.unsigned_abs()
                } else {
                    self.__len__() - idx.unsigned_abs()
                };
                Ok(SingleOrList::Single(Lit(self.cl[idx])))
            }
        }
    }

    fn __iter__(mut slf: PyRefMut<'_, Self>) -> ClauseIter {
        slf.modified = false;
        ClauseIter {
            clause: slf.into(),
            index: 0,
        }
    }

    fn extend(&mut self, lits: Vec<Lit>) {
        let lits: Vec<RsLit> = unsafe { std::mem::transmute(lits) };
        self.cl.extend(lits)
    }

    fn __eq__(&self, other: &Clause) -> bool {
        self == other
    }

    fn __ne__(&self, other: &Clause) -> bool {
        self != other
    }
}

#[pyclass]
struct ClauseIter {
    clause: Py<Clause>,
    index: usize,
}

#[pymethods]
impl ClauseIter {
    fn __iter__(slf: PyRef<'_, Self>) -> PyRef<'_, Self> {
        slf
    }

    fn __next__(mut slf: PyRefMut<'_, Self>) -> PyResult<Option<Lit>> {
        if slf.clause.borrow(slf.py()).modified {
            return Err(PyRuntimeError::new_err("clause modified during iteration"));
        }
        if slf.index < slf.clause.borrow(slf.py()).__len__() {
            slf.index += 1;
            return Ok(Some(Lit(slf.clause.borrow(slf.py()).cl[slf.index - 1])));
        }
        Ok(None)
    }
}
