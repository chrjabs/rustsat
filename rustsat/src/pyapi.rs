//! # Python API for RustSAT
//!
//! This is the Python API for RustSAT. Currently this API is very minimal and
//! not the focus of this project. For now, only the API of certain encodings is
//! available.

use pyo3::{prelude::*, types::PySlice};

use crate::{
    encodings::card::DbTotalizer,
    instances::{BasicVarManager, Cnf},
    types::{Clause, Lit},
};

#[derive(FromPyObject)]
pub enum SliceOrInt<'a> {
    Slice(&'a PySlice),
    Int(isize),
}

pub enum SingleOrList<T> {
    Single(T),
    List(Vec<T>),
}

impl<T> IntoPy<PyObject> for SingleOrList<T>
where
    T: IntoPy<PyObject>,
{
    fn into_py(self, py: Python<'_>) -> PyObject {
        match self {
            SingleOrList::Single(single) => single.into_py(py),
            SingleOrList::List(list) => list.into_py(py),
        }
    }
}

#[pymodule]
fn rustsat(_py: Python<'_>, m: &PyModule) -> PyResult<()> {
    m.add_class::<Lit>()?;
    m.add_class::<Clause>()?;
    m.add_class::<Cnf>()?;
    m.add_class::<DbTotalizer>()?;
    m.add_class::<BasicVarManager>()?;
    Ok(())
}
