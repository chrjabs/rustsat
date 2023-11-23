//! # Python API for RustSAT
//!
//! This is the Python API for RustSAT. Currently this API is very minimal and
//! not the focus of this project. For now, only the API of certain encodings is
//! available.
//!
//! ## Classes
//!
//! The following classes are available as Python bindings.
//!
//! ```bash
//! rustsat
//! ├── Clause
//! ├── Cnf
//! ├── Lit
//! ├── VarManager
//! └── encodings
//!     ├── DynamicPolyWatchdog
//!     ├── GeneralizedTotalizer
//!     └── Totalizer
//! ```
//!
//! They have similar APIs (but reduced functionality) to the following Rust types:
//!
//! | Python Class | Rust Type |
//! | --- | --- |
//! | `rustsat.Clause` | [`crate::types::Clause`] |
//! | `rustsat.Cnf` | [`crate::instances::Cnf`] |
//! | `rustsat.Lit` | [`crate::types::Lit`] |
//! | `rustsat.VarManager` | [`crate::instances::BasicVarManager`] |
//! | `rustsat.encodings.DynamicPolyWatchdog` | [`crate::encodings::pb::DynamicPolyWatchdog`] |
//! | `rustsat.encodings.GeneralizedTotalizer` | [`crate::encodings::pb::GeneralizedTotalizer`] |
//! | `rustsat.encodings.Totalizer` | [`crate::encodings::card::Totalizer`] |

use pyo3::{prelude::*, types::PySlice};

use crate::{
    encodings::{
        card::DbTotalizer,
        pb::{DbGte, DynamicPolyWatchdog},
    },
    instances::{BasicVarManager, Cnf},
    types::{Clause, Lit},
};

#[derive(FromPyObject)]
pub(crate) enum SliceOrInt<'a> {
    Slice(&'a PySlice),
    Int(isize),
}

pub(crate) enum SingleOrList<T> {
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

/// Python bindings for the RustSAT library
#[pymodule]
fn rustsat(py: Python<'_>, m: &PyModule) -> PyResult<()> {
    m.add_class::<Lit>()?;
    m.add_class::<Clause>()?;
    m.add_class::<Cnf>()?;
    m.add_class::<BasicVarManager>()?;

    let encodings = PyModule::new(py, "rustsat.encodings")?;
    encodings.add_class::<DbTotalizer>()?;
    encodings.add_class::<DbGte>()?;
    encodings.add_class::<DynamicPolyWatchdog>()?;
    m.add("encodings", encodings)?;

    // To import encodings. Fix from https://github.com/PyO3/pyo3/issues/759
    py.import("sys")?
        .getattr("modules")?
        .set_item("rustsat.encodings", encodings)?;

    Ok(())
}
