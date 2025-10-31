//! # rustsat-glucose - Interface to the Glucose SAT Solver for RustSAT
//!
//! The Glucose SAT solver to be used with the [RustSAT](https://github.com/chrjabs/rustsat) library.
//!
//! ## Features
//!
//! - `debug`: if this feature is enables, the Cpp library will be built with debug and check functionality if the Rust project is built in debug mode
//! - `quiet`: disable all glucose-internal printing to `stdout` during solving (on by default)
//!
//! ## Glucose Version
//!
//! The version of Glucose in this crate is Version 4.2.1.
//! The used Cpp source can be found
//! [here](https://github.com/chrjabs/rustsat/tree/main/glucose/cppsrc).
//!
//! ## Minimum Supported Rust Version (MSRV)
//!
//! Currently, the MSRV is 1.76.0, the plan is to always support an MSRV that is at least a year
//! old.
//!
//! Bumps in the MSRV will _not_ be considered breaking changes. If you need a specific MSRV, make
//! sure to pin a precise version of RustSAT.

#![warn(clippy::pedantic)]
#![warn(missing_docs)]
#![warn(missing_debug_implementations)]

use rustsat::{solvers::SolverState, types::Var};
use std::{ffi::c_int, fmt};
use thiserror::Error;

pub mod core;
pub mod simp;

/// Fatal error returned if the Glucose API returns an invalid value
#[derive(Error, Clone, Copy, PartialEq, Eq, Debug)]
#[error("glucose c-api returned an invalid value: {api_call} -> {value}")]
pub struct InvalidApiReturn {
    api_call: &'static str,
    value: c_int,
}

/// Error returned if a provided assumption variable was eliminated in preprocessing by the solver
///
/// Glucose does not support assumptions over eliminated variables. To prevent this, variables that
/// will be used as assumptions can be frozen via [`rustsat::solvers::FreezeVar`]
#[derive(Error, Clone, Copy, PartialEq, Eq, Debug)]
#[error("assumption variable {0} has been eliminated by glucose simplification")]
pub struct AssumpEliminated(Var);

#[derive(Debug, PartialEq, Eq, Default)]
enum InternalSolverState {
    #[default]
    Configuring,
    Input,
    Sat,
    Unsat(bool),
}

impl InternalSolverState {
    fn to_external(&self) -> SolverState {
        match self {
            InternalSolverState::Configuring => SolverState::Configuring,
            InternalSolverState::Input => SolverState::Input,
            InternalSolverState::Sat => SolverState::Sat,
            InternalSolverState::Unsat(_) => SolverState::Unsat,
        }
    }
}

/// Possible Glucose limits
#[derive(Debug, Clone, Copy)]
pub enum Limit {
    /// No limits
    None,
    /// A limit on the number of conflicts
    Conflicts(i64),
    /// A limit on the number of propagations
    Propagations(i64),
}

impl fmt::Display for Limit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Limit::None => write!(f, "none"),
            Limit::Conflicts(val) => write!(f, "conflicts ({val})"),
            Limit::Propagations(val) => write!(f, "propagations ({val})"),
        }
    }
}

macro_rules! handle_oom {
    ($val:expr) => {{
        let val = $val;
        if val == $crate::ffi::OUT_OF_MEM {
            return anyhow::Context::context(
                Err(rustsat::OutOfMemory::ExternalApi),
                "glucose out of memory",
            );
        }
        val
    }};
}
pub(crate) use handle_oom;

macro_rules! handle_oom_new {
    ($val:expr) => {{
        let val = $val;
        if val == $crate::ffi::OUT_OF_MEM {
            return Err(rustsat::OutOfMemory::ExternalApi);
        }
        val
    }};
}
pub(crate) use handle_oom_new;

/// Glucose in the initialization state
#[derive(Debug)]
pub struct Init();

/// Glucose in the input state
#[derive(Debug)]
pub struct Input();

/// Glucose in the sat state
#[derive(Debug)]
pub struct Sat();

/// Glucose in the unsat state
#[derive(Debug)]
pub struct Unsat();

/// Glucose in the unknown state
#[derive(Debug)]
pub struct Unknown();

/// Implements the basic incremental API for the core and the simp solver
macro_rules! impl_api {
    ($slvty:ty, $statety:ident, $init:ident, $reserve:ident, $add:ident, $solve:ident, $val:ident, $conflict:ident) => {
        impl rustsat::solvers::sat::Solve for $slvty {
            type Init = $statety<crate::Init>;

            type Input = $statety<crate::Input>;

            type Sat = $statety<crate::Sat>;

            type Unsat = $statety<crate::Unsat>;

            type Unknown = $statety<crate::Unknown>;

            fn signature() -> &'static str {
                let c_chars = unsafe { crate::ffi::cglucose4_signature() };
                let c_str = unsafe { CStr::from_ptr(c_chars) };
                c_str
                    .to_str()
                    .expect("Glucose signature returned invalid UTF-8.")
            }
        }

        impl rustsat::solvers::sat::SolveIncremental for $slvty {}

        impl rustsat::solvers::sat::Init for $statety<crate::Init> {
            type Config = ();

            type Option = ();

            fn set_option(&mut self, option: Self::Option) -> &mut Self {
                todo!()
            }
        }

        impl Default for $statety<crate::Init> {
            fn default() -> Self {
                let handle = unsafe { crate::ffi::$init() };
                assert!(
                    !handle.is_null(),
                    "not enough memory to initialize glucose solver"
                );
                Self {
                    handle: handle.into(),
                    _state: crate::Init(),
                }
            }
        }

        impl From<()> for $statety<crate::Init> {
            fn from(_: ()) -> Self {
                Self::default()
            }
        }

        impl rustsat::solvers::sat::Input<$slvty> for $statety<crate::Input> {
            type Option = ();

            fn reserve(&mut self, max_var: Var) -> rustsat::MightMemout<&Self> {
                crate::handle_oom_new!(unsafe {
                    #[allow(clippy::cast_possible_wrap)]
                    ffi::$reserve(self.handle.0, max_var.idx32() as c_int)
                });
                Ok(self)
            }

            fn add_clause<C>(&mut self, clause: &C) -> rustsat::MightMemout<&Self>
            where
                C: AsRef<rustsat::types::Cl> + ?Sized,
            {
                let clause = clause.as_ref();
                // Update wrapper-internal state
                crate::handle_oom_new!(unsafe {
                    crate::ffi::$add(
                        self.handle.0,
                        AsRef::<[Lit]>::as_ref(clause).as_ptr().cast(),
                        clause.len(),
                    )
                });
                Ok(self)
            }

            fn solve(self) -> rustsat::MightMemout<rustsat::solvers::sat::SolveResult<$slvty>> {
                let res = crate::handle_oom_new!(unsafe {
                    crate::ffi::$solve(self.handle.0, std::ptr::null(), 0)
                });
                Ok(match res {
                    0 => rustsat::solvers::sat::SolveResult::Unknown($statety {
                        handle: self.handle,
                        _state: crate::Unknown(),
                    }),
                    10 => rustsat::solvers::sat::SolveResult::Sat($statety {
                        handle: self.handle,
                        _state: crate::Sat(),
                    }),
                    20 => rustsat::solvers::sat::SolveResult::Unsat($statety {
                        handle: self.handle,
                        _state: crate::Unsat(),
                    }),
                    value => {
                        unreachable!("{} call should never return {value}", stringify!($solve))
                    }
                })
            }
        }

        impl rustsat::solvers::sat::SolveAssumptions<$slvty> for $statety<crate::Input> {
            fn solve_under_assumptions(
                self,
                assumptions: &[Lit],
            ) -> rustsat::MightMemout<rustsat::solvers::sat::SolveResult<$slvty>> {
                let res = crate::handle_oom_new!(unsafe {
                    crate::ffi::$solve(
                        self.handle.0,
                        assumptions.as_ptr().cast(),
                        assumptions.len(),
                    )
                });
                Ok(match res {
                    0 => rustsat::solvers::sat::SolveResult::Unknown($statety {
                        handle: self.handle,
                        _state: crate::Unknown(),
                    }),
                    10 => rustsat::solvers::sat::SolveResult::Sat($statety {
                        handle: self.handle,
                        _state: crate::Sat(),
                    }),
                    20 => rustsat::solvers::sat::SolveResult::Unsat($statety {
                        handle: self.handle,
                        _state: crate::Unsat(),
                    }),
                    value => {
                        unreachable!("{} call should never return {value}", stringify!($solve))
                    }
                })
            }
        }

        impl From<$statety<crate::Init>> for $statety<crate::Input> {
            fn from(value: $statety<crate::Init>) -> Self {
                Self {
                    handle: value.handle,
                    _state: crate::Input(),
                }
            }
        }

        impl From<$statety<crate::Sat>> for $statety<crate::Input> {
            fn from(value: $statety<crate::Sat>) -> Self {
                Self {
                    handle: value.handle,
                    _state: crate::Input(),
                }
            }
        }

        impl From<$statety<crate::Unsat>> for $statety<crate::Input> {
            fn from(value: $statety<crate::Unsat>) -> Self {
                Self {
                    handle: value.handle,
                    _state: crate::Input(),
                }
            }
        }

        impl From<$statety<crate::Unknown>> for $statety<crate::Input> {
            fn from(value: $statety<crate::Unknown>) -> Self {
                Self {
                    handle: value.handle,
                    _state: crate::Input(),
                }
            }
        }

        impl Default for $statety<crate::Input> {
            fn default() -> Self {
                let handle = unsafe { crate::ffi::$init() };
                assert!(
                    !handle.is_null(),
                    "not enough memory to initialize glucose solver"
                );
                Self {
                    handle: handle.into(),
                    _state: crate::Input(),
                }
            }
        }

        impl FromIterator<Clause> for $statety<crate::Input> {
            fn from_iter<T: IntoIterator<Item = Clause>>(iter: T) -> Self {
                use rustsat::solvers::sat::Input;
                let mut slf = Self::default();
                for clause in iter {
                    slf.move_clause(clause).expect("out of memory");
                }
                slf
            }
        }

        impl<'a> FromIterator<&'a Cl> for $statety<crate::Input> {
            fn from_iter<T: IntoIterator<Item = &'a Cl>>(iter: T) -> Self {
                use rustsat::solvers::sat::Input;
                let mut slf = Self::default();
                for clause in iter {
                    slf.add_clause(clause).expect("out of memory");
                }
                slf
            }
        }

        impl TryFrom<rustsat::instances::Cnf> for $statety<crate::Input> {
            type Error = rustsat::OutOfMemory;

            fn try_from(value: rustsat::instances::Cnf) -> Result<Self, Self::Error> {
                use rustsat::solvers::sat::Input;
                let mut slf = Self::default();
                for clause in value {
                    slf.move_clause(clause)?;
                }
                Ok(slf)
            }
        }

        impl Extend<Clause> for $statety<crate::Input> {
            fn extend<T: IntoIterator<Item = Clause>>(&mut self, iter: T) {
                use rustsat::solvers::sat::Input;
                for clause in iter {
                    self.move_clause(clause).expect("out of memory");
                }
            }
        }

        impl<'a> Extend<&'a Cl> for $statety<crate::Input> {
            fn extend<T: IntoIterator<Item = &'a Cl>>(&mut self, iter: T) {
                use rustsat::solvers::sat::Input;
                for clause in iter {
                    self.add_clause(clause).expect("out of memory");
                }
            }
        }

        impl rustsat::solvers::sat::Sat for $statety<crate::Sat> {
            fn variable_value(&self, var: Var) -> TernaryVal {
                match unsafe { crate::ffi::$val(self.handle.0, var.pos_lit().into()) } {
                    crate::ffi::T_UNASSIGNED => TernaryVal::DontCare,
                    crate::ffi::T_TRUE => TernaryVal::True,
                    crate::ffi::T_FALSE => TernaryVal::False,
                    value => unreachable!("{} should never return {value}", stringify!($val)),
                }
            }
        }

        impl rustsat::solvers::sat::UnsatIncremental for $statety<crate::Unsat> {
            fn core(&mut self) -> &[Lit] {
                let conflict = unsafe {
                    let mut conflict = std::ptr::null::<crate::ffi::c_Lit>();
                    let mut conflict_len = 0;
                    crate::ffi::$conflict(self.handle.0, &mut conflict, &mut conflict_len);
                    rustsat::utils::from_raw_parts_maybe_null(conflict.cast(), conflict_len)
                };
                conflict
            }

            fn failed(&mut self, assumption: Lit) -> bool {
                for lit in self.core() {
                    if !assumption == *lit {
                        return true;
                    }
                }
                false
            }
        }
    };
}
pub(crate) use impl_api;

pub(crate) mod ffi {
    #![allow(non_upper_case_globals)]
    #![allow(non_camel_case_types)]
    #![allow(non_snake_case)]

    use std::os::raw::c_void;

    use rustsat::types::Lit;

    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

    impl From<Lit> for c_Lit {
        fn from(value: Lit) -> Self {
            unsafe { std::mem::transmute::<Lit, c_Lit>(value) }
        }
    }

    pub extern "C" fn rustsat_glucose_collect_lits(vec: *mut c_void, lit: c_Lit) {
        let vec = vec.cast::<Vec<Lit>>();
        unsafe { (*vec).push(std::mem::transmute::<c_Lit, Lit>(lit)) };
    }
}
