//! # Common Types for SAT Solving
//!
//! Common types used throughout the library to guarantee type safety.

use core::ops::Not;
use std::fmt;
use std::os::raw::c_int;

use crate::solvers::{ipasir::IpasirError, SolverState};

/// Type representing boolean variables in a SAT problem.
#[derive(Hash, Eq, PartialEq, PartialOrd, Clone, Copy)]
pub struct Var {
    idx: usize,
}

impl Var {
    /// Creates a new variables with a given index.
    /// Indices start from 0.
    pub fn new(idx: usize) -> Var {
        Var { idx }
    }

    /// Creates a literal that is not negated.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustsat::types::{Var,Lit};
    ///
    /// let var = Var::new(5);
    /// let lit = Lit::new(5, false);
    ///
    /// assert_eq!(lit, var.pos_lit());
    /// ```
    pub fn pos_lit(self) -> Lit {
        Lit {
            v: self,
            negated: false,
        }
    }

    /// Creates a negated literal.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustsat::types::{Var,Lit};
    ///
    /// let var = Var::new(5);
    /// let lit = Lit::new(5, true);
    ///
    /// assert_eq!(lit, var.neg_lit());
    /// ```
    pub fn neg_lit(self) -> Lit {
        Lit {
            v: self,
            negated: true,
        }
    }

    /// Returns the index of the variable.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustsat::types::Var;
    ///
    /// let var = Var::new(5);
    ///
    /// assert_eq!(5, var.index());
    /// ```
    pub fn index(&self) -> usize {
        self.idx
    }
}

/// Variables can be printed with the [`Display`](std::fmt::Display) trait
impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "x{}", self.idx)
    }
}

/// Variables can be printed with the [`Debug`](std::fmt::Debug) trait
impl fmt::Debug for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

/// Type representing literals, possibly negated boolean variables.
#[derive(Hash, Eq, PartialEq, Clone, Copy)]
pub struct Lit {
    v: Var,
    negated: bool,
}

impl Lit {
    /// Creates a new (negated or not) literal with a given index.
    pub fn new(idx: usize, negated: bool) -> Lit {
        let var = Var::new(idx);
        Lit { v: var, negated }
    }

    /// Gets the variables that the literal corresponds to.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustsat::types::{Var,Lit};
    ///
    /// let var = Var::new(5);
    /// let lit = Lit::new(5, true);
    ///
    /// assert_eq!(var, *lit.var());
    /// ```
    pub fn var(&self) -> &Var {
        &self.v
    }

    /// True if the literal is positive.
    pub fn is_pos(&self) -> bool {
        !self.negated
    }

    /// True if the literal is negated.
    pub fn is_neg(&self) -> bool {
        self.negated
    }

    /// Converts the literal to an integer as accepted by the IPASIR API.
    /// The IPASIR literal will have idx+1 and be negative if the literal is
    /// negated.
    pub fn to_ipasir(self) -> c_int {
        let idx: i32 = (self.v.idx + 1)
            .try_into()
            .expect("Variable index too high to fit in int32_t");
        if self.negated {
            -idx
        } else {
            idx
        }
    }
}

/// Trait implementation allowing for negating literals with the `!` operator.
impl Not for Lit {
    type Output = Lit;

    fn not(self) -> Lit {
        Lit {
            v: self.v,
            negated: !self.negated,
        }
    }
}

/// Literals can be printed with the [`Display`](std::fmt::Display) trait
impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.negated {
            true => write!(f, "~{}", self.v),
            false => write!(f, "{}", self.v),
        }
    }
}

/// Literals can be printed with the [`Debug`](std::fmt::Debug) trait
impl fmt::Debug for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

/// Ternary value assigned to a literal or variable, including possible "don't care"
pub enum TernaryVal {
    /// Positive assignment.
    True,
    /// Negative assignment.
    False,
    /// Formula is satisfied, no matter the assignment.
    DontCare,
}

impl TernaryVal {
    /// Converts a [`TernaryVal`] to a bool with a default value for "don't cares"
    pub fn to_bool_with_def(self, def: bool) -> bool {
        match self {
            TernaryVal::True => true,
            TernaryVal::False => false,
            TernaryVal::DontCare => def,
        }
    }
}

/// Type representing a solution to a formula.
pub struct Solution {
    assignment: Vec<TernaryVal>,
}

impl Solution {
    /// Create a solution from a vector of `LitVal`s where every entry represents
    /// the assignment for the variable with the index of the entry.
    pub fn from_vec(assignment: Vec<TernaryVal>) -> Solution {
        Solution { assignment }
    }

    /// Get the value that the solution assigns to a variable.
    /// If the variable is not included in the solution, will return `None`.
    /// (Note that this is different from an explicit "don't care" for the variable.)
    pub fn var_value(&self, var: &Var) -> Option<&TernaryVal> {
        if var.idx >= self.assignment.len() {
            None
        } else {
            Some(&self.assignment[var.idx])
        }
    }

    /// Same as [`Solution::var_value`], but for literals.
    pub fn lit_value(&self, lit: &Lit) -> Option<&TernaryVal> {
        if lit.negated {
            match self.var_value(lit.var())? {
                TernaryVal::DontCare => Some(&TernaryVal::DontCare),
                TernaryVal::True => Some(&TernaryVal::False),
                TernaryVal::False => Some(&TernaryVal::True),
            }
        } else {
            self.var_value(lit.var())
        }
    }
}

/// General error type for the entire library.
/// Variants represent more detailed errors.
pub enum Error {
    /// Errors from the IPASIR interface.
    Ipasir(IpasirError),
    /// Errors in a SAT solver stemming from the solver being in an invalid
    /// state for an operation.
    /// The first [`SolverState`] member holds the state that the solver is in,
    /// the second the required state.
    StateError(SolverState, SolverState),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Ipasir(err) => write!(f, "Error in IPASIR API: {}", err),
            Error::StateError(true_state, required_state) => write!(
                f,
                "Solver needs to be in state {} but was in {}",
                required_state, true_state
            ),
        }
    }
}
