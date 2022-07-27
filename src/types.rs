//! # Common Types for SAT Solving
//!
//! Common types used throughout the library to guarantee type safety.

use core::ops::Not;
use std::fmt;

use crate::{instances::DimacsError, solvers::SolverState};

#[cfg(feature = "ipasir")]
use crate::solvers::ipasir::IpasirError;
#[cfg(feature = "ipasir")]
use std::os::raw::c_int;

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
    /// let lit = Lit::positive(5);
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
    /// let lit = Lit::negative(5);
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
    fn new(idx: usize, negated: bool) -> Lit {
        let var = Var::new(idx);
        Lit { v: var, negated }
    }

    /// Creates a new positive literal with a given index.
    pub fn positive(idx: usize) -> Lit {
        Lit::new(idx, false)
    }

    /// Creates a new negated literal with a given index.
    pub fn negative(idx: usize) -> Lit {
        Lit::new(idx, true)
    }

    #[cfg(feature = "ipasir")]
    /// Create a literal from an IPASIR integer value
    pub fn from_ipasir(val: i32) -> Result<Lit, IpasirError> {
        if val == 0 {
            return Err(IpasirError::ZeroLiteral);
        }
        let negated = if val > 0 { false } else { true };
        let idx: usize = if val > 0 {
            val.try_into().unwrap()
        } else {
            (-val).try_into().unwrap()
        };
        Ok(Lit::new(idx, negated))
    }

    /// Gets the variables that the literal corresponds to.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustsat::types::{Var,Lit};
    ///
    /// let var = Var::new(5);
    /// let lit = Lit::negative(5);
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

    #[cfg(feature = "ipasir")]
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

#[macro_export]
macro_rules! lit {
    ($l:expr) => {
        Lit::positive($l)
    };
}

#[macro_export]
macro_rules! ipasir_lit {
    ($l:expr) => {
        Lit::from_ipasir($l).unwrap()
    };
}

/// Type representing a clause
/// Wrapper around a std collection to allow for changing the data structure.
/// Optional clauses as sets will be included in the future.
#[derive(Hash, Eq, PartialEq, Clone)]
pub struct Clause {
    lits: Vec<Lit>,
}

impl Clause {
    /// Creates a new empty clause
    pub fn new() -> Clause {
        Clause { lits: Vec::new() }
    }

    /// Create a new clause from an iterator
    pub fn from<I>(lits: I) -> Clause
    where
        I: Iterator<Item = Lit>,
    {
        Clause {
            lits: lits.collect(),
        }
    }

    /// Gets the length of the clause
    pub fn len(&self) -> usize {
        self.lits.len()
    }

    /// Adds a literal to the clause
    pub fn add(&mut self, lit: Lit) {
        self.lits.push(lit)
    }

    /// Removes the first occurrence of a literal from the clause
    /// Returns true if an occurrence was found
    pub fn remove(&mut self, lit: &Lit) -> bool {
        for (i, l) in self.lits.iter().enumerate() {
            if l == lit {
                self.lits.swap_remove(i);
                return true;
            }
        }
        false
    }

    /// Removes all occurrences of a literal from the clause
    pub fn remove_thorough(&mut self, lit: &Lit) -> bool {
        let mut idxs = Vec::new();
        for (i, l) in self.lits.iter().enumerate() {
            if l == lit {
                idxs.push(i);
            }
        }
        for i in idxs.iter().rev() {
            self.lits.remove(*i);
        }
        !idxs.is_empty()
    }

    /// Gets an iterator over the clause
    pub fn iter(&self) -> std::slice::Iter<'_, Lit> {
        self.lits.iter()
    }
}

impl<'a> IntoIterator for &'a Clause {
    type Item = Lit;

    type IntoIter = std::iter::Copied<std::slice::Iter<'a, Self::Item>>;

    fn into_iter(self) -> Self::IntoIter {
        self.lits.iter().copied()
    }
}

/// Clauses can be printed with the [`Display`](std::fmt::Display) trait
impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for (i, lit) in self.iter().enumerate() {
            if i != 0 {
                write!(f, "|")?;
            }
            write!(f, "{}", lit)?
        }
        write!(f, ")")
    }
}

/// Clauses can be printed with the [`Debug`](std::fmt::Debug) trait
impl fmt::Debug for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for (i, lit) in self.iter().enumerate() {
            if i != 0 {
                write!(f, "|")?;
            }
            write!(f, "{}", lit)?
        }
        write!(f, ")")
    }
}

#[macro_export]
macro_rules! clause {
    ( $($l:expr),* ) => {
        {
            let mut tmp_clause = Clause::new();
            $(
                tmp_clause.add($l);
            )*
            tmp_clause
        }
    };
}

/// Ternary value assigned to a literal or variable, including possible "don't care"
#[derive(Clone, Copy, PartialEq)]
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

/// Ternary values can be printed with the [`Display`](std::fmt::Display) trait
impl fmt::Display for TernaryVal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TernaryVal::True => write!(f, "1"),
            TernaryVal::False => write!(f, "0"),
            TernaryVal::DontCare => write!(f, "_"),
        }
    }
}

/// Ternary values can be printed with the [`Debug`](std::fmt::Debug) trait
impl fmt::Debug for TernaryVal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TernaryVal::True => write!(f, "1"),
            TernaryVal::False => write!(f, "0"),
            TernaryVal::DontCare => write!(f, "_"),
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

    pub fn replace_dont_care(&mut self, def: bool) {
        self.assignment.iter_mut().for_each(|tv| match tv {
            TernaryVal::DontCare => {
                if def {
                    *tv = TernaryVal::True;
                } else {
                    *tv = TernaryVal::False;
                }
            }
            _ => (),
        })
    }
}

impl fmt::Debug for Solution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.assignment.iter().fold(Ok(()), |result, tv| {
            result.and_then(|_| write!(f, "{}", tv))
        })
    }
}

impl fmt::Display for Solution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.assignment.iter().fold(Ok(()), |result, tv| {
            result.and_then(|_| write!(f, "{}", tv))
        })
    }
}

/// General error type for the entire library.
/// Variants represent more detailed errors.
#[derive(Debug)]
pub enum Error {
    #[cfg(feature = "ipasir")]
    /// Errors from the IPASIR interface.
    Ipasir(IpasirError),
    /// Errors in a SAT solver stemming from the solver being in an invalid
    /// state for an operation.
    /// The first [`SolverState`] member holds the state that the solver is in,
    /// the second the required state.
    State(SolverState, SolverState),
    /// Errors when reading files
    IO(std::io::Error),
    /// Errors when parsing DIMACS
    Dimacs(DimacsError),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            #[cfg(feature = "ipasir")]
            Error::Ipasir(err) => write!(f, "Error in IPASIR API: {}", err),
            Error::State(true_state, required_state) => write!(
                f,
                "Solver needs to be in state {} but was in {}",
                required_state, true_state
            ),
            Error::IO(err) => write!(f, "File IO error: {}", err),
            Error::Dimacs(err) => write!(f, "Error parsing DIMACS: {}", err),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Lit, Solution, TernaryVal, Var};

    #[test]
    fn var_index() {
        let idx = 5;
        let var = Var::new(idx);
        assert_eq!(var.index(), idx);
    }

    #[test]
    fn var_pos_lit() {
        let idx = 5;
        let var = Var::new(idx);
        let lit = Lit::positive(idx);
        assert_eq!(var.pos_lit(), lit);
    }

    #[test]
    fn var_neg_lit() {
        let idx = 5;
        let var = Var::new(idx);
        let lit = Lit::negative(idx);
        assert_eq!(var.neg_lit(), lit);
    }

    #[test]
    fn var_from_lit() {
        let idx = 0;
        let lit = Lit::positive(idx);
        let var = Var::new(idx);
        assert_eq!(*lit.var(), var);
    }

    #[test]
    fn lit_is_pos() {
        let lit = Lit::positive(0);
        assert!(lit.is_pos());
        assert!(!lit.is_neg());
    }

    #[test]
    fn lit_is_neg() {
        let lit = Lit::negative(0);
        assert!(!lit.is_pos());
        assert!(lit.is_neg());
    }

    #[test]
    fn lit_negation() {
        let lit1 = Lit::positive(0);
        let lit2 = !lit1;
        assert!(!lit2.is_pos());
        assert!(lit2.is_neg());
        assert_eq!(lit1.var(), lit2.var());
    }

    #[test]
    fn ipasir_lit_not_zero() {
        let lit = Lit::positive(0);
        assert_ne!(lit.to_ipasir(), 0);
        let lit = !lit;
        assert_ne!(lit.to_ipasir(), 0);
    }

    #[test]
    fn ipasir_lit_idx_plus_one() {
        let idx = 5;
        let lit = Lit::positive(idx);
        assert_eq!(lit.to_ipasir(), idx as i32 + 1);
        let lit = !lit;
        assert_eq!(lit.to_ipasir(), -(idx as i32 + 1));
    }

    #[test]
    fn ternary_var_true() {
        let tv = TernaryVal::True;
        assert_eq!(tv.clone().to_bool_with_def(true), true);
        assert_eq!(tv.to_bool_with_def(false), true);
    }

    #[test]
    fn ternary_var_false() {
        let tv = TernaryVal::False;
        assert_eq!(tv.clone().to_bool_with_def(true), false);
        assert_eq!(tv.to_bool_with_def(false), false);
    }

    #[test]
    fn ternary_var_dnc() {
        let tv = TernaryVal::DontCare;
        assert_eq!(tv.clone().to_bool_with_def(true), true);
        assert_eq!(tv.to_bool_with_def(false), false);
    }

    #[test]
    fn sol_var_val() {
        let sol = Solution::from_vec(vec![
            TernaryVal::True,
            TernaryVal::False,
            TernaryVal::DontCare,
        ]);
        let val = *sol.var_value(&Var::new(0)).unwrap();
        assert_eq!(val, TernaryVal::True);
        let val = *sol.var_value(&Var::new(1)).unwrap();
        assert_eq!(val, TernaryVal::False);
        let val = *sol.var_value(&Var::new(2)).unwrap();
        assert_eq!(val, TernaryVal::DontCare);
    }

    #[test]
    fn sol_lit_val() {
        let sol = Solution::from_vec(vec![
            TernaryVal::True,
            TernaryVal::False,
            TernaryVal::DontCare,
        ]);
        let val = *sol.lit_value(&Lit::negative(0)).unwrap();
        assert_eq!(val, TernaryVal::False);
        let val = *sol.lit_value(&Lit::positive(0)).unwrap();
        assert_eq!(val, TernaryVal::True);
        let val = *sol.lit_value(&Lit::negative(1)).unwrap();
        assert_eq!(val, TernaryVal::True);
        let val = *sol.lit_value(&Lit::positive(1)).unwrap();
        assert_eq!(val, TernaryVal::False);
        let val = *sol.lit_value(&Lit::negative(2)).unwrap();
        assert_eq!(val, TernaryVal::DontCare);
        let val = *sol.lit_value(&Lit::positive(2)).unwrap();
        assert_eq!(val, TernaryVal::DontCare);
    }

    #[test]
    fn sol_repl_dont_care() {
        let mut sol = Solution::from_vec(vec![
            TernaryVal::True,
            TernaryVal::False,
            TernaryVal::DontCare,
        ]);
        sol.replace_dont_care(true);
        let val = *sol.var_value(&Var::new(0)).unwrap();
        assert_eq!(val, TernaryVal::True);
        let val = *sol.var_value(&Var::new(1)).unwrap();
        assert_eq!(val, TernaryVal::False);
        let val = *sol.var_value(&Var::new(2)).unwrap();
        assert_eq!(val, TernaryVal::True);
    }
}
