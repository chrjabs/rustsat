//! # Common Types for SAT Solving
//!
//! Common types used throughout the library to guarantee type safety.

use core::ffi::c_int;
use std::{fmt, ops};

use thiserror::Error;

#[cfg(feature = "pyapi")]
use pyo3::{exceptions::PyValueError, prelude::*};

pub mod constraints;
pub use constraints::Clause;

/// The hash map to use throughout the library
#[cfg(feature = "fxhash")]
pub type RsHashMap<K, V> = rustc_hash::FxHashMap<K, V>;
#[cfg(not(feature = "fxhash"))]
pub type RsHashMap<K, V> = std::collections::HashMap<K, V>;

/// The hash set to use throughout the library
#[cfg(feature = "fxhash")]
pub type RsHashSet<V> = rustc_hash::FxHashSet<V>;
#[cfg(not(feature = "fxhash"))]
pub type RsHashSet<V> = std::collections::HashSet<V>;

/// The hasher to use throught the library
#[cfg(feature = "fxhash")]
pub type RsHasher = rustc_hash::FxHasher;
#[cfg(not(feature = "fxhash"))]
pub type RsHasher = std::collections::hash_map::DefaultHasher;

/// Type representing boolean variables in a SAT problem. Variables indexing in
/// RustSAT starts from 0 and the maximum index is `(u32::MAX - 1) / 2`. This is
/// because literals are represented as a single `u32` as well. The memory
/// representation of variables is `u32`.
#[derive(Hash, Eq, PartialEq, PartialOrd, Clone, Copy, Ord, Debug)]
#[repr(transparent)]
pub struct Var {
    idx: u32,
}

impl Var {
    /// The maximum index that can be represented.
    pub const MAX_IDX: u32 = (u32::MAX - 1) / 2;

    /// Creates a new variables with a given index.
    /// Indices start from 0.
    /// Panics if `idx > Var::MAX_IDX`.
    pub fn new(idx: u32) -> Var {
        if idx > Var::MAX_IDX {
            panic!("variable index too high")
        }
        Var { idx }
    }

    /// Creates a new variables with a given index.
    /// Indices start from 0.
    /// Returns `Err(TypeError::IdxTooHigh(idx, Var::MAX_IDX)` if
    /// `idx > Var::MAX_IDX`.
    pub fn new_with_error(idx: u32) -> Result<Var, TypeError> {
        if idx > Var::MAX_IDX {
            return Err(TypeError::IdxTooHigh(idx, Var::MAX_IDX));
        }
        Ok(Var { idx })
    }

    /// Creates a new variables with a given index.
    /// Indices start from 0.
    /// Does not perform any check on the index, therefore might produce an inconsistent variable.
    /// Only use this for performance reasons if you are sure that `idx <= Var::MAX_IDX`.
    #[inline]
    pub fn new_unchecked(idx: u32) -> Var {
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
    #[inline]
    pub fn pos_lit(self) -> Lit {
        Lit::positive_unchecked(self.idx)
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
    #[inline]
    pub fn neg_lit(self) -> Lit {
        Lit::negative_unchecked(self.idx)
    }

    /// Returns the index of the variable. This is a `usize` to enable easier
    /// indexing of data structures like vectors, even though the internal
    /// representation of a variable is `u32`. For the 32 bit index use
    /// [`Var::idx32`].
    ///
    /// # Examples
    ///
    /// ```
    /// use rustsat::types::Var;
    ///
    /// let var = Var::new(5);
    ///
    /// assert_eq!(5, var.idx());
    /// ```
    #[inline]
    pub fn idx(&self) -> usize {
        self.idx as usize
    }

    /// Returns the 32 bit index of the variable.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustsat::types::Var;
    ///
    /// let var = Var::new(5);
    ///
    /// assert_eq!(5, var.idx32());
    /// ```
    #[inline]
    pub fn idx32(&self) -> u32 {
        self.idx
    }

    /// Converts the variable to an integer as accepted by the IPASIR API and
    /// similar. The IPASIR variable will have idx+1. Panics if the literal does not fit into a `c_int`.
    pub fn to_ipasir(self) -> c_int {
        (self.idx() + 1)
            .try_into()
            .expect("variable index too high to fit in c_int")
    }
}

/// Incrementing variables
impl ops::Add<u32> for Var {
    type Output = Var;

    fn add(self, rhs: u32) -> Self::Output {
        Var {
            idx: self.idx + rhs,
        }
    }
}

impl ops::AddAssign<u32> for Var {
    fn add_assign(&mut self, rhs: u32) {
        self.idx += rhs
    }
}

/// Decrementing variables
impl ops::Sub<u32> for Var {
    type Output = Var;

    fn sub(self, rhs: u32) -> Self::Output {
        Var {
            idx: self.idx - rhs,
        }
    }
}

impl ops::SubAssign<u32> for Var {
    fn sub_assign(&mut self, rhs: u32) {
        self.idx -= rhs
    }
}

/// Variables can be printed with the [`Display`](std::fmt::Display) trait
impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "x{}", self.idx)
    }
}

/// More easily creates variables. Mainly used in tests.
///
/// # Examples
///
/// ```
/// use rustsat::{var, types::Var};
///
/// assert_eq!(var![42], Var::new(42));
/// ```
#[macro_export]
macro_rules! var {
    ($v:expr) => {
        $crate::types::Var::new($v)
    };
}

/// Type representing literals, possibly negated boolean variables.
#[cfg_attr(feature = "pyapi", pyclass)]
#[derive(Hash, Eq, PartialEq, PartialOrd, Ord, Clone, Copy, Debug)]
#[repr(transparent)]
pub struct Lit {
    /// Literal representation is `idx << 1` with the last bit representing
    /// whether the literal is negated or not. This way the literal can directly
    /// be used to index data structures with the two literals of a variable
    /// being close together.
    lidx: u32,
}

impl Lit {
    /// Represents a literal in memory
    #[inline]
    fn represent(idx: u32, negated: bool) -> u32 {
        (idx << 1) + (negated as u32)
    }

    /// Creates a new (negated or not) literal with a given index.
    /// Panics if `idx > Var::MAX_IDX`.
    pub fn new(idx: u32, negated: bool) -> Lit {
        if idx > Var::MAX_IDX {
            panic!("variable index too high")
        }
        Lit {
            lidx: Lit::represent(idx, negated),
        }
    }

    /// Creates a new (negated or not) literal with a given index.
    /// Returns `Err(TypeError::IdxTooHigh(idx, Var::MAX_IDX)` if
    /// `idx > Var::MAX_IDX`.
    pub fn new_with_error(idx: u32, negated: bool) -> Result<Lit, TypeError> {
        if idx > Var::MAX_IDX {
            return Err(TypeError::IdxTooHigh(idx, Var::MAX_IDX));
        }
        Ok(Lit {
            lidx: Lit::represent(idx, negated),
        })
    }

    /// Creates a new (negated or not) literal with a given index.
    /// Does not perform any check on the index, therefore might produce an inconsistent variable.
    /// Only use this for performance reasons if you are sure that `idx <= Var::MAX_IDX`.
    pub fn new_unchecked(idx: u32, negated: bool) -> Lit {
        Lit {
            lidx: Lit::represent(idx, negated),
        }
    }

    /// Creates a new positive literal with a given index.
    /// Panics if `idx > Var::MAX_IDX`.
    #[inline]
    pub fn positive(idx: u32) -> Lit {
        Lit::new(idx, false)
    }

    /// Creates a new negated literal with a given index.
    /// Panics if `idx > Var::MAX_IDX`.
    #[inline]
    pub fn negative(idx: u32) -> Lit {
        Lit::new(idx, true)
    }

    /// Creates a new positive literal with a given index.
    /// Panics if `idx > Var::MAX_IDX`.
    #[inline]
    pub fn positive_with_error(idx: u32) -> Result<Lit, TypeError> {
        Lit::new_with_error(idx, false)
    }

    /// Creates a new negated literal with a given index.
    /// Panics if `idx > Var::MAX_IDX`.
    #[inline]
    pub fn negative_with_error(idx: u32) -> Result<Lit, TypeError> {
        Lit::new_with_error(idx, true)
    }

    /// Creates a new positive literal with a given index.
    /// Does not perform any check on the index, therefore might produce an inconsistent variable.
    /// Only use this for performance reasons if you are sure that `idx <= Var::MAX_IDX`.
    #[inline]
    pub fn positive_unchecked(idx: u32) -> Lit {
        Lit::new_unchecked(idx, false)
    }

    /// Creates a new negated literal with a given index.
    /// Does not perform any check on the index, therefore might produce an inconsistent variable.
    /// Only use this for performance reasons if you are sure that `idx <= Var::MAX_IDX`.
    #[inline]
    pub fn negative_unchecked(idx: u32) -> Lit {
        Lit::new_unchecked(idx, true)
    }

    /// Create a literal from an IPASIR integer value. Returns an error if
    /// the value is zero or the index too high.
    pub fn from_ipasir(val: c_int) -> Result<Lit, TypeError> {
        if val == 0 {
            return Err(TypeError::IpasirZero);
        }
        let negated = val < 0;
        let idx = val.unsigned_abs();
        Lit::new_with_error(idx - 1, negated)
    }

    /// Gets the variable index of the literal
    #[inline]
    pub fn vidx(&self) -> usize {
        (self.lidx >> 1) as usize
    }

    /// Gets the 32bit variable index of the literal
    #[inline]
    pub fn vidx32(&self) -> u32 {
        self.lidx >> 1
    }

    /// Gets a literal representation for indexing data structures
    #[inline]
    pub fn lidx(&self) -> usize {
        self.lidx as usize
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
    /// assert_eq!(var, lit.var());
    /// ```
    #[inline]
    pub fn var(&self) -> Var {
        Var::new_unchecked(self.vidx32())
    }

    /// True if the literal is positive.
    #[inline]
    pub fn is_pos(&self) -> bool {
        (self.lidx & 1u32) == 0
    }

    /// True if the literal is negated.
    #[inline]
    pub fn is_neg(&self) -> bool {
        (self.lidx & 1u32) == 1
    }

    /// Converts the literal to an integer as accepted by the IPASIR API and
    /// similar. The IPASIR literal will have idx+1 and be negative if the
    /// literal is negated. Panics if the literal does not fit into a `c_int`.
    pub fn to_ipasir(self) -> c_int {
        let negated = self.is_neg();
        let idx: c_int = (self.vidx() + 1)
            .try_into()
            .expect("variable index too high to fit in c_int");
        if negated {
            -idx
        } else {
            idx
        }
    }

    /// Converts the literal to an integer as accepted by the IPASIR API and
    /// similar. The IPASIR literal will have idx+1 and be negative if the
    /// literal is negated. Returns `Err(TypeError::IdxTooHigh(_, _))` if the
    /// literal does not fit into a `c_int`.
    pub fn to_ipasir_with_error(self) -> Result<c_int, TypeError> {
        let negated = self.is_neg();
        let idx: c_int = match (self.vidx() + 1).try_into() {
            Ok(idx) => idx,
            Err(_) => return Err(TypeError::IdxTooHigh(self.vidx32() + 1, c_int::MAX as u32)),
        };
        Ok(if negated { -idx } else { idx })
    }
}

/// Trait implementation allowing for negating literals with the `!` operator.
impl ops::Not for Lit {
    type Output = Lit;

    #[inline]
    fn not(self) -> Lit {
        Lit {
            lidx: self.lidx ^ 1u32,
        }
    }
}

/// Trait implementation allowing for negating literals with the unary `-` operator.
impl ops::Neg for Lit {
    type Output = Lit;

    #[inline]
    fn neg(self) -> Lit {
        Lit {
            lidx: self.lidx ^ 1u32,
        }
    }
}

/// Incrementing literals. This preserves the sign of the literal.
impl ops::Add<u32> for Lit {
    type Output = Lit;

    fn add(self, rhs: u32) -> Self::Output {
        Lit {
            lidx: self.lidx + 2 * rhs,
        }
    }
}

/// Decrementing literals. This preserves the sign of the literal.
impl ops::Sub<u32> for Lit {
    type Output = Lit;

    fn sub(self, rhs: u32) -> Self::Output {
        Lit {
            lidx: self.lidx - 2 * rhs,
        }
    }
}

/// Literals can be printed with the [`Display`](std::fmt::Display) trait
impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.is_neg() {
            true => write!(f, "~x{}", self.vidx()),
            false => write!(f, "x{}", self.vidx()),
        }
    }
}

#[cfg(feature = "pyapi")]
#[pymethods]
impl Lit {
    #[new]
    fn pynew(ipasir: c_int) -> PyResult<Self> {
        Self::from_ipasir(ipasir).map_err(|_| PyValueError::new_err("invalid ipasir lit"))
    }

    fn __str__(&self) -> String {
        format!("{}", self)
    }

    fn __repr__(&self) -> String {
        format!("{}", self)
    }

    fn __neg__(&self) -> Lit {
        !*self
    }

    fn __richcmp__(&self, other: &Lit, op: pyo3::basic::CompareOp) -> bool {
        op.matches(self.cmp(&other))
    }

    fn __hash__(&self) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        self.hash(&mut hasher);
        hasher.finish()
    }

    /// Gets the IPASIR representation of the literal
    #[pyo3(name = "to_ipasir")]
    fn py_ipasir(&self) -> c_int {
        let negated = self.is_neg();
        let idx: c_int = (self.vidx() + 1)
            .try_into()
            .expect("variable index too high to fit in c_int");
        if negated {
            -idx
        } else {
            idx
        }
    }
}

/// More easily creates literals. Mainly used in tests.
///
/// # Examples
///
/// ```
/// use rustsat::{lit, types::Lit};
///
/// assert_eq!(lit![42], Lit::positive(42));
/// assert_eq!(!lit![42], Lit::negative(42));
/// ```
#[macro_export]
macro_rules! lit {
    ($l:expr) => {
        $crate::types::Lit::positive($l)
    };
}

/// More easily creates literals with IPASIR indexing (starts from 1) and
/// negation (negative value is negation). Mainly used in tests.
///
/// # Examples
///
/// ```
/// use rustsat::{lit, ipasir_lit, types::Lit};
///
/// assert_eq!(ipasir_lit![42], lit![41]);
/// assert_eq!(ipasir_lit![-42], !lit![41]);
/// ```
#[macro_export]
macro_rules! ipasir_lit {
    ($l:expr) => {
        $crate::types::Lit::from_ipasir($l).unwrap()
    };
}

/// Ternary value assigned to a literal or variable, including possible "don't care"
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
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

impl From<bool> for TernaryVal {
    fn from(value: bool) -> Self {
        if value {
            return TernaryVal::True;
        }
        TernaryVal::False
    }
}

/// Type representing an assignment of variables.
#[derive(Clone, PartialEq, Eq, Default)]
#[repr(transparent)]
pub struct Assignment {
    assignment: Vec<TernaryVal>,
}

impl Assignment {
    /// Get the value that the solution assigns to a variable.
    /// If the variable is not included in the solution, will return `TernaryVal::DontCare`.
    pub fn var_value(&self, var: Var) -> TernaryVal {
        if var.idx() >= self.assignment.len() {
            TernaryVal::DontCare
        } else {
            self.assignment[var.idx()]
        }
    }

    /// Same as [`Assignment::var_value`], but for literals.
    pub fn lit_value(&self, lit: Lit) -> TernaryVal {
        if lit.is_neg() {
            match self.var_value(lit.var()) {
                TernaryVal::DontCare => TernaryVal::DontCare,
                TernaryVal::True => TernaryVal::False,
                TernaryVal::False => TernaryVal::True,
            }
        } else {
            self.var_value(lit.var())
        }
    }

    pub fn replace_dont_care(&mut self, def: bool) {
        self.assignment.iter_mut().for_each(|tv| {
            if tv == &TernaryVal::DontCare {
                if def {
                    *tv = TernaryVal::True;
                } else {
                    *tv = TernaryVal::False;
                }
            }
        })
    }

    /// Assigns a variable in the assignment
    pub fn assign_var(&mut self, var: Var, val: TernaryVal) {
        if self.assignment.len() < var.idx() + 1 {
            self.assignment.resize(var.idx() + 1, TernaryVal::DontCare);
        }
        self.assignment[var.idx()] = val;
    }

    /// Assigns a literal to true
    pub fn assign_lit(&mut self, lit: Lit) {
        let val = if lit.is_pos() {
            TernaryVal::True
        } else {
            TernaryVal::False
        };
        self.assign_var(lit.var(), val)
    }

    /// Truncates a solution to only include assignments up to a maximum variable
    pub fn truncate(mut self, max_var: Var) -> Self {
        self.assignment.truncate(max_var.idx() + 1);
        self
    }

    /// Get the maximum variable in the assignment
    pub fn max_var(&self) -> Option<Var> {
        if self.assignment.is_empty() {
            None
        } else {
            Some(var![self.assignment.len() as u32 - 1])
        }
    }
}

impl fmt::Debug for Assignment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.assignment
            .iter()
            .try_for_each(|tv| write!(f, "{}", tv))
    }
}

impl fmt::Display for Assignment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.assignment
            .iter()
            .try_for_each(|tv| write!(f, "{}", tv))
    }
}

/// Turns the solution into an iterator over all true literals
impl IntoIterator for Assignment {
    type Item = Lit;

    type IntoIter = std::iter::FilterMap<
        std::iter::Enumerate<std::vec::IntoIter<TernaryVal>>,
        fn((usize, TernaryVal)) -> Option<Lit>,
    >;

    fn into_iter(self) -> Self::IntoIter {
        self.assignment
            .into_iter()
            .enumerate()
            .filter_map(|(idx, tv)| match tv {
                TernaryVal::True => Some(Var::new(idx.try_into().unwrap()).pos_lit()),
                TernaryVal::False => Some(Var::new(idx.try_into().unwrap()).neg_lit()),
                TernaryVal::DontCare => None,
            })
    }
}

impl FromIterator<Lit> for Assignment {
    fn from_iter<T: IntoIterator<Item = Lit>>(iter: T) -> Self {
        let mut assignment = Assignment::default();
        iter.into_iter().for_each(|l| assignment.assign_lit(l));
        assignment
    }
}

impl From<Vec<TernaryVal>> for Assignment {
    fn from(assignment: Vec<TernaryVal>) -> Self {
        Self { assignment }
    }
}

/// Errors related to types
#[derive(Error, Debug)]
pub enum TypeError {
    /// The requested index is too high.
    /// Contains the requested and the maximum index.
    #[error("index {0} is too high (maximum {1})")]
    IdxTooHigh(u32, u32),
    /// IPASIR index is zero
    #[error("zero is an invalid IPASIR literal")]
    IpasirZero,
}

/// An iterator over literals
pub trait LitIter: IntoIterator<Item = Lit> {}
impl<I: IntoIterator<Item = Lit>> LitIter for I {}
/// An iterator over clauses
pub trait ClsIter: IntoIterator<Item = Clause> {}
impl<I: IntoIterator<Item = Clause>> ClsIter for I {}

/// An iterator over weighted literals
pub trait WLitIter: IntoIterator<Item = (Lit, usize)> {}
impl<I: IntoIterator<Item = (Lit, usize)>> WLitIter for I {}
/// An iterator over weighted clauses
pub trait WClsIter: IntoIterator<Item = (Clause, usize)> {}
impl<I: IntoIterator<Item = (Clause, usize)>> WClsIter for I {}
/// An iterator over integer-weighted literals
pub trait IWLitIter: IntoIterator<Item = (Lit, isize)> {}
impl<I: IntoIterator<Item = (Lit, isize)>> IWLitIter for I {}

#[cfg(test)]
mod tests {
    use std::mem::size_of;

    use super::{Assignment, Lit, TernaryVal, Var};

    #[test]
    fn var_index() {
        let idx = 5;
        let var = Var::new(idx);
        assert_eq!(var.idx(), idx as usize);
    }

    #[test]
    fn var_index32() {
        let idx = 5;
        let var = Var::new(idx);
        assert_eq!(var.idx32(), idx);
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
        assert_eq!(lit.var(), var);
    }

    #[test]
    fn lit_representation() {
        let lidx = Lit::represent(5, true);
        assert_eq!(lidx, 0b1011);
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
        let sol = Assignment::from(vec![
            TernaryVal::True,
            TernaryVal::False,
            TernaryVal::DontCare,
        ]);
        let val = sol.var_value(Var::new(0));
        assert_eq!(val, TernaryVal::True);
        let val = sol.var_value(Var::new(1));
        assert_eq!(val, TernaryVal::False);
        let val = sol.var_value(Var::new(2));
        assert_eq!(val, TernaryVal::DontCare);
    }

    #[test]
    fn sol_lit_val() {
        let sol = Assignment::from(vec![
            TernaryVal::True,
            TernaryVal::False,
            TernaryVal::DontCare,
        ]);
        let val = sol.lit_value(Lit::negative(0));
        assert_eq!(val, TernaryVal::False);
        let val = sol.lit_value(Lit::positive(0));
        assert_eq!(val, TernaryVal::True);
        let val = sol.lit_value(Lit::negative(1));
        assert_eq!(val, TernaryVal::True);
        let val = sol.lit_value(Lit::positive(1));
        assert_eq!(val, TernaryVal::False);
        let val = sol.lit_value(Lit::negative(2));
        assert_eq!(val, TernaryVal::DontCare);
        let val = sol.lit_value(Lit::positive(2));
        assert_eq!(val, TernaryVal::DontCare);
    }

    #[test]
    fn sol_repl_dont_care() {
        let mut sol = Assignment::from(vec![
            TernaryVal::True,
            TernaryVal::False,
            TernaryVal::DontCare,
        ]);
        sol.replace_dont_care(true);
        let val = sol.var_value(Var::new(0));
        assert_eq!(val, TernaryVal::True);
        let val = sol.var_value(Var::new(1));
        assert_eq!(val, TernaryVal::False);
        let val = sol.var_value(Var::new(2));
        assert_eq!(val, TernaryVal::True);
    }

    #[test]
    fn sol_from_lits() {
        let true_sol = Assignment::from(vec![
            TernaryVal::True,
            TernaryVal::DontCare,
            TernaryVal::False,
        ]);
        let sol = Assignment::from_iter(vec![lit![0], !lit![2]]);
        assert_eq!(true_sol, sol);
    }

    #[test]
    fn var_mem_size() {
        assert_eq!(size_of::<Var>(), size_of::<u32>());
    }

    #[test]
    fn lit_mem_size() {
        assert_eq!(size_of::<Lit>(), size_of::<u32>());
    }

    #[test]
    fn ternary_val_size() {
        assert_eq!(size_of::<TernaryVal>(), 1);
    }
}
