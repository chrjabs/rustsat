//! # Common Types for SAT Solving
//!
//! Common types used throughout the library to guarantee type safety.

use core::ffi::c_int;
use std::{fmt, ops};

pub mod constraints;
pub use constraints::Clause;

/// Type representing boolean variables in a SAT problem. Variables indexing in
/// RustSAT starts from 0 and the maximum index is `(usize::MAX - 1) / 2`. This is
/// because literals are represented as a single `usize` as well. The memory
/// representation of this is a single `usize`.
#[derive(Hash, Eq, PartialEq, PartialOrd, Clone, Copy, Ord, Debug)]
#[repr(transparent)]
pub struct Var {
    idx: usize,
}

impl Var {
    /// The maximum index that can be represented.
    pub const MAX_IDX: usize = (usize::MAX - 1) / 2;

    /// Creates a new variables with a given index.
    /// Indices start from 0.
    /// Panics if `idx > Var::MAX_IDX`.
    pub fn new(idx: usize) -> Var {
        if idx > Var::MAX_IDX {
            panic!("variable index too high")
        }
        Var { idx }
    }

    /// Creates a new variables with a given index.
    /// Indices start from 0.
    /// Returns `Err(TypeError::IdxTooHigh(idx, Var::MAX_IDX)` if
    /// `idx > Var::MAX_IDX`.
    pub fn new_with_error(idx: usize) -> Result<Var, TypeError> {
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
    pub fn new_unchecked(idx: usize) -> Var {
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

    /// Returns the index of the variable.
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
        self.idx
    }
}

/// Incrementing variables
impl ops::Add<usize> for Var {
    type Output = Var;

    fn add(self, rhs: usize) -> Self::Output {
        Var {
            idx: self.idx + rhs,
        }
    }
}

/// Decrementing variables
impl ops::Sub<usize> for Var {
    type Output = Var;

    fn sub(self, rhs: usize) -> Self::Output {
        Var {
            idx: self.idx - rhs,
        }
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
        Var::new($v)
    };
}

/// Type representing literals, possibly negated boolean variables.
#[derive(Hash, Eq, PartialEq, PartialOrd, Ord, Clone, Copy, Debug)]
#[repr(transparent)]
pub struct Lit {
    /// Literal representation is `idx << 1` with the last bit representing
    /// whether the literal is negated or not. This way the literal can directly
    /// be used to index data structures with the two literals of a variable
    /// being close together.
    lidx: usize,
}

impl Lit {
    /// Represents a literal in memory
    #[inline]
    fn represent(idx: usize, negated: bool) -> usize {
        (idx << 1) + (negated as usize)
    }

    /// Creates a new (negated or not) literal with a given index.
    /// Panics if `idx > Var::MAX_IDX`.
    pub fn new(idx: usize, negated: bool) -> Lit {
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
    pub fn new_with_error(idx: usize, negated: bool) -> Result<Lit, TypeError> {
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
    pub fn new_unchecked(idx: usize, negated: bool) -> Lit {
        Lit {
            lidx: Lit::represent(idx, negated),
        }
    }

    /// Creates a new positive literal with a given index.
    /// Panics if `idx > Var::MAX_IDX`.
    #[inline]
    pub fn positive(idx: usize) -> Lit {
        Lit::new(idx, false)
    }

    /// Creates a new negated literal with a given index.
    /// Panics if `idx > Var::MAX_IDX`.
    #[inline]
    pub fn negative(idx: usize) -> Lit {
        Lit::new(idx, true)
    }

    /// Creates a new positive literal with a given index.
    /// Panics if `idx > Var::MAX_IDX`.
    #[inline]
    pub fn positive_with_error(idx: usize) -> Result<Lit, TypeError> {
        Lit::new_with_error(idx, false)
    }

    /// Creates a new negated literal with a given index.
    /// Panics if `idx > Var::MAX_IDX`.
    #[inline]
    pub fn negative_with_error(idx: usize) -> Result<Lit, TypeError> {
        Lit::new_with_error(idx, true)
    }

    /// Creates a new positive literal with a given index.
    /// Does not perform any check on the index, therefore might produce an inconsistent variable.
    /// Only use this for performance reasons if you are sure that `idx <= Var::MAX_IDX`.
    #[inline]
    pub fn positive_unchecked(idx: usize) -> Lit {
        Lit::new_unchecked(idx, false)
    }

    /// Creates a new negated literal with a given index.
    /// Does not perform any check on the index, therefore might produce an inconsistent variable.
    /// Only use this for performance reasons if you are sure that `idx <= Var::MAX_IDX`.
    #[inline]
    pub fn negative_unchecked(idx: usize) -> Lit {
        Lit::new_unchecked(idx, true)
    }

    /// Create a literal from an IPASIR integer value. Returns an error if
    /// the value is zero or the index too high.
    pub fn from_ipasir(val: c_int) -> Result<Lit, TypeError> {
        if val == 0 {
            return Err(TypeError::IpasirZero);
        }
        let negated = if val > 0 { false } else { true };
        let idx: usize = if val > 0 {
            val.try_into().unwrap()
        } else {
            (-val).try_into().unwrap()
        };
        Ok(Lit::new_with_error(idx - 1, negated)?)
    }

    /// Gets the variable index of the literal
    #[inline]
    pub fn vidx(&self) -> usize {
        self.lidx >> 1
    }

    /// Gets a literal representation for indexing data structures
    #[inline]
    pub fn lidx(&self) -> usize {
        self.lidx
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
        Var::new_unchecked(self.vidx())
    }

    /// True if the literal is positive.
    #[inline]
    pub fn is_pos(&self) -> bool {
        (self.lidx & 1usize) == 0
    }

    /// True if the literal is negated.
    #[inline]
    pub fn is_neg(&self) -> bool {
        (self.lidx & 1usize) == 1
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
            Err(_) => return Err(TypeError::IdxTooHigh(self.vidx() + 1, c_int::MAX as usize)),
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
            lidx: self.lidx ^ 1usize,
        }
    }
}

/// Trait implementation allowing for negating literals with the unary `-` operator.
impl ops::Neg for Lit {
    type Output = Lit;

    #[inline]
    fn neg(self) -> Lit {
        Lit {
            lidx: self.lidx ^ 1usize,
        }
    }
}

/// Incrementing literals. This preserves the sign of the literal.
impl ops::Add<usize> for Lit {
    type Output = Lit;

    fn add(self, rhs: usize) -> Self::Output {
        Lit {
            lidx: self.lidx + 2 * rhs,
        }
    }
}

/// Decrementing literals. This preserves the sign of the literal.
impl ops::Sub<usize> for Lit {
    type Output = Lit;

    fn sub(self, rhs: usize) -> Self::Output {
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
        Lit::positive($l)
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
        Lit::from_ipasir($l).unwrap()
    };
}

/// Ternary value assigned to a literal or variable, including possible "don't care"
#[derive(Clone, Copy, PartialEq)]
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
        if lit.is_neg() {
            match self.var_value(&lit.var())? {
                TernaryVal::DontCare => Some(&TernaryVal::DontCare),
                TernaryVal::True => Some(&TernaryVal::False),
                TernaryVal::False => Some(&TernaryVal::True),
            }
        } else {
            self.var_value(&lit.var())
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

/// Errors related to types
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeError {
    /// The requested index is too high.
    /// Contains the requested and the maximum index.
    IdxTooHigh(usize, usize),
    /// IPASIR index is zero
    IpasirZero,
}

#[cfg(test)]
mod tests {
    use std::mem::size_of;

    use super::{Lit, Solution, TernaryVal, Var};

    #[test]
    fn var_index() {
        let idx = 5;
        let var = Var::new(idx);
        assert_eq!(var.idx(), idx);
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

    #[test]
    fn var_mem_size() {
        assert_eq!(size_of::<Var>(), size_of::<usize>());
    }

    #[test]
    fn lit_mem_size() {
        assert_eq!(size_of::<Lit>(), size_of::<usize>());
    }

    #[test]
    fn ternary_val_size() {
        assert_eq!(size_of::<TernaryVal>(), 1);
    }
}
