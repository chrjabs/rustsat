//! # Constraint Types
//!
//! Different types of constraints. The most important one is [`Clause`] but
//! Rust SAT supports more complex constraints like [`PBConstraint`] or
//! [`CardConstraint`].

use std::{
    fmt,
    ops::{self, Not, RangeBounds},
};

use thiserror::Error;

use super::{Assignment, IWLitIter, Lit, LitIter, RsHashSet, TernaryVal, WLitIter};

#[cfg(feature = "pyapi")]
use crate::pyapi::{SingleOrList, SliceOrInt};
#[cfg(feature = "pyapi")]
use pyo3::{
    exceptions::{PyIndexError, PyRuntimeError},
    prelude::*,
};

/// Type representing a clause.
/// Wrapper around a std collection to allow for changing the data structure.
/// Optional clauses as sets will be included in the future.
#[cfg_attr(feature = "pyapi", pyclass)]
#[derive(Eq, PartialOrd, Ord, Clone, Default)]
pub struct Clause {
    lits: Vec<Lit>,
    #[cfg(feature = "pyapi")]
    modified: bool,
}

impl PartialEq for Clause {
    fn eq(&self, other: &Self) -> bool {
        self.lits == other.lits
    }
}

impl std::hash::Hash for Clause {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.lits.hash(state);
    }
}

impl Clause {
    /// Creates a new empty clause
    pub fn new() -> Self {
        Self::default()
    }

    /// Gets the clause as a slice of literals
    pub fn lits(&self) -> &[Lit] {
        &self.lits
    }

    /// Gets the length of the clause
    #[inline]
    pub fn len(&self) -> usize {
        self.lits.len()
    }

    /// Checks if the clause is empty
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.lits.is_empty()
    }

    /// Evaluates a clause under a given assignment
    pub fn evaluate(&self, assignment: &Assignment) -> TernaryVal {
        self.iter()
            .fold(TernaryVal::False, |val, l| match assignment.lit_value(*l) {
                TernaryVal::True => TernaryVal::True,
                TernaryVal::DontCare => {
                    if val == TernaryVal::False {
                        TernaryVal::DontCare
                    } else {
                        val
                    }
                }
                TernaryVal::False => val,
            })
    }

    /// Gets an iterator over the clause
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &Lit> {
        self.lits.iter()
    }

    /// Gets a mutable iterator over the clause
    #[inline]
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Lit> {
        self.lits.iter_mut()
    }

    /// Like [`Vec::drain`]
    pub fn drain<R: RangeBounds<usize>>(&mut self, range: R) -> std::vec::Drain<'_, Lit> {
        self.lits.drain(range)
    }

    /// Normalizes the clause. This includes sorting the literals, removing
    /// duplicates and removing the entire clause if it is a tautology.
    /// Comparing two normalized clauses checks their logical equivalence.
    pub fn normalize(mut self) -> Option<Self> {
        if self.len() <= 1 {
            return Some(self);
        }
        // Sort and filter duplicates
        self.lits.sort_unstable();
        self.lits.dedup();
        // Check for tautology
        let mut neg_last = None;
        if let Err(()) = self.iter().try_for_each(|l| {
            if let Some(neg_last) = neg_last {
                if l == &neg_last {
                    // Positive lits always come first
                    return Err(());
                }
            }
            neg_last = Some(!*l);
            Ok(())
        }) {
            return None;
        }
        Some(self)
    }

    /// Sanitizes the clause. This includes removing duplicates and removing the
    /// entire clause if it is a tautology. This preserves the order of the
    /// literals in the clause.
    pub fn sanitize(mut self) -> Option<Self> {
        if self.len() <= 1 {
            return Some(self);
        }
        let mut lset = RsHashSet::default();
        let mut idx = 0;
        while idx < self.len() {
            let l = self[idx];
            if lset.contains(&!l) {
                // Tautology
                return None;
            }
            if lset.contains(&l) {
                self.lits.remove(idx);
            } else {
                lset.insert(l);
                idx += 1;
            }
        }
        Some(self)
    }

    pub fn is_sat(&self, assign: &Assignment) -> bool {
        for &lit in &self.lits {
            if assign.lit_value(lit) == TernaryVal::True {
                return true;
            }
        }
        false
    }
}

impl<const N: usize> From<[Lit; N]> for Clause {
    fn from(value: [Lit; N]) -> Self {
        Self {
            lits: Vec::from(value),
            #[cfg(feature = "pyapi")]
            modified: false,
        }
    }
}

impl From<&[Lit]> for Clause {
    fn from(value: &[Lit]) -> Self {
        Self {
            lits: Vec::from(value),
            #[cfg(feature = "pyapi")]
            modified: false,
        }
    }
}

impl Extend<Lit> for Clause {
    fn extend<T: IntoIterator<Item = Lit>>(&mut self, iter: T) {
        self.lits.extend(iter)
    }
}

impl ops::Index<usize> for Clause {
    type Output = Lit;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        &self.lits[index]
    }
}

impl ops::IndexMut<usize> for Clause {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.lits[index]
    }
}

impl<'a> IntoIterator for &'a Clause {
    type Item = &'a Lit;

    type IntoIter = std::slice::Iter<'a, Lit>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.lits.iter()
    }
}

impl<'a> IntoIterator for &'a mut Clause {
    type Item = &'a mut Lit;

    type IntoIter = std::slice::IterMut<'a, Lit>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.lits.iter_mut()
    }
}

impl IntoIterator for Clause {
    type Item = Lit;

    type IntoIter = std::vec::IntoIter<Lit>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.lits.into_iter()
    }
}

impl FromIterator<Lit> for Clause {
    fn from_iter<T: IntoIterator<Item = Lit>>(iter: T) -> Self {
        Self {
            lits: Vec::from_iter(iter),
            #[cfg(feature = "pyapi")]
            modified: false,
        }
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

#[cfg_attr(feature = "pyapi", pymethods)]
impl Clause {
    /// Checks if the clause is a unit clause
    #[inline]
    pub fn is_unit(&self) -> bool {
        self.lits.len() == 1
    }

    /// Checks if the clause is binary
    pub fn is_binary(&self) -> bool {
        self.lits.len() == 2
    }

    /// Adds a literal to the clause
    pub fn add(&mut self, lit: Lit) {
        #[cfg(feature = "pyapi")]
        {
            self.modified = true;
        }
        self.lits.push(lit)
    }

    /// Removes the first occurrence of a literal from the clause
    /// Returns true if an occurrence was found
    pub fn remove(&mut self, lit: &Lit) -> bool {
        #[cfg(feature = "pyapi")]
        {
            self.modified = true;
        }
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
        #[cfg(feature = "pyapi")]
        {
            self.modified = true;
        }
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

    #[cfg(feature = "pyapi")]
    #[new]
    fn pynew(lits: Vec<Lit>) -> Self {
        Self::from_iter(lits)
    }

    #[cfg(feature = "pyapi")]
    fn __str__(&self) -> String {
        format!("{}", self)
    }

    #[cfg(feature = "pyapi")]
    fn __repr__(&self) -> String {
        format!("{}", self)
    }

    #[cfg(feature = "pyapi")]
    fn __len__(&self) -> usize {
        self.len()
    }

    #[cfg(feature = "pyapi")]
    fn __getitem__(&self, idx: SliceOrInt) -> PyResult<SingleOrList<Lit>> {
        match idx {
            SliceOrInt::Slice(slice) => {
                let indices = slice.indices(self.len().try_into().unwrap())?;
                Ok(SingleOrList::List(
                    (indices.start as usize..indices.stop as usize)
                        .step_by(indices.step as usize)
                        .map(|idx| self[idx])
                        .collect(),
                ))
            }
            SliceOrInt::Int(idx) => {
                if idx.unsigned_abs() > self.len() || idx >= 0 && idx.unsigned_abs() >= self.len() {
                    return Err(PyIndexError::new_err("out of bounds"));
                }
                let idx = if idx >= 0 {
                    idx.unsigned_abs()
                } else {
                    self.len() - idx.unsigned_abs()
                };
                Ok(SingleOrList::Single(self[idx]))
            }
        }
    }

    #[cfg(feature = "pyapi")]
    fn __iter__(mut slf: PyRefMut<'_, Self>) -> ClauseIter {
        slf.modified = false;
        ClauseIter {
            clause: slf.into(),
            index: 0,
        }
    }

    #[cfg(feature = "pyapi")]
    #[pyo3(name = "extend")]
    fn py_extend(&mut self, lits: Vec<Lit>) {
        self.extend(lits)
    }

    #[cfg(feature = "pyapi")]
    fn __eq__(&self, other: &Clause) -> bool {
        self == other
    }

    #[cfg(feature = "pyapi")]
    fn __ne__(&self, other: &Clause) -> bool {
        self != other
    }
}

#[macro_export]
macro_rules! clause {
    ( $($l:expr),* ) => {
        {
            let mut tmp_clause = $crate::types::Clause::new();
            $(
                tmp_clause.add($l);
            )*
            tmp_clause
        }
    };
}

#[cfg(feature = "pyapi")]
#[pyclass]
struct ClauseIter {
    clause: Py<Clause>,
    index: usize,
}

#[cfg(feature = "pyapi")]
#[pymethods]
impl ClauseIter {
    fn __iter__(slf: PyRef<'_, Self>) -> PyRef<'_, Self> {
        slf
    }

    fn __next__(mut slf: PyRefMut<'_, Self>) -> PyResult<Option<Lit>> {
        if slf.clause.borrow(slf.py()).modified {
            return Err(PyRuntimeError::new_err("clause modified during iteration"));
        }
        if slf.index < slf.clause.borrow(slf.py()).len() {
            slf.index += 1;
            return Ok(Some(slf.clause.borrow(slf.py())[slf.index - 1]));
        }
        return Ok(None);
    }
}

/// Type representing a cardinality constraint.
#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub enum CardConstraint {
    /// An upper bound cardinality constraint
    UB(CardUBConstr),
    /// A lower bound cardinality constraint
    LB(CardLBConstr),
    /// An equality cardinality constraint
    EQ(CardEQConstr),
}

impl CardConstraint {
    /// Constructs a new upper bound cardinality constraint (`sum of lits <= b`)
    pub fn new_ub<LI: LitIter>(lits: LI, b: usize) -> Self {
        CardConstraint::UB(CardUBConstr {
            lits: lits.into_iter().collect(),
            b,
        })
    }

    /// Constructs a new lower bound cardinality constraint (`sum of lits >= b`)
    pub fn new_lb<LI: LitIter>(lits: LI, b: usize) -> Self {
        CardConstraint::LB(CardLBConstr {
            lits: lits.into_iter().collect(),
            b,
        })
    }

    /// Constructs a new equality cardinality constraint (`sum of lits = b`)
    pub fn new_eq<LI: LitIter>(lits: LI, b: usize) -> Self {
        CardConstraint::EQ(CardEQConstr {
            lits: lits.into_iter().collect(),
            b,
        })
    }

    /// Adds literals to the cardinality constraint
    pub fn add<LI: LitIter>(&mut self, lits: LI) {
        match self {
            CardConstraint::UB(constr) => constr.lits.extend(lits),
            CardConstraint::LB(constr) => constr.lits.extend(lits),
            CardConstraint::EQ(constr) => constr.lits.extend(lits),
        }
    }

    /// Changes the bound on the constraint
    pub fn change_bound(&mut self, b: usize) {
        match self {
            CardConstraint::UB(constr) => constr.b = b,
            CardConstraint::LB(constr) => constr.b = b,
            CardConstraint::EQ(constr) => constr.b = b,
        }
    }

    /// Checks if the constraint is always satisfied
    pub fn is_tautology(&self) -> bool {
        match self {
            CardConstraint::UB(constr) => constr.is_tautology(),
            CardConstraint::LB(constr) => constr.is_tautology(),
            CardConstraint::EQ(_) => false,
        }
    }

    /// Checks if the constraint is unsatisfiable
    pub fn is_unsat(&self) -> bool {
        match self {
            CardConstraint::UB(_) => false,
            CardConstraint::LB(constr) => constr.is_unsat(),
            CardConstraint::EQ(constr) => constr.is_unsat(),
        }
    }

    /// Checks if the constraint assigns all literals to true
    pub fn is_positive_assignment(&self) -> bool {
        match self {
            CardConstraint::UB(_) => false,
            CardConstraint::LB(constr) => constr.is_positive_assignment(),
            CardConstraint::EQ(constr) => constr.is_positive_assignment(),
        }
    }

    /// Checks if the constraint assigns all literals to false
    pub fn is_negative_assignment(&self) -> bool {
        match self {
            CardConstraint::UB(constr) => constr.is_negative_assignment(),
            CardConstraint::LB(_) => false,
            CardConstraint::EQ(constr) => constr.is_negative_assignment(),
        }
    }

    /// Checks if the constraint is a clause
    pub fn is_clause(&self) -> bool {
        match self {
            CardConstraint::UB(constr) => constr.is_clause(),
            CardConstraint::LB(constr) => constr.is_clause(),
            CardConstraint::EQ(_) => false,
        }
    }

    /// Normalizes the constraint. This only consists of sorting the literals.
    /// Comparing two normalized constraints checks their logical equivalence.
    pub fn normalize(mut self) -> Self {
        let norm = |lits: &mut Vec<Lit>| {
            if lits.len() <= 1 {
                return;
            }
            lits.sort_unstable();
        };
        match &mut self {
            CardConstraint::UB(constr) => norm(&mut constr.lits),
            CardConstraint::LB(constr) => norm(&mut constr.lits),
            CardConstraint::EQ(constr) => norm(&mut constr.lits),
        };
        self
    }

    /// Gets the literals that are in the constraint
    pub fn into_lits(self) -> Vec<Lit> {
        match self {
            CardConstraint::UB(constr) => constr.lits,
            CardConstraint::LB(constr) => constr.lits,
            CardConstraint::EQ(constr) => constr.lits,
        }
    }

    /// Converts the constraint into a clause, if possible
    pub fn as_clause(self) -> Option<Clause> {
        if !self.is_clause() {
            return None;
        }
        match self {
            CardConstraint::UB(constr) => {
                Some(Clause::from_iter(constr.lits.into_iter().map(Lit::not)))
            }
            CardConstraint::LB(constr) => Some(Clause::from_iter(constr.lits)),
            CardConstraint::EQ(_) => panic!(),
        }
    }

    /// Gets an iterator over the literals in the constraint
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &Lit> {
        match self {
            CardConstraint::UB(constr) => constr.lits.iter(),
            CardConstraint::LB(constr) => constr.lits.iter(),
            CardConstraint::EQ(constr) => constr.lits.iter(),
        }
    }

    /// Gets a mutable iterator over the literals in the constraint
    #[inline]
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Lit> {
        match self {
            CardConstraint::UB(constr) => constr.lits.iter_mut(),
            CardConstraint::LB(constr) => constr.lits.iter_mut(),
            CardConstraint::EQ(constr) => constr.lits.iter_mut(),
        }
    }

    pub fn is_sat(&self, assign: &Assignment) -> bool {
        let count = self.iter().fold(0, |cnt, lit| {
            if assign.lit_value(*lit) == TernaryVal::True {
                return cnt + 1;
            }
            cnt
        });
        match self {
            CardConstraint::UB(constr) => count <= constr.b,
            CardConstraint::LB(constr) => count >= constr.b,
            CardConstraint::EQ(constr) => count == constr.b,
        }
    }
}

/// An upper bound cardinality constraint (`sum of lits <= b`)
#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct CardUBConstr {
    lits: Vec<Lit>,
    b: usize,
}

impl CardUBConstr {
    /// Decomposes the constraint to a set of input literals and an upper bound
    pub fn decompose(self) -> (Vec<Lit>, usize) {
        (self.lits, self.b)
    }

    /// Checks if the constraint is always satisfied
    pub fn is_tautology(&self) -> bool {
        self.b >= self.lits.len()
    }

    /// Checks if the constraint assigns all literals to false
    pub fn is_negative_assignment(&self) -> bool {
        self.b == 0
    }

    /// Checks if the constraint is a clause
    pub fn is_clause(&self) -> bool {
        self.b + 1 == self.lits.len()
    }
}

/// A lower bound cardinality constraint (`sum of lits >= b`)
#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct CardLBConstr {
    lits: Vec<Lit>,
    b: usize,
}

impl CardLBConstr {
    /// Decomposes the constraint to a set of input literals and a lower bound
    pub fn decompose(self) -> (Vec<Lit>, usize) {
        (self.lits, self.b)
    }

    /// Checks if the constraint is always satisfied
    pub fn is_tautology(&self) -> bool {
        self.b == 0
    }

    /// Checks if the constraint is unsatisfiable
    pub fn is_unsat(&self) -> bool {
        self.b > self.lits.len()
    }

    /// Checks if the constraint assigns all literals to true
    pub fn is_positive_assignment(&self) -> bool {
        self.b == self.lits.len()
    }

    /// Checks if the constraint is a clause
    pub fn is_clause(&self) -> bool {
        self.b == 1
    }
}

/// An equality cardinality constraint (`sum of lits = b`)
#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub struct CardEQConstr {
    lits: Vec<Lit>,
    b: usize,
}

impl CardEQConstr {
    /// Decomposes the constraint to a set of input literals and an equality bound
    pub fn decompose(self) -> (Vec<Lit>, usize) {
        (self.lits, self.b)
    }

    /// Checks if the constraint is unsatisfiable
    pub fn is_unsat(&self) -> bool {
        self.b > self.lits.len()
    }

    /// Checks if the constraint assigns all literals to true
    pub fn is_positive_assignment(&self) -> bool {
        self.b == self.lits.len()
    }

    /// Checks if the constraint assigns all literals to false
    pub fn is_negative_assignment(&self) -> bool {
        self.b == 0
    }
}

/// Errors when converting pseudo-boolean to cardinality constraints
#[derive(Error, Debug)]
pub enum PBToCardError {
    /// the pseudo-boolean constraint is not a cardinality constraint
    #[error("the PB constraint is not a cardinality constraint")]
    NotACard,
    /// the pseudo-boolean constraint is unsatisfiable
    #[error("the PB constraint is unsatisfiable")]
    Unsat,
    /// the pseudo-boolean constraint is a tautology
    #[error("the PB constraint is a tautology")]
    Tautology,
}

/// Type representing a pseudo-boolean constraint. When literals are added to a
/// constraint, the constraint is transformed so that all coefficients are
/// positive.
#[derive(Eq, PartialEq, Clone, Debug)]
pub enum PBConstraint {
    /// An upper bound pseudo-boolean constraint
    UB(PBUBConstr),
    /// A lower bound pseudo-boolean constraint
    LB(PBLBConstr),
    /// An equality pseudo-boolean constraint
    EQ(PBEQConstr),
}

impl PBConstraint {
    /// Converts input literals to non-negative weights, also returns the weight sum and the sum to add to the bound
    fn convert_input_lits<LI: IWLitIter>(lits: LI) -> (impl WLitIter, usize, isize) {
        let mut b_add = 0;
        let mut weight_sum = 0;
        let lits: Vec<(Lit, usize)> = lits
            .into_iter()
            .map(|(l, w)| {
                if w >= 0 {
                    weight_sum += w as usize;
                    (l, w as usize)
                } else {
                    b_add -= w;
                    weight_sum += -w as usize;
                    (!l, -w as usize)
                }
            })
            .collect();
        (lits, weight_sum, b_add)
    }

    /// Constructs a new upper bound pseudo-boolean constraint (`weighted sum of lits <= b`)
    pub fn new_ub<LI: IWLitIter>(lits: LI, b: isize) -> Self {
        let (lits, weight_sum, b_add) = PBConstraint::convert_input_lits(lits);
        PBConstraint::UB(PBUBConstr {
            lits: lits.into_iter().collect(),
            weight_sum,
            b: b + b_add,
        })
    }

    /// Constructs a new lower bound pseudo-boolean constraint (`weighted sum of lits >= b`)
    pub fn new_lb<LI: IWLitIter>(lits: LI, b: isize) -> Self {
        let (lits, weight_sum, b_add) = PBConstraint::convert_input_lits(lits);
        PBConstraint::LB(PBLBConstr {
            lits: lits.into_iter().collect(),
            weight_sum,
            b: b + b_add,
        })
    }

    /// Constructs a new equality pseudo-boolean constraint (`weighted sum of lits = b`)
    pub fn new_eq<LI: IWLitIter>(lits: LI, b: isize) -> Self {
        let (lits, weight_sum, b_add) = PBConstraint::convert_input_lits(lits);
        PBConstraint::EQ(PBEQConstr {
            lits: lits.into_iter().collect(),
            weight_sum,
            b: b + b_add,
        })
    }

    /// Gets mutable references to the underlying data
    fn get_data(&mut self) -> (&mut Vec<(Lit, usize)>, &mut usize, &mut isize) {
        match self {
            PBConstraint::UB(constr) => (&mut constr.lits, &mut constr.weight_sum, &mut constr.b),
            PBConstraint::LB(constr) => (&mut constr.lits, &mut constr.weight_sum, &mut constr.b),
            PBConstraint::EQ(constr) => (&mut constr.lits, &mut constr.weight_sum, &mut constr.b),
        }
    }

    /// Adds literals to the cardinality constraint
    pub fn add<LI: IWLitIter>(&mut self, lits: LI) {
        let (lits, add_weight_sum, b_add) = PBConstraint::convert_input_lits(lits);
        let (data_lits, weight_sum, b) = self.get_data();
        data_lits.extend(lits);
        *weight_sum += add_weight_sum;
        *b += b_add;
    }

    /// Checks if the constraint is always satisfied
    pub fn is_tautology(&self) -> bool {
        match self {
            PBConstraint::UB(constr) => constr.is_tautology(),
            PBConstraint::LB(constr) => constr.is_tautology(),
            PBConstraint::EQ(_) => false,
        }
    }

    /// Checks if the constraint is unsatisfiable
    pub fn is_unsat(&self) -> bool {
        match self {
            PBConstraint::UB(constr) => constr.is_unsat(),
            PBConstraint::LB(constr) => constr.is_unsat(),
            PBConstraint::EQ(constr) => constr.is_unsat(),
        }
    }

    /// Checks if the constraint assigns all literals to true
    pub fn is_positive_assignment(&self) -> bool {
        match self {
            PBConstraint::UB(_) => false,
            PBConstraint::LB(constr) => constr.is_positive_assignment(),
            PBConstraint::EQ(constr) => constr.is_positive_assignment(),
        }
    }

    /// Checks if the constraint assigns all literals to false
    pub fn is_negative_assignment(&self) -> bool {
        match self {
            PBConstraint::UB(constr) => constr.is_negative_assignment(),
            PBConstraint::LB(_) => false,
            PBConstraint::EQ(constr) => constr.is_negative_assignment(),
        }
    }

    /// Checks if the constraint is a cardinality constraint
    pub fn is_card(&self) -> bool {
        match self {
            PBConstraint::UB(constr) => constr.find_unit_weight().is_some(),
            PBConstraint::LB(constr) => constr.find_unit_weight().is_some(),
            PBConstraint::EQ(constr) => constr.find_unit_weight().is_some(),
        }
    }

    /// Checks if the constraint is a clause
    pub fn is_clause(&self) -> bool {
        match self {
            PBConstraint::UB(constr) => constr.is_clause(),
            PBConstraint::LB(constr) => constr.is_clause(),
            PBConstraint::EQ(_) => false,
        }
    }

    /// Normalizes the constraint. This sorts the literal and merges duplicates.
    /// Comparing two normalized constraints checks their logical equivalence.
    pub fn normalize(self) -> Self {
        let norm = |mut lits: Vec<(Lit, usize)>| {
            if lits.len() <= 1 {
                return lits;
            }
            lits.sort_unstable();
            let mut merged = Vec::new();
            for (l, w) in lits {
                match merged.last_mut() {
                    Some((l2, w2)) => {
                        if l == *l2 {
                            *w2 += w;
                        } else {
                            merged.push((l, w));
                        }
                    }
                    None => merged.push((l, w)),
                }
            }
            merged
        };
        match self {
            PBConstraint::UB(constr) => PBConstraint::UB(PBUBConstr {
                lits: norm(constr.lits),
                ..constr
            }),
            PBConstraint::LB(constr) => PBConstraint::LB(PBLBConstr {
                lits: norm(constr.lits),
                ..constr
            }),
            PBConstraint::EQ(constr) => PBConstraint::EQ(PBEQConstr {
                lits: norm(constr.lits),
                ..constr
            }),
        }
    }

    /// Converts the pseudo-boolean constraint into a cardinality constraint, if possible
    pub fn as_card_constr(self) -> Result<CardConstraint, PBToCardError> {
        if self.is_tautology() {
            return Err(PBToCardError::Tautology);
        }
        if self.is_unsat() {
            return Err(PBToCardError::Unsat);
        }
        Ok(match self {
            PBConstraint::UB(constr) => {
                let unit_weight = constr.find_unit_weight();
                match unit_weight {
                    None => return Err(PBToCardError::NotACard),
                    Some(unit_weight) => {
                        let lits = constr.lits.into_iter().map(|(l, _)| l);
                        CardConstraint::new_ub(lits, constr.b as usize / unit_weight)
                    }
                }
            }
            PBConstraint::LB(constr) => {
                let unit_weight = constr.find_unit_weight();
                match unit_weight {
                    None => return Err(PBToCardError::NotACard),
                    Some(unit_weight) => {
                        let lits = constr.lits.into_iter().map(|(l, _)| l);
                        CardConstraint::new_lb(
                            lits,
                            constr.b as usize / unit_weight
                                + if constr.b as usize % unit_weight == 0 {
                                    0
                                } else {
                                    1
                                },
                        )
                    }
                }
            }
            PBConstraint::EQ(constr) => {
                let unit_weight = constr.find_unit_weight();
                match unit_weight {
                    None => return Err(PBToCardError::NotACard),
                    Some(unit_weight) => {
                        if constr.b as usize % unit_weight != 0 {
                            return Err(PBToCardError::Unsat);
                        }
                        let lits = constr.lits.into_iter().map(|(l, _)| l);
                        CardConstraint::new_eq(lits, constr.b as usize / unit_weight)
                    }
                }
            }
        })
    }

    /// Converts the constraint into a clause, if possible
    pub fn as_clause(self) -> Option<Clause> {
        if !self.is_clause() {
            return None;
        }
        match self {
            PBConstraint::UB(constr) => Some(Clause::from_iter(
                constr.lits.into_iter().map(|(lit, _)| !lit),
            )),
            PBConstraint::LB(constr) => Some(Clause::from_iter(
                constr.lits.into_iter().map(|(lit, _)| lit),
            )),
            PBConstraint::EQ(_) => panic!(),
        }
    }

    /// Gets the (positively) weighted literals that are in the constraint
    pub fn into_lits(self) -> impl WLitIter {
        match self {
            PBConstraint::UB(constr) => constr.lits,
            PBConstraint::LB(constr) => constr.lits,
            PBConstraint::EQ(constr) => constr.lits,
        }
    }

    /// Gets an iterator over the literals in the constraint
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &(Lit, usize)> {
        match self {
            PBConstraint::UB(constr) => constr.lits.iter(),
            PBConstraint::LB(constr) => constr.lits.iter(),
            PBConstraint::EQ(constr) => constr.lits.iter(),
        }
    }

    /// Gets a mutable iterator over the literals in the constraint
    #[inline]
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut (Lit, usize)> {
        match self {
            PBConstraint::UB(constr) => constr.lits.iter_mut(),
            PBConstraint::LB(constr) => constr.lits.iter_mut(),
            PBConstraint::EQ(constr) => constr.lits.iter_mut(),
        }
    }

    pub fn is_sat(&self, assign: &Assignment) -> bool {
        let sum = self.iter().fold(0, |sum, (lit, coeff)| {
            if assign.lit_value(*lit) == TernaryVal::True {
                return sum + coeff;
            }
            sum
        });
        match self {
            PBConstraint::UB(constr) => {
                if let Ok(sum) = <usize as TryInto<isize>>::try_into(sum) {
                    sum <= constr.b
                } else {
                    false
                }
            }
            PBConstraint::LB(constr) => {
                if let Ok(sum) = <usize as TryInto<isize>>::try_into(sum) {
                    sum >= constr.b
                } else {
                    true
                }
            }
            PBConstraint::EQ(constr) => {
                if let Ok(sum) = <usize as TryInto<isize>>::try_into(sum) {
                    sum == constr.b
                } else {
                    false
                }
            }
        }
    }
}

/// An upper bound pseudo-boolean constraint (`weighted sum of lits <= b`)
#[derive(Eq, PartialEq, Clone, Debug)]
pub struct PBUBConstr {
    lits: Vec<(Lit, usize)>,
    weight_sum: usize,
    b: isize,
}

impl PBUBConstr {
    /// Decomposes the constraint to a set of input literals and an upper bound
    pub fn decompose(self) -> (Vec<(Lit, usize)>, isize) {
        (self.lits, self.b)
    }

    /// Checks if the constraint is always satisfied
    pub fn is_tautology(&self) -> bool {
        if self.b < 0 {
            return false;
        }
        self.b as usize >= self.weight_sum
    }

    /// Checks if the constraint is unsatisfiable
    pub fn is_unsat(&self) -> bool {
        self.b < 0
    }

    /// Checks if the constraint assigns all literals to false
    pub fn is_negative_assignment(&self) -> bool {
        if self.is_unsat() {
            return false;
        }
        let min_coeff: usize = self
            .lits
            .iter()
            .fold(usize::MAX, |min, (_, coeff)| std::cmp::min(min, *coeff));
        min_coeff > self.b as usize
    }

    /// Gets the unit weight of the constraint, if it exists
    pub fn find_unit_weight(&self) -> Option<usize> {
        let mut unit_weight = None;
        for (_, w) in self.lits.iter() {
            if let Some(uw) = unit_weight {
                if uw != *w {
                    return None;
                }
            } else {
                unit_weight = Some(*w)
            }
        }
        unit_weight
    }

    /// Checks if the constraint is a clause
    pub fn is_clause(&self) -> bool {
        if self.is_tautology() {
            return false;
        }
        if self.is_unsat() {
            return false;
        }
        let min_coeff: usize = self
            .lits
            .iter()
            .fold(usize::MAX, |min, (_, coeff)| std::cmp::min(min, *coeff));
        self.weight_sum <= self.b as usize + min_coeff && self.weight_sum > self.b as usize
    }
}

/// A lower bound pseudo-boolean constraint (`weighted sum of lits >= b`)
#[derive(Eq, PartialEq, Clone, Debug)]
pub struct PBLBConstr {
    lits: Vec<(Lit, usize)>,
    weight_sum: usize,
    b: isize,
}

impl PBLBConstr {
    /// Decomposes the constraint to a set of input literals and a lower bound
    pub fn decompose(self) -> (Vec<(Lit, usize)>, isize) {
        (self.lits, self.b)
    }

    /// Checks if the constraint is always satisfied
    pub fn is_tautology(&self) -> bool {
        self.b <= 0
    }

    /// Checks if the constraint is unsatisfiable
    pub fn is_unsat(&self) -> bool {
        if self.b < 0 {
            return false;
        }
        self.b as usize > self.weight_sum
    }

    /// Checks if the constraint assigns all literals to true
    pub fn is_positive_assignment(&self) -> bool {
        if self.b < 0 || self.is_unsat() {
            return false;
        }
        let min_coeff: usize = self
            .lits
            .iter()
            .fold(usize::MAX, |min, (_, coeff)| std::cmp::min(min, *coeff));
        // note: self.b <= self.weight_sum is checked in is_unsat
        self.b as usize + min_coeff > self.weight_sum
    }

    /// Gets the unit weight of the constraint, if it exists
    pub fn find_unit_weight(&self) -> Option<usize> {
        let mut unit_weight = None;
        for (_, w) in self.lits.iter() {
            if let Some(uw) = unit_weight {
                if uw != *w {
                    return None;
                }
            } else {
                unit_weight = Some(*w)
            }
        }
        unit_weight
    }

    /// Checks if the constraint is a clause
    pub fn is_clause(&self) -> bool {
        if self.is_tautology() {
            return false;
        }
        if self.is_unsat() {
            return false;
        }
        let min_coeff: usize = self
            .lits
            .iter()
            .fold(usize::MAX, |min, (_, coeff)| std::cmp::min(min, *coeff));
        (self.b as usize) <= min_coeff
    }
}

/// An equality pseudo-boolean constraint (`weighted sum of lits = b`)
#[derive(Eq, PartialEq, Clone, Debug)]
pub struct PBEQConstr {
    lits: Vec<(Lit, usize)>,
    weight_sum: usize,
    b: isize,
}

impl PBEQConstr {
    /// Decomposes the constraint to a set of input literals and an equality bound
    pub fn decompose(self) -> (Vec<(Lit, usize)>, isize) {
        (self.lits, self.b)
    }

    /// Checks if the constraint is unsatisfiable
    pub fn is_unsat(&self) -> bool {
        if self.b < 0 {
            return true;
        }
        self.b as usize > self.weight_sum
    }

    /// Checks if the constraint assigns all literals to true
    pub fn is_positive_assignment(&self) -> bool {
        if self.b < 0 {
            return false;
        }
        self.b as usize == self.weight_sum
    }

    /// Checks if the constraint assigns all literals to false
    pub fn is_negative_assignment(&self) -> bool {
        if self.b < 0 {
            return false;
        }
        self.b as usize == 0
    }

    /// Gets the unit weight of the constraint, if it exists
    pub fn find_unit_weight(&self) -> Option<usize> {
        let mut unit_weight = None;
        for (_, w) in self.lits.iter() {
            if let Some(uw) = unit_weight {
                if uw != *w {
                    return None;
                }
            } else {
                unit_weight = Some(*w)
            }
        }
        unit_weight
    }
}

#[cfg(test)]
mod tests {
    use super::{CardConstraint, PBConstraint};
    use crate::{lit, types::Assignment, var};

    #[test]
    fn clause_remove() {
        let mut cl = clause![lit![0], lit![1], lit![2], lit![1]];
        assert!(!cl.remove(&lit![3]));
        assert!(cl.remove(&lit![1]));
        assert_eq!(cl.len(), 3);
    }

    #[test]
    fn clause_remove_thorough() {
        let mut cl = clause![lit![0], lit![1], lit![2], lit![1]];
        assert!(!cl.remove_thorough(&lit![3]));
        assert!(cl.remove_thorough(&lit![1]));
        assert_eq!(cl.len(), 2);
    }

    #[test]
    fn clause_normalize() {
        let taut = clause![lit![0], lit![1], lit![2], lit![3], !lit![2]];
        assert_eq!(taut.normalize(), None);
        let cl = clause![
            lit![5],
            !lit![2],
            !lit![3],
            lit![17],
            lit![0],
            lit![1],
            !lit![2]
        ];
        assert_eq!(
            cl.normalize(),
            Some(clause![
                lit![0],
                lit![1],
                !lit![2],
                !lit![3],
                lit![5],
                lit![17]
            ])
        );
    }

    macro_rules! assign {
        ($val:expr) => {{
            let mut assign = Assignment::default();
            assign.assign_var(var![0], (($val & 1) == 1).into());
            assign.assign_var(var![1], ((($val >> 1) & 1) == 1).into());
            assign.assign_var(var![2], (($val >> 2) & 1 == 1).into());
            assign
        }};
    }

    #[test]
    fn clause_is_sat() {
        let cl = clause![lit![0], lit![1], lit![2]];
        assert!(!cl.is_sat(&assign!(0b000)));
        assert!(cl.is_sat(&assign!(0b001)));
        assert!(cl.is_sat(&assign!(0b010)));
        assert!(cl.is_sat(&assign!(0b011)));
        assert!(cl.is_sat(&assign!(0b100)));
        assert!(cl.is_sat(&assign!(0b101)));
        assert!(cl.is_sat(&assign!(0b110)));
        assert!(cl.is_sat(&assign!(0b111)));
    }

    #[test]
    fn card_is_tautology() {
        let lits = vec![lit![0], lit![1], lit![2]];
        assert!(CardConstraint::new_ub(lits.clone(), 3).is_tautology());
        assert!(!CardConstraint::new_ub(lits.clone(), 2).is_tautology());
        assert!(CardConstraint::new_lb(lits.clone(), 0).is_tautology());
        assert!(!CardConstraint::new_lb(lits.clone(), 1).is_tautology());
        assert!(!CardConstraint::new_eq(lits.clone(), 2).is_tautology());
    }

    #[test]
    fn card_is_unsat() {
        let lits = vec![lit![0], lit![1], lit![2]];
        assert!(!CardConstraint::new_ub(lits.clone(), 1).is_unsat());
        assert!(!CardConstraint::new_lb(lits.clone(), 3).is_unsat());
        assert!(CardConstraint::new_lb(lits.clone(), 4).is_unsat());
        assert!(!CardConstraint::new_eq(lits.clone(), 2).is_unsat());
        assert!(CardConstraint::new_eq(lits.clone(), 4).is_unsat());
    }

    #[test]
    fn card_is_positive_assignment() {
        let lits = vec![lit![0], lit![1], lit![2]];
        assert!(!CardConstraint::new_ub(lits.clone(), 1).is_positive_assignment());
        assert!(CardConstraint::new_lb(lits.clone(), 3).is_positive_assignment());
        assert!(!CardConstraint::new_lb(lits.clone(), 2).is_positive_assignment());
        assert!(CardConstraint::new_eq(lits.clone(), 3).is_positive_assignment());
        assert!(!CardConstraint::new_eq(lits.clone(), 2).is_positive_assignment());
    }

    #[test]
    fn card_is_negative_assignment() {
        let lits = vec![lit![0], lit![1], lit![2]];
        assert!(CardConstraint::new_ub(lits.clone(), 0).is_negative_assignment());
        assert!(!CardConstraint::new_ub(lits.clone(), 1).is_negative_assignment());
        assert!(!CardConstraint::new_lb(lits.clone(), 2).is_negative_assignment());
        assert!(CardConstraint::new_eq(lits.clone(), 0).is_negative_assignment());
        assert!(!CardConstraint::new_eq(lits.clone(), 1).is_negative_assignment());
    }

    #[test]
    fn card_is_clause() {
        let lits = vec![lit![0], lit![1], lit![2]];
        assert!(!CardConstraint::new_ub(lits.clone(), 1).is_clause());
        assert!(!CardConstraint::new_lb(lits.clone(), 3).is_clause());
        assert!(CardConstraint::new_lb(lits.clone(), 1).is_clause());
        assert!(!CardConstraint::new_eq(lits.clone(), 2).is_clause());
    }

    #[test]
    fn pb_is_tautology() {
        let lits = vec![(lit![0], 1), (lit![1], 2), (lit![2], 3)];
        assert!(PBConstraint::new_ub(lits.clone(), 6).is_tautology());
        assert!(!PBConstraint::new_ub(lits.clone(), 5).is_tautology());
        assert!(PBConstraint::new_lb(lits.clone(), 0).is_tautology());
        assert!(!PBConstraint::new_lb(lits.clone(), 1).is_tautology());
        assert!(!PBConstraint::new_eq(lits.clone(), 2).is_tautology());
    }

    #[test]
    fn pb_is_unsat() {
        let lits = vec![(lit![0], 1), (lit![1], 2), (lit![2], 3)];
        assert!(!PBConstraint::new_ub(lits.clone(), 1).is_unsat());
        assert!(!PBConstraint::new_lb(lits.clone(), 6).is_unsat());
        assert!(PBConstraint::new_lb(lits.clone(), 7).is_unsat());
        assert!(!PBConstraint::new_eq(lits.clone(), 2).is_unsat());
        assert!(PBConstraint::new_eq(lits.clone(), 7).is_unsat());
    }

    #[test]
    fn pb_is_positive_assignment() {
        let lits = vec![(lit![0], 1), (lit![1], 2), (lit![2], 3)];
        assert!(!PBConstraint::new_ub(lits.clone(), 1).is_positive_assignment());
        assert!(PBConstraint::new_lb(lits.clone(), 6).is_positive_assignment());
        assert!(!PBConstraint::new_lb(lits.clone(), 2).is_positive_assignment());
        assert!(PBConstraint::new_eq(lits.clone(), 6).is_positive_assignment());
        assert!(!PBConstraint::new_eq(lits.clone(), 2).is_positive_assignment());
    }

    #[test]
    fn pb_is_negative_assignment() {
        let lits = vec![(lit![0], 2), (lit![1], 2), (lit![2], 3)];
        assert!(PBConstraint::new_ub(lits.clone(), 1).is_negative_assignment());
        assert!(!PBConstraint::new_ub(lits.clone(), 2).is_negative_assignment());
        assert!(!PBConstraint::new_lb(lits.clone(), 2).is_negative_assignment());
        assert!(PBConstraint::new_eq(lits.clone(), 0).is_negative_assignment());
        assert!(!PBConstraint::new_eq(lits.clone(), 1).is_negative_assignment());
    }

    #[test]
    fn pb_is_card() {
        let lits = vec![(lit![0], 2), (lit![1], 2), (lit![2], 2)];
        assert!(PBConstraint::new_ub(lits.clone(), 1).is_card());
        assert!(PBConstraint::new_lb(lits.clone(), 3).is_card());
        assert!(PBConstraint::new_eq(lits.clone(), 2).is_card());
        let lits = vec![(lit![0], 2), (lit![1], 1), (lit![2], 2)];
        assert!(!PBConstraint::new_ub(lits.clone(), 1).is_card());
        assert!(!PBConstraint::new_lb(lits.clone(), 3).is_card());
        assert!(!PBConstraint::new_eq(lits.clone(), 2).is_card());
    }

    #[test]
    fn pb_is_clause() {
        let lits = vec![(lit![0], 2), (lit![1], 3), (lit![2], 2)];
        assert!(PBConstraint::new_ub(lits.clone(), 6).is_clause());
        assert!(PBConstraint::new_lb(lits.clone(), 2).is_clause());
        assert!(!PBConstraint::new_ub(lits.clone(), 7).is_clause());
        assert!(!PBConstraint::new_ub(lits.clone(), 4).is_clause());
        assert!(!PBConstraint::new_lb(lits.clone(), 3).is_clause());
        assert!(!PBConstraint::new_eq(lits.clone(), 2).is_card());
    }
}
