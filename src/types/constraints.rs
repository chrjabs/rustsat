//! # Constraint Types
//!
//! Different types of constraints. The most important one is [`Clause`] but
//! Rust SAT supports more complex constraints like [`PbConstraint`] or
//! [`CardConstraint`].

use core::slice;
use std::{
    collections::TryReserveError,
    fmt,
    ops::{self, Not, RangeBounds},
};

use itertools::Itertools;
use thiserror::Error;

use super::{Assignment, IWLitIter, Lit, LitIter, RsHashSet, TernaryVal, WLitIter};

use crate::RequiresClausal;

/// A reference to any type of constraint throughout RustSAT
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConstraintRef<'constr> {
    /// A clausal constraint
    Clause(&'constr Clause),
    /// A cardinality constraint
    Card(&'constr CardConstraint),
    /// A pseudo-Boolean constraint
    Pb(&'constr PbConstraint),
}

impl fmt::Display for ConstraintRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConstraintRef::Clause(cl) => write!(f, "{cl}"),
            ConstraintRef::Card(card) => write!(f, "{card}"),
            ConstraintRef::Pb(pb) => write!(f, "{pb}"),
        }
    }
}

/// Type representing a clause.
/// Wrapper around a std collection to allow for changing the data structure.
/// Optional clauses as sets will be included in the future.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Clause {
    lits: Vec<Lit>,
}

impl std::hash::Hash for Clause {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.lits.hash(state);
    }
}

impl Clause {
    /// Creates a new empty clause
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates a new empty clause with at least the specified capacity.
    ///
    /// Uses [`Vec::with_capacity`] internally.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            lits: Vec::with_capacity(capacity),
        }
    }

    /// Reserves capacity for at least `additional` more literals.
    ///
    /// Uses [`Vec::reserve`] internally.
    pub fn reserve(&mut self, additional: usize) {
        self.lits.reserve(additional);
    }

    /// Reserves the minimum capacity for at least `additional` more literals.
    ///
    /// Uses [`Vec::reserve_exact`] internally.
    pub fn reserve_exact(&mut self, additional: usize) {
        self.lits.reserve_exact(additional);
    }

    /// Tries to reserve capacity for at least `additional` more literals.
    ///
    /// Uses [`Vec::try_reserve`] internally.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error is returned.
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.lits.try_reserve(additional)
    }

    /// Tries to reserve the minimum capacity for at least `additional` more literals.
    ///
    /// Uses [`Vec::try_reserve_exact`] internally.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error is returned.
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.lits.try_reserve_exact(additional)
    }

    /// Like [`Vec::drain`]
    pub fn drain<R: RangeBounds<usize>>(&mut self, range: R) -> std::vec::Drain<'_, Lit> {
        self.lits.drain(range)
    }

    /// Normalizes the clause. This includes sorting the literals, removing
    /// duplicates and removing the entire clause if it is a tautology.
    /// Comparing two normalized clauses checks their logical equivalence.
    #[must_use]
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
    #[must_use]
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

    /// Adds a literal to the clause
    pub fn add(&mut self, lit: Lit) {
        self.lits.push(lit);
    }

    /// Removes the first occurrence of a literal from the clause
    /// Returns true if an occurrence was found
    pub fn remove(&mut self, lit: Lit) -> bool {
        for (i, l) in self.lits.iter().enumerate() {
            if *l == lit {
                self.lits.swap_remove(i);
                return true;
            }
        }
        false
    }

    /// Removes all occurrences of a literal from the clause
    pub fn remove_thorough(&mut self, lit: Lit) -> bool {
        let mut idxs = Vec::new();
        for (i, l) in self.lits.iter().enumerate() {
            if *l == lit {
                idxs.push(i);
            }
        }
        for i in idxs.iter().rev() {
            self.lits.remove(*i);
        }
        !idxs.is_empty()
    }
}

impl ops::Deref for Clause {
    type Target = Cl;

    fn deref(&self) -> &Self::Target {
        Cl::new(self)
    }
}

impl std::ops::DerefMut for Clause {
    fn deref_mut(&mut self) -> &mut Self::Target {
        Cl::new_mut(self)
    }
}

impl AsRef<[Lit]> for Clause {
    fn as_ref(&self) -> &[Lit] {
        &self.lits
    }
}

impl AsMut<[Lit]> for Clause {
    fn as_mut(&mut self) -> &mut [Lit] {
        &mut self.lits
    }
}

impl AsRef<Cl> for Clause {
    fn as_ref(&self) -> &Cl {
        Cl::new(self)
    }
}

impl AsMut<Cl> for Clause {
    fn as_mut(&mut self) -> &mut Cl {
        Cl::new_mut(self)
    }
}

impl<const N: usize> From<[Lit; N]> for Clause {
    fn from(value: [Lit; N]) -> Self {
        Self {
            lits: Vec::from(value),
        }
    }
}

impl From<&[Lit]> for Clause {
    fn from(value: &[Lit]) -> Self {
        Self {
            lits: Vec::from(value),
        }
    }
}

impl Extend<Lit> for Clause {
    fn extend<T: IntoIterator<Item = Lit>>(&mut self, iter: T) {
        self.lits.extend(iter);
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
        }
    }
}

impl<'a> IntoIterator for &'a Clause {
    type Item = &'a Lit;

    type IntoIter = std::slice::Iter<'a, Lit>;

    fn into_iter(self) -> Self::IntoIter {
        self.lits.iter()
    }
}

impl<'a> IntoIterator for &'a mut Clause {
    type Item = &'a mut Lit;

    type IntoIter = std::slice::IterMut<'a, Lit>;

    fn into_iter(self) -> Self::IntoIter {
        self.lits.iter_mut()
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({})", self.iter().format("|"))
    }
}

impl fmt::Debug for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({})", self.iter().format("|"))
    }
}

/// Creates a clause from a list of literals
#[macro_export]
macro_rules! clause {
    () => {
        $crate::types::Clause::new()
    };
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

/// Dynamically sized clause type to be used with references
///
/// [`Clause`] is the owned version: if [`Clause`] is [`String`], this is [`str`].
#[repr(transparent)]
pub struct Cl {
    lits: [Lit],
}

impl Cl {
    /// Directly wraps a literal slice as a [`Cl`]
    ///
    /// This is a cost-free conversion
    ///
    /// # Examples
    ///
    /// ```
    /// use rustsat::{types::Cl, lit};
    ///
    /// let lits = [lit![0], lit![1]];
    /// Cl::new(&lits);
    /// ```
    pub fn new<S: AsRef<[Lit]> + ?Sized>(s: &S) -> &Cl {
        unsafe { &*(s.as_ref() as *const [Lit] as *const Cl) }
    }

    /// Directly wraps a mutable literal slice as a [`Cl`]
    pub fn new_mut<S: AsMut<[Lit]> + ?Sized>(s: &mut S) -> &mut Cl {
        unsafe { &mut *(s.as_mut() as *mut [Lit] as *mut Cl) }
    }

    /// Gets the length of the clause
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.lits.len()
    }

    /// Checks if the clause is empty
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.lits.is_empty()
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

    /// Evaluates a clause under a given assignment
    #[must_use]
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

    /// Checks whether the clause is satisfied
    #[must_use]
    #[deprecated(
        since = "0.6.0",
        note = "use `evaluate` instead and check against `TernaryVal::True`"
    )]
    pub fn is_sat(&self, assignment: &Assignment) -> bool {
        self.evaluate(assignment) == TernaryVal::True
    }

    /// Checks whether the clause is tautological
    #[must_use]
    pub fn is_tautology(&self) -> bool {
        if self.is_empty() {
            return false;
        }
        for (idx, &l1) in self[0..self.len() - 1].iter().enumerate() {
            for &l2 in &self[idx + 1..] {
                if l1 == !l2 {
                    return true;
                }
            }
        }
        false
    }

    /// Performs [`slice::sort_unstable`] on the clause
    pub fn sort(&mut self) {
        self.lits.sort_unstable();
    }

    /// Checks if the clause is a unit clause
    #[inline]
    #[must_use]
    pub fn is_unit(&self) -> bool {
        self.lits.len() == 1
    }

    /// Checks if the clause is binary
    #[inline]
    #[must_use]
    pub fn is_binary(&self) -> bool {
        self.lits.len() == 2
    }
}

impl AsRef<[Lit]> for Cl {
    fn as_ref(&self) -> &[Lit] {
        &self.lits
    }
}

impl AsMut<[Lit]> for Cl {
    fn as_mut(&mut self) -> &mut [Lit] {
        &mut self.lits
    }
}

impl<I> ops::Index<I> for Cl
where
    I: slice::SliceIndex<[Lit]>,
{
    type Output = <I as slice::SliceIndex<[Lit]>>::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        &self.lits[index]
    }
}

impl<I> ops::IndexMut<I> for Cl
where
    I: slice::SliceIndex<[Lit]>,
{
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        &mut self.lits[index]
    }
}

impl<'a> IntoIterator for &'a Cl {
    type Item = &'a Lit;

    type IntoIter = std::slice::Iter<'a, Lit>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.lits.iter()
    }
}

impl<'a> IntoIterator for &'a mut Cl {
    type Item = &'a mut Lit;

    type IntoIter = std::slice::IterMut<'a, Lit>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.lits.iter_mut()
    }
}

impl fmt::Display for Cl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({})", self.iter().format("|"))
    }
}

impl fmt::Debug for Cl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({})", self.iter().format("|"))
    }
}

impl AsRef<Cl> for [Lit] {
    fn as_ref(&self) -> &Cl {
        Cl::new(self)
    }
}

impl AsMut<Cl> for [Lit] {
    fn as_mut(&mut self) -> &mut Cl {
        Cl::new_mut(self)
    }
}

/// Type representing a cardinality constraint.
#[derive(Hash, Eq, PartialEq, Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CardConstraint {
    /// An upper bound cardinality constraint
    Ub(CardUbConstr),
    /// A lower bound cardinality constraint
    Lb(CardLbConstr),
    /// An equality cardinality constraint
    Eq(CardEqConstr),
}

impl fmt::Display for CardConstraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CardConstraint::Ub(c) => write!(f, "{c}"),
            CardConstraint::Lb(c) => write!(f, "{c}"),
            CardConstraint::Eq(c) => write!(f, "{c}"),
        }
    }
}

macro_rules! write_lit_sum {
    ($f:expr, $vec:expr) => {{
        for i in 0..$vec.len() {
            if i < $vec.len() - 1 {
                write!($f, "{} + ", $vec[i])?;
            } else {
                write!($f, "{}", $vec[i])?;
            }
        }
    }};
}

impl CardConstraint {
    /// Constructs a new upper bound cardinality constraint (`sum of lits <= b`)
    pub fn new_ub<LI: LitIter>(lits: LI, b: usize) -> Self {
        CardConstraint::Ub(CardUbConstr {
            lits: lits.into_iter().collect(),
            b,
        })
    }

    /// Constructs a new lower bound cardinality constraint (`sum of lits >= b`)
    pub fn new_lb<LI: LitIter>(lits: LI, b: usize) -> Self {
        CardConstraint::Lb(CardLbConstr {
            lits: lits.into_iter().collect(),
            b,
        })
    }

    /// Constructs a new equality cardinality constraint (`sum of lits = b`)
    pub fn new_eq<LI: LitIter>(lits: LI, b: usize) -> Self {
        CardConstraint::Eq(CardEqConstr {
            lits: lits.into_iter().collect(),
            b,
        })
    }

    /// Adds literals to the cardinality constraint
    pub fn add<LI: LitIter>(&mut self, lits: LI) {
        match self {
            CardConstraint::Ub(constr) => constr.lits.extend(lits),
            CardConstraint::Lb(constr) => constr.lits.extend(lits),
            CardConstraint::Eq(constr) => constr.lits.extend(lits),
        }
    }

    /// Gets the bound of the constraint
    #[must_use]
    pub fn bound(&self) -> usize {
        match self {
            CardConstraint::Ub(CardUbConstr { b, .. })
            | CardConstraint::Lb(CardLbConstr { b, .. })
            | CardConstraint::Eq(CardEqConstr { b, .. }) => *b,
        }
    }

    /// Gets the number of literals in the constraint
    #[must_use]
    pub fn len(&self) -> usize {
        match self {
            CardConstraint::Ub(constr) => constr.lits.len(),
            CardConstraint::Lb(constr) => constr.lits.len(),
            CardConstraint::Eq(constr) => constr.lits.len(),
        }
    }

    /// Checks whether the constraint is empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Gets the number of literals in the constraint
    #[must_use]
    pub fn n_lits(&self) -> usize {
        self.len()
    }

    /// Changes the bound on the constraint
    pub fn change_bound(&mut self, b: usize) {
        match self {
            CardConstraint::Ub(constr) => constr.b = b,
            CardConstraint::Lb(constr) => constr.b = b,
            CardConstraint::Eq(constr) => constr.b = b,
        }
    }

    /// Checks if the constraint is always satisfied
    #[must_use]
    pub fn is_tautology(&self) -> bool {
        match self {
            CardConstraint::Ub(constr) => constr.is_tautology(),
            CardConstraint::Lb(constr) => constr.is_tautology(),
            CardConstraint::Eq(_) => false,
        }
    }

    /// Checks if the constraint is unsatisfiable
    #[must_use]
    pub fn is_unsat(&self) -> bool {
        match self {
            CardConstraint::Ub(_) => false,
            CardConstraint::Lb(constr) => constr.is_unsat(),
            CardConstraint::Eq(constr) => constr.is_unsat(),
        }
    }

    /// Checks if the constraint assigns all literals to true
    #[must_use]
    pub fn is_positive_assignment(&self) -> bool {
        match self {
            CardConstraint::Ub(_) => false,
            CardConstraint::Lb(constr) => constr.is_positive_assignment(),
            CardConstraint::Eq(constr) => constr.is_positive_assignment(),
        }
    }

    /// Checks if the constraint assigns all literals to false
    #[must_use]
    pub fn is_negative_assignment(&self) -> bool {
        match self {
            CardConstraint::Ub(constr) => constr.is_negative_assignment(),
            CardConstraint::Lb(_) => false,
            CardConstraint::Eq(constr) => constr.is_negative_assignment(),
        }
    }

    /// Checks if the constraint is a clause
    #[must_use]
    pub fn is_clause(&self) -> bool {
        match self {
            CardConstraint::Ub(constr) => constr.is_clause(),
            CardConstraint::Lb(constr) => constr.is_clause(),
            CardConstraint::Eq(_) => false,
        }
    }

    /// Normalizes the constraint. This only consists of sorting the literals.
    /// Comparing two normalized constraints checks their logical equivalence.
    #[must_use]
    pub fn normalize(mut self) -> Self {
        let norm = |lits: &mut Vec<Lit>| {
            if lits.len() <= 1 {
                return;
            }
            lits.sort_unstable();
        };
        match &mut self {
            CardConstraint::Ub(constr) => norm(&mut constr.lits),
            CardConstraint::Lb(constr) => norm(&mut constr.lits),
            CardConstraint::Eq(constr) => norm(&mut constr.lits),
        };
        self
    }

    /// Gets the literals that are in the constraint
    #[must_use]
    pub fn into_lits(self) -> Vec<Lit> {
        match self {
            CardConstraint::Ub(constr) => constr.lits,
            CardConstraint::Lb(constr) => constr.lits,
            CardConstraint::Eq(constr) => constr.lits,
        }
    }

    /// Converts the constraint into a clause, if possible
    #[deprecated(
        since = "0.5.0",
        note = "as_clause has been slightly changed and renamed to into_clause and will be removed in a future release"
    )]
    #[must_use]
    #[allow(clippy::wrong_self_convention)]
    pub fn as_clause(self) -> Option<Clause> {
        self.into_clause().ok()
    }

    /// Converts the constraint into a clause, if possible
    ///
    /// # Errors
    ///
    /// If the constraint is not a clause, returns [`RequiresClausal`].
    pub fn into_clause(self) -> Result<Clause, RequiresClausal> {
        if !self.is_clause() {
            return Err(RequiresClausal);
        }
        match self {
            CardConstraint::Ub(constr) => Ok(constr.lits.into_iter().map(Lit::not).collect()),
            CardConstraint::Lb(constr) => Ok(Clause::from_iter(constr.lits)),
            CardConstraint::Eq(_) => unreachable!(),
        }
    }

    /// Gets an iterator over the literals in the constraint
    #[inline]
    pub fn iter(&self) -> std::slice::Iter<'_, Lit> {
        match self {
            CardConstraint::Ub(constr) => constr.lits.iter(),
            CardConstraint::Lb(constr) => constr.lits.iter(),
            CardConstraint::Eq(constr) => constr.lits.iter(),
        }
    }

    /// Gets a mutable iterator over the literals in the constraint
    #[inline]
    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, Lit> {
        match self {
            CardConstraint::Ub(constr) => constr.lits.iter_mut(),
            CardConstraint::Lb(constr) => constr.lits.iter_mut(),
            CardConstraint::Eq(constr) => constr.lits.iter_mut(),
        }
    }

    /// Checks whether the cardinality constraint is satisfied by the given assignment
    #[must_use]
    pub fn evaluate(&self, assign: &Assignment) -> TernaryVal {
        #[allow(clippy::range_plus_one)]
        let range = self
            .iter()
            .fold(0..0, |rng, &lit| match assign.lit_value(lit) {
                TernaryVal::True => rng.start + 1..rng.end + 1,
                TernaryVal::False => rng,
                TernaryVal::DontCare => rng.start..rng.end + 1,
            });
        if range.contains(&self.bound()) {
            return TernaryVal::DontCare;
        }
        match self {
            CardConstraint::Ub(CardUbConstr { b, .. }) => (range.start <= *b).into(),
            CardConstraint::Lb(CardLbConstr { b, .. }) => (range.start >= *b).into(),
            CardConstraint::Eq(CardEqConstr { b, .. }) => (range.start == *b).into(),
        }
    }

    /// Checks whether the cardinality constraint is satisfied by the given assignment
    #[deprecated(
        since = "0.6.0",
        note = "use `evaluate` instead and check against `TernaryVal::True`"
    )]
    #[must_use]
    pub fn is_sat(&self, assign: &Assignment) -> bool {
        self.evaluate(assign) == TernaryVal::True
    }
}

impl<'slf> IntoIterator for &'slf CardConstraint {
    type Item = &'slf Lit;

    type IntoIter = std::slice::Iter<'slf, Lit>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'slf> IntoIterator for &'slf mut CardConstraint {
    type Item = &'slf mut Lit;

    type IntoIter = std::slice::IterMut<'slf, Lit>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl From<Clause> for CardConstraint {
    fn from(value: Clause) -> Self {
        CardConstraint::new_lb(value, 1)
    }
}

/// An upper bound cardinality constraint (`sum of lits <= b`)
#[derive(Hash, Eq, PartialEq, Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CardUbConstr {
    lits: Vec<Lit>,
    b: usize,
}

#[deprecated(
    since = "0.6.0",
    note = "CardUBConstr has been renamed to CardUbConstr and will be removed in a future release"
)]
pub use CardUbConstr as CardUBConstr;

impl fmt::Display for CardUbConstr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_lit_sum!(f, self.lits);
        write!(f, " <= {}", self.b)
    }
}

impl CardUbConstr {
    /// Decomposes the constraint to a set of input literals and an upper bound
    #[must_use]
    pub fn decompose(self) -> (Vec<Lit>, usize) {
        (self.lits, self.b)
    }

    /// Get references to the constraints internals
    pub(crate) fn decompose_ref(&self) -> (&Vec<Lit>, &usize) {
        (&self.lits, &self.b)
    }

    /// Checks if the constraint is always satisfied
    #[must_use]
    pub fn is_tautology(&self) -> bool {
        self.b >= self.lits.len()
    }

    /// Checks if the constraint assigns all literals to false
    #[must_use]
    pub fn is_negative_assignment(&self) -> bool {
        self.b == 0
    }

    /// Checks if the constraint is a clause
    #[must_use]
    pub fn is_clause(&self) -> bool {
        self.b + 1 == self.lits.len()
    }
}

/// A lower bound cardinality constraint (`sum of lits >= b`)
#[derive(Hash, Eq, PartialEq, Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CardLbConstr {
    lits: Vec<Lit>,
    b: usize,
}

#[deprecated(
    since = "0.6.0",
    note = "CardLBConstr has been renamed to CardLbConstr and will be removed in a future release"
)]
pub use CardLbConstr as CardLBConstr;

impl fmt::Display for CardLbConstr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_lit_sum!(f, self.lits);
        write!(f, " >= {}", self.b)
    }
}

impl CardLbConstr {
    /// Decomposes the constraint to a set of input literals and a lower bound
    #[must_use]
    pub fn decompose(self) -> (Vec<Lit>, usize) {
        (self.lits, self.b)
    }

    /// Get references to the constraints internals
    pub(crate) fn decompose_ref(&self) -> (&Vec<Lit>, &usize) {
        (&self.lits, &self.b)
    }

    /// Checks if the constraint is always satisfied
    #[must_use]
    pub fn is_tautology(&self) -> bool {
        self.b == 0
    }

    /// Checks if the constraint is unsatisfiable
    #[must_use]
    pub fn is_unsat(&self) -> bool {
        self.b > self.lits.len()
    }

    /// Checks if the constraint assigns all literals to true
    #[must_use]
    pub fn is_positive_assignment(&self) -> bool {
        self.b == self.lits.len()
    }

    /// Checks if the constraint is a clause
    #[must_use]
    pub fn is_clause(&self) -> bool {
        self.b == 1
    }
}

/// An equality cardinality constraint (`sum of lits = b`)
#[derive(Hash, Eq, PartialEq, Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CardEqConstr {
    lits: Vec<Lit>,
    b: usize,
}

#[deprecated(
    since = "0.6.0",
    note = "CardEQConstr has been renamed to CardEqConstr and will be removed in a future release"
)]
pub use CardEqConstr as CardEQConstr;

impl fmt::Display for CardEqConstr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_lit_sum!(f, self.lits);
        write!(f, " = {}", self.b)
    }
}

impl CardEqConstr {
    /// Decomposes the constraint to a set of input literals and an equality bound
    #[must_use]
    pub fn decompose(self) -> (Vec<Lit>, usize) {
        (self.lits, self.b)
    }

    /// Get references to the constraints internals
    pub(crate) fn decompose_ref(&self) -> (&Vec<Lit>, &usize) {
        (&self.lits, &self.b)
    }

    /// Checks if the constraint is unsatisfiable
    #[must_use]
    pub fn is_unsat(&self) -> bool {
        self.b > self.lits.len()
    }

    /// Checks if the constraint assigns all literals to true
    #[must_use]
    pub fn is_positive_assignment(&self) -> bool {
        self.b == self.lits.len()
    }

    /// Checks if the constraint assigns all literals to false
    #[must_use]
    pub fn is_negative_assignment(&self) -> bool {
        self.b == 0
    }
}

/// Errors when converting pseudo-boolean to cardinality constraints
#[derive(Error, Debug)]
pub enum PbToCardError {
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

#[deprecated(
    since = "0.6.0",
    note = "PBToCardError has been renamed to PbToCardError and will be removed in a future release"
)]
pub use PbToCardError as PBToCardError;

/// Type representing a pseudo-boolean constraint. When literals are added to a
/// constraint, the constraint is transformed so that all coefficients are
/// positive.
#[derive(Eq, PartialEq, Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PbConstraint {
    /// An upper bound pseudo-boolean constraint
    Ub(PbUbConstr),
    /// A lower bound pseudo-boolean constraint
    Lb(PbLbConstr),
    /// An equality pseudo-boolean constraint
    Eq(PbEqConstr),
}

#[deprecated(
    since = "0.6.0",
    note = "PBConstraint has been renamed to PbConstraint and will be removed in a future release"
)]
pub use PbConstraint as PBConstraint;

impl fmt::Display for PbConstraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PbConstraint::Ub(c) => write!(f, "{c}"),
            PbConstraint::Lb(c) => write!(f, "{c}"),
            PbConstraint::Eq(c) => write!(f, "{c}"),
        }
    }
}

macro_rules! write_wlit_sum {
    ($f:expr, $vec:expr) => {{
        for i in 0..$vec.len() {
            if i < $vec.len() - 1 {
                write!($f, "{} {} + ", $vec[i].1, $vec[i].0)?;
            } else {
                write!($f, "{} {}", $vec[i].1, $vec[i].0)?;
            }
        }
    }};
}

impl PbConstraint {
    /// Converts input literals to non-negative weights, also returns the weight sum and the sum to add to the bound
    fn convert_input_lits<LI: IWLitIter>(lits: LI) -> (impl WLitIter, usize, isize) {
        let mut b_add = 0;
        let mut weight_sum = 0;
        let lits: Vec<(Lit, usize)> = lits
            .into_iter()
            .map(|(l, w)| {
                if w >= 0 {
                    weight_sum += w.unsigned_abs();
                    (l, w.unsigned_abs())
                } else {
                    b_add -= w;
                    weight_sum += w.unsigned_abs();
                    (!l, w.unsigned_abs())
                }
            })
            .collect();
        (lits, weight_sum, b_add)
    }

    /// Constructs a new upper bound pseudo-boolean constraint (`weighted sum of lits <= b`)
    pub fn new_ub<LI: IWLitIter>(lits: LI, b: isize) -> Self {
        let (lits, weight_sum, b_add) = PbConstraint::convert_input_lits(lits);
        PbConstraint::Ub(PbUbConstr {
            lits: lits.into_iter().collect(),
            weight_sum,
            b: b + b_add,
        })
    }

    /// Constructs a new lower bound pseudo-boolean constraint (`weighted sum of lits >= b`)
    pub fn new_lb<LI: IWLitIter>(lits: LI, b: isize) -> Self {
        let (lits, weight_sum, b_add) = PbConstraint::convert_input_lits(lits);
        PbConstraint::Lb(PbLbConstr {
            lits: lits.into_iter().collect(),
            weight_sum,
            b: b + b_add,
        })
    }

    /// Constructs a new equality pseudo-boolean constraint (`weighted sum of lits = b`)
    pub fn new_eq<LI: IWLitIter>(lits: LI, b: isize) -> Self {
        let (lits, weight_sum, b_add) = PbConstraint::convert_input_lits(lits);
        PbConstraint::Eq(PbEqConstr {
            lits: lits.into_iter().collect(),
            weight_sum,
            b: b + b_add,
        })
    }

    /// Gets mutable references to the underlying data
    fn get_data(&mut self) -> (&mut Vec<(Lit, usize)>, &mut usize, &mut isize) {
        match self {
            PbConstraint::Ub(constr) => (&mut constr.lits, &mut constr.weight_sum, &mut constr.b),
            PbConstraint::Lb(constr) => (&mut constr.lits, &mut constr.weight_sum, &mut constr.b),
            PbConstraint::Eq(constr) => (&mut constr.lits, &mut constr.weight_sum, &mut constr.b),
        }
    }

    /// Adds literals to the cardinality constraint
    pub fn add<LI: IWLitIter>(&mut self, lits: LI) {
        let (lits, add_weight_sum, b_add) = PbConstraint::convert_input_lits(lits);
        let (data_lits, weight_sum, b) = self.get_data();
        data_lits.extend(lits);
        *weight_sum += add_weight_sum;
        *b += b_add;
    }

    /// Gets the bound of the constraint
    #[must_use]
    pub fn bound(&self) -> isize {
        match self {
            PbConstraint::Ub(PbUbConstr { b, .. })
            | PbConstraint::Lb(PbLbConstr { b, .. })
            | PbConstraint::Eq(PbEqConstr { b, .. }) => *b,
        }
    }

    /// Gets the number of literals in the constraint
    #[must_use]
    pub fn len(&self) -> usize {
        match self {
            PbConstraint::Ub(constr) => constr.lits.len(),
            PbConstraint::Lb(constr) => constr.lits.len(),
            PbConstraint::Eq(constr) => constr.lits.len(),
        }
    }

    /// Checks whether the constraint is empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Gets the number of literals in the constraint
    #[must_use]
    pub fn n_lits(&self) -> usize {
        self.len()
    }

    /// Checks if the constraint is always satisfied
    #[must_use]
    pub fn is_tautology(&self) -> bool {
        match self {
            PbConstraint::Ub(constr) => constr.is_tautology(),
            PbConstraint::Lb(constr) => constr.is_tautology(),
            PbConstraint::Eq(_) => false,
        }
    }

    /// Checks if the constraint is unsatisfiable
    #[must_use]
    pub fn is_unsat(&self) -> bool {
        match self {
            PbConstraint::Ub(constr) => constr.is_unsat(),
            PbConstraint::Lb(constr) => constr.is_unsat(),
            PbConstraint::Eq(constr) => constr.is_unsat(),
        }
    }

    /// Checks if the constraint assigns all literals to true
    #[must_use]
    pub fn is_positive_assignment(&self) -> bool {
        match self {
            PbConstraint::Ub(_) => false,
            PbConstraint::Lb(constr) => constr.is_positive_assignment(),
            PbConstraint::Eq(constr) => constr.is_positive_assignment(),
        }
    }

    /// Checks if the constraint assigns all literals to false
    #[must_use]
    pub fn is_negative_assignment(&self) -> bool {
        match self {
            PbConstraint::Ub(constr) => constr.is_negative_assignment(),
            PbConstraint::Lb(_) => false,
            PbConstraint::Eq(constr) => constr.is_negative_assignment(),
        }
    }

    /// Checks if the constraint is a cardinality constraint
    #[must_use]
    pub fn is_card(&self) -> bool {
        match self {
            PbConstraint::Ub(constr) => constr.find_unit_weight().is_some(),
            PbConstraint::Lb(constr) => constr.find_unit_weight().is_some(),
            PbConstraint::Eq(constr) => constr.find_unit_weight().is_some(),
        }
    }

    /// Checks if the constraint is a clause
    #[must_use]
    pub fn is_clause(&self) -> bool {
        match self {
            PbConstraint::Ub(constr) => constr.is_clause(),
            PbConstraint::Lb(constr) => constr.is_clause(),
            PbConstraint::Eq(_) => false,
        }
    }

    /// Normalizes the constraint. This sorts the literal and merges duplicates.
    /// Comparing two normalized constraints checks their logical equivalence.
    #[must_use]
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
            PbConstraint::Ub(constr) => PbConstraint::Ub(PbUbConstr {
                lits: norm(constr.lits),
                ..constr
            }),
            PbConstraint::Lb(constr) => PbConstraint::Lb(PbLbConstr {
                lits: norm(constr.lits),
                ..constr
            }),
            PbConstraint::Eq(constr) => PbConstraint::Eq(PbEqConstr {
                lits: norm(constr.lits),
                ..constr
            }),
        }
    }

    /// Converts the pseudo-boolean constraint into a cardinality constraint, if possible
    #[deprecated(
        since = "0.5.0",
        note = "as_card_constr has been renamed to into_card_constr"
    )]
    #[allow(clippy::missing_errors_doc)]
    #[allow(clippy::wrong_self_convention)]
    pub fn as_card_constr(self) -> Result<CardConstraint, PbToCardError> {
        self.into_card_constr()
    }

    /// Converts the pseudo-boolean constraint into a cardinality constraint, if possible
    ///
    /// # Errors
    ///
    /// If the constraint is not a cardinality constraint, including when it is a tautology or
    /// unsat, returns [`PbToCardError`]
    pub fn into_card_constr(self) -> Result<CardConstraint, PbToCardError> {
        if self.is_tautology() {
            return Err(PbToCardError::Tautology);
        }
        if self.is_unsat() {
            return Err(PbToCardError::Unsat);
        }
        Ok(match self {
            PbConstraint::Ub(constr) => {
                let unit_weight = constr.find_unit_weight();
                // since this is not unsat, b is non-negative
                let b = constr.b.unsigned_abs();
                match unit_weight {
                    None => return Err(PbToCardError::NotACard),
                    Some(unit_weight) => {
                        let lits = constr.lits.into_iter().map(|(l, _)| l);
                        CardConstraint::new_ub(lits, b / unit_weight)
                    }
                }
            }
            PbConstraint::Lb(constr) => {
                let unit_weight = constr.find_unit_weight();
                // since this is not a tautology, b is non-negative
                let b = constr.b.unsigned_abs();
                match unit_weight {
                    None => return Err(PbToCardError::NotACard),
                    Some(unit_weight) => {
                        let lits = constr.lits.into_iter().map(|(l, _)| l);
                        CardConstraint::new_lb(
                            lits,
                            b / unit_weight + usize::from(b % unit_weight != 0),
                        )
                    }
                }
            }
            PbConstraint::Eq(constr) => {
                let unit_weight = constr.find_unit_weight();
                // since this is not unsat, b is non-negative
                let b = constr.b.unsigned_abs();
                match unit_weight {
                    None => return Err(PbToCardError::NotACard),
                    Some(unit_weight) => {
                        if b % unit_weight != 0 {
                            return Err(PbToCardError::Unsat);
                        }
                        let lits = constr.lits.into_iter().map(|(l, _)| l);
                        CardConstraint::new_eq(lits, b / unit_weight)
                    }
                }
            }
        })
    }

    /// Converts the constraint into a clause, if possible
    #[deprecated(
        since = "0.5.0",
        note = "as_clause has been slightly changed and renamed to into_clause and will be removed in a future release"
    )]
    #[allow(clippy::wrong_self_convention)]
    #[must_use]
    pub fn as_clause(self) -> Option<Clause> {
        self.into_clause().ok()
    }

    /// Converts the constraint into a clause, if possible
    ///
    /// # Errors
    ///
    /// If the constraint is not a clause, returns [`RequiresClausal`]
    pub fn into_clause(self) -> Result<Clause, RequiresClausal> {
        if !self.is_clause() {
            return Err(RequiresClausal);
        }
        match self {
            PbConstraint::Ub(constr) => Ok(constr.lits.into_iter().map(|(lit, _)| !lit).collect()),
            PbConstraint::Lb(constr) => Ok(constr.lits.into_iter().map(|(lit, _)| lit).collect()),
            PbConstraint::Eq(_) => unreachable!(),
        }
    }

    /// Gets the (positively) weighted literals that are in the constraint
    #[must_use]
    pub fn into_lits(self) -> impl WLitIter {
        match self {
            PbConstraint::Ub(constr) => constr.lits,
            PbConstraint::Lb(constr) => constr.lits,
            PbConstraint::Eq(constr) => constr.lits,
        }
    }

    /// Gets an iterator over the literals in the constraint
    #[inline]
    pub fn iter(&self) -> std::slice::Iter<'_, (Lit, usize)> {
        match self {
            PbConstraint::Ub(constr) => constr.lits.iter(),
            PbConstraint::Lb(constr) => constr.lits.iter(),
            PbConstraint::Eq(constr) => constr.lits.iter(),
        }
    }

    /// Gets a mutable iterator over the literals in the constraint
    #[inline]
    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, (Lit, usize)> {
        match self {
            PbConstraint::Ub(constr) => constr.lits.iter_mut(),
            PbConstraint::Lb(constr) => constr.lits.iter_mut(),
            PbConstraint::Eq(constr) => constr.lits.iter_mut(),
        }
    }

    /// Checks whether the PB constraint is satisfied by the given assignment
    #[must_use]
    pub fn evaluate(&self, assign: &Assignment) -> TernaryVal {
        #[allow(clippy::range_plus_one)]
        let range = self
            .iter()
            .fold(0..0, |rng, &(lit, coeff)| match assign.lit_value(lit) {
                TernaryVal::True => rng.start + coeff..rng.end + coeff,
                TernaryVal::False => rng,
                TernaryVal::DontCare => rng.start..rng.end + coeff,
            });
        match (isize::try_from(range.start), isize::try_from(range.end)) {
            (Ok(start), Ok(end)) => {
                if (start..end).contains(&self.bound()) {
                    return TernaryVal::DontCare;
                }
                match self {
                    PbConstraint::Ub(PbUbConstr { b, .. }) => (start <= *b).into(),
                    PbConstraint::Lb(PbLbConstr { b, .. }) => (start >= *b).into(),
                    PbConstraint::Eq(PbEqConstr { b, .. }) => (start == *b).into(),
                }
            }
            (Ok(start), Err(_)) => match self {
                PbConstraint::Ub(PbUbConstr { b, .. }) => {
                    if (start..).contains(b) {
                        return TernaryVal::DontCare;
                    }
                    TernaryVal::True
                }
                PbConstraint::Lb(PbLbConstr { b, .. }) | PbConstraint::Eq(PbEqConstr { b, .. }) => {
                    if (start..).contains(b) {
                        return TernaryVal::DontCare;
                    }
                    TernaryVal::False
                }
            },
            (Err(_), Err(_)) => matches!(self, PbConstraint::Lb(_)).into(),
            (Err(_), Ok(_)) => unreachable!(), // since end >= start
        }
    }

    /// Checks whether the PB constraint is satisfied by the given assignment
    #[deprecated(
        since = "0.6.0",
        note = "use `evaluate` instead and check against `TernaryVal::True`"
    )]
    #[must_use]
    pub fn is_sat(&self, assign: &Assignment) -> bool {
        self.evaluate(assign) == TernaryVal::True
    }
}

impl<'slf> IntoIterator for &'slf PbConstraint {
    type Item = &'slf (Lit, usize);

    type IntoIter = std::slice::Iter<'slf, (Lit, usize)>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'slf> IntoIterator for &'slf mut PbConstraint {
    type Item = &'slf mut (Lit, usize);

    type IntoIter = std::slice::IterMut<'slf, (Lit, usize)>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl From<Clause> for PbConstraint {
    fn from(value: Clause) -> Self {
        PbConstraint::new_lb(value.into_iter().map(|l| (l, 1)), 1)
    }
}

impl From<CardConstraint> for PbConstraint {
    fn from(value: CardConstraint) -> Self {
        match value {
            CardConstraint::Ub(constr) => PbConstraint::new_ub(
                constr.lits.into_iter().map(|l| (l, 1)),
                isize::try_from(constr.b).expect("cannot handle bounds higher than `isize::MAX`"),
            ),
            CardConstraint::Lb(constr) => PbConstraint::new_lb(
                constr.lits.into_iter().map(|l| (l, 1)),
                isize::try_from(constr.b).expect("cannot handle bounds higher than `isize::MAX`"),
            ),
            CardConstraint::Eq(constr) => PbConstraint::new_eq(
                constr.lits.into_iter().map(|l| (l, 1)),
                isize::try_from(constr.b).expect("cannot handle bounds higher than `isize::MAX`"),
            ),
        }
    }
}

/// An upper bound pseudo-boolean constraint (`weighted sum of lits <= b`)
#[derive(Eq, PartialEq, Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct PbUbConstr {
    lits: Vec<(Lit, usize)>,
    weight_sum: usize,
    b: isize,
}

#[deprecated(
    since = "0.6.0",
    note = "PBUBConstr has been renamed to PbUbConstr and will be removed in a future release"
)]
pub use PbUbConstr as PBUBConstr;

impl fmt::Display for PbUbConstr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_wlit_sum!(f, self.lits);
        write!(f, " <= {}", self.b)
    }
}

impl PbUbConstr {
    /// Decomposes the constraint to a set of input literals and an upper bound
    #[must_use]
    pub fn decompose(self) -> (Vec<(Lit, usize)>, isize) {
        (self.lits, self.b)
    }

    /// Gets references to the constraints internals
    pub(crate) fn decompose_ref(&self) -> (&Vec<(Lit, usize)>, &isize) {
        (&self.lits, &self.b)
    }

    /// Checks if the constraint is always satisfied
    #[must_use]
    pub fn is_tautology(&self) -> bool {
        if self.b < 0 {
            return false;
        }
        self.b.unsigned_abs() >= self.weight_sum
    }

    /// Checks if the constraint is unsatisfiable
    #[must_use]
    pub fn is_unsat(&self) -> bool {
        self.b < 0
    }

    /// Checks if the constraint assigns all literals to false
    #[must_use]
    pub fn is_negative_assignment(&self) -> bool {
        if self.is_unsat() {
            return false;
        }
        let min_coeff: usize = self
            .lits
            .iter()
            .fold(usize::MAX, |min, (_, coeff)| std::cmp::min(min, *coeff));
        // absolute is safe since is not unsat
        min_coeff > self.b.unsigned_abs()
    }

    /// Gets the unit weight of the constraint, if it exists
    #[must_use]
    pub fn find_unit_weight(&self) -> Option<usize> {
        let mut unit_weight = None;
        for (_, w) in &self.lits {
            if let Some(uw) = unit_weight {
                if uw != *w {
                    return None;
                }
            } else {
                unit_weight = Some(*w);
            }
        }
        unit_weight
    }

    /// Checks if the constraint is a clause
    #[must_use]
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
        // self.b >= 0 since not unsat
        self.weight_sum <= self.b.unsigned_abs() + min_coeff
            && self.weight_sum > self.b.unsigned_abs()
    }
}

/// A lower bound pseudo-boolean constraint (`weighted sum of lits >= b`)
#[derive(Eq, PartialEq, Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct PbLbConstr {
    lits: Vec<(Lit, usize)>,
    weight_sum: usize,
    b: isize,
}

#[deprecated(
    since = "0.6.0",
    note = "PBLBConstr has been renamed to PbLbConstr and will be removed in a future release"
)]
pub use PbLbConstr as PBLBConstr;

impl fmt::Display for PbLbConstr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_wlit_sum!(f, self.lits);
        write!(f, " >= {}", self.b)
    }
}

impl PbLbConstr {
    /// Decomposes the constraint to a set of input literals and a lower bound
    #[must_use]
    pub fn decompose(self) -> (Vec<(Lit, usize)>, isize) {
        (self.lits, self.b)
    }

    /// Gets references to the constraints internals
    pub(crate) fn decompose_ref(&self) -> (&Vec<(Lit, usize)>, &isize) {
        (&self.lits, &self.b)
    }

    /// Checks if the constraint is always satisfied
    #[must_use]
    pub fn is_tautology(&self) -> bool {
        self.b <= 0
    }

    /// Checks if the constraint is unsatisfiable
    #[must_use]
    pub fn is_unsat(&self) -> bool {
        if self.b < 0 {
            return false;
        }
        self.b.unsigned_abs() > self.weight_sum
    }

    /// Checks if the constraint assigns all literals to true
    #[must_use]
    pub fn is_positive_assignment(&self) -> bool {
        if self.b < 0 || self.is_unsat() {
            return false;
        }
        let min_coeff: usize = self
            .lits
            .iter()
            .fold(usize::MAX, |min, (_, coeff)| std::cmp::min(min, *coeff));
        // note: self.b <= self.weight_sum is checked in is_unsat
        self.b.unsigned_abs() + min_coeff > self.weight_sum
    }

    /// Gets the unit weight of the constraint, if it exists
    #[must_use]
    pub fn find_unit_weight(&self) -> Option<usize> {
        let mut unit_weight = None;
        for (_, w) in &self.lits {
            if let Some(uw) = unit_weight {
                if uw != *w {
                    return None;
                }
            } else {
                unit_weight = Some(*w);
            }
        }
        unit_weight
    }

    /// Checks if the constraint is a clause
    #[must_use]
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
        // self.b > 0 because is not tautology
        self.b.unsigned_abs() <= min_coeff
    }
}

/// An equality pseudo-boolean constraint (`weighted sum of lits = b`)
#[derive(Eq, PartialEq, Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct PbEqConstr {
    lits: Vec<(Lit, usize)>,
    weight_sum: usize,
    b: isize,
}

#[deprecated(
    since = "0.6.0",
    note = "PBEQConstr has been renamed to PbEqConstr and will be removed in a future release"
)]
pub use PbEqConstr as PBEQConstr;

impl fmt::Display for PbEqConstr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_wlit_sum!(f, self.lits);
        write!(f, " = {}", self.b)
    }
}

impl PbEqConstr {
    /// Decomposes the constraint to a set of input literals and an equality bound
    #[must_use]
    pub fn decompose(self) -> (Vec<(Lit, usize)>, isize) {
        (self.lits, self.b)
    }

    /// Gets references to the constraints internals
    pub(crate) fn decompose_ref(&self) -> (&Vec<(Lit, usize)>, &isize) {
        (&self.lits, &self.b)
    }

    /// Checks if the constraint is unsatisfiable
    ///
    /// This only checks whether the bound is smaller than the sum of weights, not if a subset sum
    /// of the inputs exists that can satisfy the equality.
    #[must_use]
    pub fn is_unsat(&self) -> bool {
        if self.b < 0 {
            return true;
        }
        self.b.unsigned_abs() > self.weight_sum
    }

    /// Checks if the constraint assigns all literals to true
    #[must_use]
    pub fn is_positive_assignment(&self) -> bool {
        if self.b < 0 {
            return false;
        }
        self.b.unsigned_abs() == self.weight_sum
    }

    /// Checks if the constraint assigns all literals to false
    #[must_use]
    pub fn is_negative_assignment(&self) -> bool {
        if self.b < 0 {
            return false;
        }
        self.b.unsigned_abs() == 0
    }

    /// Gets the unit weight of the constraint, if it exists
    #[must_use]
    pub fn find_unit_weight(&self) -> Option<usize> {
        let mut unit_weight = None;
        for (_, w) in &self.lits {
            if let Some(uw) = unit_weight {
                if uw != *w {
                    return None;
                }
            } else {
                unit_weight = Some(*w);
            }
        }
        unit_weight
    }
}

#[cfg(test)]
mod tests {
    use super::{CardConstraint, Cl, PbConstraint};
    use crate::{
        lit,
        types::{Assignment, TernaryVal},
        var,
    };

    #[test]
    fn clause_remove() {
        let mut cl = clause![lit![0], lit![1], lit![2], lit![1]];
        assert!(!cl.remove(lit![3]));
        assert!(cl.remove(lit![1]));
        assert_eq!(cl.len(), 3);
    }

    #[test]
    fn clause_remove_thorough() {
        let mut cl = clause![lit![0], lit![1], lit![2], lit![1]];
        assert!(!cl.remove_thorough(lit![3]));
        assert!(cl.remove_thorough(lit![1]));
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
    fn clause_evaluate() {
        let cl = clause![lit![0], lit![1], lit![2]];
        assert_eq!(cl.evaluate(&assign!(0b000)), TernaryVal::False);
        assert_eq!(cl.evaluate(&assign!(0b001)), TernaryVal::True);
        assert_eq!(cl.evaluate(&assign!(0b010)), TernaryVal::True);
        assert_eq!(cl.evaluate(&assign!(0b011)), TernaryVal::True);
        assert_eq!(cl.evaluate(&assign!(0b100)), TernaryVal::True);
        assert_eq!(cl.evaluate(&assign!(0b101)), TernaryVal::True);
        assert_eq!(cl.evaluate(&assign!(0b110)), TernaryVal::True);
        assert_eq!(cl.evaluate(&assign!(0b111)), TernaryVal::True);
        assert_eq!(
            cl.evaluate(&assign!(0b000).truncate(var![1])),
            TernaryVal::DontCare
        );
    }

    #[test]
    fn clause_is_tautology() {
        assert!(!Cl::new(&[lit![0], lit![1], lit![2]]).is_tautology());
        assert!(Cl::new(&[lit![0], !lit![0], lit![2]]).is_tautology());
        assert!(Cl::new(&[!lit![2], !lit![0], lit![2]]).is_tautology());
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
        assert!(PbConstraint::new_ub(lits.clone(), 6).is_tautology());
        assert!(!PbConstraint::new_ub(lits.clone(), 5).is_tautology());
        assert!(PbConstraint::new_lb(lits.clone(), 0).is_tautology());
        assert!(!PbConstraint::new_lb(lits.clone(), 1).is_tautology());
        assert!(!PbConstraint::new_eq(lits.clone(), 2).is_tautology());
    }

    #[test]
    fn pb_is_unsat() {
        let lits = vec![(lit![0], 1), (lit![1], 2), (lit![2], 3)];
        assert!(!PbConstraint::new_ub(lits.clone(), 1).is_unsat());
        assert!(!PbConstraint::new_lb(lits.clone(), 6).is_unsat());
        assert!(PbConstraint::new_lb(lits.clone(), 7).is_unsat());
        assert!(!PbConstraint::new_eq(lits.clone(), 2).is_unsat());
        assert!(PbConstraint::new_eq(lits.clone(), 7).is_unsat());
    }

    #[test]
    fn pb_is_positive_assignment() {
        let lits = vec![(lit![0], 1), (lit![1], 2), (lit![2], 3)];
        assert!(!PbConstraint::new_ub(lits.clone(), 1).is_positive_assignment());
        assert!(PbConstraint::new_lb(lits.clone(), 6).is_positive_assignment());
        assert!(!PbConstraint::new_lb(lits.clone(), 2).is_positive_assignment());
        assert!(PbConstraint::new_eq(lits.clone(), 6).is_positive_assignment());
        assert!(!PbConstraint::new_eq(lits.clone(), 2).is_positive_assignment());
    }

    #[test]
    fn pb_is_negative_assignment() {
        let lits = vec![(lit![0], 2), (lit![1], 2), (lit![2], 3)];
        assert!(PbConstraint::new_ub(lits.clone(), 1).is_negative_assignment());
        assert!(!PbConstraint::new_ub(lits.clone(), 2).is_negative_assignment());
        assert!(!PbConstraint::new_lb(lits.clone(), 2).is_negative_assignment());
        assert!(PbConstraint::new_eq(lits.clone(), 0).is_negative_assignment());
        assert!(!PbConstraint::new_eq(lits.clone(), 1).is_negative_assignment());
    }

    #[test]
    fn pb_is_card() {
        let lits = vec![(lit![0], 2), (lit![1], 2), (lit![2], 2)];
        assert!(PbConstraint::new_ub(lits.clone(), 1).is_card());
        assert!(PbConstraint::new_lb(lits.clone(), 3).is_card());
        assert!(PbConstraint::new_eq(lits.clone(), 2).is_card());
        let lits = vec![(lit![0], 2), (lit![1], 1), (lit![2], 2)];
        assert!(!PbConstraint::new_ub(lits.clone(), 1).is_card());
        assert!(!PbConstraint::new_lb(lits.clone(), 3).is_card());
        assert!(!PbConstraint::new_eq(lits.clone(), 2).is_card());
    }

    #[test]
    fn pb_is_clause() {
        let lits = vec![(lit![0], 2), (lit![1], 3), (lit![2], 2)];
        assert!(PbConstraint::new_ub(lits.clone(), 6).is_clause());
        assert!(PbConstraint::new_lb(lits.clone(), 2).is_clause());
        assert!(!PbConstraint::new_ub(lits.clone(), 7).is_clause());
        assert!(!PbConstraint::new_ub(lits.clone(), 4).is_clause());
        assert!(!PbConstraint::new_lb(lits.clone(), 3).is_clause());
        assert!(!PbConstraint::new_eq(lits.clone(), 2).is_card());
    }
}
