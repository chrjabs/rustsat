//! # Operation Types
//!
//! Types to generate sequences of operations for reverse polish notation.

use std::{
    fmt,
    num::NonZeroUsize,
    ops::{Add, Div, Mul},
};

use itertools::Itertools;

use crate::AbsConstraintId;

use super::{Axiom, ConstraintId};

/// A sequence of operations to be added to the proof in reverse polish notation
#[derive(Clone, Debug)]
pub struct OperationSequence(IntOpSeq);

/// Internal representation of operation sequence handling special empty and singleton cases to
/// avoid unnecessary allocations
#[derive(Clone, Debug, Default)]
enum IntOpSeq {
    #[default]
    Empty,
    Singleton(Operation),
    Sequence(Vec<Operation>),
}

impl Extend<Operation> for IntOpSeq {
    fn extend<T: IntoIterator<Item = Operation>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        if iter.size_hint().0 > 1 {
            let seq: Vec<_> = match std::mem::take(self) {
                IntOpSeq::Empty => iter.collect(),
                IntOpSeq::Singleton(op) => [op].into_iter().chain(iter).collect(),
                IntOpSeq::Sequence(mut seq) => {
                    seq.extend(iter);
                    seq
                }
            };
            *self = IntOpSeq::Sequence(seq);
        } else {
            todo!()
        }
    }
}

impl IntoIterator for IntOpSeq {
    type Item = Operation;

    type IntoIter = OpSeqIter;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            IntOpSeq::Empty => OpSeqIter::One(None),
            IntOpSeq::Singleton(op) => OpSeqIter::One(Some(op)),
            IntOpSeq::Sequence(seq) => OpSeqIter::More(seq.into_iter()),
        }
    }
}

enum OpSeqIter {
    One(Option<Operation>),
    More(std::vec::IntoIter<Operation>),
}

impl Iterator for OpSeqIter {
    type Item = Operation;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            OpSeqIter::One(opt) => opt.take(),
            OpSeqIter::More(seq) => seq.next(),
        }
    }
}

impl OperationSequence {
    /// Crates an empty operation sequence
    ///
    /// **Note**: Trying to write an empty operation sequence will panic
    #[must_use]
    pub fn empty() -> OperationSequence {
        OperationSequence(IntOpSeq::Empty)
    }

    /// Checks whether the operation sequence is empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        matches!(self.0, IntOpSeq::Empty)
    }

    fn push(&mut self, op: Operation) {
        self.0 = match std::mem::take(&mut self.0) {
            IntOpSeq::Empty => IntOpSeq::Singleton(op),
            IntOpSeq::Singleton(op1) => IntOpSeq::Sequence(vec![op1, op]),
            IntOpSeq::Sequence(mut seq) => {
                seq.push(op);
                IntOpSeq::Sequence(seq)
            }
        }
    }
}

impl OperationLike for OperationSequence {
    #[must_use]
    fn saturate(mut self) -> OperationSequence {
        if !self.is_empty() {
            self.push(Operation::Sat);
        }
        self
    }

    #[must_use]
    fn weaken(mut self) -> OperationSequence {
        if !self.is_empty() {
            self.push(Operation::Weak);
        }
        self
    }
}

impl From<Operation> for OperationSequence {
    fn from(value: Operation) -> Self {
        OperationSequence(IntOpSeq::Singleton(value))
    }
}

impl fmt::Display for OperationSequence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            IntOpSeq::Empty => panic!("cannot write empty operation sequence"),
            IntOpSeq::Singleton(op) => write!(f, "{op}"),
            IntOpSeq::Sequence(seq) => write!(f, "{}", seq.iter().format(" ")),
        }
    }
}

impl Mul<usize> for OperationSequence {
    type Output = OperationSequence;

    fn mul(mut self, rhs: usize) -> Self::Output {
        if !self.is_empty() {
            self.push(Operation::Mult(
                rhs.try_into().expect("cannot multiply by zero"),
            ));
        }
        self
    }
}

impl Mul<OperationSequence> for usize {
    type Output = OperationSequence;

    fn mul(self, rhs: OperationSequence) -> Self::Output {
        rhs * self
    }
}

impl Div<usize> for OperationSequence {
    type Output = OperationSequence;

    fn div(mut self, rhs: usize) -> Self::Output {
        if !self.is_empty() {
            self.push(Operation::Div(
                rhs.try_into().expect("cannot divide by zero"),
            ));
        }
        self
    }
}

/// A sequence of operations to be added to the proof in reverse polish notation
#[derive(Clone, Debug)]
pub(crate) enum Operation {
    /// A trivial identity operation to get a constraint from its [`ConstraintId`]
    Id(ConstraintId),
    /// A (possibly negated) literal axiom
    Axiom(Axiom),
    /// A negative literal axiom
    /// An addition operation over two constraints
    Add,
    /// A constant multiplication operation
    Mult(NonZeroUsize),
    /// A constant division operation
    Div(NonZeroUsize),
    /// A boolean saturation operation
    Sat,
    /// A weakening operation
    Weak,
}

impl From<ConstraintId> for Operation {
    fn from(value: ConstraintId) -> Self {
        Operation::Id(value)
    }
}

impl From<Axiom> for Operation {
    fn from(value: Axiom) -> Self {
        Operation::Axiom(value)
    }
}

impl fmt::Display for Operation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operation::Id(id) => write!(f, "{id}"),
            Operation::Axiom(ax) => write!(f, "{ax}"),
            Operation::Add => write!(f, "+"),
            Operation::Mult(fact) => write!(f, "{fact} *"),
            Operation::Div(div) => write!(f, "{div} d"),
            Operation::Sat => write!(f, "s"),
            Operation::Weak => write!(f, "w"),
        }
    }
}

/// A trait implemented by all types intended to be used in building an [`OperationSequence`]
pub trait OperationLike:
    Into<OperationSequence>
    + Add<OperationSequence, Output = OperationSequence>
    + Add<ConstraintId, Output = OperationSequence>
    + Add<AbsConstraintId, Output = OperationSequence>
    + Add<Axiom, Output = OperationSequence>
    + Mul<usize, Output = OperationSequence>
    + Div<usize, Output = OperationSequence>
{
    /// Applies saturation
    #[must_use]
    fn saturate(self) -> OperationSequence {
        Into::<OperationSequence>::into(self).saturate()
    }
    /// Applies weakening
    #[must_use]
    fn weaken(self) -> OperationSequence {
        Into::<OperationSequence>::into(self).weaken()
    }
}

impl<O: OperationLike> Add<O> for OperationSequence {
    type Output = OperationSequence;

    fn add(mut self, rhs: O) -> Self::Output {
        let rhs = Into::<OperationSequence>::into(rhs);
        if !self.is_empty() && !rhs.is_empty() {
            self.0.extend(rhs.0);
            self.push(Operation::Add);
        }
        self
    }
}

impl OperationLike for ConstraintId {}

impl From<ConstraintId> for OperationSequence {
    fn from(value: ConstraintId) -> Self {
        Into::<Operation>::into(value).into()
    }
}

impl Add<OperationSequence> for ConstraintId {
    type Output = OperationSequence;

    fn add(self, rhs: OperationSequence) -> Self::Output {
        Into::<OperationSequence>::into(self) + rhs
    }
}

impl Add<ConstraintId> for ConstraintId {
    type Output = OperationSequence;

    fn add(self, rhs: ConstraintId) -> Self::Output {
        Into::<OperationSequence>::into(self) + Into::<OperationSequence>::into(rhs)
    }
}

impl Add<AbsConstraintId> for ConstraintId {
    type Output = OperationSequence;

    fn add(self, rhs: AbsConstraintId) -> Self::Output {
        Into::<OperationSequence>::into(self) + Into::<OperationSequence>::into(rhs)
    }
}

impl Add<Axiom> for ConstraintId {
    type Output = OperationSequence;

    fn add(self, rhs: Axiom) -> Self::Output {
        Into::<OperationSequence>::into(self) + Into::<OperationSequence>::into(rhs)
    }
}

impl Mul<usize> for ConstraintId {
    type Output = OperationSequence;

    fn mul(self, rhs: usize) -> Self::Output {
        Into::<OperationSequence>::into(self) * rhs
    }
}

impl Div<usize> for ConstraintId {
    type Output = OperationSequence;

    fn div(self, rhs: usize) -> Self::Output {
        Into::<OperationSequence>::into(self) / rhs
    }
}

impl OperationLike for AbsConstraintId {}

impl From<AbsConstraintId> for OperationSequence {
    fn from(value: AbsConstraintId) -> Self {
        Into::<ConstraintId>::into(value).into()
    }
}

impl Add<OperationSequence> for AbsConstraintId {
    type Output = OperationSequence;

    fn add(self, rhs: OperationSequence) -> Self::Output {
        Into::<OperationSequence>::into(self) + rhs
    }
}

impl Add<ConstraintId> for AbsConstraintId {
    type Output = OperationSequence;

    fn add(self, rhs: ConstraintId) -> Self::Output {
        Into::<OperationSequence>::into(self) + Into::<OperationSequence>::into(rhs)
    }
}

impl Add<AbsConstraintId> for AbsConstraintId {
    type Output = OperationSequence;

    fn add(self, rhs: AbsConstraintId) -> Self::Output {
        Into::<OperationSequence>::into(self) + Into::<OperationSequence>::into(rhs)
    }
}

impl Add<Axiom> for AbsConstraintId {
    type Output = OperationSequence;

    fn add(self, rhs: Axiom) -> Self::Output {
        Into::<OperationSequence>::into(self) + Into::<OperationSequence>::into(rhs)
    }
}

impl Mul<usize> for AbsConstraintId {
    type Output = OperationSequence;

    fn mul(self, rhs: usize) -> Self::Output {
        Into::<OperationSequence>::into(self) * rhs
    }
}

impl Div<usize> for AbsConstraintId {
    type Output = OperationSequence;

    fn div(self, rhs: usize) -> Self::Output {
        Into::<OperationSequence>::into(self) / rhs
    }
}

impl OperationLike for Axiom {}

impl From<Axiom> for OperationSequence {
    fn from(value: Axiom) -> Self {
        Into::<Operation>::into(value).into()
    }
}

impl Add<OperationSequence> for Axiom {
    type Output = OperationSequence;

    fn add(self, rhs: OperationSequence) -> Self::Output {
        Into::<OperationSequence>::into(self) + rhs
    }
}

impl Add<ConstraintId> for Axiom {
    type Output = OperationSequence;

    fn add(self, rhs: ConstraintId) -> Self::Output {
        Into::<OperationSequence>::into(self) + Into::<OperationSequence>::into(rhs)
    }
}

impl Add<AbsConstraintId> for Axiom {
    type Output = OperationSequence;

    fn add(self, rhs: AbsConstraintId) -> Self::Output {
        Into::<OperationSequence>::into(self) + Into::<OperationSequence>::into(rhs)
    }
}

impl Add<Axiom> for Axiom {
    type Output = OperationSequence;

    fn add(self, rhs: Axiom) -> Self::Output {
        Into::<OperationSequence>::into(self) + Into::<OperationSequence>::into(rhs)
    }
}

impl Mul<usize> for Axiom {
    type Output = OperationSequence;

    fn mul(self, rhs: usize) -> Self::Output {
        Into::<OperationSequence>::into(self) * rhs
    }
}

impl Div<usize> for Axiom {
    type Output = OperationSequence;

    fn div(self, rhs: usize) -> Self::Output {
        Into::<OperationSequence>::into(self) / rhs
    }
}

#[cfg(test)]
mod tests {
    use super::OperationLike;
    use crate::{ConstraintId as Id, VarLike};

    #[test]
    fn constr_add() {
        let add = Id::abs(42) + Id::abs(45);
        assert_eq!(&format!("{add}"), "42 45 +");
    }

    #[test]
    fn constr_mult() {
        let mult = Id::abs(42) * 5;
        assert_eq!(&format!("{mult}"), "42 5 *");
    }

    #[test]
    fn constr_div() {
        let mult = Id::abs(42) / 5;
        assert_eq!(&format!("{mult}"), "42 5 d");
    }

    #[test]
    fn constr_saturate() {
        let mult = Id::abs(42).saturate();
        assert_eq!(&format!("{mult}"), "42 s");
    }

    #[test]
    fn constr_weaken() {
        let mult = Id::abs(42).weaken();
        assert_eq!(&format!("{mult}"), "42 w");
    }

    #[test]
    fn constr_add_axiom() {
        let var = "x5";
        let add = Id::abs(42) + var.pos_axiom();
        assert_eq!(&format!("{add}"), "42 x5 +");
        let add = Id::abs(42) + var.neg_axiom();
        assert_eq!(&format!("{add}"), "42 ~x5 +");
    }

    #[test]
    fn sequence() {
        let seq = (Id::abs(42) * 3 + Id::abs(43)).saturate() / 2;
        assert_eq!(&format!("{seq}"), "42 3 * 43 + s 2 d");
    }
}
