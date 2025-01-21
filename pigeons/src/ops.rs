//! # Operation Types
//!
//! Types to generate sequences of operations for reverse polish notation.

use std::{
    fmt,
    num::NonZeroUsize,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign},
};

use itertools::Itertools;

use crate::{AbsConstraintId, VarLike};

use super::{Axiom, ConstraintId};

/// A sequence of operations to be added to the proof in reverse polish notation
#[derive(Clone, Debug)]
pub struct OperationSequence<V: VarLike = &'static str>(IntOpSeq<V>);

/// Internal representation of operation sequence handling special empty and singleton cases to
/// avoid unnecessary allocations
#[derive(Clone, Debug, Default)]
enum IntOpSeq<V: VarLike> {
    #[default]
    Empty,
    Singleton(Operation<V>),
    Sequence(Vec<Operation<V>>),
}

impl<V: VarLike> Extend<Operation<V>> for IntOpSeq<V> {
    fn extend<T: IntoIterator<Item = Operation<V>>>(&mut self, iter: T) {
        let mut iter = iter.into_iter();
        let hint = iter.size_hint();
        if hint.0 > 1 {
            let seq: Vec<_> = match std::mem::take(self) {
                IntOpSeq::Empty => iter.collect(),
                IntOpSeq::Singleton(op) => [op].into_iter().chain(iter).collect(),
                IntOpSeq::Sequence(mut seq) => {
                    seq.extend(iter);
                    seq
                }
            };
            *self = IntOpSeq::Sequence(seq);
            return;
        }
        if matches!(hint.1, Some(1)) {
            let Some(next) = iter.next() else {
                return;
            };
            debug_assert!(iter.next().is_none());
            *self = match std::mem::take(self) {
                IntOpSeq::Empty => IntOpSeq::Singleton(next),
                IntOpSeq::Singleton(other) => IntOpSeq::Sequence(vec![other, next]),
                IntOpSeq::Sequence(mut seq) => {
                    seq.push(next);
                    IntOpSeq::Sequence(seq)
                }
            };
            return;
        }
        let seq: Vec<_> = match std::mem::take(self) {
            IntOpSeq::Empty => iter.collect(),
            IntOpSeq::Singleton(op) => [op].into_iter().chain(iter).collect(),
            IntOpSeq::Sequence(mut seq) => {
                seq.extend(iter);
                seq
            }
        };
        *self = match seq.len() {
            0 => IntOpSeq::Empty,
            1 => IntOpSeq::Singleton(seq[0]),
            _ => IntOpSeq::Sequence(seq),
        };
    }
}

impl<V: VarLike> IntoIterator for IntOpSeq<V> {
    type Item = Operation<V>;

    type IntoIter = OpSeqIter<V>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            IntOpSeq::Empty => OpSeqIter::One(None),
            IntOpSeq::Singleton(op) => OpSeqIter::One(Some(op)),
            IntOpSeq::Sequence(seq) => OpSeqIter::More(seq.into_iter()),
        }
    }
}

enum OpSeqIter<V: VarLike> {
    One(Option<Operation<V>>),
    More(std::vec::IntoIter<Operation<V>>),
}

impl<V: VarLike> Iterator for OpSeqIter<V> {
    type Item = Operation<V>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            OpSeqIter::One(opt) => opt.take(),
            OpSeqIter::More(seq) => seq.next(),
        }
    }
}

impl<V: VarLike> OperationSequence<V> {
    /// Crates an empty operation sequence
    ///
    /// **Note**: Trying to write an empty operation sequence will panic
    #[must_use]
    pub fn empty() -> Self {
        OperationSequence(IntOpSeq::Empty)
    }

    /// Checks whether the operation sequence is empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        matches!(self.0, IntOpSeq::Empty)
    }

    fn push(&mut self, op: Operation<V>) {
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

impl<V: VarLike> OperationLike<V> for OperationSequence<V> {
    #[must_use]
    fn saturate(mut self) -> Self {
        if !self.is_empty() {
            self.push(Operation::Sat);
        }
        self
    }

    #[must_use]
    fn weaken(mut self) -> Self {
        if !self.is_empty() {
            self.push(Operation::Weak);
        }
        self
    }
}

impl<V: VarLike> From<Operation<V>> for OperationSequence<V> {
    fn from(value: Operation<V>) -> Self {
        OperationSequence(IntOpSeq::Singleton(value))
    }
}

impl<V: VarLike> fmt::Display for OperationSequence<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            IntOpSeq::Empty => panic!("cannot write empty operation sequence"),
            IntOpSeq::Singleton(op) => write!(f, "{op}"),
            IntOpSeq::Sequence(seq) => write!(f, "{}", seq.iter().format(" ")),
        }
    }
}

impl<V: VarLike> Mul<usize> for OperationSequence<V> {
    type Output = OperationSequence<V>;

    fn mul(mut self, rhs: usize) -> Self::Output {
        if rhs == 0 {
            return OperationSequence::empty();
        }
        if !self.is_empty() && rhs > 1 {
            self.push(Operation::Mult(
                rhs.try_into().expect("cannot multiply by zero"),
            ));
        }
        self
    }
}

impl<V: VarLike> MulAssign<usize> for OperationSequence<V> {
    fn mul_assign(&mut self, rhs: usize) {
        if rhs == 0 {
            *self = OperationSequence::empty();
            return;
        }
        if !self.is_empty() && rhs > 1 {
            self.push(Operation::Mult(
                rhs.try_into().expect("cannot multiply by zero"),
            ));
        }
    }
}

impl<V: VarLike> Mul<OperationSequence<V>> for usize {
    type Output = OperationSequence<V>;

    fn mul(self, rhs: OperationSequence<V>) -> Self::Output {
        rhs * self
    }
}

impl<V: VarLike> Div<usize> for OperationSequence<V> {
    type Output = OperationSequence<V>;

    fn div(mut self, rhs: usize) -> Self::Output {
        if !self.is_empty() {
            self.push(Operation::Div(
                rhs.try_into().expect("cannot divide by zero"),
            ));
        }
        self
    }
}

impl<V: VarLike> DivAssign<usize> for OperationSequence<V> {
    fn div_assign(&mut self, rhs: usize) {
        if !self.is_empty() {
            self.push(Operation::Div(
                rhs.try_into().expect("cannot divide by zero"),
            ));
        }
    }
}

/// A sequence of operations to be added to the proof in reverse polish notation
#[derive(Clone, Copy, Debug)]
pub(crate) enum Operation<V: VarLike> {
    /// A trivial identity operation to get a constraint from its [`ConstraintId`]
    Id(ConstraintId),
    /// A (possibly negated) literal axiom
    Axiom(Axiom<V>),
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

impl<V: VarLike> From<ConstraintId> for Operation<V> {
    fn from(value: ConstraintId) -> Self {
        Operation::Id(value)
    }
}

impl<V: VarLike> From<Axiom<V>> for Operation<V> {
    fn from(value: Axiom<V>) -> Self {
        Operation::Axiom(value)
    }
}

impl<V: VarLike> fmt::Display for Operation<V> {
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
pub trait OperationLike<V: VarLike>:
    Into<OperationSequence<V>>
    + Add<OperationSequence<V>, Output = OperationSequence<V>>
    + Add<ConstraintId, Output = OperationSequence<V>>
    + Add<AbsConstraintId, Output = OperationSequence<V>>
    + Add<Axiom<V>, Output = OperationSequence<V>>
    + Mul<usize, Output = OperationSequence<V>>
    + Div<usize, Output = OperationSequence<V>>
{
    /// Applies saturation
    #[must_use]
    fn saturate(self) -> OperationSequence<V> {
        Into::<OperationSequence<V>>::into(self).saturate()
    }
    /// Applies weakening
    #[must_use]
    fn weaken(self) -> OperationSequence<V> {
        Into::<OperationSequence<V>>::into(self).weaken()
    }
}

impl<V: VarLike, O: Into<OperationSequence<V>>> Add<O> for OperationSequence<V> {
    type Output = OperationSequence<V>;

    fn add(mut self, rhs: O) -> Self::Output {
        let rhs = Into::<OperationSequence<V>>::into(rhs);
        if self.is_empty() {
            return rhs;
        }
        if rhs.is_empty() {
            return self;
        }
        self.0.extend(rhs.0);
        self.push(Operation::Add);
        self
    }
}

impl<V: VarLike, O: Into<OperationSequence<V>>> AddAssign<O> for OperationSequence<V> {
    fn add_assign(&mut self, rhs: O) {
        let rhs = Into::<OperationSequence<V>>::into(rhs);
        let was_empty = self.is_empty();
        if rhs.is_empty() {
            return;
        }
        self.0.extend(rhs.0);
        if was_empty {
            return;
        }
        self.push(Operation::Add);
    }
}

impl<V: VarLike> From<ConstraintId> for OperationSequence<V> {
    fn from(value: ConstraintId) -> Self {
        Into::<Operation<V>>::into(value).into()
    }
}

impl<V: VarLike> Add<OperationSequence<V>> for ConstraintId {
    type Output = OperationSequence<V>;

    fn add(self, rhs: OperationSequence<V>) -> Self::Output {
        Into::<OperationSequence<V>>::into(self) + rhs
    }
}

impl<V: VarLike> Add<Axiom<V>> for ConstraintId {
    type Output = OperationSequence<V>;

    fn add(self, rhs: Axiom<V>) -> Self::Output {
        Into::<OperationSequence<V>>::into(self) + Into::<OperationSequence<V>>::into(rhs)
    }
}

impl<V: VarLike> From<AbsConstraintId> for OperationSequence<V> {
    fn from(value: AbsConstraintId) -> Self {
        Into::<ConstraintId>::into(value).into()
    }
}

impl<V: VarLike> Add<OperationSequence<V>> for AbsConstraintId {
    type Output = OperationSequence<V>;

    fn add(self, rhs: OperationSequence<V>) -> Self::Output {
        Into::<OperationSequence<V>>::into(self) + rhs
    }
}

impl<V: VarLike> Add<Axiom<V>> for AbsConstraintId {
    type Output = OperationSequence<V>;

    fn add(self, rhs: Axiom<V>) -> Self::Output {
        Into::<OperationSequence<V>>::into(self) + Into::<OperationSequence<V>>::into(rhs)
    }
}

impl<V: VarLike> OperationLike<V> for Axiom<V> {}

impl<V: VarLike> From<Axiom<V>> for OperationSequence<V> {
    fn from(value: Axiom<V>) -> Self {
        Into::<Operation<V>>::into(value).into()
    }
}

impl<V: VarLike> Add<OperationSequence<V>> for Axiom<V> {
    type Output = OperationSequence<V>;

    fn add(self, rhs: OperationSequence<V>) -> Self::Output {
        Into::<OperationSequence<V>>::into(self) + rhs
    }
}

impl<V: VarLike> Add<ConstraintId> for Axiom<V> {
    type Output = OperationSequence<V>;

    fn add(self, rhs: ConstraintId) -> Self::Output {
        Into::<OperationSequence<V>>::into(self) + Into::<OperationSequence<V>>::into(rhs)
    }
}

impl<V: VarLike> Add<AbsConstraintId> for Axiom<V> {
    type Output = OperationSequence<V>;

    fn add(self, rhs: AbsConstraintId) -> Self::Output {
        Into::<OperationSequence<V>>::into(self) + Into::<OperationSequence<V>>::into(rhs)
    }
}

impl<V: VarLike> Add<Axiom<V>> for Axiom<V> {
    type Output = OperationSequence<V>;

    fn add(self, rhs: Axiom<V>) -> Self::Output {
        Into::<OperationSequence<V>>::into(self) + Into::<OperationSequence<V>>::into(rhs)
    }
}

impl<V: VarLike> Mul<usize> for Axiom<V> {
    type Output = OperationSequence<V>;

    fn mul(self, rhs: usize) -> Self::Output {
        Into::<OperationSequence<V>>::into(self) * rhs
    }
}

impl<V: VarLike> Div<usize> for Axiom<V> {
    type Output = OperationSequence<V>;

    fn div(self, rhs: usize) -> Self::Output {
        Into::<OperationSequence<V>>::into(self) / rhs
    }
}

#[cfg(test)]
mod tests {
    use super::OperationLike;
    use crate::{ConstraintId as Id, OperationSequence, VarLike};

    macro_rules! seq {
        ($id:expr) => {
            OperationSequence::<&'static str>::from($id)
        };
    }

    #[test]
    fn constr_add() {
        let add = seq!(Id::abs(42)) + Id::abs(45);
        assert_eq!(&format!("{add}"), "42 45 +");
    }

    #[test]
    fn constr_mult() {
        let mult = seq!(Id::abs(42)) * 5;
        assert_eq!(&format!("{mult}"), "42 5 *");
    }

    #[test]
    fn constr_div() {
        let mult = seq!(Id::abs(42)) / 5;
        assert_eq!(&format!("{mult}"), "42 5 d");
    }

    #[test]
    fn constr_saturate() {
        let mult = seq!(Id::abs(42)).saturate();
        assert_eq!(&format!("{mult}"), "42 s");
    }

    #[test]
    fn constr_weaken() {
        let mult = seq!(Id::abs(42)).weaken();
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
        let seq = (seq!(Id::abs(42)) * 3 + Id::abs(43)).saturate() / 2;
        assert_eq!(&format!("{seq}"), "42 3 * 43 + s 2 d");
    }
}
