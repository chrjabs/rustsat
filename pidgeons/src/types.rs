//! # Most Types of the Library

use std::{fmt, num::NonZeroUsize, ops::Range};

use itertools::Itertools;

use super::{unreachable_err, ConstraintLike, ObjectiveLike};

/// The proof problem type
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum ProblemType {
    /// Problem type is unknown
    #[default]
    Unknown,
    /// An optimization problem
    Optimization,
}

/// Different options to refer to a constraint
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ConstraintId(ConstrIdInternal);

impl From<ConstrIdInternal> for ConstraintId {
    fn from(value: ConstrIdInternal) -> Self {
        ConstraintId(value)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum ConstrIdInternal {
    /// An abosulte ID
    Abs(AbsConstraintId),
    /// A relative ID
    Rel(RelConstraintId),
}

impl ConstraintId {
    /// Gets an absolute constraint ID with a given value
    ///
    /// # Panics
    ///
    /// If `x` is zero.
    #[must_use]
    pub fn abs(x: usize) -> ConstraintId {
        ConstrIdInternal::Abs(AbsConstraintId(
            x.try_into().expect("constraint ID cannot be zero"),
        ))
        .into()
    }

    /// Gets a relative constraint ID to the x-last constraint
    ///
    /// # Panics
    ///
    /// If `x` is zero.
    #[must_use]
    pub fn last(x: usize) -> ConstraintId {
        ConstrIdInternal::Rel(RelConstraintId(
            x.try_into().expect("constraint ID cannot be zero"),
        ))
        .into()
    }

    /// Makes a (potentially relative) constraint ID absolute
    #[must_use]
    pub fn make_absolute(self, next_free: AbsConstraintId) -> Self {
        if let ConstraintId(ConstrIdInternal::Rel(id)) = self {
            return ConstrIdInternal::Abs(id.make_absolute(next_free)).into();
        }
        self
    }

    #[must_use]
    pub(crate) fn increment(self, next_free: AbsConstraintId) -> Self {
        match self.0 {
            ConstrIdInternal::Abs(id) => ConstrIdInternal::Abs(AbsConstraintId(unreachable_err!(
                (usize::from(id.0) + 1).try_into()
            )))
            .into(),
            ConstrIdInternal::Rel(id) => {
                let rel = usize::from(id.0);
                if rel == 1 {
                    return ConstrIdInternal::Abs(next_free).into();
                }
                ConstrIdInternal::Rel(RelConstraintId(unreachable_err!((rel - 1).try_into())))
                    .into()
            }
        }
    }

    #[must_use]
    pub(crate) fn less(self, rhs: ConstraintId, next_free: AbsConstraintId) -> bool {
        let rhs = match rhs.0 {
            ConstrIdInternal::Abs(id) => id.0,
            ConstrIdInternal::Rel(id) => id.make_absolute(next_free).0,
        };
        let lhs = match self.0 {
            ConstrIdInternal::Abs(id) => id.0,
            ConstrIdInternal::Rel(id) => id.make_absolute(next_free).0,
        };
        lhs < rhs
    }
}

impl fmt::Display for ConstraintId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            ConstrIdInternal::Abs(id) => write!(f, "{id}"),
            ConstrIdInternal::Rel(id) => write!(f, "{id}"),
        }
    }
}

impl From<AbsConstraintId> for ConstraintId {
    fn from(value: AbsConstraintId) -> Self {
        ConstrIdInternal::Abs(value).into()
    }
}

impl From<RelConstraintId> for ConstraintId {
    fn from(value: RelConstraintId) -> Self {
        ConstrIdInternal::Rel(value).into()
    }
}

/// A type representing a VeriPB constraint ID
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct AbsConstraintId(pub(crate) NonZeroUsize);

impl Default for AbsConstraintId {
    fn default() -> Self {
        Self(unreachable_err!(1.try_into()))
    }
}

impl fmt::Display for AbsConstraintId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A constraint ID of the x-last constraint. Equivalent to a negative constraint ID in VeriPB.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct RelConstraintId(pub(crate) NonZeroUsize);

impl RelConstraintId {
    /// Makes a (potentially relative) constraint ID absolute
    ///
    /// # Panics
    ///
    /// If the relative ID is larger than the number of used constraints.
    #[must_use]
    pub fn make_absolute(self, next_free: AbsConstraintId) -> AbsConstraintId {
        AbsConstraintId(
            TryInto::<NonZeroUsize>::try_into(usize::from(next_free.0) - usize::from(self.0))
                .expect("relative ID higher than used IDs"),
        )
    }
}

impl fmt::Display for RelConstraintId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "-{}", self.0)
    }
}

/// An axiom or literal
#[derive(Clone, Debug)]
pub struct Axiom {
    /// Whether the axiom/literal is negated
    pub(crate) neg: bool,
    /// The variable, represented as a string
    pub(crate) var: String,
}

impl fmt::Display for Axiom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", if self.neg { "~" } else { "" }, self.var)
    }
}

impl ConstraintLike for Axiom {
    fn constr_str(&self) -> String {
        format!("{self} >= 1")
    }
}

/// A substitution of a variable to a value or a literal
pub struct Substitution {
    /// The variable to substitute
    pub(crate) var: String,
    /// What to substitute with
    pub(crate) sub: SubstituteWith,
}

impl fmt::Display for Substitution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} -> {}", self.var, self.sub)
    }
}

/// What to substitute a variable with
pub enum SubstituteWith {
    /// Fix true value
    True,
    /// Fix false value
    False,
    /// Substitute variable with literal
    Lit(Axiom),
}

impl From<bool> for SubstituteWith {
    fn from(value: bool) -> Self {
        if value {
            SubstituteWith::True
        } else {
            SubstituteWith::False
        }
    }
}

impl fmt::Display for SubstituteWith {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SubstituteWith::True => write!(f, "1"),
            SubstituteWith::False => write!(f, "0"),
            SubstituteWith::Lit(lit) => write!(f, "{lit}"),
        }
    }
}

/// A subproof
pub struct SubProof {
    /// The sequence of [`ProofGoal`] in the subproof
    goals: Vec<ProofGoal>,
}

impl fmt::Display for SubProof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "begin")?;
        for goal in &self.goals {
            writeln!(f, "{goal}")?;
        }
        write!(f, "end")
    }
}

/// A proof target of a [`SubProof`]
pub struct ProofGoal {
    /// The goal id
    id: ProofGoalId,
}

impl fmt::Display for ProofGoal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "  proofgoal {}", self.id)?;
        todo!();
        write!(f, "  qed -1")
    }
}

/// A [`ProofGoal`] ID
pub enum ProofGoalId {
    /// A [`ProofGoal`] for a constraint
    Constraint(ConstraintId),
    /// A specified proof goal ID
    Specific(NonZeroUsize),
}

impl fmt::Display for ProofGoalId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProofGoalId::Constraint(id) => writeln!(f, "{id}"),
            ProofGoalId::Specific(id) => writeln!(f, "#{id}"),
        }
    }
}

/// An objective update step (`obju`)
pub enum ObjectiveUpdate {
    /// `new`
    New(String, Option<SubProof>),
    /// `diff`
    Diff(String),
}

impl ObjectiveUpdate {
    /// Creates an explicit objective update by specifying the entire new objective
    pub fn new<O: ObjectiveLike>(objective: &O, subproof: Option<SubProof>) -> ObjectiveUpdate {
        ObjectiveUpdate::New(objective.obj_str(), subproof)
    }

    /// Creates an objective update by specifying the difference to the old objective
    pub fn diff<O: ObjectiveLike>(diff: &O) -> ObjectiveUpdate {
        ObjectiveUpdate::Diff(diff.obj_str())
    }
}

impl fmt::Display for ObjectiveUpdate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ObjectiveUpdate::New(obj, subproof) => {
                write!(f, "new {obj} ;")?;
                if let Some(subproof) = subproof {
                    write!(f, " {subproof}")?;
                }
                Ok(())
            }
            ObjectiveUpdate::Diff(obj) => write!(f, "diff {obj} ;"),
        }
    }
}

/// Possible output guarantees for the output section
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OutputGuarantee {
    /// No guarantee
    None,
    /// All constraints are derivable
    Derivable(OutputType),
    /// The constraints are equisatisfiable
    Equisatisfiable(OutputType),
    /// The constraints are equiptimal
    Equioptimal(OutputType),
}

impl fmt::Display for OutputGuarantee {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OutputGuarantee::None => write!(f, "NONE"),
            OutputGuarantee::Derivable(t) => write!(f, "DERIVABLE {t}"),
            OutputGuarantee::Equisatisfiable(t) => write!(f, "EQUISATISFIABLE {t}"),
            OutputGuarantee::Equioptimal(t) => write!(f, "EQUIOPTIMAL {t}"),
        }
    }
}

/// Possible output types for the output section
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OutputType {
    /// Implicit output
    Implicit,
    /// File output
    File,
}

impl fmt::Display for OutputType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OutputType::Implicit => write!(f, "IMPLICIT"),
            OutputType::File => write!(f, "FILE"),
        }
    }
}

/// Possible conclusions
pub enum Conclusion {
    /// No conclusion
    None,
    /// Satisfiability
    Sat(Option<Vec<Axiom>>),
    /// Unsatisfiability
    Unsat(Option<ConstraintId>),
    /// Bounds
    Bounds(BoundsConclusion),
}

impl fmt::Display for Conclusion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Conclusion::None => write!(f, "NONE"),
            Conclusion::Sat(sol) => {
                if let Some(sol) = sol {
                    write!(f, "SAT : {}", sol.iter().format(" "))
                } else {
                    write!(f, "SAT")
                }
            }
            Conclusion::Unsat(id) => {
                if let Some(id) = id {
                    write!(f, "UNSAT : {id}")
                } else {
                    write!(f, "UNSAT")
                }
            }
            Conclusion::Bounds(dat) => {
                write!(f, "BOUNDS {}", dat.range.start)?;
                if let Some(id) = dat.lb_id {
                    write!(f, " : {id}")?;
                }
                write!(f, " {}", dat.range.end)?;
                if let Some(sol) = &dat.ub_sol {
                    write!(f, " : {}", sol.iter().format(" "))?;
                }
                Ok(())
            }
        }
    }
}

pub struct BoundsConclusion {
    pub(crate) range: Range<usize>,
    pub(crate) lb_id: Option<ConstraintId>,
    pub(crate) ub_sol: Option<Vec<Axiom>>,
}
