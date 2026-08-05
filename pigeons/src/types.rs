//! # Most Types of the Library

use std::num::NonZeroUsize;

use itertools::Itertools;

#[allow(clippy::wildcard_imports)]
use crate::keywords::*;
use crate::ConstraintLike;
use crate::ObjectiveLike;
use crate::VarLike;

/// The proof problem type
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ProblemType {
    /// Problem type is unknown
    #[default]
    Unknown,
    /// An optimization problem
    Optimization,
}

/// A constraint ID referring to a constraint
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[repr(transparent)]
pub struct ConstraintId(ConstrIdInternal);

impl From<ConstrIdInternal> for ConstraintId {
    fn from(value: ConstrIdInternal) -> Self {
        ConstraintId(value)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
enum ConstrIdInternal {
    /// An absolute ID
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
        AbsConstraintId::new(x).into()
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
            ConstrIdInternal::Abs(id) => ConstrIdInternal::Abs(AbsConstraintId(
                crate::unreachable_err!((usize::from(id.0) + 1).try_into()),
            ))
            .into(),
            ConstrIdInternal::Rel(id) => {
                let rel = usize::from(id.0);
                if rel == 1 {
                    return ConstrIdInternal::Abs(next_free).into();
                }
                ConstrIdInternal::Rel(RelConstraintId(crate::unreachable_err!(
                    (rel - 1).try_into()
                )))
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

impl std::fmt::Display for ConstraintId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[repr(transparent)]
pub struct AbsConstraintId(pub(crate) NonZeroUsize);

impl AbsConstraintId {
    /// Creates a new absolute constraint ID
    ///
    /// # Panics
    ///
    /// If `id` is zero
    #[must_use]
    pub fn new(id: usize) -> Self {
        AbsConstraintId(NonZeroUsize::new(id).expect("ID needs to be non-zero"))
    }
}

impl Default for AbsConstraintId {
    fn default() -> Self {
        Self(crate::unreachable_err!(1.try_into()))
    }
}

impl std::fmt::Display for AbsConstraintId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::ops::Add<usize> for AbsConstraintId {
    type Output = AbsConstraintId;

    fn add(self, rhs: usize) -> Self::Output {
        AbsConstraintId(crate::unreachable_err!(std::num::NonZeroUsize::try_from(
            usize::from(self.0) + rhs
        )))
    }
}

impl std::ops::AddAssign<usize> for AbsConstraintId {
    fn add_assign(&mut self, rhs: usize) {
        self.0 =
            crate::unreachable_err!(std::num::NonZeroUsize::try_from(usize::from(self.0) + rhs));
    }
}

/// A constraint ID of the x-last constraint. Equivalent to a negative constraint ID in VeriPB.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[repr(transparent)]
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

impl std::fmt::Display for RelConstraintId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "-{}", self.0)
    }
}

/// A variable that is only present in the proof
///
/// These variables format to `pv<idx>`
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ProofOnlyVar(pub(crate) u32);

impl std::fmt::Display for ProofOnlyVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "pv{}", self.0)
    }
}

impl VarLike for ProofOnlyVar {
    type Formatter = Self;
}

impl std::ops::Add<u32> for ProofOnlyVar {
    type Output = ProofOnlyVar;

    fn add(self, rhs: u32) -> Self::Output {
        ProofOnlyVar(self.0 + rhs)
    }
}

impl std::ops::AddAssign<u32> for ProofOnlyVar {
    fn add_assign(&mut self, rhs: u32) {
        self.0 += rhs;
    }
}

/// An axiom or literal
#[derive(Debug, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Axiom<V: VarLike> {
    /// Whether the axiom/literal is negated
    pub(crate) neg: bool,
    /// The variable, represented as a string
    pub(crate) var: V,
}

impl<V: VarLike> Axiom<V> {
    /// Gets the variable of the axiom
    pub fn var(&self) -> V {
        self.var
    }

    /// Returns true if the axiom is negated
    pub fn is_neg(&self) -> bool {
        self.neg
    }
}

impl<V: VarLike> std::fmt::Display for Axiom<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}{}",
            if self.neg { "~" } else { "" },
            V::Formatter::from(self.var)
        )
    }
}

impl<V: VarLike> ConstraintLike for Axiom<V> {
    type Var = V;

    fn rhs(&self) -> isize {
        1
    }

    fn sum_iter(&self) -> impl Iterator<Item = (isize, Axiom<V>)> {
        [(1, *self)].into_iter()
    }
}

impl<V: VarLike> std::ops::Not for Axiom<V> {
    type Output = Self;

    fn not(self) -> Self::Output {
        Axiom {
            neg: !self.neg,
            var: self.var,
        }
    }
}

/// A substitution of a variable to a value or a literal
#[derive(Debug, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Substitution<V: VarLike> {
    /// The variable to substitute
    pub(crate) var: V,
    /// What to substitute with
    pub(crate) sub: SubstituteWith<V>,
}

impl<V: VarLike> From<Axiom<V>> for Substitution<V> {
    fn from(value: Axiom<V>) -> Self {
        Self {
            var: value.var,
            sub: if value.neg {
                SubstituteWith::False
            } else {
                SubstituteWith::True
            },
        }
    }
}

impl<V: VarLike> Substitution<V> {
    /// Crates a new substitution
    pub fn new(v: V, with: SubstituteWith<V>) -> Self {
        Substitution { var: v, sub: with }
    }
}

impl<V: VarLike> std::fmt::Display for Substitution<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {MAP_TO} {}", V::Formatter::from(self.var), self.sub)
    }
}

/// What to substitute a variable with
#[derive(Debug, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum SubstituteWith<V: VarLike> {
    /// Fix true value
    True,
    /// Fix false value
    False,
    /// Substitute variable with literal
    Lit(Axiom<V>),
}

impl<V: VarLike> From<bool> for SubstituteWith<V> {
    fn from(value: bool) -> Self {
        if value {
            SubstituteWith::True
        } else {
            SubstituteWith::False
        }
    }
}

impl<V: VarLike> std::fmt::Display for SubstituteWith<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SubstituteWith::True => write!(f, "{TRUE}"),
            SubstituteWith::False => write!(f, "{FALSE}"),
            SubstituteWith::Lit(lit) => write!(f, "{lit}"),
        }
    }
}

/// An order that has been defined can be loaded in the proof
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Order {
    name: String,
    num_def_constraints: usize,
    num_spec_constraints: usize,
}

impl Order {
    pub(crate) fn new(name: String) -> Self {
        Self {
            name,
            num_def_constraints: 0,
            num_spec_constraints: 0,
        }
    }

    /// Gets the name of the order
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    pub(crate) fn new_def_constraint(&mut self) {
        self.num_def_constraints += 1;
    }

    #[must_use]
    pub(crate) fn num_def_constraints(&self) -> usize {
        self.num_def_constraints
    }

    pub(crate) fn new_spec_constraint(&mut self) {
        self.num_spec_constraints += 1;
    }

    #[must_use]
    pub(crate) fn num_spec_constraints(&self) -> usize {
        self.num_spec_constraints
    }
}

/// A proof goal for the transitivity and reflexivity proofs in an order definition
#[derive(Debug, Copy, Clone)]
pub struct OrderDefinitionProofGoalId(NonZeroUsize);

impl OrderDefinitionProofGoalId {
    pub(crate) fn new(id: usize) -> Self {
        Self(NonZeroUsize::new(id).expect("ID needs to be non-zero"))
    }

    pub(crate) fn as_proof_goal_id(self) -> ProofGoalId {
        ProofGoalId::Specific(self.0)
    }
}

impl std::fmt::Display for OrderDefinitionProofGoalId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{GOAL_ID}{}", self.0)
    }
}

/// A input variable to an order, allows for getting the corresponding variables used in the
/// specification, definition, and proof
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct OrderInputVar<V: VarLike>(V);

impl<V: VarLike> OrderInputVar<V> {
    pub(crate) fn new(var: V) -> Self {
        Self(var)
    }

    /// Gets the "left" variable variant
    pub fn left(self) -> OrderVar<V> {
        OrderVar(IntOrderVar::Left(self.0))
    }

    /// Gets the "right" variable variant
    pub fn right(self) -> OrderVar<V> {
        OrderVar(IntOrderVar::Right(self.0))
    }

    /// Gets the "fresh right" variable variant to be used in the transitivity proof
    pub fn fresh_right(self) -> OrderVar<V> {
        OrderVar(IntOrderVar::FreshRight(self.0))
    }
}

/// A auxiliary variable of an order, allows for getting the corresponding variables used in the
/// specification, definition, and proof
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct OrderAuxVar<V: VarLike>(V);

impl<V: VarLike> OrderAuxVar<V> {
    pub(crate) fn new(var: V) -> Self {
        Self(var)
    }

    /// Gets the usable auxiliary variable
    #[must_use]
    pub fn aux(self) -> OrderVar<V> {
        OrderVar(IntOrderVar::Aux(self.0))
    }

    /// Gets the first fresh variable variant to be used in the transitivity proof
    #[must_use]
    pub fn fresh_1(self) -> OrderVar<V> {
        OrderVar(IntOrderVar::FreshAux1(self.0))
    }

    /// Gets the second fresh variable variant to be used in the transitivity proof
    #[must_use]
    pub fn fresh_2(self) -> OrderVar<V> {
        OrderVar(IntOrderVar::FreshAux2(self.0))
    }
}

/// A variable to be used in an order definition
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OrderVar<V: VarLike>(IntOrderVar<V>);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum IntOrderVar<V: VarLike> {
    /// A variable of the left side of the order definition
    Left(V),
    /// A variable of the right side of the order definition
    Right(V),
    /// A fresh right variable used in a transitivity proof
    FreshRight(V),
    /// An auxiliary variable
    Aux(V),
    /// A fresh auxiliary variable of set 1
    FreshAux1(V),
    /// A fresh auxiliary variable of set 2
    FreshAux2(V),
}

impl<V: VarLike> VarLike for OrderVar<V> {
    type Formatter = Self;
}

impl<V: VarLike> std::fmt::Display for OrderVar<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            IntOrderVar::Left(v) => write!(f, "u_{}", V::Formatter::from(v)),
            IntOrderVar::Right(v) => write!(f, "v_{}", V::Formatter::from(v)),
            IntOrderVar::FreshRight(v) => write!(f, "w_{}", V::Formatter::from(v)),
            IntOrderVar::Aux(v) => write!(f, "$uv_{}", V::Formatter::from(v)),
            IntOrderVar::FreshAux1(v) => write!(f, "$vw_{}", V::Formatter::from(v)),
            IntOrderVar::FreshAux2(v) => write!(f, "$uw_{}", V::Formatter::from(v)),
        }
    }
}

/// A [`ProofGoal`] ID
#[derive(Debug, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ProofGoalId {
    /// A [`ProofGoal`] for a constraint
    Constraint(ConstraintId),
    /// A specified proof goal ID
    Specific(NonZeroUsize),
}

impl ProofGoalId {
    /// Create a proof goal ID for a specific proof goal, i.e., `#<id>`
    ///
    /// # Panics
    ///
    /// If `id` is zero
    #[must_use]
    pub fn specific(id: usize) -> Self {
        ProofGoalId::Specific(NonZeroUsize::try_from(id).expect("proof goal ID cannot be zero"))
    }
}

impl From<ConstraintId> for ProofGoalId {
    fn from(value: ConstraintId) -> Self {
        ProofGoalId::Constraint(value)
    }
}

impl std::fmt::Display for ProofGoalId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProofGoalId::Constraint(id) => write!(f, "{id}"),
            ProofGoalId::Specific(id) => write!(f, "{GOAL_ID}{id}"),
        }
    }
}

/// An objective update step (`obju`)
#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ObjectiveUpdate<O> {
    /// `new`
    New(O),
    /// `diff`
    Diff(O),
}

impl<O> ObjectiveUpdate<O>
where
    O: ObjectiveLike,
{
    /// Creates an explicit objective update by specifying the entire new objective
    pub fn new(objective: O) -> Self {
        ObjectiveUpdate::New(objective)
    }

    /// Creates an objective update by specifying the difference to the old objective
    pub fn diff(diff: O) -> Self {
        ObjectiveUpdate::Diff(diff)
    }
}

impl<O> std::fmt::Display for ObjectiveUpdate<O>
where
    O: ObjectiveLike,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ObjectiveUpdate::New(obj) => {
                write!(f, "{OBJ_UPDATE_NEW} {}", ObjFormatter::from(obj))
            }
            ObjectiveUpdate::Diff(obj) => {
                write!(f, "{OBJ_UPDATE_DIFF} {}", ObjFormatter::from(obj))
            }
        }
    }
}

/// Possible output guarantees for the output section
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum OutputGuarantee {
    /// No guarantee
    None,
    /// All constraints are derivable
    Derivable(OutputType),
    /// The constraints are equisatisfiable
    Equisatisfiable(OutputType),
    /// The constraints are equioptimal
    Equioptimal(OutputType),
}

impl std::fmt::Display for OutputGuarantee {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OutputGuarantee::None => write!(f, "{OUTPUT_GUARANTEE_NONE}"),
            OutputGuarantee::Derivable(t) => write!(f, "{OUTPUT_GUARANTEE_DERIVABLE} {t}"),
            OutputGuarantee::Equisatisfiable(t) => {
                write!(f, "{OUTPUT_GUARANTEE_EQUISATISFIABLE} {t}")
            }
            OutputGuarantee::Equioptimal(t) => write!(f, "{OUTPUT_GUARANTEE_EQUIOPTIMAL} {t}"),
        }
    }
}

/// Possible output types for the output section
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum OutputType {
    /// Implicit output
    Implicit,
    /// File output
    File,
    /// The output is a permutation of the core constraints
    ///
    /// **Note**: while this output type is defined in the proof specification, the proof checker
    /// does currently not implement it.
    Permutation(Vec<ConstraintId>),
    /// The output are constraints that are explicitly given
    ///
    /// **Note**: while this output type is defined in the proof specification, the proof checker
    /// does currently not implement it.
    Constraints {
        /// The number of variables in the constraints that are output
        n_vars: usize,
        /// The number of output constraints
        n_constraints: usize,
        /// An optional objective in the output
        objective: Option<String>,
        /// The constraints to be output
        constraints: Vec<String>,
    },
}

impl std::fmt::Display for OutputType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OutputType::Implicit => write!(f, "{OUTPUT_TYPE_IMPLICIT}"),
            OutputType::File => write!(f, "{OUTPUT_TYPE_FILE}"),
            OutputType::Permutation(ids) => {
                write!(f, "{OUTPUT_TYPE_PERMUTATION} {}", ids.iter().format(" "))
            }
            OutputType::Constraints {
                n_vars,
                n_constraints,
                objective,
                constraints,
            } => {
                writeln!(f, "{OUTPUT_TYPE_CONSTRAINTS} {OPB}")?;
                writeln!(f, "  * #variable= {n_vars} #constraint= {n_constraints}")?;
                if let Some(objective) = objective {
                    writeln!(f, "  {objective}{RULE_TERM}")?;
                }
                for constraint in constraints {
                    writeln!(f, "  {constraint}{RULE_TERM}")?;
                }
                write!(f, "{END} {OPB}")?;
                Ok(())
            }
        }
    }
}

impl OutputType {
    /// Creates a permutation output type from an iterator of core IDs
    pub fn permutation<I>(ids: I) -> Self
    where
        I: IntoIterator<Item = ConstraintId>,
    {
        OutputType::Permutation(ids.into_iter().collect())
    }

    /// Creates a `CONSTRAINTS` conclusion
    ///
    /// This counts the number of constraints and variables in the constraints automatically
    pub fn constraints<C, O, I>(constraints: I, objective: Option<O>) -> Self
    where
        C: ConstraintLike,
        O: ObjectiveLike,
        I: IntoIterator<Item = C>,
    {
        let mut vars = std::collections::HashSet::<String>::default();
        let objective = if let Some(objective) = objective {
            vars.extend(objective.sum_iter().map(|(_, v)| {
                format!(
                    "{}",
                    <<O as ObjectiveLike>::Var as VarLike>::Formatter::from(v.var())
                )
            }));
            Some(format!("{}", ObjFormatter::from(&objective)))
        } else {
            None
        };
        let constraints: Vec<_> = constraints
            .into_iter()
            .map(|c| {
                vars.extend(c.sum_iter().map(|(_, v)| {
                    format!(
                        "{}",
                        <<C as ConstraintLike>::Var as VarLike>::Formatter::from(v.var())
                    )
                }));
                format!("{}", ConstrFormatter::from(&c))
            })
            .collect();
        Self::Constraints {
            n_vars: vars.len(),
            n_constraints: constraints.len(),
            objective,
            constraints,
        }
    }
}

/// Possible conclusions
#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Conclusion<V: VarLike> {
    /// No conclusion
    None,
    /// Satisfiability
    Sat(Option<Vec<Axiom<V>>>),
    /// Unsatisfiability
    Unsat(Option<ConstraintId>),
    /// Bounds
    Bounds {
        /// The range of the bounds on the objective
        range: std::ops::Range<isize>,
        /// Optional [`ConstraintId`] of the lower bound
        lb_id: Option<ConstraintId>,
        /// Optional solution witnessing the upper bound
        ub_sol: Option<Vec<Axiom<V>>>,
    },
}

impl<V: VarLike> std::fmt::Display for Conclusion<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Conclusion::None => write!(f, "{CONCLUSION_NONE}"),
            Conclusion::Sat(sol) => {
                if let Some(sol) = sol {
                    write!(f, "{CONCLUSION_SAT} {SEP_B} {}", sol.iter().format(" "))
                } else {
                    write!(f, "{CONCLUSION_SAT}")
                }
            }
            Conclusion::Unsat(id) => {
                if let Some(id) = id {
                    write!(f, "{CONCLUSION_UNSAT} {SEP_B} {id}")
                } else {
                    write!(f, "{CONCLUSION_UNSAT}")
                }
            }
            Conclusion::Bounds {
                range,
                lb_id,
                ub_sol,
            } => {
                write!(f, "{CONCLUSION_BOUNDS} {}", range.start)?;
                if let Some(id) = lb_id {
                    write!(f, " {SEP_B} {id}")?;
                }
                write!(f, " {}", range.end - 1)?;
                if let Some(sol) = &ub_sol {
                    write!(f, " {SEP_B} {}", sol.iter().format(" "))?;
                }
                Ok(())
            }
        }
    }
}

pub struct ObjFormatter<'o, O: ObjectiveLike> {
    obj: &'o O,
}

impl<'o, O: ObjectiveLike> From<&'o O> for ObjFormatter<'o, O> {
    fn from(value: &'o O) -> Self {
        Self { obj: value }
    }
}

impl<O: ObjectiveLike> std::fmt::Display for ObjFormatter<'_, O> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} {}",
            self.obj
                .sum_iter()
                .format_with(" ", |(cf, ax), f| f(&format_args!("{cf} {ax}"))),
            self.obj.offset()
        )
    }
}

pub struct ConstrFormatter<'c, C: ConstraintLike> {
    constr: &'c C,
}

impl<'c, C: ConstraintLike> From<&'c C> for ConstrFormatter<'c, C> {
    fn from(value: &'c C) -> Self {
        Self { constr: value }
    }
}

impl<C: ConstraintLike> std::fmt::Display for ConstrFormatter<'_, C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.constr.reification(crate::private::Token) {
            crate::Reification::None => Ok(()),
            crate::Reification::LitsImplyConstraint(axioms) => {
                write!(f, "{} {REIFY_RIGHT} ", axioms.iter().format(" "))
            }
            crate::Reification::ConstraintImpliesLit(axiom) => write!(f, "{axiom} {REIFY_LEFT} "),
        }?;
        write!(
            f,
            "{} >= {}",
            self.constr
                .sum_iter()
                .format_with(" ", |(cf, ax), f| f(&format_args!("{cf} {ax}"))),
            self.constr.rhs(),
        )
    }
}

/// A proof checker timer handle, helping to only stop timer that have been started
#[derive(Debug)]
pub struct TimerHandle(pub(crate) String);
