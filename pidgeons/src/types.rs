//! # Most Types of the Library

use std::{
    fmt, io,
    num::NonZeroUsize,
    ops::{self, Range},
};

use itertools::Itertools;

use crate::{OperationSequence, VarLike};

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

/// A constraint ID referring to a constraint
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

/// A variable that is only present in the proof
///
/// These variables format to `pv<idx>`
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ProofOnlyVar(pub(crate) u32);

impl fmt::Display for ProofOnlyVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "pv{}", self.0)
    }
}

impl VarLike for ProofOnlyVar {}

impl ops::Add<u32> for ProofOnlyVar {
    type Output = ProofOnlyVar;

    fn add(self, rhs: u32) -> Self::Output {
        ProofOnlyVar(self.0 + rhs)
    }
}

impl ops::AddAssign<u32> for ProofOnlyVar {
    fn add_assign(&mut self, rhs: u32) {
        self.0 += rhs;
    }
}

/// An axiom or literal
#[derive(Debug, Clone, Copy)]
pub struct Axiom<V: VarLike> {
    /// Whether the axiom/literal is negated
    pub(crate) neg: bool,
    /// The variable, represented as a string
    pub(crate) var: V,
}

impl<V: VarLike> fmt::Display for Axiom<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", if self.neg { "~" } else { "" }, self.var)
    }
}

impl<V: VarLike> ConstraintLike for Axiom<V> {
    fn constr_str(&self) -> String {
        format!("{self} >= 1")
    }
}

/// A substitution of a variable to a value or a literal
#[derive(Debug, Clone, Copy)]
pub struct Substitution<V: VarLike> {
    /// The variable to substitute
    pub(crate) var: V,
    /// What to substitute with
    pub(crate) sub: SubstituteWith<V>,
}

impl<V: VarLike> Substitution<V> {
    /// Crates a new substitution
    pub fn new(v: V, with: SubstituteWith<V>) -> Self {
        Substitution { var: v, sub: with }
    }
}

impl<V: VarLike> fmt::Display for Substitution<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} -> {}", self.var, self.sub)
    }
}

/// What to substitute a variable with
#[derive(Debug, Clone, Copy)]
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

impl<V: VarLike> fmt::Display for SubstituteWith<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SubstituteWith::True => write!(f, "1"),
            SubstituteWith::False => write!(f, "0"),
            SubstituteWith::Lit(lit) => write!(f, "{lit}"),
        }
    }
}

/// An order in the proof
pub struct Order<V> {
    name: String,
    used_vars: rustc_hash::FxHashSet<V>,
    definition: Vec<String>,
    trans_proof: SubProof,
    refl_proof: Option<SubProof>,
}

impl<V: VarLike> Order<V> {
    /// Creates a new builder structure
    #[must_use]
    pub fn new(name: String) -> Self {
        Order {
            name,
            used_vars: rustc_hash::FxHashSet::default(),
            definition: vec![],
            trans_proof: SubProof { goals: vec![] },
            refl_proof: None,
        }
    }

    /// Gets the name of the order
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Gets an iterator over the used variables
    pub fn used_vars(&self) -> impl Iterator<Item = V> + '_ {
        self.used_vars.iter().copied()
    }

    /// Marks a variable as used in the order and gets its left and right variants to be used in
    /// the definitions
    pub fn use_var(&mut self, v: V) -> (String, String) {
        self.used_vars.insert(v);
        (format!("u_{v}"), format!("v_{v}"))
    }

    /// Adds a constraint to the order definition
    ///
    /// The constraint must only use left and right variables that have been marked as used
    // Since we push `constr` into the definitions, `self.definition.len()` is never zero
    #[allow(clippy::missing_panics_doc)]
    pub fn add_definition_constraint<C: ConstraintLike>(
        &mut self,
        constr: &C,
        trans_proof: Vec<OperationSequence>,
        refl_proof: Option<Vec<OperationSequence>>,
    ) {
        self.definition.push(constr.constr_str());
        self.trans_proof.goals.push(ProofGoal {
            id: ProofGoalId::Specific(NonZeroUsize::new(self.definition.len()).unwrap()),
            derivations: trans_proof,
        });
        if let Some(new_goal) = refl_proof {
            if let Some(proof) = &mut self.refl_proof {
                proof.goals.push(ProofGoal {
                    id: ProofGoalId::Specific(NonZeroUsize::new(self.definition.len()).unwrap()),
                    derivations: new_goal,
                });
            } else {
                self.refl_proof = Some(SubProof {
                    goals: vec![ProofGoal {
                        id: ProofGoalId::Specific(
                            NonZeroUsize::new(self.definition.len()).unwrap(),
                        ),
                        derivations: new_goal,
                    }],
                });
            }
        }
    }
}

impl<V: VarLike> fmt::Display for Order<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "def_order {}", self.name)?;
        // Variables
        writeln!(f, "  vars")?;
        writeln!(
            f,
            "    left {}",
            self.used_vars
                .iter()
                .format_with(" ", |v, f| f(&format_args!("u_{v}")))
        )?;
        writeln!(
            f,
            "    right {}",
            self.used_vars
                .iter()
                .format_with(" ", |v, f| f(&format_args!("v_{v}")))
        )?;
        writeln!(f, "    aux")?;
        writeln!(f, "  end")?;
        // Order definition
        writeln!(f, "  def")?;
        for def in &self.definition {
            writeln!(f, "    {def} ;")?;
        }
        writeln!(f, "  end")?;
        // Proofs
        writeln!(f, "  transitivity")?;
        writeln!(f, "    vars")?;
        writeln!(
            f,
            "      fresh_right {}",
            self.used_vars
                .iter()
                .format_with(" ", |v, f| f(&format_args!("w_{v}")))
        )?;
        writeln!(f, "    end")?;
        self.trans_proof.format_indented(f, 4)?;
        writeln!(f)?;
        writeln!(f, "  end")?;
        if let Some(proof) = &self.refl_proof {
            writeln!(f, "  reflexivity")?;
            proof.format_indented(f, 4)?;
            writeln!(f)?;
            writeln!(f, "  end")?;
        }
        write!(f, "end")
    }
}

/// A subproof
pub struct SubProof {
    /// The sequence of [`ProofGoal`] in the subproof
    goals: Vec<ProofGoal>,
}

impl FromIterator<ProofGoal> for SubProof {
    fn from_iter<T: IntoIterator<Item = ProofGoal>>(iter: T) -> Self {
        SubProof {
            goals: iter.into_iter().collect(),
        }
    }
}

impl SubProof {
    /// Writes the subproof to a writer, indented by a number of spaces
    ///
    /// # Errors
    ///
    /// If writing fails, returns an error
    pub fn write_indented<W: io::Write>(&self, writer: &mut W, indent: usize) -> io::Result<()> {
        writeln!(writer, "{:indent$}proof", "", indent = indent)?;
        for goal in &self.goals {
            goal.write_indented(writer, indent + 2)?;
            writeln!(writer)?;
        }
        write!(writer, "{:indent$}qed", "", indent = indent)
    }

    /// Formats the subproof, indented by a number of spaces
    ///
    /// # Errors
    ///
    /// If formatting fails, returns an error
    pub fn format_indented<W: fmt::Write>(&self, writer: &mut W, indent: usize) -> fmt::Result {
        writeln!(writer, "{:indent$}proof", "", indent = indent)?;
        for goal in &self.goals {
            goal.format_indented(writer, indent + 2)?;
            writeln!(writer)?;
        }
        write!(writer, "{:indent$}qed", "", indent = indent)
    }
}

impl fmt::Display for SubProof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.format_indented(f, 0)
    }
}

/// A proof target of a [`SubProof`]
pub struct ProofGoal {
    /// The goal id
    id: ProofGoalId,
    /// For now only operation derivations are supported
    derivations: Vec<OperationSequence>,
}

impl Extend<OperationSequence> for ProofGoal {
    fn extend<T: IntoIterator<Item = OperationSequence>>(&mut self, iter: T) {
        self.derivations.extend(iter);
    }
}

impl ProofGoal {
    /// Creates a new proof goal
    #[must_use]
    pub fn new(id: ProofGoalId) -> Self {
        ProofGoal {
            id,
            derivations: vec![],
        }
    }

    /// Writes the proof goal to a writer, indented by a number of spaces
    ///
    /// # Errors
    ///
    /// If writing fails, returns an error
    pub fn write_indented<W: io::Write>(&self, writer: &mut W, indent: usize) -> io::Result<()> {
        writeln!(
            writer,
            "{:indent$}proofgoal {}",
            "",
            self.id,
            indent = indent
        )?;
        for der in &self.derivations {
            writeln!(writer, "{:indent$}  pol {der}", "", indent = indent)?;
        }
        write!(writer, "{:indent$}qed -1", "", indent = indent)
    }

    /// Formats the proof goal, indented by a number of spaces
    ///
    /// # Errors
    ///
    /// If formatting fails, returns an error
    pub fn format_indented<W: fmt::Write>(&self, writer: &mut W, indent: usize) -> fmt::Result {
        writeln!(
            writer,
            "{:indent$}proofgoal {}",
            "",
            self.id,
            indent = indent
        )?;
        for der in &self.derivations {
            writeln!(writer, "{:indent$}  pol {der}", "", indent = indent)?;
        }
        write!(writer, "{:indent$}qed -1", "", indent = indent)
    }
}

impl fmt::Display for ProofGoal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.format_indented(f, 0)
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
            ProofGoalId::Constraint(id) => write!(f, "{id}"),
            ProofGoalId::Specific(id) => write!(f, "#{id}"),
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
                    subproof.format_indented(f, 2)?;
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
pub enum Conclusion<V: VarLike> {
    /// No conclusion
    None,
    /// Satisfiability
    Sat(Option<Vec<Axiom<V>>>),
    /// Unsatisfiability
    Unsat(Option<ConstraintId>),
    /// Bounds
    Bounds(BoundsConclusion<V>),
}

impl<V: VarLike> fmt::Display for Conclusion<V> {
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

pub struct BoundsConclusion<V: VarLike> {
    pub(crate) range: Range<usize>,
    pub(crate) lb_id: Option<ConstraintId>,
    pub(crate) ub_sol: Option<Vec<Axiom<V>>>,
}
