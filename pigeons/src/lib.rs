//! # Pigeons
//!
//! A proof logging library for [VeriPB](https://gitlab.com/MIAOresearch/software/VeriPB).
//!
//! This library is a simple abstraction layer for writing proofs checkable with VeriPB.
//!
//! ## Features
//!
//! - `short-keywords`: use short rule keywords, e.g., `p` instead of `pol`
//! - `serde`: add implementations for
//!   [`serde::Serialize`](https://docs.rs/serde/latest/serde/trait.Serialize.html) and
//!   [`serde::Deserialize`](https://docs.rs/serde/latest/serde/trait.Deserialize.html) for library
//!   types
//! - `version2`: use VeriPB version 2 syntax instead of version 3
//!
//! ## Coverage of VeriPB Syntax
//!
//! - [x] `f`: [`Proof::new`]
//! - [x] `pol`: [`Proof::operations`]
//! - [x] `rup`: [`Proof::reverse_unit_prop`]
//! - [x] `del`: [`Proof::delete_ids`], [`Proof::delete_id_range`], [`Proof::delete_constr`]
//! - [x] `delc`: [`Proof::delete_core_ids`]
//! - [x] `deld`: [`Proof::delete_derived_ids`]
//! - [x] `obju`: [`Proof::update_objective`]
//! - [x] `red`: [`Proof::redundant`]
//! - [x] `dom`: [`Proof::dominated`]
//! - [x] `core`: [`Proof::move_ids_to_core`], [`Proof::move_range_to_core`]
//! - [x] `sol`: [`Proof::solution`]
//! - [x] `solx`: [`Proof::exclude_solution`]
//! - [x] `soli`: [`Proof::improve_solution`]
//! - [x] `output`: [`Proof::output`], [`Proof::conclude`]
//!     - Guarantees:
//!         - [x] `NONE`
//!         - [x] `DERIVABLE`
//!         - [x] `EQUISATISFIABLE`
//!         - [x] `EQUIOPTIMAL`
//!         - [ ] `EQUIENUMERABLE` (documented but not yet implemented in VeriPB)
//!     - Types:
//!         - [x] none
//!         - [x] `FILE`
//!         - [x] `IMPLICIT`
//!         - [ ] `CONSTRAINTS` (documented but not yet implemented in VeriPB)
//!         - [ ] `PERMUTATION` (documented but not yet implemented in VeriPB)
//! - [x] `conclusion`: [`Proof::conclude`], [`Proof::new_with_conclusion`],
//!   [`Proof::update_default_conclusion`]
//! - [x] Sub-proofs
//!     - [ ] `scope leq` and `scope geq` in `red` and `dom` rules
//! - [x] `e`: [`Proof::equals`]
//! - [x] `ea`: [`Proof::equals_add`] (only with `version2` feature)
//! - [x] `eobj`: [`Proof::obj_equals`]
//! - [x] `i`: [`Proof::implied`]
//! - [x] `ia`: [`Proof::implied_add`]
//! - [x] `setlvl` (previously `#`): [`Proof::set_level`]
//! - [x] `wiplvl` (previously `w`): [`Proof::wipe_level`]
//! - [x] `strengthening_to_core`: [`Proof::strengthening_to_core`]
//! - [x] `def_order`
//! - [x] `load_order`
//! - [x] `pbc`
//! - [ ] `@` constraint labels

#![warn(clippy::pedantic)]
#![warn(missing_docs)]
#![warn(missing_debug_implementations)]

use std::{
    fmt, io,
    ops::{Bound, RangeBounds},
};

use itertools::Itertools;

mod types;
pub use types::{
    AbsConstraintId, Axiom, Conclusion, ConstraintId, Derivation, ObjectiveUpdate, Order, OrderVar,
    OutputGuarantee, OutputType, ProblemType, ProofGoal, ProofGoalId, ProofOnlyVar,
    SubproofElement, Substitution,
};

mod ops;
pub use ops::{OperationLike, OperationSequence};

mod keywords;
#[allow(clippy::wildcard_imports)]
use keywords::*;

macro_rules! unreachable_err {
    ($res:expr) => {{
        match $res {
            Ok(v) => v,
            Err(_) => unreachable!(),
        }
    }};
}
pub(crate) use unreachable_err;

use crate::types::{ConstrFormatter, ObjFormatter};

/// A type representing a VeriPB proof.
///
/// This type represents the main API of this library.
///
/// **Note**: if the proof is dropped without calling [`Proof::conclude`], the proof is ended with
/// output guarantee [`OutputGuarantee::None`] and [`Conclusion::None`], or whatever was set in
/// [`Proof::new_with_conclusion`]
#[derive(Debug)]
pub struct Proof<Writer: io::Write> {
    /// Where the proof is written to
    writer: Writer,
    // NOTE: if anything is added here, make sure to manually drop it in [`Self::end`]
    /// The next free constraint ID
    next_id: AbsConstraintId,
    /// The next free proof-only variable
    next_pv: ProofOnlyVar,
    /// The proofs problem type
    problem_type: ProblemType,
    /// The first ID of a constraint in the proof and not in the original instance
    first_proof_id: AbsConstraintId,
    /// The default conclusion that will be written when the proof is dropped
    default_conclusion: (OutputGuarantee, String),
}

impl<Writer: io::Write> Drop for Proof<Writer> {
    fn drop(&mut self) {
        writeln!(
            self.writer,
            "output {}{RULE_TERM}",
            self.default_conclusion.0
        )
        .expect("could not finish writing proof");
        writeln!(
            self.writer,
            "conclusion {}{RULE_TERM}",
            self.default_conclusion.1
        )
        .expect("could not finish writing proof");
        writeln!(self.writer, "{FOOTER}{RULE_TERM}").expect("could not finish writing proof");
    }
}

impl<Writer> Proof<Writer>
where
    Writer: io::Write,
{
    /// Initializes a proof with a given writer
    ///
    /// # Performance
    ///
    /// For performance reasons, consider using a buffered writer (e.g., [`std::io::BufWriter`].
    ///
    /// # Proof Log
    ///
    /// This writes the proof header and an `f`-rule line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn new(mut writer: Writer, num_constraints: usize, optimization: bool) -> io::Result<Self> {
        writeln!(writer, "{HEADER}")?;
        let next_id = AbsConstraintId(unreachable_err!((num_constraints + 1).try_into()));
        let mut this = Self {
            writer,
            next_id,
            next_pv: ProofOnlyVar(0),
            problem_type: ProblemType::default(),
            first_proof_id: next_id,
            default_conclusion: (
                OutputGuarantee::None,
                format!("{}", Conclusion::<&'static str>::None),
            ),
        };
        if optimization {
            this.problem_type = ProblemType::Optimization;
        }
        this.verify_num_constraints(num_constraints)?;
        Ok(this)
    }

    /// Initializes a proof with a given writer
    ///
    /// If the proof is dropped, it will conclude with the specified output guarantee and
    /// conclusion. The conclusion can be updated with [`Proof::update_default_conclusion`].
    ///
    /// # Performance
    ///
    /// For performance reasons, consider using a buffered writer (e.g., [`std::io::BufWriter`].
    ///
    /// # Proof Log
    ///
    /// This writes the proof header and an `f`-rule line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn new_with_conclusion<V: VarLike>(
        mut writer: Writer,
        num_constraints: usize,
        optimization: bool,
        output_guarantee: OutputGuarantee,
        conclusion: &Conclusion<V>,
    ) -> io::Result<Self> {
        writeln!(writer, "{HEADER}")?;
        let next_id = AbsConstraintId(unreachable_err!((num_constraints + 1).try_into()));
        let mut this = Self {
            writer,
            next_id,
            next_pv: ProofOnlyVar(0),
            problem_type: ProblemType::default(),
            first_proof_id: next_id,
            default_conclusion: (output_guarantee, format!("{conclusion}")),
        };
        if optimization {
            this.problem_type = ProblemType::Optimization;
        }
        this.verify_num_constraints(num_constraints)?;
        Ok(this)
    }

    /// Updates the conclusion that is automatically written to the proof if it is dropped
    pub fn update_default_conclusion<V: VarLike>(
        &mut self,
        output_guarantee: OutputGuarantee,
        conclusion: &Conclusion<V>,
    ) {
        self.default_conclusion = (output_guarantee, format!("{conclusion}"));
    }

    /// Gets a new [`AbsConstraintId`] and increments the counter
    #[must_use]
    fn new_id(&mut self) -> AbsConstraintId {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    /// Writes a sub-proof, if the iterator is not empty
    fn write_subproof<V, C, PI>(&mut self, proof: PI) -> io::Result<()>
    where
        V: VarLike,
        C: ConstraintLike<V>,
        PI: IntoIterator<Item = SubproofElement<V, C>>,
    {
        let mut proof = proof.into_iter().peekable();
        if proof.peek().is_some() {
            self.next_id += 1; // negated `constr`
            writeln!(self.writer, " {SEP_A} {SUBPROOF}")?;
            for element in proof {
                let bump_ids = match element {
                    SubproofElement::Derivation(derivation) => {
                        writeln!(self.writer, "  {derivation}")?;
                        1
                    }
                    SubproofElement::Goal(goal) => {
                        goal.write_indented(&mut self.writer, 2)?;
                        writeln!(self.writer)?;
                        // negated proof goal + 1 for each derivation
                        1 + goal.n_derivations()
                    }
                };
                self.next_id += bump_ids;
            }
            write!(self.writer, "{QED}")?;
        }
        Ok(())
    }

    /// Gets a new [`ProofOnlyVar`] and increments the counter
    #[must_use]
    pub fn new_proof_var(&mut self) -> ProofOnlyVar {
        let pv = self.next_pv;
        self.next_pv += 1;
        pv
    }

    /// Gets the first ID that is _not_ from the original instance
    #[must_use]
    pub fn first_proof_id(&self) -> AbsConstraintId {
        self.first_proof_id
    }

    /// Gets the next unused constraint ID in the proof
    #[must_use]
    pub fn next_id(&self) -> AbsConstraintId {
        self.next_id
    }

    /// Adds a line to verify the number of constraints in the proof
    ///
    /// Note that equality constraints count as two constraints
    ///
    /// # Proof Log
    ///
    /// This writes an `f`-rule line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn verify_num_constraints(&mut self, num_constraints: usize) -> io::Result<()> {
        writeln!(
            self.writer,
            "{NUM_CONSTRAINTS} {num_constraints}{RULE_TERM}"
        )
    }

    /// Adds an arbitrary single-line comment to the proof
    ///
    /// **Note**: if the object displays as more than one line, an invalid VeriPB line will be
    /// produced
    ///
    /// # Proof Log
    ///
    /// Adds a `*` lines
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn comment<C: fmt::Display>(&mut self, comment: &C) -> io::Result<()> {
        writeln!(self.writer, "{COMMENT} {comment}")?;
        Ok(())
    }

    /// Adds an arbitrary multi-line comment to the proof
    ///
    /// # Proof Log
    ///
    /// Adds one or more `*` lines
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn multiline_comment(&mut self, comment: &str) -> io::Result<()> {
        for line in comment.lines() {
            writeln!(self.writer, "{COMMENT} {line}")?;
        }
        Ok(())
    }

    /// Adds a new constraint that is derived via a sequence of operations and returns its
    /// [`AbsConstraintId`]
    ///
    /// # Proof Log
    ///
    /// Adds a `pol`-rule line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn operations<V: VarLike>(
        &mut self,
        operations: &OperationSequence<V>,
    ) -> io::Result<AbsConstraintId> {
        writeln!(self.writer, "{POLISH} {operations}{RULE_TERM}")?;
        Ok(self.new_id())
    }

    /// Adds a constraint implied by reverse unit propagation and returns its [`AbsConstraintId`]
    ///
    /// # Proof Log
    ///
    /// Adds a `rup`-rule line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn reverse_unit_prop<V, C, I>(
        &mut self,
        constr: &C,
        hints: I,
    ) -> io::Result<AbsConstraintId>
    where
        V: VarLike,
        C: ConstraintLike<V>,
        I: IntoIterator<Item = ConstraintId>,
    {
        let mut hints = hints.into_iter().peekable();
        if hints.peek().is_some() {
            writeln!(
                self.writer,
                "{RUP} {} {SEP_A} {}{RULE_TERM}",
                ConstrFormatter::from(constr),
                hints.format(" ")
            )?;
        } else {
            writeln!(
                self.writer,
                "{RUP} {} {SEP_AS_TERM}{RULE_TERM}",
                ConstrFormatter::from(constr)
            )?;
        }
        Ok(self.new_id())
    }

    /// Deletes a set of constraint by their [`ConstraintId`]s
    ///
    /// **Note**: `ids` must be non-empty, otherwise an invalid line is produced
    ///
    /// # Proof Log
    ///
    /// Adds a `del id`-rule line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn delete_ids<V, C, II, PI>(&mut self, ids: II, proof: PI) -> io::Result<()>
    where
        V: VarLike,
        C: ConstraintLike<V>,
        II: IntoIterator<Item = ConstraintId>,
        PI: IntoIterator<Item = SubproofElement<V, C>>,
    {
        write!(
            self.writer,
            "{DEL_ID} {} {SEP_AS_TERM}",
            ids.into_iter().format(" ")
        )?;
        self.write_subproof(proof)?;
        writeln!(self.writer, "{RULE_TERM}")
    }

    /// Deletes an explicitly specified constraint
    ///
    /// # Proof Log
    ///
    /// Adds a `del spec`-rule line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn delete_constr<V, C>(&mut self, constr: &C) -> io::Result<()>
    where
        V: VarLike,
        C: ConstraintLike<V>,
    {
        writeln!(
            self.writer,
            "{DEL_SPEC} {} {SEP_AS_TERM}{RULE_TERM}",
            ConstrFormatter::from(constr)
        )
    }

    /// Deletes a a [`ConstraintId`] range
    ///
    /// # Proof Log
    ///
    /// Adds a `del range`-rule line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    ///
    /// # Panics
    ///
    /// If `range` is empty.
    pub fn delete_id_range<R: RangeBounds<ConstraintId>>(&mut self, range: R) -> io::Result<()> {
        let range_start = match range.start_bound() {
            Bound::Included(b) => *b,
            Bound::Excluded(b) => b.increment(self.next_id),
            Bound::Unbounded => AbsConstraintId::default().into(),
        };
        let range_end = match range.end_bound() {
            Bound::Included(b) => b.increment(self.next_id),
            Bound::Excluded(b) => *b,
            Bound::Unbounded => self.next_id.into(),
        };
        assert!(range_start.less(range_end, self.next_id));
        writeln!(
            self.writer,
            "{DEL_RANGE} {range_start} {range_end}{RULE_TERM}"
        )
    }

    /// Deletes a set of core constraint by their [`ConstraintId`]s
    ///
    /// **Note**: `ids` must be non-empty, otherwise an invalid line is produced
    ///
    /// # Proof Log
    ///
    /// Adds a `delc`-rule line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn delete_core_ids<I>(&mut self, ids: I) -> io::Result<()>
    where
        I: IntoIterator<Item = ConstraintId>,
    {
        writeln!(
            self.writer,
            "{DEL_CORE} {}{RULE_TERM}",
            ids.into_iter().format(" ")
        )
    }

    /// Deletes a set of derived constraint by their [`ConstraintId`]s
    ///
    /// **Note**: `ids` must be non-empty, otherwise an invalid line is produced
    ///
    /// # Proof Log
    ///
    /// Adds a `delc`-rule line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn delete_derived_ids<I>(&mut self, ids: I) -> io::Result<()>
    where
        I: IntoIterator<Item = ConstraintId>,
    {
        writeln!(
            self.writer,
            "{DEL_DERIVED} {}{RULE_TERM}",
            ids.into_iter().format(" ")
        )
    }

    /// Updates the objective in the proof
    ///
    /// # Proof Log
    ///
    /// Adds a `obju`-rule line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    ///
    /// # Panics
    ///
    /// If the problem is not an optimization problem.
    pub fn update_objective<V, O, C>(&mut self, update: &ObjectiveUpdate<V, O, C>) -> io::Result<()>
    where
        V: VarLike,
        O: ObjectiveLike<V>,
        C: ConstraintLike<V>,
    {
        assert!(matches!(self.problem_type, ProblemType::Optimization));
        writeln!(self.writer, "{OBJ_UPDATE} {update}{RULE_TERM}")
    }

    /// Adds a proof by contradition rule
    ///
    /// # Proof Log
    ///
    /// Adds a `pbc`-rule line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn proof_by_contradiction<V, C, PI>(
        &mut self,
        constr: &C,
        proof: PI,
    ) -> io::Result<AbsConstraintId>
    where
        V: VarLike,
        C: ConstraintLike<V>,
        PI: IntoIterator<Item = SubproofElement<V, C>>,
    {
        write!(
            self.writer,
            "{PBC} {} {}",
            ConstrFormatter::from(constr),
            if cfg!(feature = "version2") {
                SEP_A
            } else {
                ""
            },
        )?;
        self.write_subproof(proof)?;
        writeln!(self.writer, "{RULE_TERM}")?;
        Ok(self.new_id())
    }

    /// Adds a constraint that is redundant, checked via redundance based strengthening
    ///
    /// # Proof Log
    ///
    /// Adds a `red`-rule line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn redundant<V, C, SI, PI>(
        &mut self,
        constr: &C,
        subs: SI,
        proof: PI,
    ) -> io::Result<AbsConstraintId>
    where
        V: VarLike,
        C: ConstraintLike<V>,
        SI: IntoIterator<Item = Substitution<V>>,
        PI: IntoIterator<Item = SubproofElement<V, C>>,
    {
        write!(
            self.writer,
            "{REDUNDANT} {} {SEP_A} {}",
            ConstrFormatter::from(constr),
            subs.into_iter().format(" ")
        )?;
        self.write_subproof(proof)?;
        writeln!(self.writer, "{RULE_TERM}")?;
        Ok(self.new_id())
    }

    /// Adds a constraint that is redundant, checked via dominance
    ///
    /// # Proof Log
    ///
    /// Adds a `dom`-rule line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn dominated<V, C, SI, PI>(
        &mut self,
        constr: &C,
        subs: SI,
        proof: PI,
    ) -> io::Result<AbsConstraintId>
    where
        V: VarLike,
        C: ConstraintLike<V>,
        SI: IntoIterator<Item = Substitution<V>>,
        PI: IntoIterator<Item = SubproofElement<V, C>>,
    {
        write!(
            self.writer,
            "{DOMINATED} {} {SEP_A} {}",
            ConstrFormatter::from(constr),
            subs.into_iter().format(" ")
        )?;
        self.write_subproof(proof)?;
        writeln!(self.writer, "{RULE_TERM}")?;
        Ok(self.new_id())
    }

    /// Moves constraints to the core set by [`ConstraintId`]
    ///
    /// **Note**: `ids` must be non-empty, otherwise an invalid line is produced
    ///
    /// # Proof Log
    ///
    /// Adds a `core id` line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn move_ids_to_core<I>(&mut self, ids: I) -> io::Result<()>
    where
        I: IntoIterator<Item = ConstraintId>,
    {
        writeln!(
            self.writer,
            "{CORE_ID} {}{RULE_TERM}",
            ids.into_iter().format(" ")
        )
    }

    /// Moves a range of constraints to the core set
    ///
    /// # Proof Log
    ///
    /// Adds a `core id` line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    ///
    /// # Panics
    ///
    /// If `range` is empty.
    pub fn move_range_to_core<R: RangeBounds<ConstraintId>>(&mut self, range: R) -> io::Result<()> {
        let range_start = match range.start_bound() {
            Bound::Included(b) => *b,
            Bound::Excluded(b) => b.increment(self.next_id),
            Bound::Unbounded => AbsConstraintId::default().into(),
        };
        let range_end = match range.end_bound() {
            Bound::Included(b) => b.increment(self.next_id),
            Bound::Excluded(b) => *b,
            Bound::Unbounded => self.next_id.into(),
        };
        assert!(range_start.less(range_end, self.next_id));
        writeln!(
            self.writer,
            "{CORE_RANGE} {range_start} {range_end}{RULE_TERM}"
        )
    }

    /// Logs a solution in the proof
    ///
    /// # Proof Log
    ///
    /// Adds a `sol` line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn solution<V, I>(&mut self, solution: I) -> io::Result<()>
    where
        V: VarLike,
        I: IntoIterator<Item = Axiom<V>>,
    {
        writeln!(
            self.writer,
            "{SOLUTION} {}{RULE_TERM}",
            solution.into_iter().format(" ")
        )
    }

    /// Logs a solution with a solution-excluding constraint in the proof
    ///
    /// # Proof Log
    ///
    /// Adds a `solx` line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn exclude_solution<V, I>(&mut self, solution: I) -> io::Result<AbsConstraintId>
    where
        V: VarLike,
        I: IntoIterator<Item = Axiom<V>>,
    {
        writeln!(
            self.writer,
            "{SOLUTION_EXCLUDE} {}{RULE_TERM}",
            solution.into_iter().format(" ")
        )?;
        Ok(self.new_id())
    }

    /// Logs a solution with a solution-improving constraint in the proof
    ///
    /// # Proof Log
    ///
    /// Adds a `soli` line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn improve_solution<V, I>(&mut self, solution: I) -> io::Result<AbsConstraintId>
    where
        V: VarLike,
        I: IntoIterator<Item = Axiom<V>>,
    {
        writeln!(
            self.writer,
            "{SOLUTION_IMPROVE} {}{RULE_TERM}",
            solution.into_iter().format(" ")
        )?;
        Ok(self.new_id())
    }

    /// Adds an output section to the proof
    ///
    /// # Proof Log
    ///
    /// Writes an `output` line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn output(&mut self, guarantee: OutputGuarantee) -> io::Result<()> {
        writeln!(self.writer, "{OUTPUT} {guarantee}{RULE_TERM}")
    }

    /// Adds a conclusion section to the proof
    ///
    /// # Proof Log
    ///
    /// Writes a `conclusion` line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    fn conclusion<V: VarLike>(&mut self, conclusion: &Conclusion<V>) -> io::Result<()> {
        writeln!(self.writer, "{CONCLUSION} {conclusion}{RULE_TERM}")
    }

    /// Ends the proof and returns the writer
    ///
    /// # Proof Log
    ///
    /// Writes an `end` line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    fn end(mut self) -> io::Result<Writer> {
        writeln!(self.writer, "{FOOTER}{RULE_TERM}")?;
        // wrap self in ManuallyDrop to avoid calling Drop on it
        let mut nodrop = std::mem::ManuallyDrop::new(self);
        // manually drop everything but the writer, after this never use any of these fields in
        // nnodrop
        unsafe {
            std::ptr::drop_in_place(&mut nodrop.next_id);
            std::ptr::drop_in_place(&mut nodrop.next_pv);
            std::ptr::drop_in_place(&mut nodrop.problem_type);
            std::ptr::drop_in_place(&mut nodrop.first_proof_id);
            std::ptr::drop_in_place(&mut nodrop.default_conclusion);
        }
        // unsafely move writer out, after this never use writer in nodrop anymore
        let writer = unsafe { std::ptr::read(&nodrop.writer) };
        Ok(writer)
    }

    /// Concludes the proof by adding the output and conclusions sections and ending the proof.
    ///
    /// # Proof Log
    ///
    /// Writes `output`, `conclusion`, and `end` lines.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn conclude<V: VarLike>(
        mut self,
        guarantee: OutputGuarantee,
        conclusion: &Conclusion<V>,
    ) -> io::Result<Writer> {
        self.output(guarantee)?;
        self.conclusion(conclusion)?;
        self.end()
    }

    /// Checks whether a constraint is equal to a constraint that is already in the database
    ///
    /// # Proof Log
    ///
    /// Writes a `e`-rule line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn equals<V, C>(&mut self, constraint: &C, equals: Option<ConstraintId>) -> io::Result<()>
    where
        V: VarLike,
        C: ConstraintLike<V>,
    {
        if let Some(id) = equals {
            writeln!(
                self.writer,
                "{EQUALS} {} {SEP_A} {id}{RULE_TERM}",
                ConstrFormatter::from(constraint)
            )
        } else {
            writeln!(
                self.writer,
                "{EQUALS} {} {SEP_AS_TERM}{RULE_TERM}",
                ConstrFormatter::from(constraint)
            )
        }
    }

    /// Checks whether a constraint is equal to a constraint that is already in the database and
    /// adds the constraint
    ///
    /// # Proof Log
    ///
    /// Writes a `ea`-rule line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    #[cfg(feature = "version2")]
    pub fn equals_add<V, C>(
        &mut self,
        constraint: &C,
        equals: Option<ConstraintId>,
    ) -> io::Result<AbsConstraintId>
    where
        V: VarLike,
        C: ConstraintLike<V>,
    {
        if let Some(id) = equals {
            writeln!(
                self.writer,
                "{EQUALS_ADD} {} {SEP_A} {id}{RULE_TERM}",
                ConstrFormatter::from(constraint)
            )?;
        } else {
            writeln!(
                self.writer,
                "{EQUALS_ADD} {} {SEP_AS_TERM}{RULE_TERM}",
                ConstrFormatter::from(constraint)
            )?;
        }
        Ok(self.new_id())
    }

    /// Checks whether the given objective is equal to the current objective
    ///
    /// # Proof Log
    ///
    /// Writes a `eobj`-rule line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    ///
    /// # Panics
    ///
    /// If the problem is not an optimization problem.
    pub fn obj_equals<V, O>(&mut self, objective: &O) -> io::Result<()>
    where
        V: VarLike,
        O: ObjectiveLike<V>,
    {
        assert!(matches!(self.problem_type, ProblemType::Optimization));
        writeln!(
            self.writer,
            "{OBJ_EQUAL} {} {SEP_AS_TERM}{RULE_TERM}",
            ObjFormatter::from(objective)
        )
    }

    /// Checks whether the given constraint is implied
    ///
    /// # Proof Log
    ///
    /// Writes an `i`-rule line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn implied<V, C>(
        &mut self,
        constraint: &C,
        implicant: Option<ConstraintId>,
    ) -> io::Result<()>
    where
        V: VarLike,
        C: ConstraintLike<V>,
    {
        if let Some(id) = implicant {
            writeln!(
                self.writer,
                "{IMPLIED} {} {SEP_A} {id}{RULE_TERM}",
                ConstrFormatter::from(constraint)
            )
        } else {
            writeln!(
                self.writer,
                "{IMPLIED} {} {SEP_AS_TERM}{RULE_TERM}",
                ConstrFormatter::from(constraint)
            )
        }
    }

    /// Checks whether the given constraint is implied and adds it
    ///
    /// # Proof Log
    ///
    /// Writes an `ia`-rule line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn implied_add<V, C>(
        &mut self,
        constraint: &C,
        implicant: Option<ConstraintId>,
    ) -> io::Result<AbsConstraintId>
    where
        V: VarLike,
        C: ConstraintLike<V>,
    {
        if let Some(id) = implicant {
            writeln!(
                self.writer,
                "{IMPLIED_ADD} {} {SEP_A} {id}{RULE_TERM}",
                ConstrFormatter::from(constraint)
            )?;
        } else {
            writeln!(
                self.writer,
                "{IMPLIED_ADD} {} {SEP_AS_TERM}{RULE_TERM}",
                ConstrFormatter::from(constraint)
            )?;
        }
        Ok(self.new_id())
    }

    /// Sets the `level` of constraints added in the future
    ///
    /// # Proof Log
    ///
    /// Writes a `#`-rule line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn set_level(&mut self, level: usize) -> io::Result<()> {
        writeln!(self.writer, "{LEVEL_SET} {level}{RULE_TERM}")
    }

    /// Wipes out constraints from the given `level` or higher
    ///
    /// # Proof Log
    ///
    /// Writes a `w`-rule line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn wipe_level(&mut self, level: usize) -> io::Result<()> {
        writeln!(self.writer, "{LEVEL_WIPE} {level}{RULE_TERM}")
    }

    /// Defines a new order with a given name and a transitivity and optional reflexivity proof
    ///
    /// # Proof Log
    ///
    /// Writes a `def_order` block
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn define_order<V, C>(&mut self, order: &Order<V, C>) -> io::Result<()>
    where
        V: VarLike,
        C: ConstraintLike<OrderVar<V>>,
    {
        writeln!(self.writer, "{order}{RULE_TERM}")
    }

    /// Loads an order that needs to be previously defined
    ///
    /// # Proof Log
    ///
    /// Writes a `load_order` line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn load_order<V, I>(&mut self, name: &str, vars: I) -> io::Result<()>
    where
        V: VarLike,
        I: IntoIterator<Item = V>,
    {
        writeln!(
            self.writer,
            "{ORDER_LOAD} {name} {}{RULE_TERM}",
            vars.into_iter()
                .format_with(" ", |v, f| f(&V::Formatter::from(v)))
        )
    }

    /// Sets the strengthening to core mode
    ///
    /// # Proof Log
    ///
    /// Writes a `strengthening_to_core` line.
    ///
    /// # Errors
    ///
    /// If writing the proof fails.
    pub fn strengthening_to_core(&mut self, value: bool) -> io::Result<()> {
        writeln!(
            self.writer,
            "{STRENGTHENING_TO_CORE} {}{RULE_TERM}",
            if value { ON } else { OFF }
        )
    }
}

/// Trait that needs to be implemented for types used as variables
///
/// A call to [`fmt::Display`] on this type must produce a valid VeriPB variable
pub trait VarLike: Copy + Eq + std::hash::Hash + std::fmt::Debug {
    /// Formatter type that if constructed from a variable must display a valid VeriPB variable
    type Formatter: fmt::Display + From<Self>;

    /// Gets a positive axiom of the variable for an operation sequence
    fn pos_axiom(self) -> Axiom<Self> {
        Axiom {
            neg: false,
            var: self,
        }
    }

    /// Gets a negative axiom of the variable for an operation sequence
    fn neg_axiom(self) -> Axiom<Self> {
        Axiom {
            neg: true,
            var: self,
        }
    }

    /// Gets an axiom with specified negation
    fn axiom(self, neg: bool) -> Axiom<Self> {
        Axiom { neg, var: self }
    }

    /// Substitutes the variables with a fixed value
    fn substitute_fixed(self, value: bool) -> Substitution<Self> {
        Substitution {
            var: self,
            sub: value.into(),
        }
    }

    /// Substitutes the variable with a literal
    fn substitute_literal(self, literal: Axiom<Self>) -> Substitution<Self> {
        Substitution {
            var: self,
            sub: types::SubstituteWith::Lit(literal),
        }
    }
}

impl VarLike for &str {
    type Formatter = Self;
}

/// Trait that needs to be implemented for types used as constraints
pub trait ConstraintLike<V: VarLike> {
    /// Gets the operator and right hand side of the constraint
    fn rhs(&self) -> isize;

    /// Gets an iterator over the coefficient literal pairs in the constraint
    fn sum_iter(&self) -> impl Iterator<Item = (isize, Axiom<V>)>;
}

/// Trait that needs to be implemented for types used as objectives
pub trait ObjectiveLike<V: VarLike> {
    /// Gets an iterator over the coefficient literal pairs in the constraint
    fn sum_iter(&self) -> impl Iterator<Item = (isize, Axiom<V>)>;
    /// Gets the constant offset of the objective
    fn offset(&self) -> isize;
}

impl<V, Iter> ObjectiveLike<V> for Iter
where
    V: VarLike,
    Iter: IntoIterator<Item = (isize, V)> + Clone,
{
    fn sum_iter(&self) -> impl Iterator<Item = (isize, Axiom<V>)> {
        self.clone().into_iter().map(|(cf, v)| (cf, v.pos_axiom()))
    }

    fn offset(&self) -> isize {
        0
    }
}

#[cfg(test)]
mod tests {
    #[allow(clippy::wildcard_imports)]
    use crate::{keywords::*, VarLike};

    #[test]
    fn new_with_conclusion() {
        let (file, proof_file) = tempfile::NamedTempFile::new()
            .expect("failed to create temporary proof file")
            .into_parts();
        let proof = super::Proof::new_with_conclusion::<&'static str>(
            file,
            0,
            false,
            super::OutputGuarantee::None,
            &super::Conclusion::Unsat(Some(super::ConstraintId::last(1))),
        )
        .expect("failed to start proof");
        drop(proof);
        let output = std::fs::read_to_string(proof_file).expect("failed to read proof");
        #[cfg(feature = "version2")]
        assert_eq!(
            output,
            r"pseudo-Boolean proof version 2.0
f 0
output NONE
conclusion UNSAT : -1
end pseudo-Boolean proof
"
        );
        #[cfg(not(feature = "version2"))]
        assert_eq!(
            output,
            r"pseudo-Boolean proof version 3.0
f 0;
output NONE;
conclusion UNSAT : -1;
end pseudo-Boolean proof;
"
        );
    }

    #[test]
    fn update_default_conclusion() {
        let (file, proof_file) = tempfile::NamedTempFile::new()
            .expect("failed to create temporary proof file")
            .into_parts();
        let mut proof = super::Proof::new(file, 0, false).expect("failed to start proof");
        proof.update_default_conclusion::<&'static str>(
            super::OutputGuarantee::None,
            &super::Conclusion::Unsat(Some(super::ConstraintId::last(1))),
        );
        drop(proof);
        let output = std::fs::read_to_string(proof_file).expect("failed to read proof");
        #[cfg(feature = "version2")]
        assert_eq!(
            output,
            r"pseudo-Boolean proof version 2.0
f 0
output NONE
conclusion UNSAT : -1
end pseudo-Boolean proof
"
        );
        #[cfg(not(feature = "version2"))]
        assert_eq!(
            output,
            r"pseudo-Boolean proof version 3.0
f 0;
output NONE;
conclusion UNSAT : -1;
end pseudo-Boolean proof;
"
        );
    }

    #[test]
    fn multiline_comment() {
        let (file, proof_file) = tempfile::NamedTempFile::new()
            .expect("failed to create temporary proof file")
            .into_parts();
        let mut proof = super::Proof::new(file, 0, false).expect("failed to start proof");
        proof
            .multiline_comment("this is a\nmultiline comment")
            .unwrap();
        drop(proof);
        let output = std::fs::read_to_string(proof_file).expect("failed to read proof");
        #[cfg(feature = "version2")]
        assert_eq!(
            output,
            r"pseudo-Boolean proof version 2.0
f 0
* this is a
* multiline comment
output NONE
conclusion NONE
end pseudo-Boolean proof
"
        );
        #[cfg(not(feature = "version2"))]
        assert_eq!(
            output,
            r"pseudo-Boolean proof version 3.0
f 0;
% this is a
% multiline comment
output NONE;
conclusion NONE;
end pseudo-Boolean proof;
"
        );
    }

    struct Constr {
        terms: Vec<(isize, bool, &'static str)>,
        rhs: isize,
    }

    impl<'slf> super::ConstraintLike<&'slf str> for Constr {
        fn rhs(&self) -> isize {
            self.rhs
        }

        fn sum_iter(&self) -> impl Iterator<Item = (isize, super::Axiom<&'slf str>)> {
            self.terms
                .iter()
                .map(|(cf, neg, v)| (*cf, (*v).axiom(*neg)))
        }
    }

    #[test]
    fn rup() {
        let (file, proof_file) = tempfile::NamedTempFile::new()
            .expect("failed to create temporary proof file")
            .into_parts();
        let mut proof = super::Proof::new(file, 0, false).expect("failed to start proof");
        proof
            .reverse_unit_prop(
                &Constr {
                    terms: vec![(3, false, "x1"), (-42, true, "x2")],
                    rhs: 2,
                },
                None,
            )
            .unwrap();
        proof
            .reverse_unit_prop(
                &Constr {
                    terms: vec![(5, false, "x3"), (-12, true, "x4")],
                    rhs: 3,
                },
                [super::ConstraintId::last(1), super::ConstraintId::abs(42)],
            )
            .unwrap();
        drop(proof);
        let output = std::fs::read_to_string(proof_file).expect("failed to read proof");
        #[cfg(feature = "version2")]
        assert_eq!(
            output,
            format!(
                "pseudo-Boolean proof version 2.0
f 0
{RUP} 3 x1 -42 ~x2 >= 2 ;
{RUP} 5 x3 -12 ~x4 >= 3 ; -1 42
output NONE
conclusion NONE
end pseudo-Boolean proof
"
            )
        );
        #[cfg(not(feature = "version2"))]
        assert_eq!(
            output,
            format!(
                "pseudo-Boolean proof version 3.0
f 0;
{RUP} 3 x1 -42 ~x2 >= 2 ;
{RUP} 5 x3 -12 ~x4 >= 3 : -1 42;
output NONE;
conclusion NONE;
end pseudo-Boolean proof;
"
            )
        );
    }
}
