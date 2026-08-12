//! # Guard Types for Substructures of the Proof

use itertools::Itertools;

use crate::AbsConstraintId;
use crate::VarLike;

/// Guard type for writing sub-proofs for rules
#[derive(Debug)]
pub struct SubProof<'proof, Writer: std::io::Write, Return = AbsConstraintId> {
    proof: &'proof mut crate::Proof<Writer>,
    negated: Option<AbsConstraintId>,
    prefix: &'static str,
    level: usize,
    _return: std::marker::PhantomData<Return>,
}

impl<'proof, Writer, Return> SubProof<'proof, Writer, Return>
where
    Writer: std::io::Write,
{
    pub(crate) fn new(proof: &'proof mut crate::Proof<Writer>, level: usize) -> Self {
        Self::new_with_prefix(proof, "", level)
    }

    pub(crate) fn new_with_prefix(
        proof: &'proof mut crate::Proof<Writer>,
        prefix: &'static str,
        level: usize,
    ) -> Self {
        Self {
            proof,
            negated: None,
            prefix,
            level,
            _return: std::marker::PhantomData,
        }
    }

    fn start(&mut self) -> std::io::Result<AbsConstraintId> {
        let negated = if let Some(negated) = self.negated {
            negated
        } else {
            // negated constraint
            let negated = self.new_id();
            self.negated = Some(negated);
            let prefix = self.prefix;
            writeln!(
                self.writer(),
                "{prefix}{} {}",
                crate::keywords::SEP_A,
                crate::keywords::SUBPROOF
            )?;
            negated
        };
        Ok(negated)
    }

    fn level(&self) -> usize {
        self.level
    }

    /// Gets the [`AbsConstraintId`] of the negated constraint of the sub-proof
    ///
    /// # Errors
    ///
    /// If writing the proof fails
    pub fn negated_constraint_id(&mut self) -> std::io::Result<AbsConstraintId> {
        self.start()
    }

    crate::macros::implement!(forward_from_proof);
    crate::macros::implement!(operations with start);
    crate::macros::implement!(reverse_unit_prop with start);
    crate::macros::implement!(proof_goal with start);

    fn write_end(&mut self) -> std::io::Result<()> {
        if self.negated.is_some() {
            let level = self.level();
            writeln!(
                self.writer(),
                "{:indent$}{qed}{term}",
                "",
                indent = (level - 1) * 2,
                qed = crate::keywords::QED,
                term = crate::keywords::RULE_TERM
            )
        } else {
            writeln!(self.writer(), "{}", crate::keywords::RULE_TERM)
        }
    }
}

impl<Writer> SubProof<'_, Writer, ()>
where
    Writer: std::io::Write,
{
    /// Closes off the sub-proof
    ///
    /// If no elements have been written in the sub-proof, no sub-proof is written
    ///
    /// # Errors
    ///
    /// If writing the proof fails
    pub fn finish(mut self) -> std::io::Result<()> {
        self.write_end()?;
        std::mem::forget(self);
        Ok(())
    }
}

impl<Writer> SubProof<'_, Writer, AbsConstraintId>
where
    Writer: std::io::Write,
{
    /// Closes off the sub-proof
    ///
    /// If no elements have been written in the sub-proof, no sub-proof is written
    ///
    /// # Errors
    ///
    /// If writing the proof fails
    pub fn finish(mut self) -> std::io::Result<AbsConstraintId> {
        self.write_end()?;
        let id = self.new_id();
        std::mem::forget(self);
        Ok(id)
    }
}

impl<Writer, Return> Drop for SubProof<'_, Writer, Return>
where
    Writer: std::io::Write,
{
    fn drop(&mut self) {
        self.write_end()
            .expect("failed to write closing of sub-proof");
    }
}

/// Guard type for writing proof goals in a sub-proof
#[derive(Debug)]
pub struct ProofGoal<'proof, Writer: std::io::Write> {
    proof: &'proof mut crate::Proof<Writer>,
    negated: AbsConstraintId,
    level: usize,
}

impl<'proof, Writer> ProofGoal<'proof, Writer>
where
    Writer: std::io::Write,
{
    fn new(
        proof: &'proof mut crate::Proof<Writer>,
        id: crate::ProofGoalId,
        level: usize,
    ) -> std::io::Result<Self> {
        let negated = proof.new_id(); // negated constraint
        writeln!(
            proof.writer(),
            "{:indent$}{proofgoal} {id}",
            "",
            indent = (level - 1) * 2,
            proofgoal = crate::keywords::PROOFGOAL
        )?;
        Ok(Self {
            proof,
            negated,
            level,
        })
    }

    /// Gets the [`AbsConstraintId`] of the negated constraint of the proof goal
    pub fn negated_constraint_id(&mut self) -> AbsConstraintId {
        self.negated
    }

    fn level(&self) -> usize {
        self.level
    }

    crate::macros::implement!(forward_from_proof);
    crate::macros::implement!(operations);
    crate::macros::implement!(reverse_unit_prop);

    /// Closes off the proof goal
    ///
    /// # Errors
    ///
    /// If writing the proof fails
    pub fn finish(mut self) -> std::io::Result<()> {
        let level = self.level();
        writeln!(
            self.writer(),
            "{:indent$}{qed}{term}",
            "",
            indent = (level - 1) * 2,
            qed = crate::keywords::QED,
            term = crate::keywords::RULE_TERM
        )?;
        std::mem::forget(self);
        Ok(())
    }
}

impl<Writer> Drop for ProofGoal<'_, Writer>
where
    Writer: std::io::Write,
{
    fn drop(&mut self) {
        let level = self.level();
        writeln!(
            self.writer(),
            "{:indent$}{qed}{term}",
            "",
            indent = (level - 1) * 2,
            qed = crate::keywords::QED,
            term = crate::keywords::RULE_TERM
        )
        .expect("failed to write closing of proof goal");
    }
}
