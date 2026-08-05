//! # Helper Macros for Easier Use of the Crate

/// Helper macro to create reified constraints with syntax looking similar to VeriPB syntax
#[macro_export]
macro_rules! reified {
    ($lit:block <== $constr:expr) => {
        $crate::ReifiedConstraint::constraint_implies_lit($constr, $crate::Axiom::from($lit))
    };
    ($($lit:block)+ ==> $constr:expr) => {
        $crate::ReifiedConstraint::lits_imply_constraint([$($crate::Axiom::from($lit)),+], $constr)
    };
    ($($lit:block),+ ==> $constr:expr) => {
        $crate::ReifiedConstraint::lits_imply_constraint([$($crate::Axiom::from($lit)),+], $constr)
    };
    (iterator: $lits:block ==> $constr:expr) => {
        $crate::ReifiedConstraint::lits_imply_constraint($lits.into_iter().map($crate::Axiom::from), $constr)
    };
}

macro_rules! implement {
    (forward from $wrapped:ident) => {
        fn writer(&mut self) -> &mut impl std::io::Write {
            self.$wrapped.writer()
        }

        fn new_id(&mut self) -> crate::AbsConstraintId {
            self.$wrapped.new_id()
        }
    };

    (operations$( with $pre:ident)?) => {
        /// Adds a new constraint that is derived via a sequence of operations and returns its
        /// [`crate::AbsConstraintId`]
        ///
        ///
        /// # Proof Log
        ///
        /// Adds a `pol`-rule line.
        ///
        /// # Errors
        ///
        /// If writing the proof fails.
        pub fn operations<V>(
            &mut self,
            operations: &crate::OperationSequence<V>,
        ) -> std::io::Result<crate::AbsConstraintId>
        where
            V: VarLike,
        {
            $(self.$pre()?;)?
            let level = self.level();
            writeln!(
                self.writer(),
                "{:indent$}{pol} {operations}{term}",
                "",
                indent = level * 2,
                pol = crate::keywords::POLISH,
                term = crate::keywords::RULE_TERM
            )?;
            Ok(self.new_id())
        }
    };

    (reverse_unit_prop$( with $pre:ident)?) => {
        /// Adds a constraint implied by reverse unit propagation and returns its
        /// [`crate::AbsConstraintId`]
        ///
        /// # Proof Log
        ///
        /// Adds a `rup`-rule line.
        ///
        /// # Errors
        ///
        /// If writing the proof fails.
        pub fn reverse_unit_prop<C, I>(
            &mut self,
            constr: &C,
            hints: I,
        ) -> std::io::Result<crate::AbsConstraintId>
        where
            C: crate::ConstraintLike,
            I: IntoIterator<Item = crate::ConstraintId>,
        {
            $(self.$pre()?;)?
            let mut hints = hints.into_iter().peekable();
            let level = self.level();
            if hints.peek().is_some() {
                writeln!(
                    self.writer(),
                    "{:indent$}{rup} {constr} {sep} {hints}{term}",
                    "",
                    indent = level * 2,
                    rup = crate::keywords::RUP,
                    constr = crate::ConstrFormatter::from(constr),
                    sep = crate::keywords::SEP_A,
                    hints = hints.format(" "),
                    term = crate::keywords::RULE_TERM,
                )?;
            } else {
                writeln!(
                    self.writer(),
                    "{:indent$}{rup} {constr}{term}",
                    "",
                    indent = level * 2,
                    rup = crate::keywords::RUP,
                    constr = crate::ConstrFormatter::from(constr),
                    term = crate::keywords::RULE_TERM,
                )?;
            }
            Ok(self.new_id())
        }
    };

    (redundant) => {
        /// Adds a constraint that is redundant, checked via redundance based strengthening
        ///
        /// # Proof Log
        ///
        /// Adds a `red`-rule line.
        ///
        /// # Errors
        ///
        /// If writing the proof fails.
        pub fn redundant<C, SI>(
            &mut self,
            constr: &C,
            subs: SI,
        ) -> std::io::Result<crate::guards::SubProof<'_, Self, AbsConstraintId, true>>
        where
            C: crate::ConstraintLike,
            SI: IntoIterator<Item = crate::Substitution<C::Var>>,
        {
            let level = self.level();
            write!(
                self.writer(),
                "{:indent$}{red} {constr} {sep} {subs}",
                "",
                indent = level * 2,
                red = crate::keywords::REDUNDANT,
                constr = crate::ConstrFormatter::from(constr),
                sep = crate::keywords::SEP_A,
                subs = subs.into_iter().format(" ")
            )?;
            Ok(crate::guards::SubProof::new(self, 1))
        }
    }
}
pub(crate) use implement;
