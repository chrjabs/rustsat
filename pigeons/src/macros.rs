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

/// Helper macro for easier notation of operation sequences
///
/// As operators, this macro uses the same notation as the VeriPB syntax, however _not_ in reverse
/// polish notation.
/// For parsing reasons of declarative macros, every element in the operation sequence must be a
/// Rust block, an identifier, or a [`usize`] literal, where they are allowed.
/// Additionally, with the `[<VeriPB ID>]` syntax literal constraint IDs (i.e., `2` or `-2`) can
/// be used.
///
/// # Examples
///
/// By default `&'static str` is used as the variable type, which works if no actual variables are
/// involved.
///
/// ```
/// let first = pigeons::AbsConstraintId::new(5);
/// let derivation = pigeons::derivation!(first c 2 + [42] * 4 d 3 + {pigeons::AbsConstraintId::new(5)});
/// assert_eq!(&format!("{derivation}"), "5 2 c 42 4 * 3 d 5 + +");
/// ```
///
/// Alternatively, the variable type can be explicitly specified.
///
/// ```
/// let first = pigeons::AbsConstraintId::new(5);
/// pigeons::derivation!(vartype &'static str: first + [42] + {pigeons::AbsConstraintId::new(5)});
/// assert_eq!(&format!("{derivation}"), "5 2 c 42 4 * 3 d 5 + +");
/// ```
///
/// One peculiarity of this macro is that sequences of additions are accumulated from the right
/// instead of the left. To counteract this, you can use parentheses.
///
/// ```
/// pigeons::derivation!([5] + [-2] + [3]);
/// assert_eq!(&format!("{derivation}"), "5 -2 3 + +");
///
/// pigeons::derivation!(([5] + [-2]) + [3]);
/// assert_eq!(&format!("{derivation}"), "5 -2 + 3 +");
/// ```
#[macro_export]
macro_rules! derivation {
    // Addition
    (vartype $vartype:ty: $left:tt + $($tail:tt)+) => {{
        $crate::derivation!(vartype $vartype: $left) + $crate::derivation!(vartype $vartype: $($tail)+)
    }};

    // Multiplication
    (vartype $vartype:ty: $left:tt * $mult:block $($tail:tt)*) => {{
        let mult: usize = $mult;
        $crate::derivation!(vartype $vartype: $left * mult $($tail)*)
    }};
    (vartype $vartype:ty: $left:tt * $mult:literal $($tail:tt)*) => {{
        let mult: usize = $mult;
        $crate::derivation!(vartype $vartype: $left * mult $($tail)*)
    }};
    (vartype $vartype:ty: $left:tt * $mult:ident $($tail:tt)*) => {{
        let mult: usize = $mult;
        let multiplied = $crate::derivation!(vartype $vartype: $left) * mult;
        $crate::derivation!(vartype $vartype: multiplied $($tail)*)
    }};

    // Division (normalized)
    (vartype $vartype:ty: $left:tt d $div:block $($tail:tt)*) => {{
        let div: usize = $div;
        $crate::derivation!(vartype $vartype: $left d div $($tail)*)
    }};
    (vartype $vartype:ty: $left:tt d $div:literal $($tail:tt)*) => {{
        let div: usize = $div;
        $crate::derivation!(vartype $vartype: $left d div $($tail)*)
    }};
    (vartype $vartype:ty: $left:tt d $div:ident $($tail:tt)*) => {{
        let div: usize = $div;
        let divided = $crate::OperationLike::normalized_form_division($crate::derivation!(vartype $vartype: $left), div);
        $crate::derivation!(vartype $vartype: divided $($tail)*)
    }};

    // Division (variable)
    (vartype $vartype:ty: $left:tt c $div:block $($tail:tt)*) => {{
        let div: usize = $div;
        $crate::derivation!(vartype $vartype: $left c div $($tail)*)
    }};
    (vartype $vartype:ty: $left:tt c $div:literal $($tail:tt)*) => {{
        let div: usize = $div;
        $crate::derivation!(vartype $vartype: $left c div $($tail)*)
    }};
    (vartype $vartype:ty: $left:tt c $div:ident $($tail:tt)*) => {{
        let div: usize = $div;
        let divided = $crate::OperationLike::variable_form_division($crate::derivation!(vartype $vartype: $left), div);
        $crate::derivation!(vartype $vartype: divided $($tail)*)
    }};

    // Saturation
    (vartype $vartype:ty: $left:tt s $($tail:tt)*) => {{
        let saturated = $crate::OperationLike::saturate($crate::derivation!(vartype $vartype: $left));
        $crate::derivation!(vartype $vartype: saturated $($tail)*)
    }};

    // Weakening
    (vartype $vartype:ty: $left:tt w $var:block $($tail:tt)*) => {{
        let var: $vartype = $var;
        $crate::derivation!(vartype $vartype: $left w var $($tail)*)
    }};
    (vartype $vartype:ty: $left:tt w $var:literal $($tail:tt)*) => {{
        let var: $vartype = $var;
        $crate::derivation!(vartype $vartype: $left w var $($tail)*)
    }};
    (vartype $vartype:ty: $left:tt w $var:ident $($tail:tt)*) => {{
        let var: $vartype = $var;
        let weakened = $crate::OperationLike::weaken($crate::derivation!(vartype $vartype: $left), var);
        $crate::derivation!(vartype $vartype: weakened $($tail)*)
    }};

    // Subtraction
    (vartype $vartype:ty: $left:tt - $sub:block $($tail:tt)*) => {{
        let sub: usize = $sub;
        $crate::derivation!(vartype $vartype: $left - sub $($tail)*)
    }};
    (vartype $vartype:ty: $left:tt - $sub:literal $($tail:tt)*) => {{
        let sub: usize = $sub;
        $crate::derivation!(vartype $vartype: $left - sub $($tail)*)
    }};
    (vartype $vartype:ty: $left:tt - $sub:ident $($tail:tt)*) => {{
        let sub: usize = $sub;
        let subtracted = $crate::derivation!(vartype $vartype: $left) - sub;
        $crate::derivation!(vartype $vartype: subtracted $($tail)*)
    }};

    // MIR cut (normalized)
    (vartype $vartype:ty: $left:tt n $mir:block $($tail:tt)*) => {{
        let mir: usize = $mir;
        $crate::derivation!(vartype $vartype: $left n mir $($tail)*)
    }};
    (vartype $vartype:ty: $left:tt n $mir:literal $($tail:tt)*) => {{
        let mir: usize = $mir;
        $crate::derivation!(vartype $vartype: $left n mir $($tail)*)
    }};
    (vartype $vartype:ty: $left:tt n $mir:ident $($tail:tt)*) => {{
        let mir: usize = $mir;
        let mir = $crate::OperationLike::normalized_form_mir_cut($crate::derivation!(vartype $vartype: $left), mir);
        $crate::derivation!(vartype $vartype: mir $($tail)*)
    }};

    // MIR cut (variable)
    (vartype $vartype:ty: $left:tt m $mir:block $($tail:tt)*) => {{
        let mir: usize = $mir;
        $crate::derivation!(vartype $vartype: $left m mir $($tail)*)
    }};
    (vartype $vartype:ty: $left:tt m $mir:literal $($tail:tt)*) => {{
        let mir: usize = $mir;
        $crate::derivation!(vartype $vartype: $left m mir $($tail)*)
    }};
    (vartype $vartype:ty: $left:tt m $mir:ident $($tail:tt)*) => {{
        let mir: usize = $mir;
        let mir = $crate::OperationLike::variable_form_mir_cut($crate::derivation!(vartype $vartype: $left), mir);
        $crate::derivation!(vartype $vartype: mir $($tail)*)
    }};

    // Base cases
    // Literal constraint ID
    (vartype $vartype:ty: [$rest:expr]) => {{
        let id: isize = $rest;
        let id = if id > 0 {
            $crate::ConstraintId::abs(id.unsigned_abs())
        } else {
            $crate::ConstraintId::last(id.unsigned_abs())
        };
        $crate::OperationSequence::<$vartype>::from(id)
    }};
    // Subexpression in parentheses
    (vartype $vartype:ty: ($($rest:tt)+)) => {
        $crate::derivation!(vartype $vartype: $($rest)+)
    };
    // Simple block
    (vartype $vartype:ty: $rest:block) => {
        $crate::OperationSequence::<$vartype>::from($rest)
    };
    // Simple identifier
    (vartype $vartype:ty: $rest:ident) => {
        $crate::OperationSequence::<$vartype>::from($rest)
    };

    // Default vartype
    ($($tail:tt)*) => {
        $crate::derivation!(vartype &'static str: $($tail)*)
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

#[cfg(test)]
mod tests {
    #[test]
    fn derivations() {
        use crate::AbsConstraintId as AId;
        use crate::VarLike;

        let named = "x42".pos_axiom();
        let first = AId::new(5);
        let second = AId::new(42);
        let third = AId::new(3);
        assert_eq!(
            &format!("{}", crate::derivation!({ "x42".pos_axiom() })),
            "x42"
        );
        assert_eq!(&format!("{}", crate::derivation!(named)), "x42");
        assert_eq!(
            &format!(
                "{}",
                crate::derivation!({ AId::new(5) } + { AId::new(42) } + { AId::new(3) })
            ),
            "5 42 3 + +"
        );
        assert_eq!(
            &format!("{}", crate::derivation!(first + second + third)),
            "5 42 3 + +"
        );
        assert_eq!(
            &format!("{}", crate::derivation!((first + second) + third)),
            "5 42 + 3 +"
        );
        assert_eq!(
            &format!("{}", crate::derivation!(first + { AId::new(42) } + third)),
            "5 42 3 + +"
        );
        assert_eq!(&format!("{}", crate::derivation!(first * 5)), "5 5 *");
        assert_eq!(
            format!("{}", crate::derivation!(first * 5 + second)),
            "5 5 * 42 +"
        );
        assert_eq!(&format!("{}", crate::derivation!(first d 5)), "5 5 d");
        assert_eq!(
            &format!("{}", crate::derivation!(first d 5 + second)),
            "5 5 d 42 +"
        );
        assert_eq!(&format!("{}", crate::derivation!(first c 5)), "5 5 c");
        assert_eq!(
            &format!("{}", crate::derivation!(first c 5 + second)),
            "5 5 c 42 +"
        );
        assert_eq!(&format!("{}", crate::derivation!(first s)), "5 s");
        assert_eq!(
            &format!("{}", crate::derivation!(first s + second)),
            "5 s 42 +"
        );
        assert_eq!(&format!("{}", crate::derivation!(first w "x42")), "5 x42 w");
        assert_eq!(
            &format!("{}", crate::derivation!(first w "x42" + second)),
            "5 x42 w 42 +"
        );
        assert_eq!(&format!("{}", crate::derivation!(first - 22)), "5 22 -");
        assert_eq!(
            &format!("{}", crate::derivation!(first - 22 + second)),
            "5 22 - 42 +"
        );
        assert_eq!(&format!("{}", crate::derivation!(first n 22)), "5 22 n");
        assert_eq!(
            &format!("{}", crate::derivation!(first n 22 + second)),
            "5 22 n 42 +"
        );
        assert_eq!(&format!("{}", crate::derivation!(first m 22)), "5 22 m");
        assert_eq!(
            &format!("{}", crate::derivation!(first m 22 + second)),
            "5 22 m 42 +"
        );
        assert_eq!(
            &format!("{}", crate::derivation!(first m 22 + [42])),
            "5 22 m 42 +"
        );
        assert_eq!(
            &format!("{}", crate::derivation!(first m 22 + [-2])),
            "5 22 m -2 +"
        );
    }
}
