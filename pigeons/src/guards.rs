//! # Guard Types for Substructures of the Proof

use std::io::Write as _;

use itertools::Itertools;

use crate::guards::sealed::ProofScope as _;
use crate::AbsConstraintId;
use crate::VarLike;

/// Trait capturing a proof scope
pub trait ProofScope: sealed::ProofScope {}

impl<T> ProofScope for T where T: sealed::ProofScope {}

/// Trait capturing a proof sub scope
pub trait SubScopeType: sealed::SubScopeType {}

impl<T> SubScopeType for T where T: sealed::SubScopeType {}

mod sealed {
    pub trait ProofScope {
        type Writer: std::io::Write;

        fn writer(&mut self) -> &mut Self::Writer;

        fn new_id(&mut self) -> crate::AbsConstraintId;

        fn increase_next_id(&mut self, num_constraints: usize);

        fn num_order_spec_constraints(&self) -> usize {
            0
        }
    }

    pub trait SubScopeType {
        const ID: &'static str;

        fn prepare_scope<Scope>(scope: &mut Scope)
        where
            Scope: ProofScope;
    }
}

impl<Writer> sealed::ProofScope for crate::Proof<Writer>
where
    Writer: std::io::Write,
{
    type Writer = Writer;

    fn writer(&mut self) -> &mut Self::Writer {
        &mut self.writer
    }

    fn new_id(&mut self) -> AbsConstraintId {
        self.new_id()
    }

    fn increase_next_id(&mut self, num_constraints: usize) {
        self.next_id += num_constraints;
    }

    fn num_order_spec_constraints(&self) -> usize {
        self.num_order_spec_constrs
    }
}

/// Guard type for writing sub-proofs for rules
#[derive(Debug)]
pub struct SubProof<'scope, Scope: ProofScope, Return = AbsConstraintId, const SCOPES: bool = false>
{
    scope: &'scope mut Scope,
    negated: Option<AbsConstraintId>,
    prefix: &'static str,
    level: usize,
    _return: std::marker::PhantomData<Return>,
}

impl<'scope, Scope, Return, const SCOPES: bool> SubProof<'scope, Scope, Return, SCOPES>
where
    Scope: ProofScope,
{
    pub(crate) fn new(scope: &'scope mut Scope, level: usize) -> Self {
        Self::new_with_prefix(scope, "", level)
    }

    pub(crate) fn new_with_prefix(
        scope: &'scope mut Scope,
        prefix: &'static str,
        level: usize,
    ) -> Self {
        Self {
            scope,
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

    crate::macros::implement!(forward from scope);
    crate::macros::implement!(operations with start);
    crate::macros::implement!(reverse_unit_prop with start);

    /// Starts a new proof goal in the sub-proof
    ///
    /// # Errors
    ///
    /// If writing the proof fails
    pub fn proof_goal(
        &mut self,
        id: crate::ProofGoalId,
    ) -> std::io::Result<crate::guards::ProofGoal<'_, Scope>> {
        self.start()?;
        let level = self.level();
        crate::guards::ProofGoal::new(self.scope, id, level)
    }

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

impl<Scope, Return> SubProof<'_, Scope, Return, true>
where
    Scope: ProofScope,
{
    /// Starts the `geq` scope related to orders with a specification
    ///
    /// # Errors
    ///
    /// If writing the proof fails
    pub fn geq_scope(&mut self) -> std::io::Result<SubScope<'_, Scope, GeqScope>> {
        self.start()?;
        SubScope::new(self.scope, self.level() + 1)
    }

    /// Starts the `leq` scope related to orders with a specification
    ///
    /// # Errors
    ///
    /// If writing the proof fails
    pub fn leq_scope(&mut self) -> std::io::Result<SubScope<'_, Scope, LeqScope>> {
        self.start()?;
        SubScope::new(self.scope, self.level() + 1)
    }
}

impl<Scope, const SCOPES: bool> SubProof<'_, Scope, (), SCOPES>
where
    Scope: ProofScope,
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

impl<Scope, const SCOPES: bool> SubProof<'_, Scope, AbsConstraintId, SCOPES>
where
    Scope: ProofScope,
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

impl<Scope, Return, const SCOPES: bool> Drop for SubProof<'_, Scope, Return, SCOPES>
where
    Scope: ProofScope,
{
    fn drop(&mut self) {
        self.write_end()
            .expect("failed to write closing of sub-proof");
    }
}

/// Guard type for writing proof goals in a sub-proof
#[derive(Debug)]
pub struct ProofGoal<'scope, Scope: ProofScope> {
    scope: &'scope mut Scope,
    negated: AbsConstraintId,
    level: usize,
}

impl<'scope, Scope> ProofGoal<'scope, Scope>
where
    Scope: ProofScope,
{
    fn new(
        scope: &'scope mut Scope,
        id: crate::ProofGoalId,
        level: usize,
    ) -> std::io::Result<Self> {
        let negated = scope.new_id(); // negated constraint
        writeln!(
            scope.writer(),
            "{:indent$}{proofgoal} {id}",
            "",
            indent = (level - 1) * 2,
            proofgoal = crate::keywords::PROOFGOAL
        )?;
        Ok(Self {
            scope,
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

    crate::macros::implement!(forward from scope);
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

impl<Scope> Drop for ProofGoal<'_, Scope>
where
    Scope: ProofScope,
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

/// Guard type for writing a partial order
#[derive(Debug)]
pub struct Order<'proof, Writer: std::io::Write> {
    wrapper: OrderAutoClosing<'proof, Writer>,
    data: crate::Order,
    input_var_set: rustc_hash::FxHashSet<String>,
    input_vars: Vec<String>,
    aux_var_set: rustc_hash::FxHashSet<String>,
    aux_vars: Vec<String>,
}

impl<'proof, Writer> Order<'proof, Writer>
where
    Writer: std::io::Write,
{
    pub(crate) fn new<S>(proof: &'proof mut crate::Proof<Writer>, name: S) -> std::io::Result<Self>
    where
        S: Into<String>,
    {
        let name: String = name.into();
        writeln!(
            proof.writer(),
            "{def} {name}",
            def = crate::keywords::ORDER_DEFINE,
        )?;
        Ok(Self {
            wrapper: OrderAutoClosing(proof),
            data: crate::Order::new(name),
            input_var_set: rustc_hash::FxHashSet::default(),
            input_vars: vec![],
            aux_var_set: rustc_hash::FxHashSet::default(),
            aux_vars: vec![],
        })
    }

    /// Adds a new input variable to the order
    ///
    /// _Note_: this can safely be called multiple times with the same variable
    pub fn add_input_var<V>(&mut self, var: V) -> crate::OrderInputVar<V>
    where
        V: VarLike,
    {
        let var_str = format!("{}", V::Formatter::from(var));
        if self.input_var_set.insert(var_str) {
            self.input_vars.push(format!("{}", V::Formatter::from(var)));
        }
        crate::OrderInputVar::new(var)
    }

    /// Adds a new auxiliary variable to the order
    ///
    /// _Note_: this can safely be called multiple times with the same name
    pub fn add_aux_var<V>(&mut self, var: V) -> crate::OrderAuxVar<V>
    where
        V: VarLike,
    {
        let var_str = format!("{}", V::Formatter::from(var));
        if self.aux_var_set.insert(var_str) {
            self.aux_vars.push(format!("{}", V::Formatter::from(var)));
        }
        crate::OrderAuxVar::new(var)
    }

    fn write_vars(&mut self) -> std::io::Result<()> {
        let writer = self.wrapper.writer();
        writeln!(writer, "  {vars}", vars = crate::keywords::ORDER_VARS)?;
        writeln!(
            writer,
            "    {left} {vars}{term}",
            left = crate::keywords::ORDER_VARS_LEFT,
            vars = self
                .input_vars
                .iter()
                .map(|v| crate::OrderInputVar::new(v.as_str()).left())
                .format(" "),
            term = crate::keywords::RULE_TERM,
        )?;
        writeln!(
            writer,
            "    {right} {vars}{term}",
            right = crate::keywords::ORDER_VARS_RIGHT,
            vars = self
                .input_vars
                .iter()
                .map(|v| crate::OrderInputVar::new(v.as_str()).right())
                .format(" "),
            term = crate::keywords::RULE_TERM,
        )?;
        if !self.aux_vars.is_empty() {
            writeln!(
                writer,
                "    {aux} {vars}{term}",
                aux = crate::keywords::ORDER_VARS_AUX,
                vars = self
                    .aux_vars
                    .iter()
                    .map(|v| crate::OrderAuxVar::new(v.as_str()).aux())
                    .format(" "),
                term = crate::keywords::RULE_TERM,
            )?;
        }
        writeln!(
            writer,
            "  {end}{term}",
            end = crate::keywords::END,
            term = crate::keywords::RULE_TERM,
        )
    }

    /// Starts the specification of the order
    ///
    /// # Errors
    ///
    /// If writing the proof fails
    pub fn specification(mut self) -> std::io::Result<OrderSpecification<'proof, Writer>> {
        self.write_vars()?;
        OrderSpecification::new(self)
    }

    /// Starts the definition of the order
    ///
    /// # Errors
    ///
    /// If writing the proof fails
    pub fn definition(mut self) -> std::io::Result<OrderDefinition<'proof, Writer>> {
        self.write_vars()?;
        let Self {
            wrapper,
            data,
            input_var_set: _,
            input_vars,
            aux_var_set: _,
            aux_vars,
        } = self;
        OrderDefinition::new(
            OrderSpecAutoClosing::new(wrapper),
            data,
            input_vars,
            aux_vars,
        )
    }

    /// Finishes the order
    ///
    /// # Errors
    ///
    /// If writing the proof fails
    pub fn finish(mut self) -> std::io::Result<crate::Order> {
        self.write_vars()?;
        let Self {
            wrapper,
            data,
            input_var_set: _,
            input_vars,
            aux_var_set: _,
            aux_vars,
        } = self;
        // NOTE: definition is mandatory
        OrderDefinition::new(
            OrderSpecAutoClosing::new(wrapper),
            data,
            input_vars,
            aux_vars,
        )?
        .finish()
    }
}

#[derive(Debug)]
struct OrderAutoClosing<'proof, Writer: std::io::Write>(&'proof mut crate::Proof<Writer>);

impl<Writer> OrderAutoClosing<'_, Writer>
where
    Writer: std::io::Write,
{
    fn writer(&mut self) -> &mut Writer {
        self.0.writer()
    }
}

impl<Writer> Drop for OrderAutoClosing<'_, Writer>
where
    Writer: std::io::Write,
{
    fn drop(&mut self) {
        // NOTE: produce syntactically correct order, but don't know about variables the user might
        // have added, so just produce empty variables section
        writeln!(
            self.writer(),
            "  {vars}",
            vars = crate::keywords::ORDER_VARS,
        )
        .expect("failed to write closing of order");
        writeln!(
            self.writer(),
            "    {left} {term}",
            left = crate::keywords::ORDER_VARS_LEFT,
            term = crate::keywords::RULE_TERM,
        )
        .expect("failed to write closing of order");
        writeln!(
            self.writer(),
            "    {right} {term}",
            right = crate::keywords::ORDER_VARS_RIGHT,
            term = crate::keywords::RULE_TERM,
        )
        .expect("failed to write closing of order");
        writeln!(
            self.writer(),
            "  {end}{term}",
            end = crate::keywords::END,
            term = crate::keywords::RULE_TERM,
        )
        .expect("failed to write closing of order");
        // NOTE: definition is mandatory
        writeln!(
            self.writer(),
            "  {def}",
            def = crate::keywords::ORDER_DEFINITION,
        )
        .expect("failed to write closing of order");
        writeln!(
            self.writer(),
            "  {end}{term}",
            end = crate::keywords::END,
            term = crate::keywords::RULE_TERM,
        )
        .expect("failed to write closing of order");
        writeln!(
            self.writer(),
            "{end}{term}",
            end = crate::keywords::END,
            term = crate::keywords::RULE_TERM,
        )
        .expect("failed to write closing of order");
    }
}

/// Guard type for writing the definition of a partial order
#[derive(Debug)]
pub struct OrderSpecification<'proof, Writer: std::io::Write> {
    wrapper: OrderSpecAutoClosing<'proof, Writer>,
    order: crate::Order,
    input_vars: Vec<String>,
    aux_vars: Vec<String>,
    next_id: AbsConstraintId,
}

impl<'proof, Writer> OrderSpecification<'proof, Writer>
where
    Writer: std::io::Write,
{
    fn new(order: Order<'proof, Writer>) -> std::io::Result<Self> {
        let Order {
            mut wrapper,
            data,
            input_var_set: _,
            input_vars,
            aux_var_set: _,
            aux_vars,
        } = order;
        writeln!(
            wrapper.writer(),
            "  {spec}",
            spec = crate::keywords::ORDER_SPECIFICATION
        )?;
        Ok(Self {
            wrapper: OrderSpecAutoClosing::new(wrapper),
            order: data,
            input_vars,
            aux_vars,
            next_id: AbsConstraintId::new(1),
        })
    }

    // required with this signature for macro implementations
    #[expect(clippy::unused_self)]
    fn level(&self) -> usize {
        2
    }

    // required with this signature for macro implementations
    #[expect(clippy::unnecessary_wraps)]
    fn new_constraint(&mut self) -> std::io::Result<()> {
        self.order.new_spec_constraint();
        Ok(())
    }

    crate::macros::implement!(operations with new_constraint);

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
    pub fn reverse_unit_prop<C, I, V>(
        &mut self,
        constr: &C,
        hints: I,
    ) -> std::io::Result<crate::AbsConstraintId>
    where
        C: crate::ConstraintLike<Var = crate::OrderVar<V>>,
        I: IntoIterator<Item = crate::ConstraintId>,
        V: VarLike,
    {
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
                "{:indent$}{rup} {constr} {term}",
                "",
                indent = level * 2,
                rup = crate::keywords::RUP,
                constr = crate::ConstrFormatter::from(constr),
                term = crate::keywords::RULE_TERM,
            )?;
        }
        self.order.new_spec_constraint();
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
    pub fn redundant<C, SI, V>(
        &mut self,
        constr: &C,
        subs: SI,
    ) -> std::io::Result<SubProof<'_, Self>>
    where
        C: crate::ConstraintLike<Var = crate::OrderVar<V>>,
        SI: IntoIterator<Item = crate::Substitution<C::Var>>,
        V: VarLike,
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
        self.order.new_spec_constraint();
        Ok(SubProof::new(self, level))
    }

    /// Starts the definition of the order
    ///
    /// # Errors
    ///
    /// If writing the proof fails
    pub fn definition(mut self) -> std::io::Result<OrderDefinition<'proof, Writer>> {
        writeln!(
            self.writer(),
            "  {end}{term}",
            end = crate::keywords::END,
            term = crate::keywords::RULE_TERM,
        )?;
        let Self {
            wrapper,
            order,
            input_vars,
            aux_vars,
            next_id: _,
        } = self;
        OrderDefinition::new(wrapper, order, input_vars, aux_vars)
    }

    /// Finishes the order
    ///
    /// # Errors
    ///
    /// If writing the proof fails
    pub fn finish(mut self) -> std::io::Result<crate::Order> {
        writeln!(
            self.wrapper.writer(),
            "  {end}{term}",
            end = crate::keywords::END,
            term = crate::keywords::RULE_TERM
        )?;
        // NOTE: definition is mandatory
        writeln!(
            self.writer(),
            "  {def}",
            def = crate::keywords::ORDER_DEFINITION,
        )?;
        writeln!(
            self.writer(),
            "  {end}{term}",
            end = crate::keywords::END,
            term = crate::keywords::RULE_TERM,
        )?;
        writeln!(
            self.wrapper.writer(),
            "{end}{term}",
            end = crate::keywords::END,
            term = crate::keywords::RULE_TERM,
        )?;
        std::mem::forget(self.wrapper);
        Ok(self.order)
    }
}

impl<Writer> sealed::ProofScope for OrderSpecification<'_, Writer>
where
    Writer: std::io::Write,
{
    type Writer = Writer;

    fn writer(&mut self) -> &mut Self::Writer {
        self.wrapper.writer()
    }

    fn new_id(&mut self) -> AbsConstraintId {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    fn increase_next_id(&mut self, num_constraints: usize) {
        self.next_id += num_constraints;
    }
}

#[derive(Debug)]
struct OrderSpecAutoClosing<'proof, Writer: std::io::Write>(
    std::mem::ManuallyDrop<OrderAutoClosing<'proof, Writer>>,
);

impl<'proof, Writer> OrderSpecAutoClosing<'proof, Writer>
where
    Writer: std::io::Write,
{
    fn new(inner: OrderAutoClosing<'proof, Writer>) -> Self {
        Self(std::mem::ManuallyDrop::new(inner))
    }

    fn writer(&mut self) -> &mut Writer {
        self.0.writer()
    }
}

impl<Writer> Drop for OrderSpecAutoClosing<'_, Writer>
where
    Writer: std::io::Write,
{
    fn drop(&mut self) {
        writeln!(
            self.writer(),
            "  {end}{term}",
            end = crate::keywords::END,
            term = crate::keywords::RULE_TERM,
        )
        .expect("failed to write closing of order");
        // NOTE: definition is mandatory
        writeln!(
            self.writer(),
            "  {def}",
            def = crate::keywords::ORDER_DEFINITION,
        )
        .expect("failed to write closing of order");
        writeln!(
            self.writer(),
            "  {end}{term}",
            end = crate::keywords::END,
            term = crate::keywords::RULE_TERM,
        )
        .expect("failed to write closing of order");
        writeln!(
            self.writer(),
            "{end}{term}",
            end = crate::keywords::END,
            term = crate::keywords::RULE_TERM,
        )
        .expect("failed to write closing of order");
    }
}

/// Guard type for writing the definition of a partial order
#[derive(Debug)]
pub struct OrderDefinition<'proof, Writer: std::io::Write> {
    wrapper: OrderDefAutoClosing<'proof, Writer>,
    order: crate::Order,
    input_vars: Vec<String>,
    aux_vars: Vec<String>,
}

impl<'proof, Writer> OrderDefinition<'proof, Writer>
where
    Writer: std::io::Write,
{
    fn new(
        mut wrapper: OrderSpecAutoClosing<'proof, Writer>,
        order: crate::Order,
        input_vars: Vec<String>,
        aux_vars: Vec<String>,
    ) -> std::io::Result<Self> {
        writeln!(
            wrapper.writer(),
            "  {def}",
            def = crate::keywords::ORDER_DEFINITION
        )?;
        Ok(Self {
            wrapper: OrderDefAutoClosing::new(wrapper),
            order,
            input_vars,
            aux_vars,
        })
    }

    /// Adds a constraint to the order definition
    ///
    /// # Errors
    ///
    /// If writing the proof fails
    pub fn definition_constraint<C, V>(
        &mut self,
        constr: &C,
    ) -> std::io::Result<crate::OrderDefinitionProofGoalId>
    where
        C: crate::ConstraintLike<Var = crate::OrderVar<V>>,
        V: VarLike,
    {
        writeln!(
            self.wrapper.writer(),
            "    {constr} ;",
            constr = crate::ConstrFormatter::from(constr),
        )?;
        self.order.new_def_constraint();
        let id = crate::OrderDefinitionProofGoalId::new(self.order.num_def_constraints());
        Ok(id)
    }

    /// Starts the transitivity proof of the order
    ///
    /// # Errors
    ///
    /// If writing the proof fails
    pub fn transitivity_proof(mut self) -> std::io::Result<OrderTransitivityProof<'proof, Writer>> {
        writeln!(
            self.wrapper.writer(),
            "  {end}{term}",
            end = crate::keywords::END,
            term = crate::keywords::RULE_TERM
        )?;
        Ok(OrderTransitivityProof::new(
            self.wrapper,
            self.order,
            self.input_vars,
            self.aux_vars,
        ))
    }

    /// Starts the reflexivity proof of the order
    ///
    /// # Errors
    ///
    /// If writing the proof fails
    pub fn reflexivity_proof(mut self) -> std::io::Result<OrderReflexivityProof<'proof, Writer>> {
        writeln!(
            self.wrapper.writer(),
            "    {qed}{term}",
            qed = crate::keywords::QED,
            term = crate::keywords::RULE_TERM,
        )
        .expect("failed to write closing of order");
        writeln!(
            self.wrapper.writer(),
            "  {end}{term}",
            end = crate::keywords::END,
            term = crate::keywords::RULE_TERM
        )?;
        Ok(OrderReflexivityProof::new(
            OrderProof::new(self.wrapper),
            self.order,
        ))
    }

    /// Finishes the order
    ///
    /// # Errors
    ///
    /// If writing the proof fails
    pub fn finish(mut self) -> std::io::Result<crate::Order> {
        writeln!(
            self.wrapper.writer(),
            "  {end}{term}",
            end = crate::keywords::END,
            term = crate::keywords::RULE_TERM
        )?;
        writeln!(
            self.wrapper.writer(),
            "{end}{term}",
            end = crate::keywords::END,
            term = crate::keywords::RULE_TERM,
        )?;
        std::mem::forget(self.wrapper);
        Ok(self.order)
    }
}

#[derive(Debug)]
struct OrderDefAutoClosing<'proof, Writer: std::io::Write>(
    std::mem::ManuallyDrop<OrderSpecAutoClosing<'proof, Writer>>,
);

impl<'proof, Writer> OrderDefAutoClosing<'proof, Writer>
where
    Writer: std::io::Write,
{
    fn new(inner: OrderSpecAutoClosing<'proof, Writer>) -> Self {
        Self(std::mem::ManuallyDrop::new(inner))
    }

    fn writer(&mut self) -> &mut Writer {
        self.0.writer()
    }
}

impl<Writer> Drop for OrderDefAutoClosing<'_, Writer>
where
    Writer: std::io::Write,
{
    fn drop(&mut self) {
        writeln!(
            self.writer(),
            "  {end}{term}",
            end = crate::keywords::END,
            term = crate::keywords::RULE_TERM,
        )
        .expect("failed to write closing of order");
        writeln!(
            self.writer(),
            "{end}{term}",
            end = crate::keywords::END,
            term = crate::keywords::RULE_TERM,
        )
        .expect("failed to write closing of order");
    }
}

/// Guard type for writing the order transitivity proof
#[derive(Debug)]
pub struct OrderTransitivityProof<'proof, Writer: std::io::Write> {
    wrapper: OrderProof<'proof, Writer>,
    order: crate::Order,
    input_vars: Vec<String>,
    aux_vars: Vec<String>,
}

impl<'proof, Writer> OrderTransitivityProof<'proof, Writer>
where
    Writer: std::io::Write,
{
    fn new(
        wrapper: OrderDefAutoClosing<'proof, Writer>,
        order: crate::Order,
        input_vars: Vec<String>,
        aux_vars: Vec<String>,
    ) -> Self {
        Self {
            wrapper: OrderProof::new(wrapper),
            order,
            input_vars,
            aux_vars,
        }
    }

    fn start(&mut self) -> std::io::Result<()> {
        if self.wrapper.used {
            return Ok(());
        }
        let writer = self.wrapper.writer();
        writeln!(
            writer,
            "  {trans}",
            trans = crate::keywords::ORDER_TRANSITIVITY
        )?;
        writeln!(writer, "    {vars}", vars = crate::keywords::ORDER_VARS)?;
        writeln!(
            writer,
            "      {fresh} {vars}{term}",
            fresh = crate::keywords::ORDER_VARS_FRESH_RIGHT,
            vars = self
                .input_vars
                .iter()
                .map(|v| crate::OrderInputVar::new(v.as_str()).fresh_right())
                .format(" "),
            term = crate::keywords::RULE_TERM,
        )?;
        if !self.aux_vars.is_empty() {
            writeln!(
                writer,
                "      {aux} {vars}{term}",
                aux = crate::keywords::ORDER_VARS_FRESH_AUX_1,
                vars = self
                    .aux_vars
                    .iter()
                    .map(|v| crate::OrderAuxVar::new(v.as_str()).fresh_1())
                    .format(" "),
                term = crate::keywords::RULE_TERM,
            )?;
            writeln!(
                writer,
                "      {aux} {vars}{term}",
                aux = crate::keywords::ORDER_VARS_FRESH_AUX_2,
                vars = self
                    .aux_vars
                    .iter()
                    .map(|v| crate::OrderAuxVar::new(v.as_str()).fresh_2())
                    .format(" "),
                term = crate::keywords::RULE_TERM,
            )?;
        }
        writeln!(
            writer,
            "    {end}{term}",
            end = crate::keywords::END,
            term = crate::keywords::RULE_TERM,
        )?;
        writeln!(self.writer(), "    {proof}", proof = crate::keywords::PROOF)?;
        self.wrapper.used = true;
        self.wrapper.next_id = AbsConstraintId::new(
            self.order.num_def_constraints() * 2 + self.order.num_spec_constraints() * 3 + 1,
        );
        Ok(())
    }

    // required with this signature for macro implementations
    #[expect(clippy::unused_self)]
    fn level(&self) -> usize {
        3
    }

    crate::macros::implement!(forward from wrapper);
    crate::macros::implement!(operations with start);
    crate::macros::implement!(reverse_unit_prop with start);

    /// Starts a new proof goal in the transitivity proof
    ///
    /// # Errors
    ///
    /// If writing the proof fails
    pub fn proof_goal(
        &mut self,
        id: crate::OrderDefinitionProofGoalId,
    ) -> std::io::Result<crate::guards::ProofGoal<'_, OrderProof<'proof, Writer>>> {
        self.start()?;
        crate::guards::ProofGoal::new(&mut self.wrapper, id.as_proof_goal_id(), 4)
    }

    /// Starts the reflexivity proof of the order
    ///
    /// # Errors
    ///
    /// If writing the proof fails
    pub fn reflexivity_proof(mut self) -> std::io::Result<OrderReflexivityProof<'proof, Writer>> {
        writeln!(
            self.writer(),
            "    {qed}{term}",
            qed = crate::keywords::QED,
            term = crate::keywords::RULE_TERM,
        )
        .expect("failed to write closing of order");
        writeln!(
            self.wrapper.writer(),
            "  {end}{term}",
            end = crate::keywords::END,
            term = crate::keywords::RULE_TERM
        )?;
        Ok(OrderReflexivityProof::new(self.wrapper, self.order))
    }

    /// Finishes the order
    ///
    /// # Errors
    ///
    /// If writing the proof fails
    pub fn finish(mut self) -> std::io::Result<crate::Order> {
        if self.wrapper.used {
            writeln!(
                self.writer(),
                "    {qed}{term}",
                qed = crate::keywords::QED,
                term = crate::keywords::RULE_TERM,
            )?;
            writeln!(
                self.wrapper.writer(),
                "  {end}{term}",
                end = crate::keywords::END,
                term = crate::keywords::RULE_TERM
            )?;
        }
        writeln!(
            self.wrapper.writer(),
            "{end}{term}",
            end = crate::keywords::END,
            term = crate::keywords::RULE_TERM,
        )?;
        std::mem::forget(self.wrapper);
        Ok(self.order)
    }
}

/// Guard type for writing the order transitivity proof
#[derive(Debug)]
pub struct OrderReflexivityProof<'proof, Writer: std::io::Write> {
    wrapper: OrderProof<'proof, Writer>,
    order: crate::Order,
}

impl<'proof, Writer> OrderReflexivityProof<'proof, Writer>
where
    Writer: std::io::Write,
{
    fn new(mut wrapper: OrderProof<'proof, Writer>, order: crate::Order) -> Self {
        wrapper.used = false;
        Self { wrapper, order }
    }

    fn start(&mut self) -> std::io::Result<()> {
        if self.wrapper.used {
            return Ok(());
        }
        let writer = self.wrapper.writer();
        writeln!(
            writer,
            "  {trans}",
            trans = crate::keywords::ORDER_REFLEXIVITY
        )?;
        writeln!(self.writer(), "    {proof}", proof = crate::keywords::PROOF)?;
        self.wrapper.used = true;
        self.wrapper.next_id += self.order.num_spec_constraints();
        Ok(())
    }

    // required with this signature for macro implementations
    #[expect(clippy::unused_self)]
    fn level(&self) -> usize {
        3
    }

    crate::macros::implement!(forward from wrapper);
    crate::macros::implement!(operations with start);
    crate::macros::implement!(reverse_unit_prop with start);

    /// Starts a new proof goal in the reflexivity proof
    ///
    /// # Errors
    ///
    /// If writing the proof fails
    pub fn proof_goal(
        &mut self,
        id: crate::OrderDefinitionProofGoalId,
    ) -> std::io::Result<crate::guards::ProofGoal<'_, OrderProof<'proof, Writer>>> {
        self.start()?;
        crate::guards::ProofGoal::new(&mut self.wrapper, id.as_proof_goal_id(), 4)
    }

    /// Finishes the order
    ///
    /// # Errors
    ///
    /// If writing the proof fails
    pub fn finish(mut self) -> std::io::Result<crate::Order> {
        if self.wrapper.used {
            writeln!(
                self.writer(),
                "    {qed}{term}",
                qed = crate::keywords::QED,
                term = crate::keywords::RULE_TERM,
            )?;
            writeln!(
                self.wrapper.writer(),
                "  {end}{term}",
                end = crate::keywords::END,
                term = crate::keywords::RULE_TERM
            )?;
        }
        writeln!(
            self.wrapper.writer(),
            "{end}{term}",
            end = crate::keywords::END,
            term = crate::keywords::RULE_TERM,
        )?;
        std::mem::forget(self.wrapper);
        Ok(self.order)
    }
}

/// The proof scope of the transitivity and reflexivity proofs of an order
#[derive(Debug)]
pub struct OrderProof<'proof, Writer: std::io::Write> {
    wrapper: std::mem::ManuallyDrop<OrderDefAutoClosing<'proof, Writer>>,
    next_id: AbsConstraintId,
    used: bool,
}

impl<'proof, Writer> OrderProof<'proof, Writer>
where
    Writer: std::io::Write,
{
    fn new(wrapper: OrderDefAutoClosing<'proof, Writer>) -> Self {
        Self {
            wrapper: std::mem::ManuallyDrop::new(wrapper),
            next_id: AbsConstraintId::new(1),
            used: false,
        }
    }
}

impl<Writer> sealed::ProofScope for OrderProof<'_, Writer>
where
    Writer: std::io::Write,
{
    type Writer = Writer;

    fn writer(&mut self) -> &mut Self::Writer {
        self.wrapper.writer()
    }

    fn new_id(&mut self) -> AbsConstraintId {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    fn increase_next_id(&mut self, num_constraints: usize) {
        self.next_id += num_constraints;
    }
}

impl<Writer> Drop for OrderProof<'_, Writer>
where
    Writer: std::io::Write,
{
    fn drop(&mut self) {
        if self.used {
            writeln!(
                self.writer(),
                "    {qed}{term}",
                qed = crate::keywords::QED,
                term = crate::keywords::RULE_TERM,
            )
            .expect("failed to write closing of order");
            writeln!(
                self.wrapper.writer(),
                "  {end}{term}",
                end = crate::keywords::END,
                term = crate::keywords::RULE_TERM
            )
            .expect("failed to write closing of order");
        }
        writeln!(
            self.wrapper.writer(),
            "{end}{term}",
            end = crate::keywords::END,
            term = crate::keywords::RULE_TERM,
        )
        .expect("failed to write closing of order");
    }
}

/// The scope type of the `geq` sub scope
#[derive(Debug)]
pub struct GeqScope;

impl sealed::SubScopeType for GeqScope {
    const ID: &'static str = crate::keywords::GEQ_SCOPE;

    fn prepare_scope<Scope>(scope: &mut Scope)
    where
        Scope: ProofScope,
    {
        scope.increase_next_id(scope.num_order_spec_constraints());
    }
}

/// The scope type of the `leq` sub scope
#[derive(Debug)]
pub struct LeqScope;

impl sealed::SubScopeType for LeqScope {
    const ID: &'static str = crate::keywords::LEQ_SCOPE;

    fn prepare_scope<Scope>(scope: &mut Scope)
    where
        Scope: ProofScope,
    {
        scope.increase_next_id(scope.num_order_spec_constraints());
    }
}

/// Guard type for writing proof sub-scopes
#[derive(Debug)]
pub struct SubScope<'scope, Scope: ProofScope, Type: SubScopeType> {
    scope: &'scope mut Scope,
    level: usize,
    _scope: std::marker::PhantomData<Type>,
}

impl<'scope, Scope, Type> SubScope<'scope, Scope, Type>
where
    Scope: ProofScope,
    Type: SubScopeType,
{
    pub(crate) fn new(scope: &'scope mut Scope, level: usize) -> std::io::Result<Self> {
        writeln!(
            scope.writer(),
            "{:indent$}{scope} {typ}",
            "",
            indent = (level - 1) * 2,
            scope = crate::keywords::SCOPE,
            typ = Type::ID,
        )?;
        Type::prepare_scope(scope);
        Ok(Self {
            scope,
            level,
            _scope: std::marker::PhantomData,
        })
    }

    fn level(&self) -> usize {
        self.level
    }

    crate::macros::implement!(forward from scope);
    crate::macros::implement!(operations);
    crate::macros::implement!(reverse_unit_prop);

    /// Starts a new proof goal in the scope
    ///
    /// # Errors
    ///
    /// If writing the proof fails
    pub fn proof_goal(
        &mut self,
        id: crate::ProofGoalId,
    ) -> std::io::Result<crate::guards::ProofGoal<'_, Scope>> {
        let level = self.level();
        crate::guards::ProofGoal::new(self.scope, id, level)
    }

    fn write_end(&mut self) -> std::io::Result<()> {
        let level = self.level();
        writeln!(
            self.writer(),
            "{:indent$}{end}{term}",
            "",
            indent = level * 2,
            end = crate::keywords::END,
            term = crate::keywords::RULE_TERM
        )
    }

    /// Finishes writing the sub-scope
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

impl<Scope, Type> Drop for SubScope<'_, Scope, Type>
where
    Scope: ProofScope,
    Type: SubScopeType,
{
    fn drop(&mut self) {
        self.write_end().expect("failed to write closing of scope");
    }
}
