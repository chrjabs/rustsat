//! # Certified Totalizer Database

use std::{
    num::{NonZero, NonZeroUsize},
    ops,
};

use crate::{
    encodings::{
        atomics,
        nodedb::{NodeById, NodeCon, NodeId, NodeLike},
    },
    instances::ManageVars,
    lit,
    types::{constraints::PbConstraint, Lit, Var},
    utils::unreachable_none,
};

use pigeons::{AbsConstraintId, Axiom, OperationLike, OperationSequence, VarLike};

use super::{con_idx, LitData, Node, PrecondOutcome, Semantics, UnitNode, UnweightedPrecondResult};

/// Helper to get the output literal with a given index
macro_rules! get_olit {
    ($self:expr, $id:expr, $idx:expr) => {
        match &$self.nodes[$id.0] {
            Node::Leaf(lit) => {
                debug_assert_eq!($idx, 0);
                *lit
            }
            Node::Unit(UnitNode { lits, .. }) => *unreachable_none!(lits[$idx].lit()),
            Node::General(_) | Node::Dummy => unreachable!(),
        }
    };
}

impl super::Db {
    #[expect(clippy::too_many_arguments)]
    fn define_semantics<W>(
        &mut self,
        id: NodeId,
        offset: usize,
        mut len_limit: Option<NonZeroUsize>,
        mut value: usize,
        typ: SemDefTyp,
        leafs: impl Iterator<Item = (Lit, usize)> + Clone,
        proof: &mut pigeons::Proof<W>,
    ) -> std::io::Result<SemDefinition>
    where
        W: std::io::Write,
    {
        debug_assert!(value <= self[id].max_val() + 1);
        debug_assert!(offset <= self[id].max_val());

        // If the limit is trivial, remove it
        if let Some(limit) = len_limit {
            if limit.get() + offset >= self[id].max_val() {
                len_limit = None;
            }
        }

        if value <= offset {
            value = 0;
        }

        let def_id = SemDefId {
            id,
            value,
            offset,
            len_limit,
        };

        if let Some(defs) = self.semantic_defs.get(&def_id) {
            return Ok(defs.get(typ).into());
        }

        if self[id].is_leaf()
            || offset + 1 >= self[id].max_val()
            || len_limit.is_some_and(|lim| lim.get() == 1)
        {
            // leaf or pseudo-leaf, i.e., only transmitting a single literal
            if value == 0 && typ == SemDefTyp::OnlyIf {
                let olit = self[id][offset + 1];
                return Ok(olit.into());
            }
            if value == offset + 2 && typ == SemDefTyp::If {
                let olit = self[id][offset + 1];
                return Ok((!olit).into());
            }
            return Ok(SemDefinition::None);
        }

        if offset == 0 && len_limit.is_none() {
            // "normal" case, i.e., semantics need not be rewritten
            let defs = self.define_real_semantics(id, value, leafs, proof)?;
            return Ok(defs.get(typ).into());
        }

        // because of offset or len_limit, semantics need to be rewritten in terms of the outputs
        // itself. this function define all possibly required pseudo semantics at once to not get issues where
        // we get proof obligations from the semantics of the nodes above
        let defs = self.define_pseudo_semantics(id, offset, len_limit, value, leafs, proof)?;
        Ok(defs.get(typ).into())
    }

    fn define_real_semantics<W>(
        &mut self,
        id: NodeId,
        value: usize,
        leafs: impl Iterator<Item = (Lit, usize)> + Clone,
        proof: &mut pigeons::Proof<W>,
    ) -> std::io::Result<SemDefs>
    where
        W: std::io::Write,
    {
        let def_id = SemDefId {
            id,
            value,
            offset: 0,
            len_limit: None,
        };

        let sum = PbConstraint::new_lb_unsigned(
            leafs.clone(),
            isize::try_from(value).expect("cannot handle values larger than `isize::MAX`"),
        );

        #[cfg(feature = "verbose-proofs")]
        proof.comment(&format_args!(
            "output semantics for node {id}, value {value}",
        ))?;
        // must always add both semantic definitions straight away, later they might not be
        // trivially redundant anymore
        let defs = if value == 0 {
            SemDefs::new(None, Some(proof.redundant::<Var, _, _, _>(&sum, [], [])?))
        } else if value > self[id].max_val() {
            let sum = PbConstraint::new_lb_unsigned(leafs.map(|(l, w)| (!l, w)), 0);
            SemDefs::new(Some(proof.redundant::<Var, _, _, _>(&sum, [], [])?), None)
        } else {
            let olit = self[id][value];
            SemDefs::new(
                Some(proof.redundant(
                    &atomics::pb_impl_lit(&sum, olit),
                    [olit.var().substitute_fixed(true)],
                    None,
                )?),
                Some(proof.redundant(
                    &atomics::lit_impl_pb(olit, &sum),
                    [olit.var().substitute_fixed(false)],
                    None,
                )?),
            )
        };
        debug_assert!(!self.semantic_defs.contains_key(&def_id));
        self.semantic_defs.insert(def_id, defs);
        Ok(defs)
    }

    #[expect(clippy::too_many_lines)]
    fn define_pseudo_semantics<W>(
        &mut self,
        id: NodeId,
        offset: usize,
        len_limit: Option<NonZeroUsize>,
        value: usize,
        leafs: impl Iterator<Item = (Lit, usize)> + Clone,
        proof: &mut pigeons::Proof<W>,
    ) -> std::io::Result<SemDefs>
    where
        W: std::io::Write,
    {
        debug_assert!(offset > 0 || len_limit.is_some());

        // Check that the rewritten sum matches what we were passed as leafs
        {
            let mut sum = offset;
            debug_assert!(leafs.clone().eq(self[id]
                .vals(offset + 1..)
                .take(len_limit.map_or(usize::MAX, NonZero::get))
                .map(|val| {
                    let cf = val - sum;
                    sum = val;
                    (self[id][val], cf)
                })));
        }

        #[cfg(feature = "verbose-proofs")]
        proof.comment(&format_args!(
            "pseudo semantics for node {id}, offset {offset}, len_limit {len_limit:?}",
        ))?;

        let mut output_defs = None;

        // These are the pseudo semantics for `value == offset`
        #[cfg(feature = "verbose-proofs")]
        proof.comment(&"value == offset")?;
        let defs = SemDefs::new(
            None,
            Some(proof.redundant::<Var, _, _, _>(
                &PbConstraint::new_lb_unsigned(leafs.clone(), 0),
                [],
                [],
            )?),
        );
        let def_id = SemDefId {
            id,
            value: 0,
            offset,
            len_limit,
        };
        debug_assert!(!self.semantic_defs.contains_key(&def_id));
        self.semantic_defs.insert(def_id, defs);
        debug_assert!(value > offset || value == 0);
        if value == 0 {
            output_defs = Some(defs);
        }

        let mut true_leafs: Vec<_> = vec![];
        // NOTE: the `.take(usize::MAX)` here and below is slightly hacky in order to get the same
        // type no matter whether `len_limit` is some or none
        for val in self[id]
            .vals(offset + 1..)
            .take(len_limit.map_or(usize::MAX, NonZero::get))
        {
            if self.get_semantics(id, 0, val).is_none() {
                if true_leafs.is_empty() {
                    true_leafs = self.leaf_iter(id).collect();
                }
                self.define_real_semantics(id, val, true_leafs.iter().copied(), proof)?;
            }
        }

        // NOTE: the `.take(usize::MAX)` here and below is slightly hacky in order to get the same
        // type no matter whether `len_limit` is some or none
        for main_val in self[id]
            .vals(offset + 1..)
            .take(len_limit.map_or(usize::MAX, NonZero::get))
        {
            #[cfg(feature = "verbose-proofs")]
            proof.comment(&format_args!("pseudo semantics value {main_val}"))?;
            let this_defs = self
                .get_semantics(id, 0, main_val)
                .expect("should have been defined above");
            // the actual rewrite happens here
            let mut if_def = OperationSequence::<Var>::empty();
            let mut only_if_def = OperationSequence::<Var>::empty();
            let mut last_val = offset;
            for sub_val in self[id]
                .vals(offset + 1..)
                .take(len_limit.map_or(usize::MAX, NonZero::get))
            {
                let defs = self
                    .get_semantics(id, 0, sub_val)
                    .expect("should have added the definitions earlier");
                match sub_val.cmp(&main_val) {
                    std::cmp::Ordering::Less => {
                        if_def += Axiom::from(!self[id][sub_val]) * (sub_val - last_val);
                        only_if_def +=
                            (((OperationSequence::<Var>::from(this_defs.only_if_def.unwrap())
                                + defs.if_def.unwrap())
                                / (main_val - sub_val + 1))
                                .saturate())
                                * (sub_val - last_val);
                    }
                    std::cmp::Ordering::Greater => {
                        if_def += (((OperationSequence::<Var>::from(this_defs.if_def.unwrap())
                            + defs.only_if_def.unwrap())
                            / (sub_val - main_val + 1))
                            .saturate())
                            * (sub_val - last_val);
                        only_if_def += Axiom::from(self[id][sub_val]) * (sub_val - last_val);
                    }
                    std::cmp::Ordering::Equal => {
                        if_def += Axiom::from(!self[id][sub_val]) * (sub_val - last_val - 1);
                    }
                }
                last_val = sub_val;
            }
            let if_def = proof.operations::<Var>(&if_def)?;
            let only_if_def = proof.operations::<Var>(&only_if_def)?;
            #[cfg(feature = "verbose-proofs")]
            {
                let sum = PbConstraint::new_lb_unsigned(
                    leafs.clone(),
                    isize::try_from(main_val - offset)
                        .expect("cannot handle values larger than `isize::MAX`"),
                );
                let olit = self[id][main_val];
                proof.equals(&atomics::pb_impl_lit(&sum, olit), Some(if_def.into()))?;
                proof.equals(&atomics::lit_impl_pb(olit, &sum), Some(only_if_def.into()))?;
            }
            let defs = SemDefs::new(Some(if_def), Some(only_if_def));

            let def_id = SemDefId {
                id,
                value: main_val,
                offset,
                len_limit,
            };
            debug_assert!(!self.semantic_defs.contains_key(&def_id));
            self.semantic_defs.insert(def_id, defs);
            if main_val == value {
                output_defs = Some(defs);
            }
        }

        if matches!(self[id], Node::Unit(_)) {
            // NOTE: these semantics are only needed to encode the "only if" direction, and
            // therefore only for unweighteed nodes. For weighted nodes, determining what `max_cost
            // + 1` is is not so trivial.
            let sum = PbConstraint::new_lb_unsigned(leafs.map(|(l, w)| (!l, w)), 0);
            #[cfg(feature = "verbose-proofs")]
            proof.comment(&"value > max")?;
            let defs = SemDefs::new(Some(proof.redundant::<Var, _, _, _>(&sum, [], [])?), None);
            let def_id = SemDefId {
                id,
                value: len_limit.map_or(self[id].max_val() + 1, |lim| lim.get() + offset + 1),
                offset,
                len_limit,
            };
            debug_assert!(!self.semantic_defs.contains_key(&def_id));
            self.semantic_defs.insert(def_id, defs);
            if value == def_id.value {
                output_defs = Some(defs);
            }
        }

        Ok(output_defs.expect("`value` should have been included in `vals`"))
    }

    /// Gets the semantic definitions for an output value, if they exist
    #[must_use]
    pub fn get_semantics(&self, id: NodeId, offset: usize, value: usize) -> Option<SemDefs> {
        self.semantic_defs
            .get(&SemDefId {
                id,
                value,
                offset,
                len_limit: None,
            })
            .copied()
    }

    /// Ensures that the semantics definitions for an output are in the proof
    ///
    /// # Errors
    ///
    /// If writing the proof fails, returns [`std::io::Error`]
    #[cfg(feature = "internals")]
    pub fn ensure_semantics<W>(
        &mut self,
        id: NodeId,
        offset: usize,
        value: usize,
        leafs: impl Iterator<Item = (Lit, usize)> + Clone,
        proof: &mut pigeons::Proof<W>,
    ) -> std::io::Result<SemDefs>
    where
        W: std::io::Write,
    {
        debug_assert!(value <= self[id].max_val());
        debug_assert!(value > offset);
        let def_id = SemDefId {
            id,
            value,
            offset,
            len_limit: None,
        };
        if let Some(&defs) = self.semantic_defs.get(&def_id) {
            return Ok(defs);
        }
        // NOTE: doesn't matter which type we specify here, since both will be introduced anyway
        self.define_semantics(id, offset, None, value, SemDefTyp::If, leafs, proof)?;
        Ok(unreachable_none!(self.semantic_defs.get(&def_id).copied()))
    }

    /// Deletes all semantic definitions from the proof
    ///
    /// # Errors
    ///
    /// If writing the proof fails, returns [`std::io::Error`]
    pub fn delete_semantics<W>(&mut self, proof: &mut pigeons::Proof<W>) -> std::io::Result<()>
    where
        W: std::io::Write,
    {
        let iter = self
            .semantic_defs
            .iter()
            .flat_map(|(_, def)| def.iter())
            .map(Into::into);
        proof.delete_ids::<Var, crate::types::Clause, _, _>(iter, None)?;
        self.semantic_defs.clear();
        Ok(())
    }

    /// Generates the encoding to define the positive output literal with value `val`, if it is not
    /// already defined. The derivation of the generated clauses is certified in the provided
    /// proof. Recurses down the tree. The returned literal is the output literal and the encoding
    /// is added to the `collector`.
    ///
    /// # Errors
    ///
    /// - If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
    /// - If writing the proof fails, returns [`std::io::Error`].
    #[expect(clippy::too_many_lines)]
    pub fn define_weighted_cert<Col, W>(
        &mut self,
        id: NodeId,
        val: usize,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
        (leafs, mut leafs_init, leafs_needed): (&mut [(Lit, usize)], bool, bool),
    ) -> anyhow::Result<Option<(Lit, bool)>>
    where
        Col: crate::encodings::CollectCertClauses,
        W: std::io::Write,
    {
        use pigeons::OperationLike;

        debug_assert!(val <= self[id].max_val());
        debug_assert!(val > 0);
        debug_assert_eq!(leafs.len(), self[id].n_leafs());
        match &self[id] {
            Node::Leaf(lit) => {
                debug_assert_eq!(val, 1);
                if !leafs_init {
                    leafs[0] = (*lit, 1);
                    leafs_init = true;
                }
                if val != 1 {
                    return Ok(None);
                }
                Ok(Some((*lit, leafs_init)))
            }
            Node::Unit(node) => {
                if val > node.lits.len() || val == 0 {
                    return Ok(None);
                }

                let mut unweighted_leafs: Vec<_> = leafs.iter().map(|(l, _)| *l).collect();
                let (olit, _) = self.define_unweighted_cert(
                    id,
                    val - 1,
                    Semantics::If,
                    collector,
                    var_manager,
                    proof,
                    (&mut unweighted_leafs, leafs_init, leafs_needed),
                )?;
                if leafs_needed && !leafs_init {
                    for (idx, &lit) in unweighted_leafs.iter().enumerate() {
                        leafs[idx] = (lit, 1);
                    }
                    leafs_init = true;
                }
                Ok(Some((olit, leafs_init)))
            }
            Node::General(node) => {
                // Check if already encoded
                if let Some(lit_data) = node.lits.get(&val) {
                    if let LitData::Lit {
                        lit,
                        semantics: Some(semantics),
                    } = lit_data
                    {
                        if semantics.has_if() {
                            if leafs_needed && !leafs_init {
                                self.populate_weighted_leafs(NodeCon::full(id), leafs);
                                leafs_init = true;
                            }
                            return Ok(Some((*lit, leafs_init)));
                        }
                    }
                } else {
                    return Ok(None);
                }

                debug_assert!(node.lits.contains_key(&val));

                let lcon = node.left;
                let rcon = node.right;

                // Reserve variable for this node, if needed
                let olit = if let Some(&olit) = node.lit(val) {
                    olit
                } else {
                    let olit = var_manager.new_var().pos_lit();
                    *unreachable_none!(self[id].mut_general().lits.get_mut(&val)) =
                        LitData::new_lit(olit);
                    olit
                };

                let mut left_leafs_populated = leafs_init;
                let mut right_leafs_populated = leafs_init;

                let n_left_leafs = lcon.len_limit.map_or(
                    if lcon.offset() == 0 {
                        self[lcon.id].n_leafs()
                    } else {
                        self[lcon.id].vals(lcon.offset() + 1..).count()
                    },
                    NonZero::get,
                );

                if leafs_init {
                    // to have the correct weights at the child nodes, need to divide the
                    // populated leaf weights
                    debug_assert_eq!(lcon.divisor(), 1);
                    debug_assert_eq!(rcon.divisor(), 1);
                    for (idx, (_, w)) in leafs.iter_mut().enumerate() {
                        if idx < n_left_leafs {
                            *w /= lcon.multiplier();
                        } else {
                            *w /= rcon.multiplier();
                        }
                    }
                }
                let (left_leafs, right_leafs) = leafs.split_at_mut(n_left_leafs);

                #[cfg(feature = "verbose-proofs")]
                proof.comment(&format_args!(
                    "derive GTE clauses for node {id}, value {val}",
                ))?;

                // Propagate sums
                // We do this first to have a higher chance of populating the leaf vector during
                // recursion
                if lcon.map(lcon.offset() + 1) < val {
                    let lvals = self[lcon.id].vals(lcon.offset() + 1..lcon.rev_map_round_up(val));
                    let rmax = self[rcon.id].max_val();
                    for lval in lvals {
                        let rval = val - lcon.map(lval);
                        debug_assert!(rval > 0);
                        let rval_rev = rcon.rev_map(rval);
                        if rcon.is_possible(rval) && rval_rev <= rmax {
                            if let Some(rlit) = self.define_weighted_treat_pseudo_leafs(
                                rcon,
                                rval_rev,
                                collector,
                                var_manager,
                                proof,
                                (right_leafs, right_leafs_populated),
                            )? {
                                right_leafs_populated = true;
                                debug_assert!(
                                    lcon.len_limit.is_none() || lcon.offset() + 1 == lval
                                );
                                let llit = unreachable_none!(self
                                    .define_weighted_treat_pseudo_leafs(
                                        lcon,
                                        lval,
                                        collector,
                                        var_manager,
                                        proof,
                                        (left_leafs, left_leafs_populated)
                                    )?);
                                left_leafs_populated = true;
                                let left_def = self.define_semantics(
                                    lcon.id,
                                    lcon.offset(),
                                    lcon.len_limit,
                                    lval,
                                    SemDefTyp::OnlyIf,
                                    left_leafs.iter().copied(),
                                    proof,
                                )?;
                                let right_def = self.define_semantics(
                                    rcon.id,
                                    rcon.offset(),
                                    rcon.len_limit,
                                    rcon.rev_map_no_limit(rval),
                                    SemDefTyp::OnlyIf,
                                    right_leafs.iter().copied(),
                                    proof,
                                )?;
                                let this_def = self.define_semantics(
                                    id,
                                    0,
                                    None,
                                    val,
                                    SemDefTyp::If,
                                    left_leafs
                                        .iter()
                                        .map(|(l, w)| (*l, *w * lcon.multiplier()))
                                        .chain(
                                            right_leafs
                                                .iter()
                                                .map(|(l, w)| (*l, *w * rcon.multiplier())),
                                        ),
                                    proof,
                                )?;
                                let id = proof.operations(
                                    &(this_def
                                        + (left_def * lcon.multiplier())
                                        + (right_def * rcon.multiplier()))
                                    .saturate(),
                                )?;
                                let clause = atomics::cube_impl_lit(&[llit, rlit], olit);
                                #[cfg(feature = "verbose-proofs")]
                                proof.equals(&clause, Some(id.into()))?;
                                collector.add_cert_clause(clause, id)?;
                            }
                        }
                    }
                }

                // Propagate value
                if lcon.is_possible(val) && lcon.rev_map(val) <= self[lcon.id].max_val() {
                    if let Some(llit) = self.define_weighted_treat_pseudo_leafs(
                        lcon,
                        lcon.rev_map(val),
                        collector,
                        var_manager,
                        proof,
                        (left_leafs, left_leafs_populated),
                    )? {
                        left_leafs_populated = true;
                        if !right_leafs_populated {
                            // We have not recursed down the right branch yet and therefore need to
                            // manually populate the right half of the leaf vector
                            self.populate_weighted_leafs(rcon, right_leafs);
                            right_leafs_populated = true;
                        }
                        let left_def = self.define_semantics(
                            lcon.id,
                            lcon.offset(),
                            lcon.len_limit,
                            lcon.rev_map_no_limit(val),
                            SemDefTyp::OnlyIf,
                            left_leafs.iter().copied(),
                            proof,
                        )?;
                        let right_def = self.define_semantics(
                            rcon.id,
                            rcon.offset(),
                            rcon.len_limit,
                            0,
                            SemDefTyp::OnlyIf,
                            right_leafs.iter().copied(),
                            proof,
                        )?;
                        let this_def = self.define_semantics(
                            id,
                            0,
                            None,
                            val,
                            SemDefTyp::If,
                            left_leafs
                                .iter()
                                .map(|(l, w)| (*l, *w * lcon.multiplier()))
                                .chain(
                                    right_leafs
                                        .iter()
                                        .map(|(l, w)| (*l, *w * rcon.multiplier())),
                                ),
                            proof,
                        )?;
                        let id = proof.operations(
                            &(this_def
                                + (left_def * lcon.multiplier())
                                + (right_def * rcon.multiplier()))
                            .saturate(),
                        )?;
                        let clause = atomics::lit_impl_lit(llit, olit);
                        #[cfg(feature = "verbose-proofs")]
                        proof.equals(&clause, Some(id.into()))?;
                        collector.add_cert_clause(clause, id)?;
                    }
                }
                if rcon.is_possible(val) && rcon.rev_map(val) <= self[rcon.id].max_val() {
                    if let Some(rlit) = self.define_weighted_treat_pseudo_leafs(
                        rcon,
                        rcon.rev_map(val),
                        collector,
                        var_manager,
                        proof,
                        (right_leafs, right_leafs_populated),
                    )? {
                        right_leafs_populated = true;
                        if !left_leafs_populated {
                            // We have not recursed down the left branch yet and therefore need to
                            // manually populate the left half of the leaf vector
                            self.populate_weighted_leafs(lcon, left_leafs);
                            left_leafs_populated = true;
                        }
                        let left_def = self.define_semantics(
                            lcon.id,
                            lcon.offset(),
                            lcon.len_limit,
                            0,
                            SemDefTyp::OnlyIf,
                            left_leafs.iter().copied(),
                            proof,
                        )?;
                        let right_def = self.define_semantics(
                            rcon.id,
                            rcon.offset(),
                            rcon.len_limit,
                            rcon.rev_map_no_limit(val),
                            SemDefTyp::OnlyIf,
                            right_leafs.iter().copied(),
                            proof,
                        )?;
                        let this_def = self.define_semantics(
                            id,
                            0,
                            None,
                            val,
                            SemDefTyp::If,
                            left_leafs
                                .iter()
                                .map(|(l, w)| (*l, *w * lcon.multiplier()))
                                .chain(
                                    right_leafs
                                        .iter()
                                        .map(|(l, w)| (*l, *w * rcon.multiplier())),
                                ),
                            proof,
                        )?;
                        let id = proof.operations(
                            &(this_def
                                + (left_def * lcon.multiplier())
                                + (right_def * rcon.multiplier()))
                            .saturate(),
                        )?;
                        let clause = atomics::lit_impl_lit(rlit, olit);
                        #[cfg(feature = "verbose-proofs")]
                        proof.equals(&clause, Some(id.into()))?;
                        collector.add_cert_clause(clause, id)?;
                    };
                }

                // Only now finally multiply the leaf weights since they won't be used at lower
                // levels any more
                debug_assert_eq!(lcon.divisor(), 1);
                debug_assert_eq!(rcon.divisor(), 1);
                for (idx, (_, w)) in leafs.iter_mut().enumerate() {
                    if idx < n_left_leafs {
                        *w *= lcon.multiplier();
                    } else {
                        *w *= rcon.multiplier();
                    }
                }

                // Mark "if" semantics as encoded
                unreachable_none!(self[id].mut_general().lits.get_mut(&val))
                    .add_semantics(Semantics::If);

                debug_assert!(!leafs_needed || left_leafs_populated && right_leafs_populated);
                Ok(Some((olit, left_leafs_populated && right_leafs_populated)))
            }
            Node::Dummy => Ok(None),
        }
    }

    fn define_weighted_treat_pseudo_leafs<Col, W>(
        &mut self,
        con: NodeCon,
        val: usize,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
        (leafs, leafs_init): (&mut [(Lit, usize)], bool),
    ) -> anyhow::Result<Option<Lit>>
    where
        Col: crate::encodings::CollectCertClauses,
        W: std::io::Write,
    {
        if con.offset() == 0 && con.len_limit.is_none() {
            // normal recursion case
            let ret = self.define_weighted_cert(
                con.id,
                val,
                collector,
                var_manager,
                proof,
                (leafs, leafs_init, true),
            )?;
            debug_assert!(ret.map_or(true, |(_, i)| i));
            Ok(ret.map(|(l, _)| l))
        } else {
            // with length limit or offset, treat intermediate output nodes as leafs
            // for this, recurse without keeping track of leafs, if not required for encoding
            // NOTE: this could be in efficient if we encode many outputs with a new empty leaf
            // vector each time
            let mut true_leafs = vec![(lit![0], 0); self[con.id].n_leafs()];
            let ret = self.define_weighted_cert(
                con.id,
                val,
                collector,
                var_manager,
                proof,
                (&mut true_leafs, false, false),
            )?;
            if !leafs_init {
                self.populate_weighted_leafs(con, leafs);
            }
            Ok(ret.map(|(l, _)| l))
        }
    }

    fn populate_weighted_leafs(&self, con: NodeCon, leafs: &mut [(Lit, usize)]) {
        if con.offset() == 0 && con.len_limit.is_none() {
            for (idx, leaf) in self.leaf_iter(con.id).enumerate() {
                leafs[idx] = leaf;
            }
        } else {
            let mut last_val = con.offset();
            for (idx, val) in self[con.id]
                .vals(con.offset() + 1..)
                .take(con.len_limit.map_or(usize::MAX, NonZero::get))
                .enumerate()
            {
                leafs[idx] = (self[con.id][val], (val - last_val));
                last_val = val;
            }
        }
    }

    /// Recursion for unweighted totalizer encoding with certificate
    fn recurse_unweighted_cert<Col, W>(
        &mut self,
        pre: &UnweightedPrecondResult,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
        (leafs, leafs_init): (&mut [Lit], bool),
    ) -> anyhow::Result<bool>
    where
        Col: crate::encodings::CollectCertClauses,
        W: std::io::Write,
    {
        let n_left_leafs = pre.lcon.len_limit.map_or(
            if pre.lcon.offset() == 0 {
                self[pre.lcon.id].n_leafs()
            } else {
                self[pre.lcon.id].len() - pre.lcon.offset()
            },
            NonZero::get,
        );
        let (left_leafs, right_leafs) = leafs.split_at_mut(n_left_leafs);
        let mut left_leafs_populated = leafs_init;
        let mut right_leafs_populated = leafs_init;
        left_leafs_populated = self.recurse_unweighted_single_node(
            pre.lcon,
            pre.left_if.clone(),
            Semantics::If,
            collector,
            var_manager,
            proof,
            (left_leafs, left_leafs_populated),
        )?;
        right_leafs_populated = self.recurse_unweighted_single_node(
            pre.rcon,
            pre.right_if.clone(),
            Semantics::If,
            collector,
            var_manager,
            proof,
            (right_leafs, right_leafs_populated),
        )?;
        left_leafs_populated = self.recurse_unweighted_single_node(
            pre.lcon,
            pre.left_only_if.clone(),
            Semantics::OnlyIf,
            collector,
            var_manager,
            proof,
            (left_leafs, left_leafs_populated),
        )?;
        right_leafs_populated = self.recurse_unweighted_single_node(
            pre.rcon,
            pre.right_only_if.clone(),
            Semantics::OnlyIf,
            collector,
            var_manager,
            proof,
            (right_leafs, right_leafs_populated),
        )?;
        // in the unweighted case, there are always both sides involved, both halfs of the leaf
        // slice must therefore be populated
        debug_assert!(left_leafs_populated);
        debug_assert!(right_leafs_populated);
        Ok(left_leafs_populated && right_leafs_populated)
    }

    #[expect(clippy::too_many_arguments)]
    fn recurse_unweighted_single_node<Col, W>(
        &mut self,
        con: NodeCon,
        range: ops::RangeInclusive<usize>,
        sems: Semantics,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
        (leafs, mut leafs_init): (&mut [Lit], bool),
    ) -> anyhow::Result<bool>
    where
        Col: crate::encodings::CollectCertClauses,
        W: std::io::Write,
    {
        if con.offset() == 0 && con.len_limit.is_none() {
            // normal recursion case
            for val in range {
                if matches!(sems, Semantics::If) && val == 0
                    || matches!(sems, Semantics::OnlyIf) && val == self.con_len(con)
                {
                    continue;
                }
                let idx = match sems {
                    Semantics::If => val - 1,
                    Semantics::OnlyIf => val,
                    Semantics::IfAndOnlyIf => {
                        panic!("should never call this for both semantics at once")
                    }
                };
                self.define_unweighted_cert(
                    con.id,
                    con_idx(idx, con),
                    sems,
                    collector,
                    var_manager,
                    proof,
                    (leafs, leafs_init, true),
                )?;
                leafs_init = true;
            }
        } else {
            // with length limit or offset, treat intermediate output nodes as leafs
            // for this, recurse without keeping track of leafs, if not required for encoding
            let mut true_leafs = vec![lit![0]; self[con.id].n_leafs()];
            let mut true_leafs_init = false;
            for val in range {
                if matches!(sems, Semantics::If) && val == 0
                    || matches!(sems, Semantics::OnlyIf) && val == self.con_len(con)
                {
                    continue;
                }
                let oidx = match sems {
                    Semantics::If => val - 1,
                    Semantics::OnlyIf => val,
                    Semantics::IfAndOnlyIf => {
                        panic!("should never call this for both semantics at once")
                    }
                };
                (_, true_leafs_init) = self.define_unweighted_cert(
                    con.id,
                    con_idx(oidx, con),
                    sems,
                    collector,
                    var_manager,
                    proof,
                    (&mut true_leafs, true_leafs_init, false),
                )?;
            }
            if !leafs_init {
                for (idx, leaf) in leafs.iter_mut().enumerate() {
                    *leaf = self[con.id][idx + con.offset() + 1];
                }
            }
            leafs_init = true;
        }
        Ok(leafs_init)
    }

    /// Last step of [`Self::define_unweighted_cert`]
    ///
    /// # Panics
    ///
    /// If the semantics are already encoded.
    #[expect(clippy::too_many_arguments)]
    #[expect(clippy::too_many_lines)]
    fn encode_unweighted_cert<W, Col>(
        &mut self,
        id: NodeId,
        idx: usize,
        olit: Lit,
        req_semantics: Semantics,
        pre: &UnweightedPrecondResult,
        collector: &mut Col,
        proof: &mut pigeons::Proof<W>,
        leafs: &mut [Lit],
    ) -> anyhow::Result<()>
    where
        Col: crate::encodings::CollectCertClauses,
        W: std::io::Write,
    {
        use pigeons::OperationLike;

        // Store what part of the encoding we need to build
        let new_semantics = self[id].unit().lits[idx]
            .missing_semantics(req_semantics)
            .expect("semantics are already encoded");

        // Mark positive literal as encoded (done first to avoid borrow checker problems)
        self[id].mut_unit().lits[idx].add_semantics(req_semantics);

        let n_left_leafs = pre.lcon.len_limit.map_or(
            if pre.lcon.offset() == 0 {
                self[pre.lcon.id].n_leafs()
            } else {
                self[pre.lcon.id].len() - pre.lcon.offset()
            },
            NonZero::get,
        );
        let (left_leafs, right_leafs) = leafs.split_at(n_left_leafs);

        #[cfg(feature = "verbose-proofs")]
        proof.comment(&format_args!(
            "derive totalizer clauses for node {id}, value {}",
            idx + 1
        ))?;

        // Encode
        // If semantics
        for lval in pre.left_if.clone() {
            let rval = idx + 1 - lval;
            debug_assert!(pre.right_if.contains(&rval));
            debug_assert!(new_semantics.has_if());
            let mut lhs = [lit![0], lit![0]]; // avoids allocation
            let mut nlits = 0;
            if lval > 0 {
                lhs[nlits] = get_olit!(self, pre.lcon.id, con_idx(lval - 1, pre.lcon));
                nlits += 1;
            }
            if rval > 0 {
                lhs[nlits] = get_olit!(self, pre.rcon.id, con_idx(rval - 1, pre.rcon));
                nlits += 1;
            }
            let left_def = self.define_semantics(
                pre.lcon.id,
                pre.lcon.offset(),
                pre.lcon.len_limit,
                pre.lcon.rev_map_no_limit(lval),
                SemDefTyp::OnlyIf,
                left_leafs.iter().map(|l| (*l, 1)),
                proof,
            )?;
            let right_def = self.define_semantics(
                pre.rcon.id,
                pre.rcon.offset(),
                pre.rcon.len_limit,
                pre.rcon.rev_map_no_limit(rval),
                SemDefTyp::OnlyIf,
                right_leafs.iter().map(|l| (*l, 1)),
                proof,
            )?;
            let this_def = self.define_semantics(
                id,
                0,
                None,
                idx + 1,
                SemDefTyp::If,
                leafs.iter().map(|l| (*l, 1)),
                proof,
            )?;
            let id = proof.operations(&(this_def + left_def + right_def).saturate())?;
            let clause = atomics::cube_impl_lit(&lhs[..nlits], olit);
            #[cfg(feature = "verbose-proofs")]
            proof.equals(&clause, Some(id.into()))?;
            collector.add_cert_clause(clause, id)?;
        }
        // Only if semantics
        for lval in pre.left_only_if.clone() {
            let rval = idx - lval;
            debug_assert!(pre.right_only_if.contains(&rval));
            debug_assert!(new_semantics.has_only_if());
            let mut lhs = [lit![0], lit![0]]; // avoids allocation
            let mut nlits = 0;
            if lval < self.con_len(pre.lcon) {
                lhs[nlits] = !get_olit!(self, pre.lcon.id, con_idx(lval, pre.lcon));
                nlits += 1;
            }
            if rval < self.con_len(pre.rcon) {
                lhs[nlits] = !get_olit!(self, pre.rcon.id, con_idx(rval, pre.rcon));
                nlits += 1;
            }
            let left_def = self.define_semantics(
                pre.lcon.id,
                pre.lcon.offset(),
                pre.lcon.len_limit,
                pre.lcon.rev_map_no_limit(lval + 1),
                SemDefTyp::If,
                left_leafs.iter().map(|l| (*l, 1)),
                proof,
            )?;
            let right_def = self.define_semantics(
                pre.rcon.id,
                pre.rcon.offset(),
                pre.rcon.len_limit,
                pre.rcon.rev_map_no_limit(rval + 1),
                SemDefTyp::If,
                right_leafs.iter().map(|l| (*l, 1)),
                proof,
            )?;
            let this_def = self.define_semantics(
                id,
                0,
                None,
                idx + 1,
                SemDefTyp::OnlyIf,
                leafs.iter().map(|l| (*l, 1)),
                proof,
            )?;
            let id = proof.operations(&(this_def + left_def + right_def).saturate())?;
            let clause = atomics::cube_impl_lit(&lhs[..nlits], !olit);
            #[cfg(feature = "verbose-proofs")]
            proof.equals(&clause, Some(id.into()))?;
            collector.add_cert_clause(clause, id)?;
        }

        Ok(())
    }

    /// Defines a positive output, assuming that the structure is a non-weighted totalizer, and
    /// certifies its derivation in the provided proof
    ///
    /// The `idx` parameter is the output index, i.e., not the value represented by the output, but
    /// `value - 1`.
    ///
    /// Leafs must be a reference to a slice with length of the size of the given node (`id`). It
    /// is used to more efficiently keep track of the leafs affecting the given node, which is
    /// required for proof logging.
    ///
    /// # Errors
    ///
    /// - If the clause collector runs out of memory, returns [`crate::OutOfMemory`]
    /// - If writing the proof fails, returns [`std::io::Error`]
    #[allow(clippy::too_many_arguments)]
    pub fn define_unweighted_cert<Col, W>(
        &mut self,
        id: NodeId,
        idx: usize,
        semantics: Semantics,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pigeons::Proof<W>,
        (leafs, mut leafs_init, leafs_needed): (&mut [Lit], bool, bool),
    ) -> anyhow::Result<(Lit, bool)>
    where
        Col: crate::encodings::CollectCertClauses,
        W: std::io::Write,
    {
        debug_assert_eq!(leafs.len(), self[id].n_leafs());

        let pre = match self.precond_unweighted(id, idx, semantics) {
            PrecondOutcome::Return(lit) => {
                if leafs_needed && !leafs_init {
                    let mut new_leafs = collect_leafs_unweighted(self, id);
                    leafs.swap_with_slice(&mut new_leafs);
                    leafs_init = true;
                }
                return Ok((lit, leafs_init));
            }
            PrecondOutcome::Passthrough(_) => {
                // TODO: Decide what to do here
                // It probably doesn't make much sense to support this case with proof logging,
                // since the semantics of the output literals change when the dummy is replaced.
                // If the dummy is never replaced, then it should be avoided in the first place.
                todo!()
            }
            PrecondOutcome::Continue(pre) => pre,
        };

        // Encode children (recurse)
        leafs_init =
            self.recurse_unweighted_cert(&pre, collector, var_manager, proof, (leafs, leafs_init))?;

        // Reserve variable for this node, if needed
        let olit = self.get_olit(id, idx, var_manager);

        // Encode this node
        self.encode_unweighted_cert(id, idx, olit, semantics, &pre, collector, proof, leafs)?;

        Ok((olit, leafs_init))
    }
}

// This is a separate function to have a name for it while profiling
fn collect_leafs_unweighted(db: &super::Db, id: NodeId) -> Vec<Lit> {
    db.leaf_iter(id).map(|(l, _)| l).collect()
}

/// The semantic definitions related to a totalizer output
#[derive(Hash, Clone, Copy, PartialEq, Eq, Debug)]
pub struct SemDefs {
    /// The if implication direction, i.e., `sum >= k -> olit`
    pub if_def: Option<AbsConstraintId>,
    /// The only if implication direction, i.e., `olit -> sum >= k`
    pub only_if_def: Option<AbsConstraintId>,
}

impl SemDefs {
    fn new(if_def: Option<AbsConstraintId>, only_if_def: Option<AbsConstraintId>) -> Self {
        Self {
            if_def,
            only_if_def,
        }
    }

    fn get(&self, typ: SemDefTyp) -> AbsConstraintId {
        match typ {
            SemDefTyp::If => self.if_def.unwrap(),
            SemDefTyp::OnlyIf => self.only_if_def.unwrap(),
        }
    }

    fn iter(&self) -> impl Iterator<Item = AbsConstraintId> {
        self.if_def.into_iter().chain(self.only_if_def)
    }
}

/// The data needed to identify a semantic definition
#[derive(Hash, Clone, Copy, PartialEq, Eq, Debug)]
pub struct SemDefId {
    /// The ID of the node that the definition is for
    id: NodeId,
    /// The output value of the node, disregarding the offset
    value: usize,
    /// The offset. If the offset is non-zero, the semantic definitions need to be rewritten.
    offset: usize,
    /// The length limit of the connection
    len_limit: Option<NonZeroUsize>,
}

#[derive(Hash, Clone, Copy, PartialEq, Eq, Debug)]
enum SemDefinition {
    None,
    Id(AbsConstraintId),
    Axiom(Lit),
}

impl From<AbsConstraintId> for SemDefinition {
    fn from(value: AbsConstraintId) -> Self {
        Self::Id(value)
    }
}

impl From<Lit> for SemDefinition {
    fn from(value: Lit) -> Self {
        Self::Axiom(value)
    }
}

impl ops::Add<SemDefinition> for SemDefinition {
    type Output = pigeons::OperationSequence<Var>;

    fn add(self, rhs: SemDefinition) -> Self::Output {
        match self {
            SemDefinition::None => match rhs {
                SemDefinition::None => pigeons::OperationSequence::empty(),
                SemDefinition::Id(rhs) => rhs.into(),
                SemDefinition::Axiom(rhs) => pigeons::Axiom::from(rhs).into(),
            },
            SemDefinition::Id(lhs) => match rhs {
                SemDefinition::None => lhs.into(),
                SemDefinition::Id(rhs) => Self::Output::from(lhs) + rhs,
                SemDefinition::Axiom(rhs) => lhs + pigeons::Axiom::from(rhs),
            },
            SemDefinition::Axiom(lhs) => match rhs {
                SemDefinition::None => pigeons::Axiom::from(lhs).into(),
                SemDefinition::Id(rhs) => pigeons::Axiom::from(lhs) + rhs,
                SemDefinition::Axiom(rhs) => pigeons::Axiom::from(lhs) + pigeons::Axiom::from(rhs),
            },
        }
    }
}

impl ops::Add<SemDefinition> for pigeons::OperationSequence<Var> {
    type Output = pigeons::OperationSequence<Var>;

    fn add(self, rhs: SemDefinition) -> Self::Output {
        match rhs {
            SemDefinition::None => self,
            SemDefinition::Id(rhs) => self + rhs,
            SemDefinition::Axiom(rhs) => self + pigeons::Axiom::from(rhs),
        }
    }
}

impl ops::Add<pigeons::OperationSequence<Var>> for SemDefinition {
    type Output = pigeons::OperationSequence<Var>;

    fn add(self, rhs: pigeons::OperationSequence<Var>) -> Self::Output {
        match self {
            SemDefinition::None => rhs,
            SemDefinition::Id(id) => id + rhs,
            SemDefinition::Axiom(ax) => pigeons::Axiom::from(ax) + rhs,
        }
    }
}

impl ops::Mul<usize> for SemDefinition {
    type Output = pigeons::OperationSequence<Var>;

    fn mul(self, rhs: usize) -> Self::Output {
        match self {
            SemDefinition::None => pigeons::OperationSequence::empty(),
            SemDefinition::Id(id) => Self::Output::from(id) * rhs,
            SemDefinition::Axiom(ax) => pigeons::Axiom::from(ax) * rhs,
        }
    }
}

#[derive(Hash, Clone, Copy, PartialEq, Eq)]
pub(super) enum SemDefTyp {
    If,
    OnlyIf,
}

#[cfg(test)]
mod tests {
    use std::{
        fs::File,
        io::{BufRead, BufReader},
        path::Path,
        process::Command,
    };

    use crate::{
        encodings::{
            nodedb::{NodeById, NodeCon, NodeLike},
            totdb::{Db, Node, Semantics},
        },
        instances::{BasicVarManager, Cnf},
        lit,
        types::Var,
        var,
    };

    fn print_file<P: AsRef<Path>>(path: P) {
        println!();
        for line in BufReader::new(File::open(path).expect("could not open file")).lines() {
            println!("{}", line.unwrap());
        }
        println!();
    }

    fn verify_proof<P1: AsRef<Path>, P2: AsRef<Path>>(instance: P1, proof: P2) {
        if let Ok(veripb) = std::env::var("VERIPB_CHECKER") {
            println!("start checking proof");
            let out = Command::new(veripb)
                .arg(instance.as_ref())
                .arg(proof.as_ref())
                .output()
                .expect("failed to run veripb");
            print_file(proof);
            if out.status.success() {
                return;
            }
            panic!("verification failed: {out:?}")
        } else {
            println!("`$VERIPB_CHECKER` not set, omitting proof checking");
        }
    }

    fn new_proof(
        num_constraints: usize,
        optimization: bool,
    ) -> pigeons::Proof<tempfile::NamedTempFile> {
        let file = tempfile::NamedTempFile::new().expect("failed to create temporary proof file");
        pigeons::Proof::new(file, num_constraints, optimization).expect("failed to start proof")
    }

    #[test]
    fn tot_db_if() {
        let mut db = Db::default();
        let root = db.lit_tree(&[lit![0], lit![1], lit![2], lit![3]]);
        debug_assert_eq!(db[root].depth(), 3);
        let mut var_manager = BasicVarManager::from_next_free(var![4]);

        let mut proof = new_proof(0, false);

        let mut cnf = Cnf::new();
        let mut leafs = [lit![0]; 4];
        let mut leafs_init = false;

        for idx in 0..=3 {
            (_, leafs_init) = db
                .define_unweighted_cert(
                    root,
                    idx,
                    Semantics::If,
                    &mut cnf,
                    &mut var_manager,
                    &mut proof,
                    (&mut leafs, leafs_init, false),
                )
                .unwrap();
        }

        let proof_file = proof
            .conclude::<Var>(pigeons::OutputGuarantee::None, &pigeons::Conclusion::None)
            .unwrap();
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path());
    }

    #[test]
    fn tot_db_only_if() {
        let mut db = Db::default();
        let root = db.lit_tree(&[lit![0], lit![1], lit![2], lit![3]]);
        debug_assert_eq!(db[root].depth(), 3);
        let mut var_manager = BasicVarManager::from_next_free(var![4]);

        let mut proof = new_proof(0, false);

        let mut cnf = Cnf::new();
        let mut leafs = [lit![0]; 4];
        let mut leafs_init = false;

        for idx in 0..=3 {
            (_, leafs_init) = db
                .define_unweighted_cert(
                    root,
                    idx,
                    Semantics::OnlyIf,
                    &mut cnf,
                    &mut var_manager,
                    &mut proof,
                    (&mut leafs, leafs_init, false),
                )
                .unwrap();
        }

        let proof_file = proof
            .conclude::<Var>(pigeons::OutputGuarantee::None, &pigeons::Conclusion::None)
            .unwrap();
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path());
    }

    #[test]
    fn gte_db() {
        let mut db = Db::default();
        let root = db.weighted_lit_tree(&[(lit![0], 4), (lit![1], 3), (lit![2], 2), (lit![3], 1)]);
        assert_eq!(root.offset(), 0);
        assert_eq!(root.multiplier(), 1);
        let root = root.id;
        let mut var_manager = BasicVarManager::from_next_free(var![4]);

        let mut proof = new_proof(0, false);

        let mut cnf = Cnf::new();
        let mut leafs = [(lit![0], 0); 4];
        let mut leafs_init = false;

        for val in 1..=10 {
            let ret = db
                .define_weighted_cert(
                    root,
                    val,
                    &mut cnf,
                    &mut var_manager,
                    &mut proof,
                    (&mut leafs, leafs_init, false),
                )
                .unwrap();
            leafs_init |= ret.is_some_and(|(_, i)| i);
        }

        let proof_file = proof
            .conclude::<Var>(pigeons::OutputGuarantee::None, &pigeons::Conclusion::None)
            .unwrap();
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path());
    }

    #[test]
    fn gte_db2() {
        let mut db = Db::default();
        let root = db.weighted_lit_tree(&[
            (lit![0], 1),
            (lit![1], 2),
            (lit![2], 3),
            (lit![3], 4),
            (lit![4], 5),
        ]);
        assert_eq!(root.offset(), 0);
        assert_eq!(root.multiplier(), 1);
        let root = root.id;
        let mut var_manager = BasicVarManager::from_next_free(var![5]);

        let mut proof = new_proof(0, false);

        let mut cnf = Cnf::new();
        let mut leafs = [(lit![0], 0); 5];
        let mut leafs_init = false;

        for val in 1..=10 {
            let ret = db
                .define_weighted_cert(
                    root,
                    val,
                    &mut cnf,
                    &mut var_manager,
                    &mut proof,
                    (&mut leafs, leafs_init, false),
                )
                .unwrap();
            leafs_init |= ret.is_some_and(|(_, i)| i);
        }

        let proof_file = proof
            .conclude::<Var>(pigeons::OutputGuarantee::None, &pigeons::Conclusion::None)
            .unwrap();
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path());
    }

    #[test]
    fn totalizer_equal_clause_order() {
        let mut db = Db::default();
        let root = db.lit_tree(&[lit![0], lit![1], lit![2], lit![3]]);
        debug_assert_eq!(db[root].depth(), 3);
        let mut var_manager = BasicVarManager::from_next_free(var![4]);

        let mut proof = new_proof(0, false);

        let mut cert_cnf = Cnf::new();
        let mut leafs = [lit![0]; 4];
        let mut leafs_init = false;

        for idx in 0..=3 {
            (_, leafs_init) = db
                .define_unweighted_cert(
                    root,
                    idx,
                    Semantics::If,
                    &mut cert_cnf,
                    &mut var_manager,
                    &mut proof,
                    (&mut leafs, leafs_init, false),
                )
                .unwrap();
        }

        let mut db = Db::default();
        let root = db.lit_tree(&[lit![0], lit![1], lit![2], lit![3]]);
        debug_assert_eq!(db[root].depth(), 3);
        let mut var_manager = BasicVarManager::from_next_free(var![4]);

        let mut norm_cnf = Cnf::new();

        for idx in 0..=3 {
            db.define_unweighted(root, idx, Semantics::If, &mut norm_cnf, &mut var_manager)
                .unwrap();
        }

        assert_eq!(norm_cnf, cert_cnf);
    }

    #[test]
    fn gte_equal_clause_order() {
        let mut db = Db::default();
        let root = db.weighted_lit_tree(&[(lit![0], 4), (lit![1], 3), (lit![2], 2), (lit![3], 1)]);
        assert_eq!(root.offset(), 0);
        assert_eq!(root.multiplier(), 1);
        let root = root.id;
        let mut var_manager = BasicVarManager::from_next_free(var![4]);

        let mut proof = new_proof(0, false);

        let mut cert_cnf = Cnf::new();
        let mut leafs = [(lit![0], 0); 4];
        let mut leafs_init = false;

        for val in 1..=10 {
            let ret = db
                .define_weighted_cert(
                    root,
                    val,
                    &mut cert_cnf,
                    &mut var_manager,
                    &mut proof,
                    (&mut leafs, leafs_init, false),
                )
                .unwrap();
            leafs_init |= ret.is_some_and(|(_, i)| i);
        }

        let mut db = Db::default();
        let root = db.weighted_lit_tree(&[(lit![0], 4), (lit![1], 3), (lit![2], 2), (lit![3], 1)]);
        assert_eq!(root.offset(), 0);
        assert_eq!(root.multiplier(), 1);
        let root = root.id;
        let mut var_manager = BasicVarManager::from_next_free(var![4]);

        let mut norm_cnf = Cnf::new();

        for val in 1..=10 {
            db.define_weighted(root, val, &mut norm_cnf, &mut var_manager)
                .unwrap();
        }

        assert_eq!(norm_cnf, cert_cnf);
    }

    #[test]
    fn tot_db_single() {
        let mut db = Db::default();
        let a = db.lit_tree(&[lit![0], lit![1], lit![2], lit![3]]);
        let b = db.lit_tree(&[lit![4], lit![5]]);
        let c = db.insert(Node::internal(
            NodeCon::single(a, 3, 1),
            NodeCon::full(b),
            &db,
        ));
        let mut var_manager = BasicVarManager::from_next_free(var![6]);
        db[a].reserve_vars(3..=3, &mut var_manager);

        let mut proof = new_proof(0, false);

        let mut cnf = Cnf::new();
        let mut leafs = [lit![0]; 3];
        let mut leafs_init = false;

        for idx in 0..=2 {
            (_, leafs_init) = db
                .define_unweighted_cert(
                    c,
                    idx,
                    Semantics::IfAndOnlyIf,
                    &mut cnf,
                    &mut var_manager,
                    &mut proof,
                    (&mut leafs, leafs_init, false),
                )
                .unwrap();
        }

        let proof_file = proof
            .conclude::<Var>(pigeons::OutputGuarantee::None, &pigeons::Conclusion::None)
            .unwrap();
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path());
    }

    #[test]
    fn tot_db_limited() {
        let mut db = Db::default();
        let a = db.lit_tree(&[lit![0], lit![1], lit![2], lit![3]]);
        let b = db.lit_tree(&[lit![4], lit![5]]);
        let c = db.insert(Node::internal(
            NodeCon::limited(a, 0, 2, 1),
            NodeCon::full(b),
            &db,
        ));
        let mut var_manager = BasicVarManager::from_next_free(var![6]);
        db[a].reserve_vars(..=2, &mut var_manager);

        let mut proof = new_proof(0, false);

        let mut cnf = Cnf::new();
        let mut leafs = [lit![0]; 4];
        let mut leafs_init = false;

        for idx in 0..=3 {
            (_, leafs_init) = db
                .define_unweighted_cert(
                    c,
                    idx,
                    Semantics::IfAndOnlyIf,
                    &mut cnf,
                    &mut var_manager,
                    &mut proof,
                    (&mut leafs, leafs_init, false),
                )
                .unwrap();
        }

        let proof_file = proof
            .conclude::<Var>(pigeons::OutputGuarantee::None, &pigeons::Conclusion::None)
            .unwrap();
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path());
    }

    #[test]
    fn tot_db_limited_offset() {
        let mut db = Db::default();
        let a = db.lit_tree(&[lit![0], lit![1], lit![2], lit![3]]);
        let b = db.lit_tree(&[lit![4], lit![5]]);
        let c = db.insert(Node::internal(
            NodeCon::limited(a, 1, 2, 1),
            NodeCon::full(b),
            &db,
        ));
        let mut var_manager = BasicVarManager::from_next_free(var![6]);
        db[a].reserve_vars(2..=4, &mut var_manager);

        let mut proof = new_proof(0, false);

        let mut cnf = Cnf::new();
        let mut leafs = [lit![0]; 4];
        let mut leafs_init = false;

        for idx in 0..=3 {
            (_, leafs_init) = db
                .define_unweighted_cert(
                    c,
                    idx,
                    Semantics::IfAndOnlyIf,
                    &mut cnf,
                    &mut var_manager,
                    &mut proof,
                    (&mut leafs, leafs_init, false),
                )
                .unwrap();
        }

        let proof_file = proof
            .conclude::<Var>(pigeons::OutputGuarantee::None, &pigeons::Conclusion::None)
            .unwrap();
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path());
    }

    #[test]
    fn tot_db_offset() {
        let mut db = Db::default();
        let a = db.lit_tree(&[lit![0], lit![1], lit![2], lit![3]]);
        let b = db.lit_tree(&[lit![4], lit![5]]);
        let c = db.insert(Node::internal(
            NodeCon::offset_weighted(a, 2, 1),
            NodeCon::full(b),
            &db,
        ));
        let mut var_manager = BasicVarManager::from_next_free(var![6]);
        db[a].reserve_vars(3.., &mut var_manager);

        let mut proof = new_proof(0, false);

        let mut cnf = Cnf::new();
        let mut leafs = [lit![0]; 4];
        let mut leafs_init = false;

        for idx in 0..=3 {
            (_, leafs_init) = db
                .define_unweighted_cert(
                    c,
                    idx,
                    Semantics::IfAndOnlyIf,
                    &mut cnf,
                    &mut var_manager,
                    &mut proof,
                    (&mut leafs, leafs_init, false),
                )
                .unwrap();
        }

        let proof_file = proof
            .conclude::<Var>(pigeons::OutputGuarantee::None, &pigeons::Conclusion::None)
            .unwrap();
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path());
    }

    #[test]
    fn tot_db_offset_2() {
        let mut db = Db::default();
        let a = db.lit_tree(&[lit![0], lit![1], lit![2], lit![3]]);
        let b = db.lit_tree(&[lit![4], lit![5]]);
        let c = db.insert(Node::internal(
            NodeCon::offset_weighted(a, 1, 1),
            NodeCon::full(b),
            &db,
        ));
        let mut var_manager = BasicVarManager::from_next_free(var![6]);
        db[a].reserve_vars(2.., &mut var_manager);

        let mut proof = new_proof(0, false);

        let mut cnf = Cnf::new();
        let mut leafs = [lit![0]; 5];
        let mut leafs_init = false;

        for idx in 0..=4 {
            (_, leafs_init) = db
                .define_unweighted_cert(
                    c,
                    idx,
                    Semantics::IfAndOnlyIf,
                    &mut cnf,
                    &mut var_manager,
                    &mut proof,
                    (&mut leafs, leafs_init, false),
                )
                .unwrap();
        }

        let proof_file = proof
            .conclude::<Var>(pigeons::OutputGuarantee::None, &pigeons::Conclusion::None)
            .unwrap();
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path());
    }

    #[test]
    fn gte_db_offset() {
        let mut db = Db::default();
        let a = db.weighted_lit_tree(&[(lit![0], 1), (lit![1], 2), (lit![2], 10)]);
        let b = db.lit_tree(&[lit![4], lit![5]]);
        let c = db.insert(Node::internal(
            NodeCon::offset_weighted(a.id, 2, 1),
            NodeCon::full(b),
            &db,
        ));
        let mut var_manager = BasicVarManager::from_next_free(var![6]);
        db[a.id].reserve_vars(3.., &mut var_manager);

        let mut proof = new_proof(0, false);

        let mut cnf = Cnf::new();
        let mut leafs = [(lit![0], 0); 7];
        let mut leafs_init = false;

        for idx in 1..=13 {
            let ret = db
                .define_weighted_cert(
                    c,
                    idx,
                    &mut cnf,
                    &mut var_manager,
                    &mut proof,
                    (&mut leafs, leafs_init, false),
                )
                .unwrap();
            leafs_init |= ret.is_some_and(|(_, i)| i);
        }

        let proof_file = proof
            .conclude::<Var>(pigeons::OutputGuarantee::None, &pigeons::Conclusion::None)
            .unwrap();
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path());
    }
}
