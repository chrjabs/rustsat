//! # Totalizer Database

use std::{cmp, collections::BTreeMap, ops};

use crate::{
    encodings::atomics,
    instances::ManageVars,
    types::{Lit, RsHashMap},
    utils::unreachable_none,
};

use super::{
    nodedb::{NodeById, NodeCon, NodeId, NodeLike},
    nodedbimpl::DrainError,
    CollectClauses,
};

#[inline]
fn con_idx(idx: usize, con: NodeCon) -> usize {
    con.rev_map(idx + 1) - 1
}

/// A totalizer database
#[derive(Default, Clone)]
#[cfg_attr(feature = "internals", visibility::make(pub))]
#[cfg_attr(docsrs, doc(cfg(feature = "internals")))]
pub(super) struct Db {
    /// The node database of the totalizer
    nodes: Vec<Node>,
    /// Mapping literals to leaf nodes
    lookup_leaf: RsHashMap<Lit, NodeId>,
    /// Dummy Node ID
    dummy_id: Option<NodeId>,
    #[cfg(feature = "proof-logging")]
    semantic_defs: RsHashMap<(NodeId, usize, SemDefTyp), pidgeons::AbsConstraintId>,
}

impl NodeById for Db {
    type Node = Node;

    fn insert(&mut self, node: Self::Node) -> NodeId {
        match node.0 {
            INode::Leaf(lit) => {
                if let Some(&id) = self.lookup_leaf.get(&lit) {
                    return id;
                }
                self.lookup_leaf.insert(lit, NodeId(self.nodes.len()));
            }
            INode::Dummy => {
                if let Some(id) = self.dummy_id {
                    return id;
                }
                self.dummy_id = Some(NodeId(self.nodes.len()));
            }
            _ => (),
        }
        self.nodes.push(node);
        NodeId(self.nodes.len() - 1)
    }

    type Iter<'own> = std::slice::Iter<'own, Node>;

    fn iter(&self) -> Self::Iter<'_> {
        self.nodes.iter()
    }

    fn len(&self) -> usize {
        self.nodes.len()
    }

    type Drain<'own> = std::vec::Drain<'own, Node>;

    fn drain<R: ops::RangeBounds<NodeId>>(
        &mut self,
        range: R,
    ) -> Result<Self::Drain<'_>, DrainError> {
        let range = match range.start_bound() {
            ops::Bound::Included(id) => *id,
            ops::Bound::Excluded(id) => id + 1,
            ops::Bound::Unbounded => NodeId(0),
        }..match range.end_bound() {
            ops::Bound::Included(id) => id + 1,
            ops::Bound::Excluded(id) => *id,
            ops::Bound::Unbounded => NodeId(self.nodes.len()),
        };
        if range.is_empty() {
            return Ok(self.nodes.drain(self.nodes.len()..self.nodes.len()));
        }
        (range.end.0..self.nodes.len()).try_for_each(|idx| {
            self.nodes[idx]
                .drain(range.clone())
                .map_err(|con| DrainError {
                    referencing: NodeId(idx),
                    referenced: con,
                })
        })?;
        self.lookup_leaf.retain(|_, id| !range.contains(id));
        self.lookup_leaf.values_mut().for_each(|id| {
            if *id >= range.end {
                *id -= range.end - range.start;
            }
        });
        Ok(self.nodes.drain(range.start.0..range.end.0))
    }
}

impl ops::IndexMut<NodeId> for Db {
    fn index_mut(&mut self, index: NodeId) -> &mut Self::Output {
        &mut self.nodes[index.0]
    }
}

impl ops::Index<NodeId> for Db {
    type Output = Node;

    fn index(&self, index: NodeId) -> &Self::Output {
        &self.nodes[index.0]
    }
}

impl Db {
    /// Generates the encoding to define the positive output literal with value
    /// `val`, if it is not already defined. Recurses down the tree. The
    /// returned literal is the output literal and the encoding is added to the
    /// `collector`.
    ///
    /// # Errors
    ///
    /// If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
    pub fn define_pos<Col>(
        &mut self,
        id: NodeId,
        val: usize,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<Option<Lit>, crate::OutOfMemory>
    where
        Col: CollectClauses,
    {
        debug_assert!(val <= self[id].max_val());
        debug_assert!(val > 0);
        match &self[id].0 {
            INode::Leaf(lit) => {
                debug_assert_eq!(val, 1);
                if val != 1 {
                    return Ok(None);
                }
                Ok(Some(*lit))
            }
            INode::Unit(node) => {
                if val > node.lits.len() || val == 0 {
                    return Ok(None);
                }

                // Check if already encoded
                if let LitData::Lit { lit, enc_pos, .. } = node.lits[val - 1] {
                    if enc_pos {
                        return Ok(Some(lit));
                    }
                }

                Ok(Some(self.define_pos_tot(
                    id,
                    val - 1,
                    collector,
                    var_manager,
                )?))
            }
            INode::General(node) => {
                // Check if already encoded
                if let Some(lit_data) = node.lits.get(&val) {
                    if let LitData::Lit {
                        lit, enc_pos: true, ..
                    } = lit_data
                    {
                        return Ok(Some(*lit));
                    }
                } else {
                    return Ok(None);
                }

                debug_assert!(val <= node.max_val);
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

                // Propagate value
                if lcon.is_possible(val) && lcon.rev_map(val) <= self[lcon.id].max_val() {
                    if let Some(llit) =
                        self.define_pos(lcon.id, lcon.rev_map(val), collector, var_manager)?
                    {
                        collector.add_clause(atomics::lit_impl_lit(llit, olit))?;
                    }
                }
                if rcon.is_possible(val) && rcon.rev_map(val) <= self[rcon.id].max_val() {
                    if let Some(rlit) =
                        self.define_pos(rcon.id, rcon.rev_map(val), collector, var_manager)?
                    {
                        collector.add_clause(atomics::lit_impl_lit(rlit, olit))?;
                    };
                }

                // Propagate sums
                if lcon.map(lcon.offset() + 1) < val {
                    let lvals = self[lcon.id].vals(lcon.offset() + 1..lcon.rev_map_round_up(val));
                    let rmax = self[rcon.id].max_val();
                    for lval in lvals {
                        let rval = val - lcon.map(lval);
                        debug_assert!(rval > 0);
                        let rval_rev = rcon.rev_map(rval);
                        if rcon.is_possible(rval) && rval_rev <= rmax {
                            if let Some(rlit) =
                                self.define_pos(rcon.id, rval_rev, collector, var_manager)?
                            {
                                debug_assert!(
                                    lcon.len_limit.is_none() || lcon.offset() + 1 == lval
                                );
                                let llit = unreachable_none!(self.define_pos(
                                    lcon.id,
                                    lval,
                                    collector,
                                    var_manager
                                )?);
                                collector
                                    .add_clause(atomics::cube_impl_lit(&[llit, rlit], olit))?;
                            }
                        }
                    }
                }

                // Mark positive literal as encoded
                match &mut unreachable_none!(self[id].mut_general().lits.get_mut(&val)) {
                    LitData::None => unreachable!(),
                    LitData::Lit { enc_pos, .. } => *enc_pos = true,
                };

                Ok(Some(olit))
            }
            INode::Dummy => Ok(None),
        }
    }

    /// Stores the constraint IDs of the semantic definitions of an output literal
    #[cfg(feature = "proof-logging")]
    fn get_semantics<W: std::io::Write>(
        &mut self,
        id: NodeId,
        val: usize,
        leafs: &[Lit],
        typ: SemDefTyp,
        proof: &mut pidgeons::Proof<W>,
    ) -> std::io::Result<SemDefinition> {
        use crate::types::constraints::CardConstraint;
        use pidgeons::VarLike;

        debug_assert!(val <= self[id].len());
        Ok(if let Some(def) = self.semantic_defs.get(&(id, val, typ)) {
            (*def).into()
        } else {
            if self[id].is_leaf() {
                if val == 0 {
                    let olit = *self[id].lit(1).unwrap();
                    return Ok(olit.into());
                }
                return Ok(SemDefinition::None);
            }
            let sem = CardConstraint::new_lb(leafs.iter().copied(), val);
            let def = if val == 0 {
                match typ {
                    SemDefTyp::If => panic!("If semantic with `val=0` is undefined"),
                    SemDefTyp::OnlyIf => proof.redundant(&sem, &[])?,
                }
            } else {
                let olit = *self[id].lit(val).unwrap();
                match typ {
                    SemDefTyp::If => proof.redundant(
                        &atomics::card_impl_lit(&sem, olit),
                        &[olit.var().substitute_fixed(true)],
                    )?,
                    SemDefTyp::OnlyIf => proof.redundant(
                        &atomics::lit_impl_card(olit, &sem),
                        &[olit.var().substitute_fixed(false)],
                    )?,
                }
            };
            self.semantic_defs.insert((id, val, typ), def);
            def.into()
        })
    }

    /// First step of [`Self::define_pos_tot`]: checks preconditions and potentially returns
    fn precond_pos_tot(&mut self, id: NodeId, idx: usize) -> PrecondOutcome {
        let node = &self[id];
        debug_assert!(idx < node.max_val());
        if node.is_leaf() {
            debug_assert_eq!(idx, 0);
            return PrecondOutcome::Return(node[1]);
        }
        let lcon = unreachable_none!(node.left());
        let rcon = unreachable_none!(node.right());
        debug_assert!(matches!(
            self[lcon.id].0,
            INode::Leaf(_) | INode::Unit(_) | INode::Dummy
        ));
        debug_assert!(matches!(
            self[rcon.id].0,
            INode::Leaf(_) | INode::Unit(_) | INode::Dummy
        ));
        debug_assert_eq!(lcon.multiplier(), 1);
        debug_assert_eq!(rcon.multiplier(), 1);
        let node = node.unit();

        // Check if already encoded
        if let LitData::Lit { lit, enc_pos, .. } = node.lits[idx] {
            if enc_pos {
                return PrecondOutcome::Return(lit);
            }
        }

        // treat dummy nodes by passing through other connection
        if matches!(self[lcon.id].0, INode::Dummy) || matches!(self[rcon.id].0, INode::Dummy) {
            let realcon = if matches!(self[lcon.id].0, INode::Dummy) {
                rcon
            } else {
                lcon
            };
            debug_assert!(matches!(
                self[realcon.id].0,
                INode::Leaf(_) | INode::Unit(_)
            ));
            return PrecondOutcome::Passthrough(realcon);
        }

        // The maximum indices of left and right that influence the current
        // literal (ignoring offset and divisor)
        let l_max_idx = cmp::min(self.con_len(lcon) - 1, idx);
        let r_max_idx = cmp::min(self.con_len(rcon) - 1, idx);

        // The minimum indices of left and right that influence the current literal (ignoring
        // offset and divisor)
        let l_min_idx = if idx == r_max_idx {
            0
        } else {
            idx - r_max_idx - 1
        };
        let r_min_idx = if idx == l_max_idx {
            0
        } else {
            idx - l_max_idx - 1
        };

        PrecondOutcome::Continue(PrecondResult {
            lcon,
            rcon,
            l_max_idx,
            r_max_idx,
            l_min_idx,
            r_min_idx,
        })
    }

    /// Gets the correct `olit` to encode, reserving one if not yet done
    fn get_olit(&mut self, id: NodeId, idx: usize, var_manager: &mut dyn ManageVars) -> Lit {
        if let Some(&olit) = self[id].lit(idx + 1) {
            olit
        } else {
            let olit = var_manager.new_var().pos_lit();
            self[id].mut_unit().lits[idx] = LitData::new_lit(olit);
            olit
        }
    }

    /// Last step of [`Self::define_pos_tot`]
    fn encode_pos_tot<Col>(
        &mut self,
        id: NodeId,
        idx: usize,
        olit: Lit,
        pre: &PrecondResult,
        collector: &mut Col,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
    {
        // Mark positive literal as encoded (done first to avoid borrow checker problems)
        match &mut self[id].mut_unit().lits[idx] {
            LitData::None => unreachable!(),
            LitData::Lit { enc_pos, .. } => *enc_pos = true,
        };

        // Get lit slices of children
        let l_tmp_olit;
        let llits = match &self[pre.lcon.id].0 {
            INode::Leaf(lit) => {
                l_tmp_olit = LitData::new_lit(*lit);
                std::slice::from_ref(&l_tmp_olit)
            }
            INode::Unit(UnitNode { lits, .. }) => lits,
            INode::General(_) | INode::Dummy => unreachable!(),
        };
        let r_tmp_olit;
        let rlits = match &self[pre.rcon.id].0 {
            INode::Leaf(lit) => {
                r_tmp_olit = LitData::new_lit(*lit);
                std::slice::from_ref(&r_tmp_olit)
            }
            INode::Unit(UnitNode { lits, .. }) => lits,
            INode::General(_) | INode::Dummy => unreachable!(),
        };

        // Encode
        if pre.l_max_idx == idx {
            collector.add_clause(atomics::lit_impl_lit(
                *unreachable_none!(llits[con_idx(idx, pre.lcon)].lit()),
                olit,
            ))?;
        }
        if pre.r_max_idx == idx {
            collector.add_clause(atomics::lit_impl_lit(
                *unreachable_none!(rlits[con_idx(idx, pre.rcon)].lit()),
                olit,
            ))?;
        }
        let clause_for_lidx = |lidx: usize| {
            let ridx = idx - lidx - 1;
            debug_assert!(ridx <= pre.r_max_idx);
            let llit = *unreachable_none!(llits[con_idx(lidx, pre.lcon)].lit());
            let rlit = *unreachable_none!(rlits[con_idx(ridx, pre.rcon)].lit());
            atomics::cube_impl_lit(&[llit, rlit], olit)
        };
        let clause_iter = (pre.l_min_idx..cmp::min(pre.l_max_idx + 1, idx)).map(clause_for_lidx);
        collector.extend_clauses(clause_iter)?;

        Ok(())
    }

    /// Defines a positive output, assuming that the structure is a non-weighted totalizer
    ///
    /// The `idx` parameter is the output index, i.e., not the value represented by the output, but
    /// `value - 1`.
    ///
    /// # Errors
    ///
    /// If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
    pub fn define_pos_tot<Col>(
        &mut self,
        id: NodeId,
        idx: usize,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<Lit, crate::OutOfMemory>
    where
        Col: CollectClauses,
    {
        let pre = match self.precond_pos_tot(id, idx) {
            PrecondOutcome::Return(lit) => return Ok(lit),
            PrecondOutcome::Passthrough(con) => {
                let ilit =
                    self.define_pos_tot(con.id, con_idx(idx, con), collector, var_manager)?;
                let olit = self.get_olit(id, idx, var_manager);
                collector.add_clause(atomics::lit_impl_lit(ilit, olit))?;
                // Mark positive literal as encoded
                match &mut self[id].mut_unit().lits[idx] {
                    LitData::None => unreachable!(),
                    LitData::Lit { enc_pos, .. } => *enc_pos = true,
                };
                return Ok(olit);
            }
            PrecondOutcome::Continue(pre) => pre,
        };

        // Encode children (recurse)
        for lidx in pre.l_min_idx..=pre.l_max_idx {
            self.define_pos_tot(pre.lcon.id, con_idx(lidx, pre.lcon), collector, var_manager)?;
        }
        for ridx in pre.r_min_idx..=pre.r_max_idx {
            self.define_pos_tot(pre.rcon.id, con_idx(ridx, pre.rcon), collector, var_manager)?;
        }

        // Reserve variable for this node, if needed
        let olit = self.get_olit(id, idx, var_manager);

        // Encode this node
        self.encode_pos_tot(id, idx, olit, &pre, collector)?;

        Ok(olit)
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
    #[cfg(feature = "proof-logging")]
    pub fn define_pos_tot_cert<Col, W>(
        &mut self,
        id: NodeId,
        idx: usize,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pidgeons::Proof<W>,
        leafs: &mut [Lit],
    ) -> anyhow::Result<Lit>
    where
        Col: CollectClauses,
        W: std::io::Write,
    {
        use pidgeons::OperationLike;

        debug_assert_eq!(leafs.len(), self[id].len());

        let pre = match self.precond_pos_tot(id, idx) {
            PrecondOutcome::Return(lit) => {
                let mut new_leafs: Vec<_> = self.leaf_iter(id).collect();
                leafs.swap_with_slice(&mut new_leafs);
                return Ok(lit);
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
        let left_len = self.con_len(pre.lcon);
        let (left_leafs, right_leafs) = leafs.split_at_mut(left_len);
        for lidx in pre.l_min_idx..=pre.l_max_idx {
            self.define_pos_tot_cert(
                pre.lcon.id,
                con_idx(lidx, pre.lcon),
                collector,
                var_manager,
                proof,
                left_leafs,
            )?;
        }
        for ridx in pre.r_min_idx..=pre.r_max_idx {
            self.define_pos_tot_cert(
                pre.rcon.id,
                con_idx(ridx, pre.rcon),
                collector,
                var_manager,
                proof,
                right_leafs,
            )?;
        }

        // Reserve variable for this node, if needed
        let olit = self.get_olit(id, idx, var_manager);

        // Encode this node
        self.encode_pos_tot(id, idx, olit, &pre, collector)?;

        // Derive clauses in proof (in the same order that they were yielded)
        if pre.l_max_idx == idx {
            let (left_leafs, right_leafs) = leafs.split_at(left_len);
            let left_def =
                self.get_semantics(pre.lcon.id, idx + 1, left_leafs, SemDefTyp::OnlyIf, proof)?;
            let right_def =
                self.get_semantics(pre.rcon.id, 0, right_leafs, SemDefTyp::OnlyIf, proof)?;
            let this_def = self.get_semantics(id, idx + 1, leafs, SemDefTyp::If, proof)?;
            proof.operations(&(left_def + right_def + this_def))?;
        }
        if pre.r_max_idx == idx {
            let (left_leafs, right_leafs) = leafs.split_at(left_len);
            let left_def =
                self.get_semantics(pre.lcon.id, 0, left_leafs, SemDefTyp::OnlyIf, proof)?;
            let right_def =
                self.get_semantics(pre.rcon.id, idx + 1, right_leafs, SemDefTyp::OnlyIf, proof)?;
            let this_def = self.get_semantics(id, idx + 1, leafs, SemDefTyp::If, proof)?;
            proof.operations(&(left_def + right_def + this_def).saturate())?;
        }
        for lidx in pre.l_min_idx..cmp::min(pre.l_max_idx + 1, idx) {
            let (left_leafs, right_leafs) = leafs.split_at(left_len);
            let lval = pre.lcon.rev_map(lidx + 1);
            let rval = pre.rcon.rev_map(idx - lidx);
            debug_assert!(rval <= pre.r_max_idx + 1);
            let left_def =
                self.get_semantics(pre.lcon.id, lval, left_leafs, SemDefTyp::OnlyIf, proof)?;
            let right_def =
                self.get_semantics(pre.rcon.id, rval, right_leafs, SemDefTyp::OnlyIf, proof)?;
            let this_def = self.get_semantics(id, idx + 1, leafs, SemDefTyp::If, proof)?;
            proof.operations(&(this_def + left_def + right_def).saturate())?;
        }

        Ok(olit)
    }

    /// Recursively reserves all variables in the subtree rooted at the given node
    pub fn reserve_vars(&mut self, id: NodeId, var_manager: &mut dyn ManageVars) {
        if matches!(self[id].0, INode::Leaf(_) | INode::Dummy) {
            return;
        }

        // Recurse
        self.reserve_vars(unreachable_none!(self[id].left()).id, var_manager);
        self.reserve_vars(unreachable_none!(self[id].right()).id, var_manager);

        match &mut self[id].0 {
            INode::Unit(UnitNode { lits, .. }) => {
                for olit in lits {
                    if let LitData::None = olit {
                        *olit = LitData::new_lit(var_manager.new_var().pos_lit());
                    }
                }
            }
            INode::General(GeneralNode { lits, .. }) => {
                for (_, olit) in lits.iter_mut() {
                    if let LitData::None = olit {
                        *olit = LitData::new_lit(var_manager.new_var().pos_lit());
                    }
                }
            }
            INode::Leaf(_) | INode::Dummy => unreachable!(),
        }
    }

    /// Resets the status of what has already been encoded
    pub fn reset_encoded(&mut self) {
        for node in &mut self.nodes {
            match &mut node.0 {
                INode::Unit(UnitNode { lits, .. }) => {
                    for lit in lits {
                        if let LitData::Lit { enc_pos, .. } = lit {
                            *enc_pos = false;
                        }
                    }
                }
                INode::General(GeneralNode { lits, .. }) => {
                    for lit in lits.values_mut() {
                        if let LitData::Lit { enc_pos, .. } = lit {
                            *enc_pos = false;
                        }
                    }
                }
                INode::Leaf(_) | INode::Dummy => (),
            }
        }
    }

    /// Resets the reserved variables in the database. This also resets the
    /// status of what has already been encoded.
    #[cfg(feature = "internals")]
    pub fn reset_vars(&mut self) {
        for node in &mut self.nodes {
            match &mut node.0 {
                INode::Leaf(_) | INode::Dummy => (),
                INode::Unit(UnitNode { lits, .. }) => {
                    for lit in lits {
                        *lit = LitData::None;
                    }
                }
                INode::General(GeneralNode { lits, .. }) => {
                    for lit in lits.values_mut() {
                        *lit = LitData::None;
                    }
                }
            }
        }
    }
}

enum PrecondOutcome {
    Return(Lit),
    Continue(PrecondResult),
    Passthrough(NodeCon),
}

struct PrecondResult {
    lcon: NodeCon,
    rcon: NodeCon,
    l_max_idx: usize,
    r_max_idx: usize,
    l_min_idx: usize,
    r_min_idx: usize,
}

#[cfg(feature = "proof-logging")]
#[derive(Hash, Clone, Copy, PartialEq, Eq)]
enum SemDefinition {
    None,
    Id(pidgeons::AbsConstraintId),
    Axiom(Lit),
}

#[cfg(feature = "proof-logging")]
impl From<pidgeons::AbsConstraintId> for SemDefinition {
    fn from(value: pidgeons::AbsConstraintId) -> Self {
        Self::Id(value)
    }
}

#[cfg(feature = "proof-logging")]
impl From<Lit> for SemDefinition {
    fn from(value: Lit) -> Self {
        Self::Axiom(value)
    }
}

#[cfg(feature = "proof-logging")]
impl ops::Add<SemDefinition> for SemDefinition {
    type Output = pidgeons::OperationSequence;

    fn add(self, rhs: SemDefinition) -> Self::Output {
        match self {
            SemDefinition::None => match rhs {
                SemDefinition::None => panic!("cannot add two non-definitions"),
                SemDefinition::Id(rhs) => rhs.into(),
                SemDefinition::Axiom(rhs) => pidgeons::Axiom::from(rhs).into(),
            },
            SemDefinition::Id(lhs) => match rhs {
                SemDefinition::None => lhs.into(),
                SemDefinition::Id(rhs) => lhs + rhs,
                SemDefinition::Axiom(rhs) => lhs + pidgeons::Axiom::from(rhs),
            },
            SemDefinition::Axiom(lhs) => match rhs {
                SemDefinition::None => pidgeons::Axiom::from(lhs).into(),
                SemDefinition::Id(rhs) => pidgeons::Axiom::from(lhs) + rhs,
                SemDefinition::Axiom(rhs) => {
                    pidgeons::Axiom::from(lhs) + pidgeons::Axiom::from(rhs)
                }
            },
        }
    }
}

#[cfg(feature = "proof-logging")]
impl ops::Add<SemDefinition> for pidgeons::OperationSequence {
    type Output = pidgeons::OperationSequence;

    fn add(self, rhs: SemDefinition) -> Self::Output {
        match rhs {
            SemDefinition::None => self,
            SemDefinition::Id(rhs) => self + rhs,
            SemDefinition::Axiom(rhs) => self + pidgeons::Axiom::from(rhs),
        }
    }
}

#[cfg(feature = "proof-logging")]
#[derive(Hash, Clone, Copy, PartialEq, Eq)]
enum SemDefTyp {
    If,
    OnlyIf,
}

/// A totalizer adder node
#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(transparent)]
#[cfg(not(feature = "internals"))]
pub struct Node(pub(in crate::encodings) INode);

/// A totalizer adder node
///
/// The internal node [`INode`] representation is only accessible on crate feature `internals`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(transparent)]
#[cfg(feature = "internals")]
pub struct Node(pub INode);

impl From<INode> for Node {
    fn from(value: INode) -> Self {
        Self(value)
    }
}

/// The internal totalizer node type
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "internals", visibility::make(pub))]
#[cfg_attr(docsrs, doc(cfg(feature = "internals")))]
pub(in crate::encodings) enum INode {
    /// An input literal, i.e., a leaf of the tree
    Leaf(Lit),
    /// An internal node with unit weight
    Unit(UnitNode),
    /// An internal weighted node
    General(GeneralNode),
    /// A dummy node to patch in another structure later on
    Dummy,
}

impl NodeLike for Node {
    type ValIter = std::iter::Chain<ops::Range<usize>, std::vec::IntoIter<usize>>;

    fn is_leaf(&self) -> bool {
        matches!(self.0, INode::Leaf(_))
    }

    fn max_val(&self) -> usize {
        match &self.0 {
            INode::Leaf(_) => 1,
            INode::Unit(node) => node.lits.len(),
            INode::General(node) => node.max_val,
            INode::Dummy => 0,
        }
    }

    fn len(&self) -> usize {
        match &self.0 {
            INode::Leaf(_) => 1,
            INode::Unit(node) => node.lits.len(),
            INode::General(node) => node.lits.len(),
            INode::Dummy => 0,
        }
    }

    fn vals<R>(&self, range: R) -> Self::ValIter
    where
        R: ops::RangeBounds<usize>,
    {
        match &self.0 {
            INode::Leaf(_) => {
                if range.contains(&1) {
                    return (1..2).chain(vec![]);
                }
                (0..0).chain(vec![])
            }
            INode::Unit(node) => {
                let lb = match range.start_bound() {
                    ops::Bound::Included(b) => cmp::max(*b, 1),
                    ops::Bound::Excluded(b) => b + 1,
                    ops::Bound::Unbounded => 1,
                };
                let ub = match range.end_bound() {
                    ops::Bound::Included(b) => cmp::min(b + 1, node.lits.len() + 1),
                    ops::Bound::Excluded(b) => cmp::min(*b, node.lits.len() + 1),
                    ops::Bound::Unbounded => node.lits.len() + 1,
                };
                (lb..ub).chain(vec![])
            }
            INode::General(node) => {
                let vals: Vec<_> = node.lits.range(range).map(|(val, _)| *val).collect();
                (0..0).chain(vals)
            }
            INode::Dummy => (0..0).chain(vec![]),
        }
    }

    fn right(&self) -> Option<NodeCon> {
        match &self.0 {
            INode::Leaf(..) | INode::Dummy => None,
            INode::Unit(node) => Some(node.right),
            INode::General(node) => Some(node.right),
        }
    }

    fn left(&self) -> Option<NodeCon> {
        match &self.0 {
            INode::Leaf(..) | INode::Dummy => None,
            INode::Unit(node) => Some(node.left),
            INode::General(node) => Some(node.left),
        }
    }

    fn depth(&self) -> usize {
        match &self.0 {
            INode::Leaf(..) | INode::Dummy => 1,
            INode::Unit(node) => node.depth,
            INode::General(node) => node.depth,
        }
    }

    fn internal<Db>(left: NodeCon, right: NodeCon, db: &Db) -> Self
    where
        Db: NodeById<Node = Self>,
    {
        let general = left.multiplier != right.multiplier
            || matches!(&db[left.id].0, INode::General(_))
            || matches!(&db[right.id].0, INode::General(_));
        if general {
            let lvals: Vec<_> = db[left.id]
                .vals(left.offset()..)
                .map(|val| left.map(val))
                .collect();
            let rvals: Vec<_> = db[right.id]
                .vals(right.offset()..)
                .map(|val| right.map(val))
                .collect();
            return INode::General(GeneralNode::new(
                &lvals,
                &rvals,
                std::cmp::max(db[left.id].depth(), db[right.id].depth()) + 1,
                left,
                right,
            ))
            .into();
        }
        // if both inputs have the same weight, the multiplier should be 1
        debug_assert!(left.multiplier() == 1 && right.multiplier() == 1);
        INode::Unit(UnitNode::new(
            db.con_len(left) + db.con_len(right),
            std::cmp::max(db[left.id].depth(), db[right.id].depth()) + 1,
            left,
            right,
        ))
        .into()
    }

    fn leaf(lit: Lit) -> Self {
        INode::Leaf(lit).into()
    }
}

impl Node {
    /// Panic-safe version of literal indexing
    #[must_use]
    pub fn lit(&self, val: usize) -> Option<&Lit> {
        match &self.0 {
            INode::Leaf(lit, ..) => {
                if val != 1 {
                    return None;
                }
                Some(lit)
            }
            INode::Unit(node) => node.lit(val),
            INode::General(node) => node.lit(val),
            INode::Dummy => None,
        }
    }

    /// Checks if a given output value is positively encoded
    #[must_use]
    pub fn encoded_pos(&self, val: usize) -> bool {
        match &self.0 {
            INode::Leaf(..) => {
                if val != 1 {
                    return false;
                }
                true
            }
            INode::Unit(node) => node.encoded_pos(val),
            INode::General(node) => node.encoded_pos(val),
            INode::Dummy => true,
        }
    }

    /// Returns the internal node and panics if the node is not a unit
    pub(crate) fn unit(&self) -> &UnitNode {
        match &self.0 {
            INode::Unit(node) => node,
            _ => panic!("called `unit` on non-unit node"),
        }
    }

    /// Returns the internal node and panics if the node is not a unit
    pub(crate) fn mut_unit(&mut self) -> &mut UnitNode {
        match &mut self.0 {
            INode::Unit(node) => node,
            _ => panic!("called `unit` on non-unit node"),
        }
    }

    /// Returns the internal node and panics if the node is not general
    pub(crate) fn mut_general(&mut self) -> &mut GeneralNode {
        match &mut self.0 {
            INode::General(node) => node,
            _ => panic!("called `unit` on non-general node"),
        }
    }

    /// Adjusts the connections of the node to draining a range of nodes. If the
    /// nodes references a nodes within the drained range, it returns that
    /// [`NodeId`] as an Error.
    fn drain(&mut self, range: ops::Range<NodeId>) -> Result<(), NodeId> {
        match &mut self.0 {
            INode::Leaf(_) | INode::Dummy => Ok(()),
            INode::Unit(UnitNode { left, right, .. })
            | INode::General(GeneralNode { left, right, .. }) => {
                if range.contains(&left.id) {
                    return Err(left.id);
                }
                if range.contains(&right.id) {
                    return Err(right.id);
                }
                if left.id >= range.end {
                    left.id -= range.end - range.start;
                }
                if right.id >= range.end {
                    right.id -= range.end - range.start;
                }
                Ok(())
            }
        }
    }
}

/// Access to output literals. Panics if the literal has not been reserved yet.
/// The index is the output literal _value_, not it's index.
impl ops::Index<usize> for Node {
    type Output = Lit;

    fn index(&self, val: usize) -> &Self::Output {
        self.lit(val).unwrap()
    }
}

/// An internal node of the totalizer
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnitNode {
    pub(crate) lits: Vec<LitData>,
    pub(crate) depth: usize,
    pub(crate) left: NodeCon,
    pub(crate) right: NodeCon,
}

impl UnitNode {
    fn new(len: usize, depth: usize, left: NodeCon, right: NodeCon) -> Self {
        // Length of node can never change
        let mut lits = vec![];
        lits.reserve_exact(len);
        (0..len).for_each(|_| lits.push(LitData::default()));
        Self {
            lits,
            depth,
            left,
            right,
        }
    }

    /// Panic-safe version of literal indexing
    #[inline]
    #[must_use]
    pub fn lit(&self, val: usize) -> Option<&Lit> {
        self.lits[val - 1].lit()
    }

    /// Checks if a given value is positively encoded
    #[inline]
    #[must_use]
    pub fn encoded_pos(&self, val: usize) -> bool {
        self.lits[val - 1].encoded_pos()
    }
}

impl ops::Index<usize> for UnitNode {
    type Output = Lit;

    fn index(&self, index: usize) -> &Self::Output {
        self.lit(index).unwrap()
    }
}

/// An internal _general_ (weighted) node
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GeneralNode {
    pub(crate) lits: BTreeMap<usize, LitData>,
    pub(crate) depth: usize,
    pub(crate) max_val: usize,
    pub(crate) left: NodeCon,
    pub(crate) right: NodeCon,
}

impl GeneralNode {
    fn new(lvals: &[usize], rvals: &[usize], depth: usize, left: NodeCon, right: NodeCon) -> Self {
        let mut lits: BTreeMap<_, _> = lvals.iter().map(|&val| (val, LitData::default())).collect();
        for val in rvals {
            if !lits.contains_key(val) {
                lits.insert(*val, LitData::default());
            }
        }
        let mut max_val = 0;
        for lval in lvals {
            for rval in rvals {
                let val = lval + rval;
                max_val = val;
                lits.entry(val).or_insert_with(LitData::default);
            }
        }
        Self {
            lits,
            depth,
            max_val,
            left,
            right,
        }
    }

    /// Panic-safe version of literal indexing
    #[must_use]
    pub fn lit(&self, val: usize) -> Option<&Lit> {
        self.lits.get(&val).and_then(|dat| dat.lit())
    }

    /// Checks if a given value is positively encoded
    #[inline]
    #[must_use]
    pub fn encoded_pos(&self, val: usize) -> bool {
        self.lits.get(&val).map_or(false, LitData::encoded_pos)
    }
}

/// Data associated with an output literal in a [`Node`]
#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub(crate) enum LitData {
    #[default]
    None,
    Lit {
        lit: Lit,
        enc_pos: bool,
        // needed when getting around to implement lower bounding
        // enc_neg: bool,
    },
}

impl LitData {
    fn new_lit(lit: Lit) -> Self {
        LitData::Lit {
            lit,
            enc_pos: false,
        }
    }

    #[inline]
    fn lit(&self) -> Option<&Lit> {
        match self {
            LitData::None => None,
            LitData::Lit { lit, .. } => Some(lit),
        }
    }

    #[inline]
    fn encoded_pos(&self) -> bool {
        match self {
            LitData::None => false,
            LitData::Lit { enc_pos, .. } => *enc_pos,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        encodings::nodedb::{NodeById, NodeCon, NodeLike},
        instances::{BasicVarManager, Cnf, ManageVars},
        lit, var,
    };

    use super::Db;

    #[test]
    fn tot_db() {
        let mut db = Db::default();
        let root = db.lit_tree(&[lit![0], lit![1], lit![2], lit![3]]);
        debug_assert_eq!(db[root].depth(), 3);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);

        let mut cnf = Cnf::new();
        db.define_pos_tot(root, 0, &mut cnf, &mut var_manager)
            .unwrap();
        debug_assert_eq!(cnf.len(), 6);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos_tot(root, 1, &mut cnf, &mut var_manager)
            .unwrap();
        debug_assert_eq!(cnf.len(), 9);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos_tot(root, 2, &mut cnf, &mut var_manager)
            .unwrap();
        debug_assert_eq!(cnf.len(), 8);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos_tot(root, 3, &mut cnf, &mut var_manager)
            .unwrap();
        debug_assert_eq!(cnf.len(), 3);
    }

    #[test]
    fn weighted_tot_db() {
        let mut db = Db::default();
        let con = db.weighted_lit_tree(&[(lit![0], 4), (lit![1], 4), (lit![2], 7), (lit![3], 7)]);
        debug_assert_eq!(con.multiplier(), 1);
        debug_assert_eq!(con.offset(), 0);
        debug_assert_eq!(con.divisor(), 1);
        let root = con.id;
        debug_assert_eq!(db[root].depth(), 3);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);

        let mut cnf = Cnf::new();
        db.define_pos(root, 1, &mut cnf, &mut var_manager).unwrap();
        debug_assert_eq!(cnf.len(), 0);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos(root, 4, &mut cnf, &mut var_manager).unwrap();
        debug_assert_eq!(cnf.len(), 3);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos(root, 7, &mut cnf, &mut var_manager).unwrap();
        debug_assert_eq!(cnf.len(), 3);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos(root, 8, &mut cnf, &mut var_manager).unwrap();
        debug_assert_eq!(cnf.len(), 2);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos(root, 15, &mut cnf, &mut var_manager).unwrap();
        debug_assert_eq!(cnf.len(), 4);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos(root, 22, &mut cnf, &mut var_manager).unwrap();
        debug_assert_eq!(cnf.len(), 3);
    }

    #[test]
    fn weighted_tot_db2() {
        let mut db = Db::default();
        let con = db.weighted_lit_tree(&[(lit![0], 3), (lit![1], 2), (lit![2], 1)]);
        debug_assert_eq!(con.multiplier(), 1);
        debug_assert_eq!(con.offset(), 0);
        debug_assert_eq!(con.divisor(), 1);
        let root = con.id;
        debug_assert_eq!(db[root].depth(), 3);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![3]);

        let mut cnf = Cnf::new();
        db.define_pos(root, 1, &mut cnf, &mut var_manager).unwrap();
        debug_assert_eq!(cnf.len(), 2);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos(root, 2, &mut cnf, &mut var_manager).unwrap();
        debug_assert_eq!(cnf.len(), 2);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos(root, 3, &mut cnf, &mut var_manager).unwrap();
        debug_assert_eq!(cnf.len(), 3);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos(root, 4, &mut cnf, &mut var_manager).unwrap();
        debug_assert_eq!(cnf.len(), 2);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos(root, 5, &mut cnf, &mut var_manager).unwrap();
        debug_assert_eq!(cnf.len(), 2);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos(root, 6, &mut cnf, &mut var_manager).unwrap();
        debug_assert_eq!(cnf.len(), 2);
    }

    #[test]
    fn drain() {
        let mut db = Db::default();
        let t1 = db.lit_tree(&[lit![0], lit![1], lit![2], lit![3]]);
        let t2 = db.lit_tree(&[lit![4], lit![5], lit![6], lit![7]]);
        let t3 = db.lit_tree(&[lit![8], lit![9], lit![10], lit![11]]);
        db.merge(&[NodeCon::full(t1), NodeCon::full(t3)]);
        db.drain(t1 + 1..=t2).unwrap();
    }

    #[cfg(feature = "proof-logging")]
    mod proofs {
        use std::{
            fs::File,
            io::{BufRead, BufReader},
            path::Path,
            process::Command,
        };

        use crate::{
            encodings::nodedb::{NodeById, NodeLike},
            instances::{BasicVarManager, Cnf, ManageVars},
            lit, var,
        };

        use super::Db;

        fn print_file<P: AsRef<Path>>(path: P) {
            println!();
            for line in BufReader::new(File::open(path).expect("could not open file")).lines() {
                println!("{}", line.unwrap());
            }
            println!();
        }

        fn verify_proof<P1: AsRef<Path>, P2: AsRef<Path>>(instance: P1, proof: P2) {
            println!("start checking proof");
            let out = Command::new("veripb")
                .arg(instance.as_ref())
                .arg(proof.as_ref())
                .output()
                .expect("failed to run veripb");
            if out.status.success() {
                print_file(proof);
                return;
            }
            print_file(proof);
            panic!("verification failed: {out:?}")
        }

        fn new_proof(
            num_constraints: usize,
            optimization: bool,
        ) -> pidgeons::Proof<tempfile::NamedTempFile> {
            let file =
                tempfile::NamedTempFile::new().expect("failed to create temporary proof file");
            pidgeons::Proof::new(file, num_constraints, optimization)
                .expect("failed to start proof")
        }

        #[test]
        fn tot_db_cert() {
            let mut db = Db::default();
            let root = db.lit_tree(&[lit![0], lit![1], lit![2], lit![3]]);
            debug_assert_eq!(db[root].depth(), 3);
            let mut var_manager = BasicVarManager::default();
            var_manager.increase_next_free(var![4]);

            let mut proof = new_proof(0, false);

            let mut cnf = Cnf::new();
            let mut lits = [lit![0]; 4];
            db.define_pos_tot_cert(root, 0, &mut cnf, &mut var_manager, &mut proof, &mut lits)
                .unwrap();
            db.define_pos_tot_cert(root, 1, &mut cnf, &mut var_manager, &mut proof, &mut lits)
                .unwrap();
            db.define_pos_tot_cert(root, 2, &mut cnf, &mut var_manager, &mut proof, &mut lits)
                .unwrap();
            db.define_pos_tot_cert(root, 3, &mut cnf, &mut var_manager, &mut proof, &mut lits)
                .unwrap();

            let proof_file = proof
                .conclude(pidgeons::OutputGuarantee::None, &pidgeons::Conclusion::None)
                .unwrap();
            let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
            verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path());
        }
    }
}
