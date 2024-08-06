//! # Totalizer Database

use std::{cmp, collections::BTreeMap, ops};

use crate::{
    encodings::atomics,
    instances::ManageVars,
    lit,
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

/// Helper to get a slice of the output literals of a given unweighted node
macro_rules! get_lit_slice {
    ($self:expr, $id:expr, $buf:expr) => {{
        match &$self.nodes[$id.0] {
            Node::Leaf(lit) => {
                $buf = LitData::new_lit(*lit);
                std::slice::from_ref(&$buf)
            }
            Node::Unit(UnitNode { lits, .. }) => lits,
            Node::General(_) | Node::Dummy => unreachable!(),
        }
    }};
}

/// Helper to get the output literal with a given index
#[cfg(feature = "proof-logging")]
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

macro_rules! weighted_pre {
    ($self:expr, $id:expr, $node:expr, $val:expr, $vm:expr) => {{
        // Check if already encoded
        if let Some(lit_data) = $node.lits.get(&$val) {
            if let LitData::Lit {
                lit,
                semantics: Some(semantics),
            } = lit_data
            {
                if semantics.has_if() {
                    return Ok(Some(*lit));
                }
            }
        } else {
            return Ok(None);
        }

        debug_assert!($node.lits.contains_key(&$val));

        let lcon = $node.left;
        let rcon = $node.right;

        // Reserve variable for this node, if needed
        let olit = if let Some(&olit) = $node.lit($val) {
            olit
        } else {
            let olit = $vm.new_var().pos_lit();
            *unreachable_none!($self[$id].mut_general().lits.get_mut(&$val)) =
                LitData::new_lit(olit);
            olit
        };

        WeightedPrecondResult { lcon, rcon, olit }
    }};
}

/// A totalizer database
#[derive(Default, Clone)]
pub struct Db {
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
        match node {
            Node::Leaf(lit) => {
                if let Some(&id) = self.lookup_leaf.get(&lit) {
                    return id;
                }
                self.lookup_leaf.insert(lit, NodeId(self.nodes.len()));
            }
            Node::Dummy => {
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
    pub fn define_weighted<Col>(
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
        match &self[id] {
            Node::Leaf(lit) => {
                debug_assert_eq!(val, 1);
                if val != 1 {
                    return Ok(None);
                }
                Ok(Some(*lit))
            }
            Node::Unit(node) => {
                if val > node.lits.len() || val == 0 {
                    return Ok(None);
                }

                Ok(Some(self.define_unweighted(
                    id,
                    val - 1,
                    Semantics::If,
                    collector,
                    var_manager,
                )?))
            }
            Node::General(node) => {
                let pre = weighted_pre!(self, id, node, val, var_manager);

                // Propagate value
                if pre.lcon.is_possible(val) && pre.lcon.rev_map(val) <= self[pre.lcon.id].max_val()
                {
                    if let Some(llit) = self.define_weighted(
                        pre.lcon.id,
                        pre.lcon.rev_map(val),
                        collector,
                        var_manager,
                    )? {
                        collector.add_clause(atomics::lit_impl_lit(llit, pre.olit))?;
                    }
                }
                if pre.rcon.is_possible(val) && pre.rcon.rev_map(val) <= self[pre.rcon.id].max_val()
                {
                    if let Some(rlit) = self.define_weighted(
                        pre.rcon.id,
                        pre.rcon.rev_map(val),
                        collector,
                        var_manager,
                    )? {
                        collector.add_clause(atomics::lit_impl_lit(rlit, pre.olit))?;
                    };
                }

                // Propagate sums
                if pre.lcon.map(pre.lcon.offset() + 1) < val {
                    let lvals = self[pre.lcon.id]
                        .vals(pre.lcon.offset() + 1..pre.lcon.rev_map_round_up(val));
                    let rmax = self[pre.rcon.id].max_val();
                    for lval in lvals {
                        let rval = val - pre.lcon.map(lval);
                        debug_assert!(rval > 0);
                        let rval_rev = pre.rcon.rev_map(rval);
                        if pre.rcon.is_possible(rval) && rval_rev <= rmax {
                            if let Some(rlit) =
                                self.define_weighted(pre.rcon.id, rval_rev, collector, var_manager)?
                            {
                                debug_assert!(
                                    pre.lcon.len_limit.is_none() || pre.lcon.offset() + 1 == lval
                                );
                                let llit = unreachable_none!(self.define_weighted(
                                    pre.lcon.id,
                                    lval,
                                    collector,
                                    var_manager
                                )?);
                                collector
                                    .add_clause(atomics::cube_impl_lit(&[llit, rlit], pre.olit))?;
                            }
                        }
                    }
                }

                // Mark "if" semantics as encoded
                unreachable_none!(self[id].mut_general().lits.get_mut(&val))
                    .add_semantics(Semantics::If);

                Ok(Some(pre.olit))
            }
            Node::Dummy => Ok(None),
        }
    }

    /// Generates the encoding to define the positive output literal with value `val`, if it is not
    /// already defined. The derivation of the generated clauses is certified in the provided
    /// proof. Recurses down the tree. The returned literal is the output literal and the encoding
    /// is added to the `collector`.
    ///
    /// # Errors
    ///
    /// If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
    #[cfg(feature = "proof-logging")]
    pub fn define_weighted_cert<Col, W>(
        &mut self,
        id: NodeId,
        val: usize,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pidgeons::Proof<W>,
        leafs: &mut [(Lit, usize)],
    ) -> anyhow::Result<Option<Lit>>
    where
        Col: crate::encodings::CollectCertClauses,
        W: std::io::Write,
    {
        use pidgeons::OperationLike;

        debug_assert!(val <= self[id].max_val());
        debug_assert!(val > 0);
        debug_assert_eq!(leafs.len(), self[id].n_leafs());
        match &self[id] {
            Node::Leaf(lit) => {
                debug_assert_eq!(val, 1);
                leafs[0] = (*lit, 1);
                if val != 1 {
                    return Ok(None);
                }
                Ok(Some(*lit))
            }
            Node::Unit(node) => {
                if val > node.lits.len() || val == 0 {
                    return Ok(None);
                }

                let mut unweighted_leafs: Vec<_> = leafs.iter().map(|(l, _)| *l).collect();
                let olit = self.define_unweighted_cert(
                    id,
                    val - 1,
                    Semantics::If,
                    collector,
                    var_manager,
                    proof,
                    &mut unweighted_leafs,
                )?;
                for (idx, &lit) in unweighted_leafs.iter().enumerate() {
                    leafs[idx] = (lit, 1);
                }
                Ok(Some(olit))
            }
            Node::General(node) => {
                let pre = weighted_pre!(self, id, node, val, var_manager);

                let (left_leafs, right_leafs) = leafs.split_at_mut(self[pre.lcon.id].n_leafs());

                // Propagate value
                if pre.lcon.is_possible(val) && pre.lcon.rev_map(val) <= self[pre.lcon.id].max_val()
                {
                    if let Some(llit) = self.define_weighted_cert(
                        pre.lcon.id,
                        pre.lcon.rev_map(val),
                        collector,
                        var_manager,
                        proof,
                        left_leafs,
                    )? {
                        let left_def = self.get_semantics(
                            pre.lcon.id,
                            pre.lcon.rev_map(val),
                            SemDefTyp::OnlyIf,
                            left_leafs.iter().copied(),
                            proof,
                        )?;
                        let right_def = self.get_semantics(
                            pre.rcon.id,
                            0,
                            SemDefTyp::OnlyIf,
                            right_leafs.iter().copied(),
                            proof,
                        )?;
                        let this_def = self.get_semantics(
                            id,
                            val,
                            SemDefTyp::If,
                            left_leafs
                                .iter()
                                .map(|(l, w)| (*l, *w * pre.lcon.multiplier()))
                                .chain(
                                    right_leafs
                                        .iter()
                                        .map(|(l, w)| (*l, *w * pre.rcon.multiplier())),
                                ),
                            proof,
                        )?;
                        let id = proof.operations(
                            &(this_def
                                + (left_def * pre.lcon.multiplier())
                                + (right_def * pre.rcon.multiplier()))
                            .saturate(),
                        )?;
                        collector.add_cert_clause(atomics::lit_impl_lit(llit, pre.olit), id)?;
                    }
                }
                if pre.rcon.is_possible(val) && pre.rcon.rev_map(val) <= self[pre.rcon.id].max_val()
                {
                    if let Some(rlit) = self.define_weighted_cert(
                        pre.rcon.id,
                        pre.rcon.rev_map(val),
                        collector,
                        var_manager,
                        proof,
                        right_leafs,
                    )? {
                        let left_def = self.get_semantics(
                            pre.lcon.id,
                            0,
                            SemDefTyp::OnlyIf,
                            left_leafs.iter().copied(),
                            proof,
                        )?;
                        let right_def = self.get_semantics(
                            pre.rcon.id,
                            pre.rcon.rev_map(val),
                            SemDefTyp::OnlyIf,
                            right_leafs.iter().copied(),
                            proof,
                        )?;
                        let this_def = self.get_semantics(
                            id,
                            val,
                            SemDefTyp::If,
                            left_leafs
                                .iter()
                                .map(|(l, w)| (*l, *w * pre.lcon.multiplier()))
                                .chain(
                                    right_leafs
                                        .iter()
                                        .map(|(l, w)| (*l, *w * pre.rcon.multiplier())),
                                ),
                            proof,
                        )?;
                        let id = proof.operations(
                            &(this_def
                                + (left_def * pre.lcon.multiplier())
                                + (right_def * pre.rcon.multiplier()))
                            .saturate(),
                        )?;
                        collector.add_cert_clause(atomics::lit_impl_lit(rlit, pre.olit), id)?;
                    };
                }

                // Propagate sums
                if pre.lcon.map(pre.lcon.offset() + 1) < val {
                    let lvals = self[pre.lcon.id]
                        .vals(pre.lcon.offset() + 1..pre.lcon.rev_map_round_up(val));
                    let rmax = self[pre.rcon.id].max_val();
                    for lval in lvals {
                        let rval = val - pre.lcon.map(lval);
                        debug_assert!(rval > 0);
                        let rval_rev = pre.rcon.rev_map(rval);
                        if pre.rcon.is_possible(rval) && rval_rev <= rmax {
                            if let Some(rlit) = self.define_weighted_cert(
                                pre.rcon.id,
                                rval_rev,
                                collector,
                                var_manager,
                                proof,
                                right_leafs,
                            )? {
                                debug_assert!(
                                    pre.lcon.len_limit.is_none() || pre.lcon.offset() + 1 == lval
                                );
                                let llit = unreachable_none!(self.define_weighted_cert(
                                    pre.lcon.id,
                                    lval,
                                    collector,
                                    var_manager,
                                    proof,
                                    left_leafs
                                )?);
                                let left_def = self.get_semantics(
                                    pre.lcon.id,
                                    lval,
                                    SemDefTyp::OnlyIf,
                                    left_leafs.iter().copied(),
                                    proof,
                                )?;
                                let right_def = self.get_semantics(
                                    pre.rcon.id,
                                    rval_rev,
                                    SemDefTyp::OnlyIf,
                                    right_leafs.iter().copied(),
                                    proof,
                                )?;
                                let this_def = self.get_semantics(
                                    id,
                                    val,
                                    SemDefTyp::If,
                                    left_leafs
                                        .iter()
                                        .map(|(l, w)| (*l, *w * pre.lcon.multiplier()))
                                        .chain(
                                            right_leafs
                                                .iter()
                                                .map(|(l, w)| (*l, *w * pre.rcon.multiplier())),
                                        ),
                                    proof,
                                )?;
                                let id = proof.operations(
                                    &(this_def
                                        + (left_def * pre.lcon.multiplier())
                                        + (right_def * pre.rcon.multiplier()))
                                    .saturate(),
                                )?;
                                collector.add_cert_clause(
                                    atomics::cube_impl_lit(&[llit, rlit], pre.olit),
                                    id,
                                )?;
                            }
                        }
                    }
                }

                // Only now finally multiply the leaf weights since they won't be used at lower
                // levels any more
                for (idx, (_, w)) in leafs.iter_mut().enumerate() {
                    if idx < self[pre.lcon.id].n_leafs() {
                        *w *= pre.lcon.multiplier();
                    } else {
                        *w *= pre.rcon.multiplier();
                    }
                }

                // Mark "if" semantics as encoded
                unreachable_none!(self[id].mut_general().lits.get_mut(&val))
                    .add_semantics(Semantics::If);

                Ok(Some(pre.olit))
            }
            Node::Dummy => Ok(None),
        }
    }

    /// First step of [`Self::define_unweighted`]: checks preconditions and potentially returns
    fn precond_unweighted(
        &mut self,
        id: NodeId,
        idx: usize,
        req_semantics: Semantics,
    ) -> PrecondOutcome {
        let node = &self[id];
        debug_assert!(idx < node.max_val());
        if node.is_leaf() {
            debug_assert_eq!(idx, 0);
            return PrecondOutcome::Return(node[1]);
        }
        let lcon = unreachable_none!(node.left());
        let rcon = unreachable_none!(node.right());
        debug_assert!(matches!(
            self[lcon.id],
            Node::Leaf(_) | Node::Unit(_) | Node::Dummy
        ));
        debug_assert!(matches!(
            self[rcon.id],
            Node::Leaf(_) | Node::Unit(_) | Node::Dummy
        ));
        debug_assert_eq!(lcon.multiplier(), 1);
        debug_assert_eq!(rcon.multiplier(), 1);
        let node = node.unit();

        // Check if already encoded
        let mut new_semantics = req_semantics;
        if let LitData::Lit {
            lit,
            semantics: Some(semantics),
        } = node.lits[idx]
        {
            new_semantics = if let Some(sem) = semantics.missing(req_semantics) {
                sem
            } else {
                return PrecondOutcome::Return(lit);
            }
        }

        // treat dummy nodes by passing through other connection
        if matches!(self[lcon.id], Node::Dummy) || matches!(self[rcon.id], Node::Dummy) {
            let realcon = if matches!(self[lcon.id], Node::Dummy) {
                rcon
            } else {
                lcon
            };
            debug_assert!(matches!(self[realcon.id], Node::Leaf(_) | Node::Unit(_)));
            return PrecondOutcome::Passthrough(realcon);
        }

        // The maximum values contributed from each child
        let (left_if, right_if) = if new_semantics.has_if() {
            let left_if_max = cmp::min(self.con_len(lcon), idx + 1);
            let right_if_max = cmp::min(self.con_len(rcon), idx + 1);
            (
                idx + 1 - right_if_max..=left_if_max,
                idx + 1 - left_if_max..=right_if_max,
            )
        } else {
            #[allow(clippy::reversed_empty_ranges)]
            (1..=0, 1..=0)
        };

        let (left_only_if, right_only_if) = if new_semantics.has_only_if() {
            let left_oif_max = cmp::min(self.con_len(lcon), idx);
            let right_oif_max = cmp::min(self.con_len(rcon), idx);
            (
                idx - right_oif_max..=left_oif_max,
                idx - left_oif_max..=right_oif_max,
            )
        } else {
            #[allow(clippy::reversed_empty_ranges)]
            (1..=0, 1..=0)
        };

        PrecondOutcome::Continue(UnweightedPrecondResult {
            lcon,
            rcon,
            left_if,
            right_if,
            left_only_if,
            right_only_if,
        })
    }

    /// Recursion for unweighted totalizer encoding
    fn recurse_unweighted<Col>(
        &mut self,
        pre: &UnweightedPrecondResult,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
    {
        for lval in pre.left_if.clone() {
            if lval == 0 {
                continue;
            }
            self.define_unweighted(
                pre.lcon.id,
                con_idx(lval - 1, pre.lcon),
                Semantics::If,
                collector,
                var_manager,
            )?;
        }
        for rval in pre.right_if.clone() {
            if rval == 0 {
                continue;
            }
            self.define_unweighted(
                pre.rcon.id,
                con_idx(rval - 1, pre.rcon),
                Semantics::If,
                collector,
                var_manager,
            )?;
        }
        for lval in pre.left_only_if.clone() {
            if lval == self.con_len(pre.lcon) {
                continue;
            }
            self.define_unweighted(
                pre.lcon.id,
                con_idx(lval, pre.lcon),
                Semantics::OnlyIf,
                collector,
                var_manager,
            )?;
        }
        for rval in pre.right_only_if.clone() {
            if rval == self.con_len(pre.rcon) {
                continue;
            }
            self.define_unweighted(
                pre.rcon.id,
                con_idx(rval, pre.rcon),
                Semantics::OnlyIf,
                collector,
                var_manager,
            )?;
        }
        Ok(())
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

    #[cfg(feature = "proof-logging")]
    fn get_semantics<W>(
        &mut self,
        id: NodeId,
        val: usize,
        typ: SemDefTyp,
        leafs: impl Iterator<Item = (Lit, usize)>,
        proof: &mut pidgeons::Proof<W>,
    ) -> std::io::Result<SemDefinition>
    where
        W: std::io::Write,
    {
        use crate::types::constraints::PbConstraint;

        debug_assert!(val <= self[id].len() + 1);
        if let Some(def) = self.semantic_defs.get(&(id, val, typ)) {
            return Ok((*def).into());
        }
        if self[id].is_leaf() {
            if val == 0 {
                let olit = *self[id].lit(1).unwrap();
                return Ok(olit.into());
            }
            return Ok(SemDefinition::None);
        }
        let def = if val == 0 {
            match typ {
                SemDefTyp::If => panic!("If semantic with `val=0` is undefined"),
                SemDefTyp::OnlyIf => {
                    let sem = PbConstraint::new_lb(
                        leafs.map(|(l, w)| {
                            (
                                l,
                                isize::try_from(w)
                                    .expect("cannot handle weights larger than `isize::MAX`"),
                            )
                        }),
                        isize::try_from(val)
                            .expect("cannot handle values larger than `isize::MAX`"),
                    );
                    proof.redundant(&sem, &[])?
                }
            }
        } else if val > self[id].len() {
            match typ {
                SemDefTyp::If => proof.redundant(
                    &PbConstraint::new_lb(
                        leafs.map(|(l, w)| {
                            (
                                !l,
                                isize::try_from(w)
                                    .expect("cannot handle values larger than `isize::MAX`"),
                            )
                        }),
                        0,
                    ),
                    &[],
                )?,
                SemDefTyp::OnlyIf => {
                    panic!("Only if semantic with `val=|X|+1` is undefined")
                }
            }
        } else {
            let olit = *self[id].lit(val).unwrap();
            let sem = PbConstraint::new_lb(
                leafs.map(|(l, w)| {
                    (
                        l,
                        isize::try_from(w).expect("cannot handle weights larger than `isize::MAX`"),
                    )
                }),
                isize::try_from(val).expect("cannot handle values larger than `isize::MAX`"),
            );
            match typ {
                SemDefTyp::If => proof.redundant(
                    &atomics::pb_impl_lit(&sem, olit),
                    &[<crate::types::Var as pidgeons::VarLike>::substitute_fixed(
                        &olit.var(),
                        true,
                    )],
                )?,
                SemDefTyp::OnlyIf => proof.redundant(
                    &atomics::lit_impl_pb(olit, &sem),
                    &[<crate::types::Var as pidgeons::VarLike>::substitute_fixed(
                        &olit.var(),
                        false,
                    )],
                )?,
            }
        };
        self.semantic_defs.insert((id, val, typ), def);
        Ok(def.into())
    }

    /// Last step of [`Self::define_unweighted`]
    ///
    /// # Panics
    ///
    /// If the semantics are already encoded.
    fn encode_unweighted<Col>(
        &mut self,
        id: NodeId,
        idx: usize,
        olit: Lit,
        req_semantics: Semantics,
        pre: &UnweightedPrecondResult,
        collector: &mut Col,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
    {
        // Store what part of the encoding we need to build
        let new_semantics = self[id].unit().lits[idx]
            .missing_semantics(req_semantics)
            .expect("semantics are already encoded");

        // Mark positive literal as encoded (done first to avoid borrow checker problems)
        self[id].mut_unit().lits[idx].add_semantics(req_semantics);

        // Get lit slices of children
        let l_tmp_olit;
        let llits = get_lit_slice!(self, pre.lcon.id, l_tmp_olit);
        let r_tmp_olit;
        let rlits = get_lit_slice!(self, pre.rcon.id, r_tmp_olit);

        // Encode
        // If semantics
        let if_clause = |lval: usize| {
            let rval = idx + 1 - lval;
            debug_assert!(pre.right_if.contains(&rval));
            debug_assert!(new_semantics.has_if());
            let mut lhs = [lit![0], lit![0]]; // avoids allocation
            let mut nlits = 0;
            if lval > 0 {
                lhs[nlits] = *unreachable_none!(llits[con_idx(lval - 1, pre.lcon)].lit());
                nlits += 1;
            }
            if rval > 0 {
                lhs[nlits] = *unreachable_none!(rlits[con_idx(rval - 1, pre.rcon)].lit());
                nlits += 1;
            }
            atomics::cube_impl_lit(&lhs[..nlits], olit)
        };
        collector.extend_clauses(pre.left_if.clone().map(if_clause))?;
        // Only if semantics
        let only_if_clause = |lval: usize| {
            let rval = idx - lval;
            debug_assert!(pre.right_only_if.contains(&rval));
            debug_assert!(new_semantics.has_only_if());
            let mut lhs = [lit![0], lit![0]]; // avoids allocation
            let mut nlits = 0;
            if lval < self.con_len(pre.lcon) {
                lhs[nlits] = !*unreachable_none!(llits[con_idx(lval, pre.lcon)].lit());
                nlits += 1;
            }
            if rval < self.con_len(pre.rcon) {
                lhs[nlits] = !*unreachable_none!(rlits[con_idx(rval, pre.rcon)].lit());
                nlits += 1;
            }
            atomics::cube_impl_lit(&lhs[..nlits], !olit)
        };
        collector.extend_clauses(pre.left_only_if.clone().map(only_if_clause))?;

        Ok(())
    }

    /// Defines an output literal, assuming that the structure is a non-weighted totalizer
    ///
    /// The `idx` parameter is the output index, i.e., not the value represented by the output, but
    /// `value - 1`.
    ///
    /// # Errors
    ///
    /// If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
    pub fn define_unweighted<Col>(
        &mut self,
        id: NodeId,
        idx: usize,
        semantics: Semantics,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<Lit, crate::OutOfMemory>
    where
        Col: CollectClauses,
    {
        let pre = match self.precond_unweighted(id, idx, semantics) {
            PrecondOutcome::Return(lit) => return Ok(lit),
            PrecondOutcome::Passthrough(con) => {
                let ilit = self.define_unweighted(
                    con.id,
                    con_idx(idx, con),
                    semantics,
                    collector,
                    var_manager,
                )?;
                let olit = self.get_olit(id, idx, var_manager);
                collector.add_clause(atomics::lit_impl_lit(ilit, olit))?;
                // Mark positive literal as encoded
                self[id].mut_unit().lits[idx].add_semantics(semantics);
                return Ok(olit);
            }
            PrecondOutcome::Continue(pre) => pre,
        };

        // Encode children (recurse)
        self.recurse_unweighted(&pre, collector, var_manager)?;

        // Reserve variable for this node, if needed
        let olit = self.get_olit(id, idx, var_manager);

        // Encode this node
        self.encode_unweighted(id, idx, olit, semantics, &pre, collector)?;

        Ok(olit)
    }

    #[cfg(feature = "proof-logging")]
    /// Recursion for unweighted totalizer encoding with certificate
    fn recurse_unweighted_cert<Col, W>(
        &mut self,
        pre: &UnweightedPrecondResult,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pidgeons::Proof<W>,
        leafs: &mut [Lit],
    ) -> anyhow::Result<()>
    where
        Col: crate::encodings::CollectCertClauses,
        W: std::io::Write,
    {
        let (left_leafs, right_leafs) = leafs.split_at_mut(self[pre.lcon.id].n_leafs());
        for lval in pre.left_if.clone() {
            if lval == 0 {
                continue;
            }
            self.define_unweighted_cert(
                pre.lcon.id,
                con_idx(lval - 1, pre.lcon),
                Semantics::If,
                collector,
                var_manager,
                proof,
                left_leafs,
            )?;
        }
        for rval in pre.right_if.clone() {
            if rval == 0 {
                continue;
            }
            self.define_unweighted_cert(
                pre.rcon.id,
                con_idx(rval - 1, pre.rcon),
                Semantics::If,
                collector,
                var_manager,
                proof,
                right_leafs,
            )?;
        }
        for lval in pre.left_only_if.clone() {
            if lval == self.con_len(pre.lcon) {
                continue;
            }
            self.define_unweighted_cert(
                pre.lcon.id,
                con_idx(lval, pre.lcon),
                Semantics::OnlyIf,
                collector,
                var_manager,
                proof,
                left_leafs,
            )?;
        }
        for rval in pre.right_only_if.clone() {
            if rval == self.con_len(pre.rcon) {
                continue;
            }
            self.define_unweighted_cert(
                pre.rcon.id,
                con_idx(rval, pre.rcon),
                Semantics::OnlyIf,
                collector,
                var_manager,
                proof,
                right_leafs,
            )?;
        }
        Ok(())
    }

    /// Last step of [`Self::define_unweighted_cert`]
    ///
    /// # Panics
    ///
    /// If the semantics are already encoded.
    #[cfg(feature = "proof-logging")]
    #[allow(clippy::too_many_arguments)]
    fn encode_unweighted_cert<W, Col>(
        &mut self,
        id: NodeId,
        idx: usize,
        olit: Lit,
        req_semantics: Semantics,
        pre: &UnweightedPrecondResult,
        collector: &mut Col,
        proof: &mut pidgeons::Proof<W>,
        leafs: &mut [Lit],
    ) -> anyhow::Result<()>
    where
        Col: crate::encodings::CollectCertClauses,
        W: std::io::Write,
    {
        use pidgeons::OperationLike;

        // Store what part of the encoding we need to build
        let new_semantics = self[id].unit().lits[idx]
            .missing_semantics(req_semantics)
            .expect("semantics are already encoded");

        // Mark positive literal as encoded (done first to avoid borrow checker problems)
        self[id].mut_unit().lits[idx].add_semantics(req_semantics);

        let (left_leafs, right_leafs) = leafs.split_at(self[pre.lcon.id].n_leafs());

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
            let left_def = self.get_semantics(
                pre.lcon.id,
                pre.lcon.rev_map(lval),
                SemDefTyp::OnlyIf,
                left_leafs.iter().map(|l| (*l, 1)),
                proof,
            )?;
            let right_def = self.get_semantics(
                pre.rcon.id,
                pre.rcon.rev_map(rval),
                SemDefTyp::OnlyIf,
                right_leafs.iter().map(|l| (*l, 1)),
                proof,
            )?;
            let this_def = self.get_semantics(
                id,
                idx + 1,
                SemDefTyp::If,
                leafs.iter().map(|l| (*l, 1)),
                proof,
            )?;
            let id = proof.operations(&(this_def + left_def + right_def).saturate())?;
            collector.add_cert_clause(atomics::cube_impl_lit(&lhs[..nlits], olit), id)?;
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
            let left_def = self.get_semantics(
                pre.lcon.id,
                pre.lcon.rev_map(lval + 1),
                SemDefTyp::If,
                left_leafs.iter().map(|l| (*l, 1)),
                proof,
            )?;
            let right_def = self.get_semantics(
                pre.rcon.id,
                pre.rcon.rev_map(rval + 1),
                SemDefTyp::If,
                right_leafs.iter().map(|l| (*l, 1)),
                proof,
            )?;
            let this_def = self.get_semantics(
                id,
                idx + 1,
                SemDefTyp::OnlyIf,
                leafs.iter().map(|l| (*l, 1)),
                proof,
            )?;
            let id = proof.operations(&(this_def + left_def + right_def).saturate())?;
            collector.add_cert_clause(atomics::cube_impl_lit(&lhs[..nlits], !olit), id)?;
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
    #[cfg(feature = "proof-logging")]
    #[allow(clippy::too_many_arguments)]
    pub fn define_unweighted_cert<Col, W>(
        &mut self,
        id: NodeId,
        idx: usize,
        semantics: Semantics,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pidgeons::Proof<W>,
        leafs: &mut [Lit],
    ) -> anyhow::Result<Lit>
    where
        Col: crate::encodings::CollectCertClauses,
        W: std::io::Write,
    {
        debug_assert_eq!(leafs.len(), self[id].len());

        let pre = match self.precond_unweighted(id, idx, semantics) {
            PrecondOutcome::Return(lit) => {
                let mut new_leafs: Vec<_> = self.leaf_iter(id).map(|(l, _)| l).collect();
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
        self.recurse_unweighted_cert(&pre, collector, var_manager, proof, leafs)?;

        // Reserve variable for this node, if needed
        let olit = self.get_olit(id, idx, var_manager);

        // Encode this node
        self.encode_unweighted_cert(id, idx, olit, semantics, &pre, collector, proof, leafs)?;

        Ok(olit)
    }

    /// Recursively reserves all variables in the subtree rooted at the given node
    pub fn reserve_vars(&mut self, id: NodeId, var_manager: &mut dyn ManageVars) {
        if matches!(self[id], Node::Leaf(_) | Node::Dummy) {
            return;
        }

        // Recurse
        self.reserve_vars(unreachable_none!(self[id].left()).id, var_manager);
        self.reserve_vars(unreachable_none!(self[id].right()).id, var_manager);

        match &mut self[id] {
            Node::Unit(UnitNode { lits, .. }) => {
                for olit in lits {
                    if let LitData::None = olit {
                        *olit = LitData::new_lit(var_manager.new_var().pos_lit());
                    }
                }
            }
            Node::General(GeneralNode { lits, .. }) => {
                for (_, olit) in lits.iter_mut() {
                    if let LitData::None = olit {
                        *olit = LitData::new_lit(var_manager.new_var().pos_lit());
                    }
                }
            }
            Node::Leaf(_) | Node::Dummy => unreachable!(),
        }
    }

    /// Resets the status of what has already been encoded
    pub fn reset_encoded(&mut self, reset_semantics: Semantics) {
        for node in &mut self.nodes {
            match node {
                Node::Unit(UnitNode { lits, .. }) => {
                    for lit in lits {
                        lit.remove_semantics(reset_semantics);
                    }
                }
                Node::General(GeneralNode { lits, .. }) => {
                    for lit in lits.values_mut() {
                        lit.remove_semantics(reset_semantics);
                    }
                }
                Node::Leaf(_) | Node::Dummy => (),
            }
        }
    }

    /// Resets the reserved variables in the database. This also resets the
    /// status of what has already been encoded.
    #[cfg(feature = "internals")]
    pub fn reset_vars(&mut self) {
        for node in &mut self.nodes {
            match node {
                Node::Leaf(_) | Node::Dummy => (),
                Node::Unit(UnitNode { lits, .. }) => {
                    for lit in lits {
                        *lit = LitData::None;
                    }
                }
                Node::General(GeneralNode { lits, .. }) => {
                    for lit in lits.values_mut() {
                        *lit = LitData::None;
                    }
                }
            }
        }
    }
}

/// Defines the semantics with which a totalizer output can be encoded
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Semantics {
    /// `(input lits >= bound) -> olit`
    If,
    /// `olit -> (input lits >= bound)`
    OnlyIf,
    /// `olit <-> (input lits >= bound)`
    IfAndOnlyIf,
}

impl Semantics {
    /// Checks if the if semantics are included
    #[inline]
    #[must_use]
    pub fn has_if(self) -> bool {
        matches!(self, Semantics::If | Semantics::IfAndOnlyIf)
    }

    /// Checks if the if semantics are included
    #[inline]
    #[must_use]
    pub fn has_only_if(self) -> bool {
        matches!(self, Semantics::OnlyIf | Semantics::IfAndOnlyIf)
    }

    /// Checks whether the given semantics already satisfy required semantics
    #[inline]
    #[must_use]
    pub fn satisfies(self, required: Semantics) -> bool {
        match required {
            Semantics::If => self.has_if(),
            Semantics::OnlyIf => self.has_only_if(),
            Semantics::IfAndOnlyIf => matches!(self, Semantics::IfAndOnlyIf),
        }
    }

    /// Updates the given semantics with additional semantics
    #[inline]
    pub fn add(&mut self, new: Semantics) {
        if matches!(
            (*self, new),
            (Semantics::If, Semantics::OnlyIf)
                | (Semantics::OnlyIf, Semantics::If)
                | (_, Semantics::IfAndOnlyIf)
        ) {
            *self = Semantics::IfAndOnlyIf;
        }
    }

    /// Updates the given semantics by removing semantics
    #[inline]
    #[must_use]
    pub fn remove(self, remove: Semantics) -> Option<Semantics> {
        match (self, remove) {
            (Semantics::IfAndOnlyIf | Semantics::OnlyIf, Semantics::If) => Some(Semantics::OnlyIf),
            (Semantics::IfAndOnlyIf | Semantics::If, Semantics::OnlyIf) => Some(Semantics::If),
            _ => None,
        }
    }

    /// Gets the missing semantics between this and required semantics
    #[inline]
    #[must_use]
    pub fn missing(self, required: Semantics) -> Option<Semantics> {
        match (self, required) {
            (Semantics::If, Semantics::IfAndOnlyIf | Semantics::OnlyIf) => Some(Semantics::OnlyIf),
            (Semantics::OnlyIf, Semantics::IfAndOnlyIf | Semantics::If) => Some(Semantics::If),
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
enum PrecondOutcome {
    Return(Lit),
    Continue(UnweightedPrecondResult),
    Passthrough(NodeCon),
}

#[derive(Clone, Debug)]
struct UnweightedPrecondResult {
    lcon: NodeCon,
    rcon: NodeCon,
    left_if: ops::RangeInclusive<usize>,
    right_if: ops::RangeInclusive<usize>,
    left_only_if: ops::RangeInclusive<usize>,
    right_only_if: ops::RangeInclusive<usize>,
}

#[derive(Copy, Clone, Debug)]
struct WeightedPrecondResult {
    lcon: NodeCon,
    rcon: NodeCon,
    olit: Lit,
}

#[cfg(feature = "proof-logging")]
#[derive(Hash, Clone, Copy, PartialEq, Eq, Debug)]
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
                SemDefinition::None => pidgeons::OperationSequence::empty(),
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
impl ops::Add<pidgeons::OperationSequence> for SemDefinition {
    type Output = pidgeons::OperationSequence;

    fn add(self, rhs: pidgeons::OperationSequence) -> Self::Output {
        match self {
            SemDefinition::None => rhs,
            SemDefinition::Id(id) => id + rhs,
            SemDefinition::Axiom(ax) => pidgeons::Axiom::from(ax) + rhs,
        }
    }
}

#[cfg(feature = "proof-logging")]
impl ops::Mul<usize> for SemDefinition {
    type Output = pidgeons::OperationSequence;

    fn mul(self, rhs: usize) -> Self::Output {
        match self {
            SemDefinition::None => pidgeons::OperationSequence::empty(),
            SemDefinition::Id(id) => id * rhs,
            SemDefinition::Axiom(ax) => pidgeons::Axiom::from(ax) * rhs,
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
pub enum Node {
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
        matches!(self, Node::Leaf(_))
    }

    fn max_val(&self) -> usize {
        match &self {
            Node::Leaf(_) => 1,
            Node::Unit(node) => node.lits.len(),
            Node::General(node) => node.max_val,
            Node::Dummy => 0,
        }
    }

    fn len(&self) -> usize {
        match &self {
            Node::Leaf(_) => 1,
            Node::Unit(node) => node.lits.len(),
            Node::General(node) => node.lits.len(),
            Node::Dummy => 0,
        }
    }

    fn vals<R>(&self, range: R) -> Self::ValIter
    where
        R: ops::RangeBounds<usize>,
    {
        match &self {
            Node::Leaf(_) => {
                if range.contains(&1) {
                    return (1..2).chain(vec![]);
                }
                (0..0).chain(vec![])
            }
            Node::Unit(node) => {
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
            Node::General(node) => {
                let vals: Vec<_> = node.lits.range(range).map(|(val, _)| *val).collect();
                (0..0).chain(vals)
            }
            Node::Dummy => (0..0).chain(vec![]),
        }
    }

    fn right(&self) -> Option<NodeCon> {
        match &self {
            Node::Leaf(..) | Node::Dummy => None,
            Node::Unit(node) => Some(node.right),
            Node::General(node) => Some(node.right),
        }
    }

    fn left(&self) -> Option<NodeCon> {
        match &self {
            Node::Leaf(..) | Node::Dummy => None,
            Node::Unit(node) => Some(node.left),
            Node::General(node) => Some(node.left),
        }
    }

    fn depth(&self) -> usize {
        match &self {
            Node::Leaf(..) | Node::Dummy => 1,
            Node::Unit(UnitNode { depth, .. }) | Node::General(GeneralNode { depth, .. }) => *depth,
        }
    }

    fn n_leafs(&self) -> usize {
        match &self {
            Node::Leaf(..) => 1,
            Node::Dummy => 0,
            Node::Unit(UnitNode { n_leafs, .. }) | Node::General(GeneralNode { n_leafs, .. }) => {
                *n_leafs
            }
        }
    }

    fn internal<Db>(left: NodeCon, right: NodeCon, db: &Db) -> Self
    where
        Db: NodeById<Node = Self>,
    {
        let general = left.multiplier != right.multiplier
            || matches!(&db[left.id], Node::General(_))
            || matches!(&db[right.id], Node::General(_));
        if general {
            let lvals: Vec<_> = db[left.id]
                .vals(left.offset()..)
                .map(|val| left.map(val))
                .collect();
            let rvals: Vec<_> = db[right.id]
                .vals(right.offset()..)
                .map(|val| right.map(val))
                .collect();
            return Node::General(GeneralNode::new(
                &lvals,
                &rvals,
                std::cmp::max(db[left.id].depth(), db[right.id].depth()) + 1,
                db[left.id].n_leafs() + db[right.id].n_leafs(),
                left,
                right,
            ));
        }
        // if both inputs have the same weight, the multiplier should be 1
        debug_assert!(left.multiplier() == 1 && right.multiplier() == 1);
        Node::Unit(UnitNode::new(
            db.con_len(left) + db.con_len(right),
            std::cmp::max(db[left.id].depth(), db[right.id].depth()) + 1,
            db[left.id].n_leafs() + db[right.id].n_leafs(),
            left,
            right,
        ))
    }

    fn leaf(lit: Lit) -> Self {
        Node::Leaf(lit)
    }
}

impl Node {
    /// Panic-safe version of literal indexing
    #[must_use]
    pub fn lit(&self, val: usize) -> Option<&Lit> {
        match &self {
            Node::Leaf(lit, ..) => {
                if val != 1 {
                    return None;
                }
                Some(lit)
            }
            Node::Unit(node) => node.lit(val),
            Node::General(node) => node.lit(val),
            Node::Dummy => None,
        }
    }

    /// Checks if a given output value has "if" semantics encoded
    #[cfg(feature = "internals")]
    #[must_use]
    pub fn semantics_if(&self, val: usize) -> bool {
        match &self {
            Node::Leaf(..) => {
                if val != 1 {
                    return false;
                }
                true
            }
            Node::Unit(node) => node.semantics_if(val),
            Node::General(node) => node.semantics_if(val),
            Node::Dummy => true,
        }
    }

    /// Checks if a given output value has "if" semantics encoded
    #[cfg(feature = "internals")]
    #[must_use]
    pub fn semantics_only_if(&self, val: usize) -> bool {
        match &self {
            Node::Leaf(..) => {
                if val != 1 {
                    return false;
                }
                true
            }
            Node::Unit(node) => node.semantics_only_if(val),
            Node::General(node) => node.semantics_only_if(val),
            Node::Dummy => true,
        }
    }

    /// Returns the internal node and panics if the node is not a unit
    pub(crate) fn unit(&self) -> &UnitNode {
        match self {
            Node::Unit(node) => node,
            _ => panic!("called `unit` on non-unit node"),
        }
    }

    /// Returns the internal node and panics if the node is not a unit
    pub(crate) fn mut_unit(&mut self) -> &mut UnitNode {
        match self {
            Node::Unit(node) => node,
            _ => panic!("called `unit` on non-unit node"),
        }
    }

    /// Returns the internal node and panics if the node is not general
    pub(crate) fn mut_general(&mut self) -> &mut GeneralNode {
        match self {
            Node::General(node) => node,
            _ => panic!("called `unit` on non-general node"),
        }
    }

    /// Adjusts the connections of the node to draining a range of nodes. If the
    /// nodes references a nodes within the drained range, it returns that
    /// [`NodeId`] as an Error.
    #[allow(dead_code)]
    fn drain(&mut self, range: ops::Range<NodeId>) -> Result<(), NodeId> {
        match self {
            Node::Leaf(_) | Node::Dummy => Ok(()),
            Node::Unit(UnitNode { left, right, .. })
            | Node::General(GeneralNode { left, right, .. }) => {
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
    pub(crate) n_leafs: usize,
    pub(crate) left: NodeCon,
    pub(crate) right: NodeCon,
}

impl UnitNode {
    fn new(len: usize, depth: usize, n_leafs: usize, left: NodeCon, right: NodeCon) -> Self {
        // Length of node can never change
        let mut lits = vec![];
        lits.reserve_exact(len);
        (0..len).for_each(|_| lits.push(LitData::default()));
        Self {
            lits,
            depth,
            n_leafs,
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

    /// Checks if a given value has "if" semantics encoded
    #[cfg(feature = "internals")]
    #[inline]
    #[must_use]
    pub fn semantics_if(&self, val: usize) -> bool {
        self.lits[val - 1].semantics_if()
    }

    /// Checks if a given value has "only if" semantics encoded
    #[cfg(feature = "internals")]
    #[inline]
    #[must_use]
    pub fn semantics_only_if(&self, val: usize) -> bool {
        self.lits[val - 1].semantics_only_if()
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
    pub(crate) n_leafs: usize,
    pub(crate) max_val: usize,
    pub(crate) left: NodeCon,
    pub(crate) right: NodeCon,
}

impl GeneralNode {
    fn new(
        lvals: &[usize],
        rvals: &[usize],
        depth: usize,
        n_leafs: usize,
        left: NodeCon,
        right: NodeCon,
    ) -> Self {
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
            n_leafs,
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

    /// Checks if a given value has the "if" semantics encoded
    #[cfg(feature = "internals")]
    #[inline]
    #[must_use]
    pub fn semantics_if(&self, val: usize) -> bool {
        self.lits
            .get(&val)
            .copied()
            .map_or(false, LitData::semantics_if)
    }

    /// Checks if a given value has the "only if" semantics encoded
    #[cfg(feature = "internals")]
    #[inline]
    #[must_use]
    pub fn semantics_only_if(&self, val: usize) -> bool {
        self.lits
            .get(&val)
            .copied()
            .map_or(false, LitData::semantics_only_if)
    }
}

/// Data associated with an output literal in a [`Node`]
#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LitData {
    #[default]
    None,
    Lit {
        lit: Lit,
        semantics: Option<Semantics>,
    },
}

impl LitData {
    fn new_lit(lit: Lit) -> Self {
        LitData::Lit {
            lit,
            semantics: None,
        }
    }

    #[inline]
    fn lit(&self) -> Option<&Lit> {
        match self {
            LitData::None => None,
            LitData::Lit { lit, .. } => Some(lit),
        }
    }

    #[cfg(feature = "internals")]
    #[inline]
    #[must_use]
    fn semantics_if(self) -> bool {
        match self {
            LitData::None => false,
            LitData::Lit { semantics, .. } => semantics.map_or(false, Semantics::has_if),
        }
    }

    #[cfg(feature = "internals")]
    #[inline]
    #[must_use]
    fn semantics_only_if(self) -> bool {
        match self {
            LitData::None => false,
            LitData::Lit { semantics, .. } => semantics.map_or(false, Semantics::has_only_if),
        }
    }

    #[inline]
    fn add_semantics(&mut self, new_semantics: Semantics) {
        match self {
            LitData::None => panic!(),
            LitData::Lit {
                semantics: Some(sem),
                ..
            } => sem.add(new_semantics),
            LitData::Lit { semantics, .. } => *semantics = Some(new_semantics),
        }
    }

    #[inline]
    fn remove_semantics(&mut self, remove_semantics: Semantics) {
        match self {
            LitData::None => (),
            LitData::Lit { semantics, .. } => {
                if let Some(sem) = semantics {
                    *semantics = sem.remove(remove_semantics);
                }
            }
        }
    }

    #[inline]
    #[must_use]
    fn missing_semantics(self, required: Semantics) -> Option<Semantics> {
        match self {
            LitData::Lit {
                semantics: Some(semantics),
                ..
            } => semantics.missing(required),
            _ => Some(required),
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

    use super::{Db, Semantics};

    #[test]
    fn tot_db_if() {
        let mut db = Db::default();
        let root = db.lit_tree(&[lit![0], lit![1], lit![2], lit![3]]);
        debug_assert_eq!(db[root].depth(), 3);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);

        let mut cnf = Cnf::new();
        db.define_unweighted(root, 0, Semantics::If, &mut cnf, &mut var_manager)
            .unwrap();
        debug_assert_eq!(cnf.len(), 6);

        db.reset_encoded(Semantics::IfAndOnlyIf);
        let mut cnf = Cnf::new();
        db.define_unweighted(root, 1, Semantics::If, &mut cnf, &mut var_manager)
            .unwrap();
        debug_assert_eq!(cnf.len(), 9);

        db.reset_encoded(Semantics::IfAndOnlyIf);
        let mut cnf = Cnf::new();
        db.define_unweighted(root, 2, Semantics::If, &mut cnf, &mut var_manager)
            .unwrap();
        debug_assert_eq!(cnf.len(), 8);

        db.reset_encoded(Semantics::IfAndOnlyIf);
        let mut cnf = Cnf::new();
        db.define_unweighted(root, 3, Semantics::If, &mut cnf, &mut var_manager)
            .unwrap();
        debug_assert_eq!(cnf.len(), 3);
    }

    #[test]
    fn tot_db_only_if() {
        let mut db = Db::default();
        let root = db.lit_tree(&[lit![0], lit![1], lit![2], lit![3]]);
        debug_assert_eq!(db[root].depth(), 3);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);

        let mut cnf = Cnf::new();
        db.define_unweighted(root, 0, Semantics::OnlyIf, &mut cnf, &mut var_manager)
            .unwrap();
        debug_assert_eq!(cnf.len(), 3);

        db.reset_encoded(Semantics::IfAndOnlyIf);
        let mut cnf = Cnf::new();
        db.define_unweighted(root, 1, Semantics::OnlyIf, &mut cnf, &mut var_manager)
            .unwrap();
        debug_assert_eq!(cnf.len(), 8);

        db.reset_encoded(Semantics::IfAndOnlyIf);
        let mut cnf = Cnf::new();
        db.define_unweighted(root, 2, Semantics::OnlyIf, &mut cnf, &mut var_manager)
            .unwrap();
        debug_assert_eq!(cnf.len(), 9);

        db.reset_encoded(Semantics::IfAndOnlyIf);
        let mut cnf = Cnf::new();
        db.define_unweighted(root, 3, Semantics::OnlyIf, &mut cnf, &mut var_manager)
            .unwrap();
        debug_assert_eq!(cnf.len(), 6);
    }

    #[test]
    fn tot_db_if_and_only_if() {
        let mut db = Db::default();
        let root = db.lit_tree(&[lit![0], lit![1], lit![2], lit![3]]);
        debug_assert_eq!(db[root].depth(), 3);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);

        let mut cnf = Cnf::new();
        db.define_unweighted(root, 0, Semantics::IfAndOnlyIf, &mut cnf, &mut var_manager)
            .unwrap();
        debug_assert_eq!(cnf.len(), 9);

        db.reset_encoded(Semantics::IfAndOnlyIf);
        let mut cnf = Cnf::new();
        db.define_unweighted(root, 1, Semantics::IfAndOnlyIf, &mut cnf, &mut var_manager)
            .unwrap();
        debug_assert_eq!(cnf.len(), 17);

        db.reset_encoded(Semantics::IfAndOnlyIf);
        let mut cnf = Cnf::new();
        db.define_unweighted(root, 2, Semantics::IfAndOnlyIf, &mut cnf, &mut var_manager)
            .unwrap();
        debug_assert_eq!(cnf.len(), 17);

        db.reset_encoded(Semantics::IfAndOnlyIf);
        let mut cnf = Cnf::new();
        db.define_unweighted(root, 3, Semantics::IfAndOnlyIf, &mut cnf, &mut var_manager)
            .unwrap();
        debug_assert_eq!(cnf.len(), 9);
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
        db.define_weighted(root, 1, &mut cnf, &mut var_manager)
            .unwrap();
        debug_assert_eq!(cnf.len(), 0);

        db.reset_encoded(Semantics::IfAndOnlyIf);
        let mut cnf = Cnf::new();
        db.define_weighted(root, 4, &mut cnf, &mut var_manager)
            .unwrap();
        debug_assert_eq!(cnf.len(), 3);

        db.reset_encoded(Semantics::IfAndOnlyIf);
        let mut cnf = Cnf::new();
        db.define_weighted(root, 7, &mut cnf, &mut var_manager)
            .unwrap();
        debug_assert_eq!(cnf.len(), 3);

        db.reset_encoded(Semantics::IfAndOnlyIf);
        let mut cnf = Cnf::new();
        db.define_weighted(root, 8, &mut cnf, &mut var_manager)
            .unwrap();
        debug_assert_eq!(cnf.len(), 2);

        db.reset_encoded(Semantics::IfAndOnlyIf);
        let mut cnf = Cnf::new();
        db.define_weighted(root, 15, &mut cnf, &mut var_manager)
            .unwrap();
        debug_assert_eq!(cnf.len(), 4);

        db.reset_encoded(Semantics::IfAndOnlyIf);
        let mut cnf = Cnf::new();
        db.define_weighted(root, 22, &mut cnf, &mut var_manager)
            .unwrap();
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
        db.define_weighted(root, 1, &mut cnf, &mut var_manager)
            .unwrap();
        debug_assert_eq!(cnf.len(), 2);

        db.reset_encoded(Semantics::IfAndOnlyIf);
        let mut cnf = Cnf::new();
        db.define_weighted(root, 2, &mut cnf, &mut var_manager)
            .unwrap();
        debug_assert_eq!(cnf.len(), 2);

        db.reset_encoded(Semantics::IfAndOnlyIf);
        let mut cnf = Cnf::new();
        db.define_weighted(root, 3, &mut cnf, &mut var_manager)
            .unwrap();
        debug_assert_eq!(cnf.len(), 3);

        db.reset_encoded(Semantics::IfAndOnlyIf);
        let mut cnf = Cnf::new();
        db.define_weighted(root, 4, &mut cnf, &mut var_manager)
            .unwrap();
        debug_assert_eq!(cnf.len(), 2);

        db.reset_encoded(Semantics::IfAndOnlyIf);
        let mut cnf = Cnf::new();
        db.define_weighted(root, 5, &mut cnf, &mut var_manager)
            .unwrap();
        debug_assert_eq!(cnf.len(), 2);

        db.reset_encoded(Semantics::IfAndOnlyIf);
        let mut cnf = Cnf::new();
        db.define_weighted(root, 6, &mut cnf, &mut var_manager)
            .unwrap();
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

        use super::{Db, Semantics};

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
            print_file(proof);
            if out.status.success() {
                return;
            }
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
        fn tot_db_if_cert() {
            let mut db = Db::default();
            let root = db.lit_tree(&[lit![0], lit![1], lit![2], lit![3]]);
            debug_assert_eq!(db[root].depth(), 3);
            let mut var_manager = BasicVarManager::default();
            var_manager.increase_next_free(var![4]);

            let mut proof = new_proof(0, false);

            let mut cnf = Cnf::new();
            let mut lits = [lit![0]; 4];
            db.define_unweighted_cert(
                root,
                0,
                Semantics::If,
                &mut cnf,
                &mut var_manager,
                &mut proof,
                &mut lits,
            )
            .unwrap();
            db.define_unweighted_cert(
                root,
                1,
                Semantics::If,
                &mut cnf,
                &mut var_manager,
                &mut proof,
                &mut lits,
            )
            .unwrap();
            db.define_unweighted_cert(
                root,
                2,
                Semantics::If,
                &mut cnf,
                &mut var_manager,
                &mut proof,
                &mut lits,
            )
            .unwrap();
            db.define_unweighted_cert(
                root,
                3,
                Semantics::If,
                &mut cnf,
                &mut var_manager,
                &mut proof,
                &mut lits,
            )
            .unwrap();

            let proof_file = proof
                .conclude(pidgeons::OutputGuarantee::None, &pidgeons::Conclusion::None)
                .unwrap();
            let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
            verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path());
        }

        #[test]
        fn tot_db_only_if_cert() {
            let mut db = Db::default();
            let root = db.lit_tree(&[lit![0], lit![1], lit![2], lit![3]]);
            debug_assert_eq!(db[root].depth(), 3);
            let mut var_manager = BasicVarManager::default();
            var_manager.increase_next_free(var![4]);

            let mut proof = new_proof(0, false);

            let mut cnf = Cnf::new();
            let mut lits = [lit![0]; 4];
            db.define_unweighted_cert(
                root,
                0,
                Semantics::OnlyIf,
                &mut cnf,
                &mut var_manager,
                &mut proof,
                &mut lits,
            )
            .unwrap();
            db.define_unweighted_cert(
                root,
                1,
                Semantics::OnlyIf,
                &mut cnf,
                &mut var_manager,
                &mut proof,
                &mut lits,
            )
            .unwrap();
            db.define_unweighted_cert(
                root,
                2,
                Semantics::OnlyIf,
                &mut cnf,
                &mut var_manager,
                &mut proof,
                &mut lits,
            )
            .unwrap();
            db.define_unweighted_cert(
                root,
                3,
                Semantics::OnlyIf,
                &mut cnf,
                &mut var_manager,
                &mut proof,
                &mut lits,
            )
            .unwrap();

            let proof_file = proof
                .conclude(pidgeons::OutputGuarantee::None, &pidgeons::Conclusion::None)
                .unwrap();
            let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
            verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path());
        }

        #[test]
        fn gte_db_cert() {
            let mut db = Db::default();
            let root =
                db.weighted_lit_tree(&[(lit![0], 4), (lit![1], 3), (lit![2], 2), (lit![3], 1)]);
            assert_eq!(root.offset(), 0);
            assert_eq!(root.multiplier(), 1);
            let root = root.id;
            let mut var_manager = BasicVarManager::default();
            var_manager.increase_next_free(var![4]);

            let mut proof = new_proof(0, false);

            let mut cnf = Cnf::new();
            let mut lits = [(lit![0], 0); 4];
            db.define_weighted_cert(root, 1, &mut cnf, &mut var_manager, &mut proof, &mut lits)
                .unwrap();
            db.define_weighted_cert(root, 2, &mut cnf, &mut var_manager, &mut proof, &mut lits)
                .unwrap();
            db.define_weighted_cert(root, 3, &mut cnf, &mut var_manager, &mut proof, &mut lits)
                .unwrap();
            db.define_weighted_cert(root, 4, &mut cnf, &mut var_manager, &mut proof, &mut lits)
                .unwrap();
            db.define_weighted_cert(root, 5, &mut cnf, &mut var_manager, &mut proof, &mut lits)
                .unwrap();
            db.define_weighted_cert(root, 6, &mut cnf, &mut var_manager, &mut proof, &mut lits)
                .unwrap();
            db.define_weighted_cert(root, 7, &mut cnf, &mut var_manager, &mut proof, &mut lits)
                .unwrap();
            db.define_weighted_cert(root, 8, &mut cnf, &mut var_manager, &mut proof, &mut lits)
                .unwrap();
            db.define_weighted_cert(root, 9, &mut cnf, &mut var_manager, &mut proof, &mut lits)
                .unwrap();
            db.define_weighted_cert(root, 10, &mut cnf, &mut var_manager, &mut proof, &mut lits)
                .unwrap();

            let proof_file = proof
                .conclude(pidgeons::OutputGuarantee::None, &pidgeons::Conclusion::None)
                .unwrap();
            let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
            verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path());
        }
    }
}
