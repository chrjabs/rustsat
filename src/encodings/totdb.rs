//! # Totalizer Database

use std::{cmp, num::NonZeroUsize, ops};

use crate::{
    encodings::atomics,
    instances::ManageVars,
    lit,
    types::{Assignment, Lit, RsHashMap},
    utils::unreachable_none,
};

use super::{
    nodedb::{NodeById, NodeCon, NodeId, NodeLike},
    nodedbimpl::DrainError,
    CollectClauses,
};

#[cfg(feature = "proof-logging")]
#[path = "totdb/cert.rs"]
pub mod cert;

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

/// A totalizer database
#[derive(Default, Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Db {
    /// The node database of the totalizer
    nodes: Vec<Node>,
    /// Mapping literals to leaf nodes
    lookup_leaf: RsHashMap<Lit, NodeId>,
    /// Dummy Node ID
    dummy_id: Option<NodeId>,
    #[cfg(feature = "proof-logging")]
    semantic_defs: RsHashMap<cert::SemDefId, cert::SemDefs>,
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
                // Check if already encoded
                if let Some(lit_data) = node.lit_data(val) {
                    if let LitData::Lit {
                        lit,
                        semantics: Some(semantics),
                    } = lit_data
                    {
                        if semantics.has_if() {
                            return Ok(Some(lit));
                        }
                    }
                } else {
                    return Ok(None);
                }

                debug_assert!(node.lit_data(val).is_some());

                let lcon = node.left;
                let rcon = node.right;

                // Reserve variable for this node, if needed
                let olit = if let Some(&olit) = node.lit(val) {
                    olit
                } else {
                    let olit = var_manager.new_var().pos_lit();
                    *unreachable_none!(self[id].mut_general().lit_data_mut(val)) =
                        LitData::new_lit(olit);
                    olit
                };

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
                                self.define_weighted(rcon.id, rval_rev, collector, var_manager)?
                            {
                                debug_assert!(
                                    lcon.len_limit.is_none() || lcon.offset() + 1 == lval
                                );
                                let llit = unreachable_none!(self.define_weighted(
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

                // Propagate value
                if lcon.is_possible(val) && lcon.rev_map(val) <= self[lcon.id].max_val() {
                    if let Some(llit) =
                        self.define_weighted(lcon.id, lcon.rev_map(val), collector, var_manager)?
                    {
                        collector.add_clause(atomics::lit_impl_lit(llit, olit))?;
                    }
                }
                if rcon.is_possible(val) && rcon.rev_map(val) <= self[rcon.id].max_val() {
                    if let Some(rlit) =
                        self.define_weighted(rcon.id, rcon.rev_map(val), collector, var_manager)?
                    {
                        collector.add_clause(atomics::lit_impl_lit(rlit, olit))?;
                    }
                }

                // Mark "if" semantics as encoded
                unreachable_none!(self[id].mut_general().lit_data_mut(val))
                    .add_semantics(Semantics::If);

                Ok(Some(olit))
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
            let left_only_if_max = cmp::min(self.con_len(lcon), idx);
            let right_only_if_max = cmp::min(self.con_len(rcon), idx);
            (
                idx - right_only_if_max..=left_only_if_max,
                idx - left_only_if_max..=right_only_if_max,
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

    /// Recursively reserves all variables in the sub-tree rooted at the given node
    pub fn reserve_vars(&mut self, id: NodeId, var_manager: &mut dyn ManageVars) {
        if matches!(self[id], Node::Leaf(_) | Node::Dummy) {
            return;
        }

        // Recurse
        self.reserve_vars(unreachable_none!(self[id].left()).id, var_manager);
        self.reserve_vars(unreachable_none!(self[id].right()).id, var_manager);

        self[id].reserve_vars(.., var_manager);
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
                    for (_, lit) in lits.iter_mut() {
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
                    for (_, lit) in lits.iter_mut() {
                        *lit = LitData::None;
                    }
                }
            }
        }
    }

    /// Extends an assignment to the input literals to an assignment over the totalizer variables,
    /// following strict semantics, i.e., `sum >= k <-> olit`
    #[must_use]
    pub fn strictly_extend_assignment<'db>(
        &'db self,
        root: NodeId,
        assign: &'db Assignment,
    ) -> AssignIter<'db> {
        AssignIter::new(self, root, assign)
    }
}

/// Defines the semantics with which a totalizer output can be encoded
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
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

/// A totalizer adder node
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
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
                let bin_search = |val| {
                    node.lits
                        .binary_search_by_key(&val, |dat| dat.0)
                        .unwrap_or_else(|e| e)
                };
                let from = match range.start_bound() {
                    ops::Bound::Included(b) => bin_search(*b),
                    ops::Bound::Excluded(b) => bin_search(*b + 1),
                    ops::Bound::Unbounded => 0,
                };
                let till = match range.end_bound() {
                    ops::Bound::Included(b) => bin_search(*b + 1),
                    ops::Bound::Excluded(b) => bin_search(*b),
                    ops::Bound::Unbounded => node.lits.len(),
                };
                let vals: Vec<_> = node.lits[from..till].iter().map(|(val, _)| *val).collect();
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

    fn n_leaves(&self) -> usize {
        match &self {
            Node::Leaf(..) => 1,
            Node::Dummy => 0,
            Node::Unit(UnitNode { n_leaves, .. }) | Node::General(GeneralNode { n_leaves, .. }) => {
                *n_leaves
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
        let depth = std::cmp::max(db[left.id].depth(), db[right.id].depth()) + 1;
        let n_leaves = left.len_limit.map_or(
            if left.offset() == 0 {
                db[left.id].n_leaves()
            } else {
                db[left.id].vals(left.offset() + 1..).count()
            },
            NonZeroUsize::get,
        ) + right.len_limit.map_or(
            if right.offset() == 0 {
                db[right.id].n_leaves()
            } else {
                db[right.id].vals(right.offset() + 1..).count()
            },
            NonZeroUsize::get,
        );
        if general {
            let lvals: Vec<_> = if let Some(limit) = left.len_limit {
                db[left.id]
                    .vals(left.offset() + 1..)
                    .take(limit.into())
                    .map(|val| left.map(val))
                    .collect()
            } else {
                db[left.id]
                    .vals(left.offset() + 1..)
                    .map(|val| left.map(val))
                    .collect()
            };
            debug_assert!('assert: {
                for (idx, &val) in lvals.iter().enumerate().skip(1) {
                    if val <= lvals[idx - 1] {
                        break 'assert false;
                    }
                }
                true
            });
            let rvals: Vec<_> = if let Some(limit) = right.len_limit {
                db[right.id]
                    .vals(right.offset() + 1..)
                    .take(limit.into())
                    .map(|val| right.map(val))
                    .collect()
            } else {
                db[right.id]
                    .vals(right.offset() + 1..)
                    .map(|val| right.map(val))
                    .collect()
            };
            debug_assert!('assert: {
                for (idx, &val) in rvals.iter().enumerate().skip(1) {
                    if val <= rvals[idx - 1] {
                        break 'assert false;
                    }
                }
                true
            });
            return Node::General(GeneralNode::new(
                &lvals, &rvals, depth, n_leaves, left, right,
            ));
        }
        // if both inputs have the same weight, the multiplier should be 1
        debug_assert!(left.multiplier() == 1 && right.multiplier() == 1);
        Node::Unit(UnitNode::new(
            db.con_len(left) + db.con_len(right),
            depth,
            n_leaves,
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

    /// Reserves variables for all the outputs of this node in the given range
    pub fn reserve_vars<R>(&mut self, range: R, var_manager: &mut dyn ManageVars)
    where
        R: ops::RangeBounds<usize>,
    {
        match self {
            Node::Unit(UnitNode { lits, .. }) => {
                let range = match range.start_bound() {
                    ops::Bound::Included(&v) => v - 1,
                    ops::Bound::Excluded(&v) => v,
                    ops::Bound::Unbounded => 0,
                }..match range.end_bound() {
                    ops::Bound::Included(&v) => v,
                    ops::Bound::Excluded(&v) => v - 1,
                    ops::Bound::Unbounded => lits.len(),
                };
                for olit in &mut lits[range] {
                    if let LitData::None = olit {
                        *olit = LitData::new_lit(var_manager.new_var().pos_lit());
                    }
                }
            }
            Node::General(GeneralNode { lits, .. }) => {
                let bin_search = |val| {
                    lits.binary_search_by_key(&val, |dat| dat.0)
                        .unwrap_or_else(|e| e)
                };
                let from = match range.start_bound() {
                    ops::Bound::Included(b) => bin_search(*b),
                    ops::Bound::Excluded(b) => bin_search(*b + 1),
                    ops::Bound::Unbounded => 0,
                };
                let till = match range.end_bound() {
                    ops::Bound::Included(b) => bin_search(*b + 1),
                    ops::Bound::Excluded(b) => bin_search(*b),
                    ops::Bound::Unbounded => lits.len(),
                };
                for (_, olit) in &mut lits[from..till] {
                    if let LitData::None = olit {
                        *olit = LitData::new_lit(var_manager.new_var().pos_lit());
                    }
                }
            }
            Node::Leaf(_) | Node::Dummy => (),
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

    fn iter_olits(&self) -> OLitIter<'_> {
        OLitIter::new(self)
    }
}

/// Access to output literals. Panics if the literal has not been reserved yet.
/// The index is the output literal _value_, not it's index.
impl ops::Index<usize> for Node {
    type Output = Lit;

    fn index(&self, val: usize) -> &Self::Output {
        self.lit(val).unwrap_or_else(|| {
            panic!("trying to access output literal {val} that has not been reserved")
        })
    }
}

/// An internal node of the totalizer
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct UnitNode {
    pub(crate) lits: Vec<LitData>,
    pub(crate) depth: usize,
    pub(crate) n_leaves: usize,
    pub(crate) left: NodeCon,
    pub(crate) right: NodeCon,
}

impl UnitNode {
    fn new(len: usize, depth: usize, n_leaves: usize, left: NodeCon, right: NodeCon) -> Self {
        // Length of node can never change
        let mut lits = vec![];
        lits.reserve_exact(len);
        (0..len).for_each(|_| lits.push(LitData::default()));
        Self {
            lits,
            depth,
            n_leaves,
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
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GeneralNode {
    pub(crate) lits: Vec<(usize, LitData)>,
    pub(crate) depth: usize,
    pub(crate) n_leaves: usize,
    pub(crate) max_val: usize,
    pub(crate) left: NodeCon,
    pub(crate) right: NodeCon,
}

impl GeneralNode {
    fn new(
        lvals: &[usize],
        rvals: &[usize],
        depth: usize,
        n_leaves: usize,
        left: NodeCon,
        right: NodeCon,
    ) -> Self {
        // interleave the sorted value ranges and sums
        let mut lits = Vec::with_capacity(lvals.len() + rvals.len());
        lits.extend(lvals.iter().map(|&v| (v, LitData::default())));
        let mut idx = 0;
        for &r in rvals {
            while idx < lits.len() && lits[idx].0 < r {
                idx += 1;
            }
            if idx >= lits.len() || lits[idx].0 > r {
                lits.insert(idx, (r, LitData::default()));
            }
            idx += 1;
        }
        for (lidx, &l) in lvals.iter().enumerate() {
            let mut idx = lidx;
            for (ridx, &r) in rvals.iter().enumerate() {
                // TODO: can we do a bit better here? `lidx * ridx` does not work, as there might
                // be duplicate values that were already merged
                idx = cmp::max(idx, ridx);
                let val = l + r;
                while idx < lits.len() && lits[idx].0 < val {
                    idx += 1;
                }
                if idx >= lits.len() || lits[idx].0 > val {
                    lits.insert(idx, (val, LitData::default()));
                }
                idx += 1;
            }
        }
        lits.shrink_to_fit();
        let max_val = lits.last().unwrap().0;
        debug_assert!(lits[0].0 > 0);
        debug_assert!('assert: {
            for (idx, &(val, _)) in lits.iter().enumerate().skip(1) {
                if val <= lits[idx - 1].0 {
                    break 'assert false;
                }
            }
            true
        });
        Self {
            lits,
            depth,
            n_leaves,
            max_val,
            left,
            right,
        }
    }

    /// Gets a reference to the literal data for the output of a given value
    #[must_use]
    pub(crate) fn lit_data(&self, val: usize) -> Option<LitData> {
        self.lits
            .binary_search_by_key(&val, |dat| dat.0)
            .ok()
            .map(|idx| self.lits[idx].1)
    }

    /// Gets a reference to the literal data for the output of a given value
    #[must_use]
    fn lit_data_ref(&self, val: usize) -> Option<&LitData> {
        self.lits
            .binary_search_by_key(&val, |dat| dat.0)
            .ok()
            .map(|idx| &self.lits[idx].1)
    }

    /// Gets a mutable reference to the literal data for the output of a given value
    #[must_use]
    pub(crate) fn lit_data_mut(&mut self, val: usize) -> Option<&mut LitData> {
        self.lits
            .binary_search_by_key(&val, |dat| dat.0)
            .ok()
            .map(|idx| &mut self.lits[idx].1)
    }

    /// Panic-safe version of literal indexing
    #[inline]
    #[must_use]
    pub fn lit(&self, val: usize) -> Option<&Lit> {
        self.lit_data_ref(val).and_then(LitData::lit)
    }

    /// Checks if a given value has the "if" semantics encoded
    #[cfg(feature = "internals")]
    #[inline]
    #[must_use]
    pub fn semantics_if(&self, val: usize) -> bool {
        self.lit_data(val).is_some_and(LitData::semantics_if)
    }

    /// Checks if a given value has the "only if" semantics encoded
    #[cfg(feature = "internals")]
    #[inline]
    #[must_use]
    pub fn semantics_only_if(&self, val: usize) -> bool {
        self.lit_data(val).is_some_and(LitData::semantics_only_if)
    }
}

/// Data associated with an output literal in a [`Node`]
#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
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
            LitData::Lit { semantics, .. } => semantics.is_some_and(Semantics::has_if),
        }
    }

    #[cfg(feature = "internals")]
    #[inline]
    #[must_use]
    fn semantics_only_if(self) -> bool {
        match self {
            LitData::None => false,
            LitData::Lit { semantics, .. } => semantics.is_some_and(Semantics::has_only_if),
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

/// A depth first search iterator over the nodes in the tree, computing the sum of input value at
/// each node
#[derive(Debug)]
pub struct ValueIter<'a> {
    /// The database that the tree is in
    db: &'a Db,
    /// The trace of the iterator. Everything left of the last node in the trace has already been
    /// explored.
    ///
    /// (Connection how we got here, Left value if explored)
    trace: Vec<(NodeCon, Option<usize>)>,
    /// The assignment to the input literals
    assign: &'a Assignment,
    // TODO: figure out whether we can avoid always caching for _all_ nodes
    /// Cache for values already computed, since the structure does not have to be a tree
    /// We use [`usize::MAX`] to mark not computed values
    cache: Vec<usize>,
}

impl<'a> ValueIter<'a> {
    /// Creates a new depth-first search iterator
    pub fn new(db: &'a Db, root: NodeId, assign: &'a Assignment) -> Self {
        // build trace extending to left-most leaf
        let mut trace = vec![(NodeCon::full(root), None)];
        let mut current = root;
        while let Some(con) = db[current].left() {
            trace.push((con, None));
            current = con.id;
        }
        // store leaf value
        let last = unreachable_none!(trace.last_mut());
        match db[last.0.id] {
            Node::Leaf(lit) => {
                last.1 = Some(match assign.lit_value(lit) {
                    crate::types::TernaryVal::True => 1,
                    crate::types::TernaryVal::False => 0,
                    crate::types::TernaryVal::DontCare => {
                        panic!("assignment must assign all input literals")
                    }
                });
            }
            _ => panic!("expected last in trace to be a leaf"),
        }
        let cache = vec![usize::MAX; root.0 + 1];
        Self {
            db,
            trace,
            assign,
            cache,
        }
    }
}

impl Iterator for ValueIter<'_> {
    type Item = (NodeId, usize);

    fn next(&mut self) -> Option<Self::Item> {
        // get item to yield and cut last element off of trace
        let popped = self.trace.pop()?;
        let (popped_con, Some(popped_val)) = popped else {
            panic!("expected last entry in trace to have a value")
        };
        // if right of new last element has already been explored, only add value
        let last = match self.trace.last_mut() {
            Some((con, Some(val))) => {
                // right branch has been explored, add value
                *val += popped_con.map(popped_val);
                // cache the value for the last node in case we come back to it
                self.cache[con.id.0] = *val;
                return Some((popped_con.id, popped_val));
            }
            Some(last) => last,
            _ => return Some((popped_con.id, popped_val)),
        };
        debug_assert!(last.1.is_none());
        // Ensure we have cached the value (if the node is not a leaf)
        debug_assert!(
            self.db[popped_con.id].is_leaf() || self.cache[popped_con.id.0] == popped_val
        );
        // mark left branch as explored and storing left value
        last.1 = Some(popped_con.map(popped_val));
        // if the node does not have a right child, do nothing
        let Some(right) = self.db[last.0.id].right() else {
            return Some((popped_con.id, popped_val));
        };
        if self.cache[right.id.0] < usize::MAX {
            // have encountered this node before and cached its value
            let val = popped_con.map(popped_val) + right.map(self.cache[right.id.0]);
            last.1 = Some(val);
            self.cache[last.0.id.0] = val;
            return Some((popped_con.id, popped_val));
        }
        self.trace.push((right, None));
        let mut current = right.id;
        while let Some(con) = self.db[current].left() {
            if self.cache[con.id.0] < usize::MAX {
                // have encountered this node before and cached its value
                let last = unreachable_none!(self.trace.last_mut());
                last.1 = Some(con.map(self.cache[con.id.0]));
                let right = self.db[current].right().unwrap();
                if self.cache[right.id.0] < usize::MAX {
                    // have also encountered the right child, so do not need to recurse further
                    let val = con.map(self.cache[con.id.0]) + right.map(self.cache[right.id.0]);
                    last.1 = Some(val);
                    self.cache[last.0.id.0] = val;
                    return Some((popped_con.id, popped_val));
                }
                // put right child in trace and continue
                self.trace.push((right, None));
                current = right.id;
                continue;
            }
            self.trace.push((con, None));
            current = con.id;
        }
        // store leaf value
        let last = unreachable_none!(self.trace.last_mut());
        match self.db[last.0.id] {
            Node::Leaf(lit) => {
                last.1 = Some(match self.assign.lit_value(lit) {
                    crate::types::TernaryVal::True => 1,
                    crate::types::TernaryVal::False => 0,
                    crate::types::TernaryVal::DontCare => {
                        panic!("assignment must assign all input literals")
                    }
                });
            }
            _ => panic!("expected last in trace to be a leaf"),
        }
        // return popped node
        Some((popped_con.id, popped_val))
    }
}

/// An iterator over a nodes encoded output literals
#[derive(Debug)]
enum OLitIter<'node> {
    Unit(std::iter::Enumerate<std::slice::Iter<'node, LitData>>),
    General(std::slice::Iter<'node, (usize, LitData)>),
    None,
}

impl<'node> OLitIter<'node> {
    fn new(node: &'node Node) -> Self {
        match node {
            Node::Unit(UnitNode { lits, .. }) => Self::Unit(lits.iter().enumerate()),
            Node::General(GeneralNode { lits, .. }) => Self::General(lits.iter()),
            Node::Leaf(_) | Node::Dummy => Self::None,
        }
    }
}

impl Iterator for OLitIter<'_> {
    type Item = (Lit, usize);

    fn next(&mut self) -> Option<Self::Item> {
        let (val, lit_data) = match self {
            OLitIter::Unit(iter) => match iter.next() {
                Some(val) => (val.0 + 1, *val.1),
                None => return None,
            },
            OLitIter::General(iter) => match iter.next() {
                Some(val) => (val.0, val.1),
                None => return None,
            },
            OLitIter::None => return None,
        };
        match lit_data {
            LitData::None => self.next(),
            LitData::Lit { lit, .. } => Some((lit, val)),
        }
    }
}

/// An iterator over assigned totalizer variables
#[derive(Debug)]
pub struct AssignIter<'db> {
    db: &'db Db,
    val_iter: ValueIter<'db>,
    lit_iter: OLitIter<'db>,
    current_val: usize,
}

impl<'db> AssignIter<'db> {
    fn new(db: &'db Db, root: NodeId, assign: &'db Assignment) -> Self {
        let mut val_iter = ValueIter::new(db, root, assign);
        let Some((id, value)) = val_iter.next() else {
            unreachable!()
        };
        Self {
            db,
            val_iter,
            lit_iter: db[id].iter_olits(),
            current_val: value,
        }
    }
}

impl Iterator for AssignIter<'_> {
    type Item = Lit;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((lit, val)) = self.lit_iter.next() {
            Some(if self.current_val >= val { lit } else { !lit })
        } else {
            let (id, value) = self.val_iter.next()?;
            self.lit_iter = self.db[id].iter_olits();
            self.current_val = value;
            self.next()
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

    use super::{Db, Node, Semantics};

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

    #[test]
    fn leaf_iter() {
        let mut lits = vec![(lit![0], 3), (lit![1], 2), (lit![2], 1), (lit![3], 42)];
        let mut db = Db::default();
        let con = db.weighted_lit_tree(&lits);
        assert_eq!(con.multiplier(), 1);
        assert_eq!(con.divisor(), 1);
        assert_eq!(con.offset(), 0);
        let mut leaves: Vec<_> = db.leaf_iter(con.id).collect();
        lits.sort_unstable();
        leaves.sort_unstable();
        assert_eq!(lits, leaves);
        assert_eq!(leaves.len(), db[con.id].n_leaves());
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn leaf_iter_pseudo_leaf() {
        let mut vm = BasicVarManager::from_next_free(var![3]);
        let mut db = Db::default();
        let a = db.insert(Node::leaf(lit![0]));
        let b = db.insert(Node::leaf(lit![1]));
        let c = db.insert(Node::internal(NodeCon::full(a), NodeCon::full(b), &db));
        let leaves: Vec<_> = db.leaf_iter(c).collect();
        assert_eq!(vec![(lit![0], 1), (lit![1], 1)], leaves);
        assert_eq!(leaves.len(), db[c].n_leaves());
        let d = db.insert(Node::leaf(lit![2]));
        let e = db.insert(Node::internal(
            NodeCon::full(d),
            NodeCon::single(c, 2, 1),
            &db,
        ));
        db[c].reserve_vars(2..=2, &mut vm);
        let leaves: Vec<_> = db.leaf_iter(e).collect();
        assert_eq!(vec![(lit![2], 1), (db[c][2], 1)], leaves);
        assert_eq!(leaves.len(), db[e].n_leaves());
    }

    #[test]
    fn leaf_iter_offset() {
        let mut vm = BasicVarManager::from_next_free(var![8]);
        let mut db = Db::default();
        let lits = [lit![0], lit![1], lit![2], lit![3]];
        let a = db.lit_tree(&lits);
        db[a].reserve_vars(3.., &mut vm);
        let lits = [lit![4], lit![5], lit![6], lit![7]];
        let b = db.lit_tree(&lits);
        db[b].reserve_vars(2.., &mut vm);
        let c = db.insert(Node::internal(
            NodeCon::offset_weighted(a, 2, 2),
            NodeCon::offset_weighted(b, 1, 4),
            &db,
        ));
        let leaves: Vec<_> = db.leaf_iter(c).collect();
        assert_eq!(
            vec![
                (db[a][3], 2),
                (db[a][4], 2),
                (db[b][2], 4),
                (db[b][3], 4),
                (db[b][4], 4)
            ],
            leaves
        );
        assert_eq!(leaves.len(), db[c].n_leaves());
    }

    #[test]
    fn leaf_iter_offset_weighted() {
        let mut vm = BasicVarManager::from_next_free(var![4]);
        let mut db = Db::default();
        let lits = [(lit![0], 1), (lit![1], 2), (lit![2], 10)];
        let a = db.weighted_lit_tree(&lits);
        db[a.id].reserve_vars(3.., &mut vm);
        let b = db.insert(Node::leaf(lit![3]));
        let c = db.insert(Node::internal(
            NodeCon::offset_weighted(a.id, 2, 1),
            NodeCon::full(b),
            &db,
        ));
        let leaves: Vec<_> = db.leaf_iter(c).collect();
        assert_eq!(
            vec![
                (db[a.id][3], 1),
                (db[a.id][10], 7),
                (db[a.id][11], 1),
                (db[a.id][12], 1),
                (db[a.id][13], 1),
                (lit![3], 1)
            ],
            leaves
        );
        assert_eq!(leaves.len(), db[c].n_leaves());
    }

    #[test]
    fn weighted_vals() {
        // Mock up a DB with a single weighted node to test the `NodeLike::vals` implementation
        let db = Db {
            nodes: vec![
                Node::Dummy,
                Node::General(super::GeneralNode::new(
                    &[6, 8, 12],
                    &[6, 9, 13],
                    1,
                    4,
                    NodeCon::full(super::NodeId(0)),
                    NodeCon::full(super::NodeId(0)),
                )),
            ],
            dummy_id: Some(super::NodeId(0)),
            ..Db::default()
        };
        let node = &db[super::NodeId(1)];
        assert!(node
            .vals(..)
            .eq([6, 8, 9, 12, 13, 14, 15, 17, 18, 19, 21, 25]));
        assert!(node.vals(0..6).next().is_none());
        assert!(node.vals(0..=5).next().is_none());
        assert!(node.vals(9..17).eq([9, 12, 13, 14, 15]));
        assert!(node.vals(9..=17).eq([9, 12, 13, 14, 15, 17]));
    }
}
