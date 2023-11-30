//! # Totalizer Encoding Based On a Node Database
//!
//! This is an alternative implementation of the
//! [`crate::encodings::card::Totalizer`] encoding.

use std::{
    cmp,
    collections::BTreeMap,
    ops::{Bound, Index, IndexMut, Range, RangeBounds},
};

use crate::{
    encodings::{
        atomics,
        nodedb::{NodeById, NodeCon, NodeId, NodeLike},
        CollectClauses, EncodeStats, Error,
    },
    instances::ManageVars,
    types::{Lit, RsHashMap},
};

use super::{BoundUpper, BoundUpperIncremental, Encode, EncodeIncremental};

#[cfg(feature = "pyapi")]
use crate::instances::{BasicVarManager, Cnf};
#[cfg(feature = "pyapi")]
use pyo3::prelude::*;

/// Implementation of the binary adder tree totalizer encoding \[1\].
/// The implementation is incremental as extended in \[2\].
/// The implementation is based on a node database.
/// For now, this implementation only supports upper bounding.
///
/// # References
///
/// - \[1\] Olivier Bailleux and Yacine Boufkhad: _Efficient CNF Encoding of Boolean Cardinality Constraints_, CP 2003.
/// - \[2\] Ruben Martins and Saurabh Joshi and Vasco Manquinho and Ines Lynce: _Incremental Cardinality Constraints for MaxSAT_, CP 2014.
#[cfg_attr(feature = "pyapi", pyclass(name = "Totalizer"))]
#[derive(Default)]
pub struct DbTotalizer {
    /// Literals added but not yet in the encoding
    lit_buffer: Vec<Lit>,
    /// The root of the tree, if constructed
    root: Option<NodeId>,
    /// The number of variables in the totalizer
    n_vars: u32,
    /// The number of clauses in the totalizer
    n_clauses: usize,
    /// The node database of the totalizer
    db: TotDb,
}

impl DbTotalizer {
    fn extend_tree(&mut self) {
        if self.lit_buffer.is_empty() {
            return;
        }
        let new_tree = self.db.lit_tree(&self.lit_buffer);
        self.root = Some(match self.root {
            Some(old_root) => {
                self.db
                    .merge(&[NodeCon::full(old_root), NodeCon::full(new_tree)])
                    .id
            }
            None => new_tree,
        });
        self.lit_buffer.clear();
    }

    /// Gets the maximum depth of the tree
    pub fn depth(&self) -> usize {
        match &self.root {
            None => 0,
            Some(root) => self.db[*root].depth(),
        }
    }
}

impl Encode for DbTotalizer {
    fn n_lits(&self) -> usize {
        self.lit_buffer.len()
            + match self.root {
                Some(id) => self.db[id].len(),
                None => 0,
            }
    }
}

impl EncodeIncremental for DbTotalizer {
    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        if let Some(root) = self.root {
            self.db.reserve_vars(root, var_manager)
        }
    }
}

impl BoundUpper for DbTotalizer {
    fn encode_ub<Col, R>(&mut self, range: R, collector: &mut Col, var_manager: &mut dyn ManageVars)
    where
        Col: CollectClauses,
        R: RangeBounds<usize>,
    {
        self.db.reset_encoded();
        self.encode_ub_change(range, collector, var_manager)
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, Error> {
        if ub >= self.n_lits() {
            return Ok(vec![]);
        }
        if !self.lit_buffer.is_empty() {
            return Err(Error::NotEncoded);
        }
        if let Some(id) = self.root {
            match &self.db[id] {
                Node::Leaf(lit) => {
                    debug_assert_eq!(ub, 0);
                    return Ok(vec![!*lit]);
                }
                Node::Unit(node) => {
                    if let LitData::Lit { lit, enc_pos } = node.lits[ub] {
                        if enc_pos {
                            return Ok(vec![!lit]);
                        }
                    }
                }
                Node::General(_) => panic!(),
            }
        }
        Err(Error::NotEncoded)
    }
}

impl BoundUpperIncremental for DbTotalizer {
    fn encode_ub_change<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) where
        Col: CollectClauses,
        R: RangeBounds<usize>,
    {
        let range = super::prepare_ub_range(self, range);
        if range.is_empty() {
            return;
        }
        self.extend_tree();
        if let Some(id) = self.root {
            let n_vars_before = var_manager.n_used();
            let n_clauses_before = collector.n_clauses();
            for idx in range {
                self.db.define_pos_tot(id, idx, collector, var_manager);
            }
            self.n_clauses += collector.n_clauses() - n_clauses_before;
            self.n_vars += var_manager.n_used() - n_vars_before;
        }
    }
}

impl EncodeStats for DbTotalizer {
    fn n_clauses(&self) -> usize {
        self.n_clauses
    }

    fn n_vars(&self) -> u32 {
        self.n_vars
    }
}

impl From<Vec<Lit>> for DbTotalizer {
    fn from(lits: Vec<Lit>) -> Self {
        Self {
            lit_buffer: lits,
            root: Default::default(),
            n_vars: Default::default(),
            n_clauses: Default::default(),
            db: Default::default(),
        }
    }
}

impl FromIterator<Lit> for DbTotalizer {
    fn from_iter<T: IntoIterator<Item = Lit>>(iter: T) -> Self {
        Self {
            lit_buffer: Vec::from_iter(iter),
            root: Default::default(),
            n_vars: Default::default(),
            n_clauses: Default::default(),
            db: Default::default(),
        }
    }
}

impl Extend<Lit> for DbTotalizer {
    fn extend<T: IntoIterator<Item = Lit>>(&mut self, iter: T) {
        self.lit_buffer.extend(iter)
    }
}

/// A totalizer adder node
#[derive(Clone)]
pub enum Node {
    Leaf(Lit),
    Unit(UnitNode),
    General(GeneralNode),
}

impl NodeLike for Node {
    type ValIter = std::iter::Chain<Range<usize>, std::vec::IntoIter<usize>>;

    fn max_val(&self) -> usize {
        match self {
            Node::Leaf(_) => 1,
            Node::Unit(node) => node.lits.len(),
            Node::General(node) => node.max_val,
        }
    }

    fn len(&self) -> usize {
        match self {
            Node::Leaf(_) => 1,
            Node::Unit(node) => node.lits.len(),
            Node::General(node) => node.lits.len(),
        }
    }

    fn vals<R>(&self, range: R) -> Self::ValIter
    where
        R: RangeBounds<usize>,
    {
        match self {
            Node::Leaf(_) => {
                if range.contains(&1) {
                    return (1..2).chain(vec![]);
                }
                (0..0).chain(vec![])
            }
            Node::Unit(node) => {
                let lb = match range.start_bound() {
                    Bound::Included(b) => cmp::max(*b, 1),
                    Bound::Excluded(b) => b + 1,
                    Bound::Unbounded => 1,
                };
                let ub = match range.end_bound() {
                    Bound::Included(b) => cmp::min(b + 1, node.lits.len() + 1),
                    Bound::Excluded(b) => cmp::min(*b, node.lits.len() + 1),
                    Bound::Unbounded => node.lits.len() + 1,
                };
                (lb..ub).chain(vec![])
            }
            Node::General(node) => {
                let vals: Vec<_> = node.lits.range(range).map(|(val, _)| *val).collect();
                (0..0).chain(vals)
            }
        }
    }

    fn right(&self) -> Option<NodeCon> {
        match self {
            Node::Leaf(..) => None,
            Node::Unit(node) => Some(node.left),
            Node::General(node) => Some(node.left),
        }
    }

    fn left(&self) -> Option<NodeCon> {
        match self {
            Node::Leaf(..) => None,
            Node::Unit(node) => Some(node.right),
            Node::General(node) => Some(node.right),
        }
    }

    fn depth(&self) -> usize {
        match self {
            Node::Leaf(..) => 1,
            Node::Unit(node) => node.depth,
            Node::General(node) => node.depth,
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
            return Self::General(GeneralNode::new(
                &lvals,
                &rvals,
                std::cmp::max(db[left.id].depth(), db[right.id].depth()) + 1,
                left,
                right,
            ));
        }
        // if both inputs have the same weight, the multiplier should be 1
        debug_assert!(left.multiplier() == 1 && right.multiplier() == 1);
        Self::Unit(UnitNode::new(
            db.con_len(left) + db.con_len(right),
            std::cmp::max(db[left.id].depth(), db[right.id].depth()) + 1,
            left,
            right,
        ))
    }

    fn leaf(lit: Lit) -> Self {
        Self::Leaf(lit)
    }
}

impl Node {
    /// Panic-safe version of literal indexing
    pub fn lit(&self, val: usize) -> Option<&Lit> {
        match self {
            Node::Leaf(lit, ..) => {
                if val != 1 {
                    return None;
                }
                Some(lit)
            }
            Node::Unit(node) => node.lit(val),
            Node::General(node) => node.lit(val),
        }
    }

    /// Checks if a given output value is positively encoded
    pub fn encoded_pos(&self, val: usize) -> bool {
        match self {
            Node::Leaf(..) => {
                if val != 1 {
                    return false;
                }
                true
            }
            Node::Unit(node) => node.encoded_pos(val),
            Node::General(node) => node.encoded_pos(val),
        }
    }

    /// Returns the internal node and panics if the node is not a unit
    pub(super) fn unit(&self) -> &UnitNode {
        match self {
            Node::Unit(node) => node,
            _ => panic!("called `unit` on non-unit node"),
        }
    }

    /// Returns the internal node and panics if the node is not a unit
    pub(super) fn mut_unit(&mut self) -> &mut UnitNode {
        match self {
            Node::Unit(node) => node,
            _ => panic!("called `unit` on non-unit node"),
        }
    }

    /// Returns the internal node and panics if the node is not general
    pub(super) fn mut_general(&mut self) -> &mut GeneralNode {
        match self {
            Node::General(node) => node,
            _ => panic!("called `unit` on non-general node"),
        }
    }

    /// Adjusts the connections of the node to draining a range of nodes. If the
    /// nodes references a nodes within the drained range, it returns that
    /// [`NodeId`] as an Error.
    fn drain(&mut self, range: Range<NodeId>) -> Result<(), NodeId> {
        match self {
            Node::Leaf(_) => Ok(()),
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
impl Index<usize> for Node {
    type Output = Lit;

    fn index(&self, val: usize) -> &Self::Output {
        self.lit(val).unwrap()
    }
}

/// An internal node of the totalizer
#[derive(Clone)]
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
    pub fn lit(&self, val: usize) -> Option<&Lit> {
        self.lits[val - 1].lit()
    }

    /// Checks if a given value is positively encoded
    #[inline]
    pub fn encoded_pos(&self, val: usize) -> bool {
        self.lits[val - 1].encoded_pos()
    }
}

impl Index<usize> for UnitNode {
    type Output = Lit;

    fn index(&self, index: usize) -> &Self::Output {
        self.lit(index).unwrap()
    }
}

/// An internal _general_ (weighted) node
#[derive(Clone)]
pub struct GeneralNode {
    pub(crate) lits: BTreeMap<usize, LitData>,
    pub(crate) depth: usize,
    pub(crate) max_val: usize,
    pub(crate) left: NodeCon,
    pub(crate) right: NodeCon,
}

impl GeneralNode {
    fn new(lvals: &[usize], rvals: &[usize], depth: usize, left: NodeCon, right: NodeCon) -> Self {
        let mut lits = BTreeMap::from_iter(lvals.iter().map(|&val| (val, LitData::default())));
        rvals.iter().for_each(|val| {
            if !lits.contains_key(val) {
                lits.insert(*val, LitData::default());
            }
        });
        let mut max_val = 0;
        lvals.iter().for_each(|lval| {
            rvals.iter().for_each(|rval| {
                let val = lval + rval;
                max_val = val;
                lits.entry(val).or_insert_with(LitData::default);
            })
        });
        Self {
            lits,
            depth,
            max_val,
            left,
            right,
        }
    }

    /// Panic-safe version of literal indexing
    pub fn lit(&self, val: usize) -> Option<&Lit> {
        self.lits.get(&val).and_then(|dat| dat.lit())
    }

    /// Checks if a given value is positively encoded
    #[inline]
    pub fn encoded_pos(&self, val: usize) -> bool {
        self.lits
            .get(&val)
            .map(|dat| dat.encoded_pos())
            .unwrap_or(false)
    }
}

/// Data associated with an output literal in a [`Node`]
#[derive(Default, Clone)]
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

/// A totalizer database
#[derive(Default, Clone)]
#[cfg_attr(feature = "internals", visibility::make(pub))]
pub(in crate::encodings) struct TotDb {
    /// The node database of the totalizer
    nodes: Vec<Node>,
    /// Mapping literals to leaf nodes
    lookup_leaf: RsHashMap<Lit, NodeId>,
}

impl NodeById for TotDb {
    type Node = Node;

    fn insert(&mut self, node: Self::Node) -> NodeId {
        if let Node::Leaf(lit) = node {
            if let Some(&id) = self.lookup_leaf.get(&lit) {
                return id;
            }
            self.lookup_leaf.insert(lit, NodeId(self.nodes.len()));
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

    fn drain<R: RangeBounds<NodeId>>(
        &mut self,
        range: R,
    ) -> Result<Self::Drain<'_>, (NodeId, NodeId)> {
        let range = match range.start_bound() {
            Bound::Included(id) => *id,
            Bound::Excluded(id) => id + 1,
            Bound::Unbounded => NodeId(0),
        }..match range.end_bound() {
            Bound::Included(id) => id + 1,
            Bound::Excluded(id) => *id,
            Bound::Unbounded => NodeId(self.nodes.len()),
        };
        if range.is_empty() {
            return Ok(self.nodes.drain(self.nodes.len()..self.nodes.len()));
        }
        (range.end.0..self.nodes.len()).try_for_each(|idx| {
            self.nodes[idx]
                .drain(range.clone())
                .map_err(|con| (NodeId(idx), con))
        })?;
        self.lookup_leaf.retain(|_, id| !range.contains(id));
        self.lookup_leaf.values_mut().for_each(|id| {
            if *id >= range.end {
                *id -= range.end - range.start
            }
        });
        Ok(self.nodes.drain(range.start.0..range.end.0))
    }
}

impl IndexMut<NodeId> for TotDb {
    fn index_mut(&mut self, index: NodeId) -> &mut Self::Output {
        &mut self.nodes[index.0]
    }
}

impl Index<NodeId> for TotDb {
    type Output = Node;

    fn index(&self, index: NodeId) -> &Self::Output {
        &self.nodes[index.0]
    }
}

impl TotDb {
    /// Generates the encoding to define the positive output literal with value
    /// `val`, if it is not already defined. Recurses down the tree. The
    /// returned literal is the output literal and the encoding is added to the
    /// `collector`.
    pub fn define_pos<Col>(
        &mut self,
        id: NodeId,
        val: usize,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Option<Lit>
    where
        Col: CollectClauses,
    {
        debug_assert!(val <= self[id].max_val());
        debug_assert!(val > 0);
        match &self[id] {
            Node::Leaf(lit) => {
                debug_assert_eq!(val, 1);
                if val != 1 {
                    return None;
                }
                Some(*lit)
            }
            Node::Unit(node) => {
                if val > node.lits.len() || val == 0 {
                    return None;
                }

                // Check if already encoded
                if let LitData::Lit { lit, enc_pos, .. } = node.lits[val - 1] {
                    if enc_pos {
                        return Some(lit);
                    }
                }

                Some(self.define_pos_tot(id, val - 1, collector, var_manager))
            }
            Node::General(node) => {
                // Check if already encoded
                if let Some(lit_data) = node.lits.get(&val) {
                    if let LitData::Lit {
                        lit, enc_pos: true, ..
                    } = lit_data
                    {
                        return Some(*lit);
                    }
                } else {
                    return None;
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
                    *self[id].mut_general().lits.get_mut(&val).unwrap() = LitData::new_lit(olit);
                    olit
                };

                // Propagate value
                if lcon.is_possible(val) && lcon.rev_map(val) <= self[lcon.id].max_val() {
                    if let Some(llit) =
                        self.define_pos(lcon.id, lcon.rev_map(val), collector, var_manager)
                    {
                        collector.extend([atomics::lit_impl_lit(llit, olit)]);
                    }
                }
                if rcon.is_possible(val) && rcon.rev_map(val) <= self[rcon.id].max_val() {
                    if let Some(rlit) =
                        self.define_pos(rcon.id, rcon.rev_map(val), collector, var_manager)
                    {
                        collector.extend([atomics::lit_impl_lit(rlit, olit)]);
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
                                self.define_pos(rcon.id, rval_rev, collector, var_manager)
                            {
                                debug_assert!(
                                    lcon.len_limit.is_none() || lcon.offset() + 1 == lval
                                );
                                let llit = self
                                    .define_pos(lcon.id, lval, collector, var_manager)
                                    .unwrap();
                                collector.extend([atomics::cube_impl_lit(&[llit, rlit], olit)]);
                            }
                        }
                    }
                }

                // Mark positive literal as encoded
                match &mut self[id].mut_general().lits.get_mut(&val).unwrap() {
                    LitData::None => panic!(),
                    LitData::Lit { enc_pos, .. } => *enc_pos = true,
                };

                Some(olit)
            }
        }
    }

    pub fn define_pos_tot<Col>(
        &mut self,
        id: NodeId,
        idx: usize,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Lit
    where
        Col: CollectClauses,
    {
        let node = &self[id];
        debug_assert!(idx < node.max_val());
        if node.is_leaf() {
            debug_assert_eq!(idx, 0);
            return node[1];
        }
        let lcon = node.left().unwrap();
        let rcon = node.right().unwrap();
        debug_assert!(matches!(self[lcon.id], Node::Leaf(_) | Node::Unit(_)));
        debug_assert!(matches!(self[rcon.id], Node::Leaf(_) | Node::Unit(_)));
        debug_assert_eq!(lcon.multiplier(), 1);
        debug_assert_eq!(rcon.multiplier(), 1);
        let node = node.unit();

        // Check if already encoded
        if let LitData::Lit { lit, enc_pos, .. } = node.lits[idx] {
            if enc_pos {
                return lit;
            }
        }

        let con_idx = |idx: usize, con: NodeCon| con.rev_map(idx + 1) - 1;

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

        // Encode children (recurse)
        for lidx in l_min_idx..=l_max_idx {
            self.define_pos_tot(lcon.id, con_idx(lidx, lcon), collector, var_manager);
        }
        for ridx in r_min_idx..=r_max_idx {
            self.define_pos_tot(rcon.id, con_idx(ridx, rcon), collector, var_manager);
        }

        // Reserve variable for this node, if needed
        let olit = if let Some(&olit) = self[id].lit(idx + 1) {
            olit
        } else {
            let olit = var_manager.new_var().pos_lit();
            self[id].mut_unit().lits[idx] = LitData::new_lit(olit);
            olit
        };

        // Get reference to literals of children
        let tmp_olit_l;
        let llits = match &self[lcon.id] {
            Node::Leaf(lit) => {
                tmp_olit_l = LitData::new_lit(*lit);
                std::slice::from_ref(&tmp_olit_l)
            }
            Node::Unit(UnitNode { lits, .. }) => lits,
            _ => panic!(),
        };
        let tmp_olit_r;
        let rlits = match &self[rcon.id] {
            Node::Leaf(lit) => {
                tmp_olit_r = LitData::new_lit(*lit);
                std::slice::from_ref(&tmp_olit_r)
            }
            Node::Unit(UnitNode { lits, .. }) => lits,
            _ => panic!(),
        };

        // Encode this node
        if l_max_idx == idx {
            collector.extend([atomics::lit_impl_lit(
                *llits[con_idx(idx, lcon)].lit().unwrap(),
                olit,
            )]);
        }
        if r_max_idx == idx {
            collector.extend([atomics::lit_impl_lit(
                *rlits[con_idx(idx, rcon)].lit().unwrap(),
                olit,
            )]);
        }
        let clause_for_lidx = |lidx: usize| {
            let ridx = idx - lidx - 1;
            debug_assert!(ridx <= r_max_idx);
            let llit = *llits[con_idx(lidx, lcon)].lit().unwrap();
            let rlit = *rlits[con_idx(ridx, rcon)].lit().unwrap();
            atomics::cube_impl_lit(&[llit, rlit], olit)
        };
        let clause_iter = (l_min_idx..cmp::min(l_max_idx + 1, idx)).map(clause_for_lidx);
        collector.extend(clause_iter);

        // Mark positive literal as encoded
        match &mut self[id].mut_unit().lits[idx] {
            LitData::None => panic!(),
            LitData::Lit { enc_pos, .. } => *enc_pos = true,
        };

        olit
    }

    /// Recursively reserves all variables in the subtree rooted at the given node
    pub fn reserve_vars(&mut self, id: NodeId, var_manager: &mut dyn ManageVars) {
        if self[id].is_leaf() {
            return;
        }

        // Recurse
        self.reserve_vars(self[id].left().unwrap().id, var_manager);
        self.reserve_vars(self[id].right().unwrap().id, var_manager);

        match &mut self[id] {
            Node::Unit(UnitNode { lits, .. }) => {
                for olit in lits {
                    if let LitData::None = olit {
                        *olit = LitData::new_lit(var_manager.new_var().pos_lit())
                    }
                }
            }
            Node::General(GeneralNode { lits, .. }) => {
                for (_, olit) in lits.iter_mut() {
                    if let LitData::None = olit {
                        *olit = LitData::new_lit(var_manager.new_var().pos_lit())
                    }
                }
            }
            Node::Leaf(_) => panic!(),
        }
    }

    /// Resets the status of what has already been encoded
    pub fn reset_encoded(&mut self) {
        for node in &mut self.nodes {
            match node {
                Node::Unit(UnitNode { lits, .. }) => {
                    for lit in lits {
                        if let LitData::Lit { enc_pos, .. } = lit {
                            *enc_pos = false
                        }
                    }
                }
                Node::General(GeneralNode { lits, .. }) => {
                    for lit in lits.values_mut() {
                        if let LitData::Lit { enc_pos, .. } = lit {
                            *enc_pos = false
                        }
                    }
                }
                Node::Leaf(_) => (),
            }
        }
    }

    /// Resets the reserved variables in the database. This also resets the
    /// status of what has already been encoded.
    #[cfg(feature = "internals")]
    pub fn reset_vars(&mut self) {
        for node in &mut self.nodes {
            match node {
                Node::Leaf(_) => (),
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

#[cfg(feature = "internals")]
pub mod referenced {
    use std::cell::RefCell;

    use crate::{
        encodings::{
            card::{BoundUpper, BoundUpperIncremental, Encode, EncodeIncremental},
            nodedb::{NodeId, NodeLike},
            CollectClauses, Error,
        },
        instances::ManageVars,
        types::Lit,
    };

    use super::{LitData, Node, TotDb};

    /// Implementation of the binary adder tree totalizer encoding \[1\].
    /// The implementation is incremental as extended in \[2\].
    /// This uses a _mutable reference_ to a totalizer database.
    ///
    /// # References
    ///
    /// - \[1\] Olivier Bailleux and Yacine Boufkhad: _Efficient CNF Encoding of Boolean Cardinality Constraints_, CP 2003.
    /// - \[2\] Ruben Martins and Saurabh Joshi and Vasco Manquinho and Ines Lynce: _Incremental Cardinality Constraints for MaxSAT_, CP 2014.
    pub struct Tot<'totdb> {
        /// The root of the tree, if constructed
        root: NodeId,
        /// The node database of the totalizer
        db: &'totdb mut TotDb,
    }

    /// Implementation of the binary adder tree totalizer encoding \[1\].
    /// The implementation is incremental as extended in \[2\].
    /// This uses a [`RefCell`] to a totalizer database.
    ///
    /// # References
    ///
    /// - \[1\] Olivier Bailleux and Yacine Boufkhad: _Efficient CNF Encoding of Boolean Cardinality Constraints_, CP 2003.
    /// - \[2\] Ruben Martins and Saurabh Joshi and Vasco Manquinho and Ines Lynce: _Incremental Cardinality Constraints for MaxSAT_, CP 2014.
    pub struct TotCell<'totdb> {
        /// The root of the tree, if constructed
        root: NodeId,
        /// The node database of the totalizer
        db: &'totdb RefCell<&'totdb mut TotDb>,
    }

    impl<'totdb> Tot<'totdb> {
        /// Constructs a new Totalizer encoding referencing a totalizer database
        pub fn new(root: NodeId, db: &'totdb mut TotDb) -> Self {
            Self { root, db }
        }

        /// Gets the maximum depth of the tree
        pub fn depth(&self) -> usize {
            self.db[self.root].depth()
        }
    }

    impl<'totdb> TotCell<'totdb> {
        /// Constructs a new Totalizer encoding referencing a totalizer database
        pub fn new(root: NodeId, db: &'totdb RefCell<&'totdb mut TotDb>) -> Self {
            Self { root, db }
        }

        /// Gets the maximum depth of the tree
        pub fn depth(&self) -> usize {
            self.db.borrow()[self.root].depth()
        }
    }

    impl Encode for Tot<'_> {
        fn n_lits(&self) -> usize {
            self.db[self.root].len()
        }
    }

    impl Encode for TotCell<'_> {
        fn n_lits(&self) -> usize {
            self.db.borrow()[self.root].len()
        }
    }

    impl EncodeIncremental for Tot<'_> {
        fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
            self.db.reserve_vars(self.root, var_manager)
        }
    }

    impl EncodeIncremental for TotCell<'_> {
        fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
            self.db.borrow_mut().reserve_vars(self.root, var_manager)
        }
    }

    impl BoundUpper for Tot<'_> {
        fn encode_ub<Col, R>(
            &mut self,
            range: R,
            collector: &mut Col,
            var_manager: &mut dyn ManageVars,
        ) where
            Col: CollectClauses,
            R: std::ops::RangeBounds<usize>,
        {
            self.db.reset_encoded();
            self.encode_ub_change(range, collector, var_manager)
        }

        fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, Error> {
            if ub >= self.n_lits() {
                return Ok(vec![]);
            }
            match &self.db[self.root] {
                Node::Leaf(lit) => {
                    debug_assert_eq!(ub, 0);
                    return Ok(vec![!*lit]);
                }
                Node::Unit(node) => {
                    if let LitData::Lit { lit, enc_pos } = node.lits[ub] {
                        if enc_pos {
                            return Ok(vec![!lit]);
                        }
                    }
                }
                Node::General(_) => panic!(),
            }
            Err(Error::NotEncoded)
        }
    }

    impl BoundUpper for TotCell<'_> {
        fn encode_ub<Col, R>(
            &mut self,
            range: R,
            collector: &mut Col,
            var_manager: &mut dyn ManageVars,
        ) where
            Col: CollectClauses,
            R: std::ops::RangeBounds<usize>,
        {
            self.db.borrow_mut().reset_encoded();
            self.encode_ub_change(range, collector, var_manager)
        }

        fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, Error> {
            if ub >= self.n_lits() {
                return Ok(vec![]);
            }
            match &self.db.borrow()[self.root] {
                Node::Leaf(lit) => {
                    debug_assert_eq!(ub, 0);
                    return Ok(vec![!*lit]);
                }
                Node::Unit(node) => {
                    if let LitData::Lit { lit, enc_pos } = node.lits[ub] {
                        if enc_pos {
                            return Ok(vec![!lit]);
                        }
                    }
                }
                Node::General(_) => panic!(),
            }
            Err(Error::NotEncoded)
        }
    }

    impl BoundUpperIncremental for Tot<'_> {
        fn encode_ub_change<Col, R>(
            &mut self,
            range: R,
            collector: &mut Col,
            var_manager: &mut dyn ManageVars,
        ) where
            Col: CollectClauses,
            R: std::ops::RangeBounds<usize>,
        {
            let range = super::super::prepare_ub_range(self, range);
            if range.is_empty() {
                return;
            }
            for idx in range {
                self.db
                    .define_pos_tot(self.root, idx, collector, var_manager);
            }
        }
    }

    impl BoundUpperIncremental for TotCell<'_> {
        fn encode_ub_change<Col, R>(
            &mut self,
            range: R,
            collector: &mut Col,
            var_manager: &mut dyn ManageVars,
        ) where
            Col: CollectClauses,
            R: std::ops::RangeBounds<usize>,
        {
            let range = super::super::prepare_ub_range(self, range);
            if range.is_empty() {
                return;
            }
            for idx in range {
                self.db
                    .borrow_mut()
                    .define_pos_tot(self.root, idx, collector, var_manager);
            }
        }
    }
}

#[cfg(feature = "pyapi")]
#[pymethods]
impl DbTotalizer {
    #[new]
    fn new(lits: Vec<Lit>) -> Self {
        Self::from(lits)
    }

    /// Adds additional input literals to the totalizer
    #[pyo3(name = "extend")]
    fn py_extend(&mut self, lits: Vec<Lit>) {
        self.extend(lits)
    }

    /// Gets the number of input literals in the encoding
    #[pyo3(name = "n_lits")]
    fn py_n_lits(&self) -> usize {
        self.n_lits()
    }

    /// Gets the number of clauses in the encoding
    #[pyo3(name = "n_clauses")]
    fn py_n_clauses(&self) -> usize {
        self.n_clauses()
    }

    /// Gets the number of variables in the encoding
    #[pyo3(name = "n_vars")]
    fn py_n_vars(&self) -> u32 {
        self.n_vars()
    }

    /// Incrementally builds the totalizer encoding to that upper bounds
    /// in the range `max_ub..=min_ub` can be enforced. New variables will
    /// be taken from `var_manager`.
    #[pyo3(name = "encode_ub")]
    fn py_encode_ub(
        &mut self,
        max_ub: usize,
        min_ub: usize,
        var_manager: &mut BasicVarManager,
    ) -> Cnf {
        let mut cnf = Cnf::new();
        <Self as BoundUpperIncremental>::encode_ub_change(
            self,
            max_ub..=min_ub,
            &mut cnf,
            var_manager,
        );
        cnf
    }

    /// Gets assumptions to enforce the given upper bound. Make sure that
    /// the required encoding is built first.
    #[pyo3(name = "enforce_ub")]
    fn py_enforce_ub(&self, ub: usize) -> PyResult<Vec<Lit>> {
        Ok(self.enforce_ub(ub)?)
    }
}

#[cfg(test)]
mod tests {
    use super::{DbTotalizer, TotDb};
    use crate::{
        encodings::{
            card::{BoundUpper, BoundUpperIncremental},
            nodedb::{NodeById, NodeCon, NodeLike},
            EncodeStats, Error,
        },
        instances::{BasicVarManager, Cnf, ManageVars},
        lit, var,
    };

    #[test]
    fn tot_db() {
        let mut db = TotDb::default();
        let root = db.lit_tree(&[lit![0], lit![1], lit![2], lit![3]]);
        debug_assert_eq!(db[root].depth(), 3);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);

        let mut cnf = Cnf::new();
        db.define_pos_tot(root, 0, &mut cnf, &mut var_manager);
        debug_assert_eq!(cnf.len(), 6);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos_tot(root, 1, &mut cnf, &mut var_manager);
        debug_assert_eq!(cnf.len(), 9);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos_tot(root, 2, &mut cnf, &mut var_manager);
        debug_assert_eq!(cnf.len(), 8);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos_tot(root, 3, &mut cnf, &mut var_manager);
        debug_assert_eq!(cnf.len(), 3);
    }

    #[test]
    fn weighted_tot_db() {
        let mut db = TotDb::default();
        let con = db.weighted_lit_tree(&[(lit![0], 4), (lit![1], 4), (lit![2], 7), (lit![3], 7)]);
        debug_assert_eq!(con.multiplier(), 1);
        debug_assert_eq!(con.offset(), 0);
        debug_assert_eq!(con.divisor(), 1);
        let root = con.id;
        debug_assert_eq!(db[root].depth(), 3);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);

        let mut cnf = Cnf::new();
        db.define_pos(root, 1, &mut cnf, &mut var_manager);
        debug_assert_eq!(cnf.len(), 0);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos(root, 4, &mut cnf, &mut var_manager);
        debug_assert_eq!(cnf.len(), 3);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos(root, 7, &mut cnf, &mut var_manager);
        debug_assert_eq!(cnf.len(), 3);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos(root, 8, &mut cnf, &mut var_manager);
        debug_assert_eq!(cnf.len(), 2);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos(root, 15, &mut cnf, &mut var_manager);
        debug_assert_eq!(cnf.len(), 4);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos(root, 22, &mut cnf, &mut var_manager);
        debug_assert_eq!(cnf.len(), 3);
    }

    #[test]
    fn weighted_tot_db2() {
        let mut db = TotDb::default();
        let con = db.weighted_lit_tree(&[(lit![0], 3), (lit![1], 2), (lit![2], 1)]);
        debug_assert_eq!(con.multiplier(), 1);
        debug_assert_eq!(con.offset(), 0);
        debug_assert_eq!(con.divisor(), 1);
        let root = con.id;
        debug_assert_eq!(db[root].depth(), 3);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![3]);

        let mut cnf = Cnf::new();
        db.define_pos(root, 1, &mut cnf, &mut var_manager);
        debug_assert_eq!(cnf.len(), 2);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos(root, 2, &mut cnf, &mut var_manager);
        debug_assert_eq!(cnf.len(), 2);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos(root, 3, &mut cnf, &mut var_manager);
        debug_assert_eq!(cnf.len(), 3);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos(root, 4, &mut cnf, &mut var_manager);
        debug_assert_eq!(cnf.len(), 2);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos(root, 5, &mut cnf, &mut var_manager);
        debug_assert_eq!(cnf.len(), 2);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos(root, 6, &mut cnf, &mut var_manager);
        debug_assert_eq!(cnf.len(), 2);
    }

    #[test]
    fn functions() {
        let mut tot = DbTotalizer::default();
        tot.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        assert_eq!(tot.enforce_ub(2), Err(Error::NotEncoded));
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);
        let mut cnf = Cnf::new();
        tot.encode_ub(0..5, &mut cnf, &mut var_manager);
        assert_eq!(tot.depth(), 3);
        println!("len: {}, {:?}", cnf.len(), cnf);
        assert_eq!(cnf.len(), 14);
        assert_eq!(tot.n_clauses(), 14);
        assert_eq!(tot.n_vars(), 8);
        assert_eq!(tot.enforce_ub(2).unwrap().len(), 1);
    }

    #[test]
    fn functions_min_rhs() {
        let mut tot = DbTotalizer::default();
        tot.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);
        let mut cnf = Cnf::new();
        tot.encode_ub(3..4, &mut cnf, &mut var_manager);
        assert_eq!(tot.depth(), 3);
        assert_eq!(cnf.len(), 3);
        assert_eq!(cnf.len(), tot.n_clauses());
    }

    #[test]
    fn incremental_building_ub() {
        let mut tot1 = DbTotalizer::default();
        tot1.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);
        let mut cnf1 = Cnf::new();
        tot1.encode_ub(0..5, &mut cnf1, &mut var_manager);
        let mut tot2 = DbTotalizer::default();
        tot2.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);
        let mut cnf2 = Cnf::new();
        tot2.encode_ub(0..3, &mut cnf2, &mut var_manager);
        tot2.encode_ub_change(0..5, &mut cnf2, &mut var_manager);
        assert_eq!(cnf1.len(), cnf2.len());
        assert_eq!(cnf1.len(), tot1.n_clauses());
        assert_eq!(cnf2.len(), tot2.n_clauses());
    }

    #[test]
    fn drain() {
        let mut db = TotDb::default();
        let t1 = db.lit_tree(&[lit![0], lit![1], lit![2], lit![3]]);
        let t2 = db.lit_tree(&[lit![4], lit![5], lit![6], lit![7]]);
        let t3 = db.lit_tree(&[lit![8], lit![9], lit![10], lit![11]]);
        db.merge(&[NodeCon::full(t1), NodeCon::full(t3)]);
        db.drain(t1 + 1..=t2).unwrap();
    }
}
