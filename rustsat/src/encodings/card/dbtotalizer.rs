//! # Totalizer Encoding Based On a Node Database
//!
//! This is an alternative implementation of the
//! [`rustst::encodings::card::Totalizer`] encoding.

use std::{
    cmp,
    ops::{Index, IndexMut},
};

use crate::{
    encodings::{
        nodedb::{NodeById, NodeCon, NodeId, NodeLike},
        EncodeStats, Error,
    },
    instances::{Cnf, ManageVars},
    types::Lit,
};

use super::{BoundUpper, Encode, EncodeIncremental, BoundUpperIncremental};

/// Implementation of the binary adder tree totalizer encoding \[1\].
/// The implementation is incremental as extended in \[2\].
/// The implementation is based on a node database.
/// For now, this implementation only supports upper bounding.
///
/// # References
///
/// - \[1\] Olivier Bailleux and Yacine Boufkhad: _Efficient CNF Encoding of Boolean Cardinality Constraints_, CP 2003.
/// - \[2\] Ruben Martins and Saurabh Joshi and Vasco Manquinho and Ines Lynce: _Incremental Cardinality Constraints for MaxSAT_, CP 2014.
#[derive(Default)]
pub struct DbTotalizer {
    /// Input literals to the totalizer
    in_lits: Vec<Lit>,
    /// Index of the next literal in [`Totalizer::in_lits`] that is not in the tree yet
    not_enc_idx: usize,
    /// The root of the tree, if constructed
    root: Option<NodeId>,
    /// The number of variables in the totalizer
    n_vars: usize,
    /// The number of clauses in the totalizer
    n_clauses: usize,
    /// The node database of the totalizer
    db: TotDb,
}

impl DbTotalizer {
    fn extend_tree(&mut self) {
        if self.not_enc_idx >= self.in_lits.len() {
            return;
        }
        let new_lits = &self.in_lits[self.not_enc_idx..];
        let new_tree = self.db.lit_tree(new_lits);
        self.root = Some(match self.root {
            Some(old_root) => {
                self.db.merge(&[NodeCon::full(old_root), NodeCon::full(new_tree)])
                    .id
            }
            None => new_tree,
        });
        self.not_enc_idx = self.in_lits.len();
    }
}

impl Encode for DbTotalizer {
    type Iter<'a> = super::totalizer::TotIter<'a>;

    fn iter(&self) -> Self::Iter<'_> {
        self.in_lits.iter().copied()
    }

    fn n_lits(&self) -> usize {
        self.in_lits.len()
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
    fn encode_ub(
        &mut self,
        range: std::ops::Range<usize>,
        var_manager: &mut dyn ManageVars,
    ) -> Cnf {
        if range.is_empty() {
            return Cnf::new();
        }
        self.extend_tree();
        match self.root {
            Some(id) => {
                let n_vars_before = var_manager.n_used();
                let mut cnf = Cnf::new();
                for val in range {
                    self.db.define_pos(id, val + 1, &mut cnf, var_manager, true);
                }
                self.n_clauses += cnf.n_clauses();
                self.n_vars += var_manager.n_used() - n_vars_before;
                cnf
            }
            None => Cnf::new(),
        }
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, Error> {
        if self.not_enc_idx < self.in_lits.len() {
            return Err(Error::NotEncoded);
        }
        if ub >= self.in_lits.len() {
            return Ok(vec![]);
        }
        match self.root {
            Some(id) => Ok(vec![!self.db[id][ub]]),
            None => Err(Error::NotEncoded),
        }
    }
}

impl BoundUpperIncremental for DbTotalizer {
    fn encode_ub_change(&mut self, range: std::ops::Range<usize>, var_manager: &mut dyn ManageVars) -> Cnf {
        if range.is_empty() {
            return Cnf::new();
        }
        self.extend_tree();
        match self.root {
            Some(id) => {
                let n_vars_before = var_manager.n_used();
                let mut cnf = Cnf::new();
                for val in range {
                    self.db.define_pos(id, val + 1, &mut cnf, var_manager, false);
                }
                self.n_clauses += cnf.n_clauses();
                self.n_vars += var_manager.n_used() - n_vars_before;
                cnf
            }
            None => Cnf::new(),
        }
    }
}

impl EncodeStats for DbTotalizer {
    fn n_clauses(&self) -> usize {
        self.n_clauses
    }

    fn n_vars(&self) -> usize {
        self.n_vars
    }
}

impl From<Vec<Lit>> for DbTotalizer {
    fn from(lits: Vec<Lit>) -> Self {
        Self {
            in_lits: lits,
            not_enc_idx: Default::default(),
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
            in_lits: Vec::from_iter(iter),
            not_enc_idx: Default::default(),
            root: Default::default(),
            n_vars: Default::default(),
            n_clauses: Default::default(),
            db: Default::default(),
        }
    }
}

impl Extend<Lit> for DbTotalizer {
    fn extend<T: IntoIterator<Item = Lit>>(&mut self, iter: T) {
        self.in_lits.extend(iter)
    }
}

/// A totalizer adder node
pub enum Node {
    Leaf(Lit),
    Internal(INode),
}

impl NodeLike for Node {
    fn len(&self) -> usize {
        match self {
            Node::Leaf(_) => 1,
            Node::Internal(node) => node.lits.len(),
        }
    }

    fn right(&self) -> Option<NodeCon> {
        match self {
            Node::Leaf(_) => None,
            Node::Internal(node) => Some(node.left),
        }
    }

    fn left(&self) -> Option<NodeCon> {
        match self {
            Node::Leaf(_) => None,
            Node::Internal(node) => Some(node.right),
        }
    }

    fn internal(len: usize, left: NodeCon, right: NodeCon) -> Self {
        Self::Internal(INode::new(len, left, right))
    }

    fn leaf(lit: Lit) -> Self {
        Self::Leaf(lit)
    }
}

impl Node {
    /// Panic-safe version of literal indexing
    fn lit(&self, index: usize) -> Option<&Lit> {
        match self {
            Node::Leaf(lit) => {
                if index != 0 {
                    return None;
                }
                Some(lit)
            }
            Node::Internal(node) => node.lit(index),
        }
    }

    /// Returns the internal node and panics if the node is a leaf
    fn unwrap(&mut self) -> &mut INode {
        match self {
            Node::Leaf(_) => panic!("called unwrap on leaf node"),
            Node::Internal(node) => node,
        }
    }
}

/// Access to output literals. Panics if the literal has not been reserved yet.
impl Index<usize> for Node {
    type Output = Lit;

    fn index(&self, index: usize) -> &Self::Output {
        self.lit(index).unwrap()
    }
}

/// An internal node of the totalizer
pub struct INode {
    pub(super) lits: Vec<LitData>,
    pub(super) left: NodeCon,
    pub(super) right: NodeCon,
}

impl INode {
    fn new(len: usize, left: NodeCon, right: NodeCon) -> Self {
        // Length of node can never change, therefore make sure that the
        let mut lits = vec![];
        lits.reserve_exact(len);
        (0..len).for_each(|_| lits.push(LitData::default()));
        Self { lits, left, right }
    }
}

impl INode {
    /// Panic-safe version of literal indexing
    pub fn lit(&self, index: usize) -> Option<&Lit> {
        self.lits[index].lit()
    }
}

impl Index<usize> for INode {
    type Output = Lit;

    fn index(&self, index: usize) -> &Self::Output {
        self.lit(index).unwrap()
    }
}

/// Data associated with an output literal in a [`Node`]
#[derive(Default)]
pub(super) enum LitData {
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

    fn lit(&self) -> Option<&Lit> {
        match self {
            LitData::None => None,
            LitData::Lit { lit, .. } => Some(lit),
        }
    }
}

/// A totalizer database
#[derive(Default)]
pub(in crate::encodings) struct TotDb {
    /// The node database of the totalizer
    nodes: Vec<Node>,
}

impl NodeById for TotDb {
    type Node = Node;

    fn insert(&mut self, node: Self::Node) -> NodeId {
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
    /// Generates the encoding to define the  output literal encoding that
    /// `val` input literals of node `node_id` are set, if it is not
    /// already defined. Recurses down the tree. The returned literal is the
    /// output literal and the encoding is added to the [`Cnf`]. The encoding is
    /// not returned in order to save on memory allocations.
    fn define_pos(
        &mut self,
        id: NodeId,
        val: usize,
        encoding: &mut Cnf,
        var_manager: &mut dyn ManageVars,
        ignore_encoded: bool,
    ) -> Lit {
        let node = &self[id];
        debug_assert!(val <= node.len());
        debug_assert_ne!(val, 0);
        if node.is_leaf() {
            debug_assert_eq!(val, 1);
            return node[0];
        }
        let lcon = node.left().unwrap();
        let rcon = node.right().unwrap();
        let node = match node {
            Node::Leaf(_) => panic!(),
            Node::Internal(node) => node,
        };

        // Check if already encoded
        if let LitData::Lit { lit, enc_pos, .. } = node.lits[val - 1] {
            if enc_pos && !ignore_encoded {
                return lit;
            }
        }

        // Maximum values that left and right will contribute
        let l_max_val = cmp::min(self.max_value(lcon), val);
        let r_max_val = cmp::min(self.max_value(rcon), val);

        // Encode children (recurse)
        for lval in (cmp::max(val + lcon.offset - r_max_val, 1) * lcon.divisor
            ..(l_max_val * lcon.divisor) + 1)
            .step_by(lcon.divisor)
        {
            self.define_pos(lcon.id, lval, encoding, var_manager, ignore_encoded);
        }
        for rval in (cmp::max(val + rcon.offset - l_max_val, 1) * rcon.divisor
            ..(r_max_val * rcon.divisor) + 1)
            .step_by(rcon.divisor)
        {
            self.define_pos(rcon.id, rval, encoding, var_manager, ignore_encoded);
        }

        // Reserve variable for this node, if needed
        let olit = if let Some(&olit) = self[id].lit(val - 1) {
            olit
        } else {
            let olit = var_manager.new_var().pos_lit();
            self[id].unwrap().lits[val - 1] = LitData::new_lit(olit);
            olit
        };

        // Get reference to literals of children
        let tmp_olit_l;
        let llits = match &self[lcon.id] {
            Node::Leaf(lit) => {
                tmp_olit_l = LitData::new_lit(*lit);
                std::slice::from_ref(&tmp_olit_l)
            }
            Node::Internal(node) => &node.lits[lcon.offset..],
        };
        let tmp_olit_r;
        let rlits = match &self[rcon.id] {
            Node::Leaf(lit) => {
                tmp_olit_r = LitData::new_lit(*lit);
                std::slice::from_ref(&tmp_olit_r)
            }
            Node::Internal(node) => &node.lits[rcon.offset..],
        };

        // Encode this node
        if l_max_val == val {
            encoding.add_lit_impl_lit(*llits[(val * lcon.divisor) - 1].lit().unwrap(), olit);
        }
        if r_max_val == val {
            encoding.add_lit_impl_lit(*rlits[(val * rcon.divisor) - 1].lit().unwrap(), olit);
        }
        let pairs_l_min = cmp::max(val - r_max_val, 1);
        let pairs_l_max = cmp::min(l_max_val + 1, val);
        for lval in pairs_l_min..pairs_l_max {
            let rval = val - lval;
            debug_assert!(rval <= r_max_val);
            let llit = *llits[(lval * lcon.divisor) - 1].lit().unwrap();
            let rlit = *rlits[(rval * rcon.divisor) - 1].lit().unwrap();
            encoding.add_cube_impl_lit(vec![llit, rlit], olit);
        }

        // Mark positive literal as encoded
        match &mut self[id].unwrap().lits[val - 1] {
            LitData::None => panic!(),
            LitData::Lit { enc_pos, .. } => *enc_pos = true,
        };

        olit
    }

    /// Recursively reserves all variables in the subtree rooted at the given node
    fn reserve_vars(&mut self, id: NodeId, var_manager: &mut dyn ManageVars) {
        if self[id].is_leaf() {
            return;
        }

        // Recurse
        self.reserve_vars(self[id].left().unwrap().id, var_manager);
        self.reserve_vars(self[id].right().unwrap().id, var_manager);

        for olit in &mut self[id].unwrap().lits {
            if let LitData::None = olit {
                *olit = LitData::new_lit(var_manager.new_var().pos_lit())
            }
        }
    }
}
