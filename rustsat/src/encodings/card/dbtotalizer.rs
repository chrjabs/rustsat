//! # Totalizer Encoding Based On a Node Database
//!
//! This is an alternative implementation of the
//! [`rustst::encodings::card::Totalizer`] encoding.

use std::{
    cmp,
    ops::{Index, IndexMut, Range},
};

use crate::{
    encodings::{
        nodedb::{NodeById, NodeCon, NodeId, NodeLike},
        EncodeStats, Error,
    },
    instances::{Cnf, ManageVars},
    types::Lit,
};

use super::{BoundUpper, BoundUpperIncremental, Encode, EncodeIncremental};

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
                self.db
                    .merge(&[NodeCon::full(old_root), NodeCon::full(new_tree)])
                    .id
            }
            None => new_tree,
        });
        self.not_enc_idx = self.in_lits.len();
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
    fn encode_ub(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> Cnf {
        self.db.reset_encoded();
        self.encode_ub_change(range, var_manager)
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
    fn encode_ub_change(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> Cnf {
        if range.is_empty() {
            return Cnf::new();
        }
        self.extend_tree();
        match self.root {
            Some(id) => {
                let n_vars_before = var_manager.n_used();
                let mut cnf = Cnf::new();
                for idx in range {
                    if idx < self.db[id].len() {
                        self.db.define_pos(id, idx, &mut cnf, var_manager);
                    }
                }
                self.n_clauses += cnf.len();
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

    fn depth(&self) -> usize {
        match self {
            Node::Leaf(_) => 1,
            Node::Internal(node) => node.depth,
        }
    }

    fn internal(len: usize, depth: usize, left: NodeCon, right: NodeCon) -> Self {
        Self::Internal(INode::new(len, depth, left, right))
    }

    fn leaf(lit: Lit) -> Self {
        Self::Leaf(lit)
    }
}

impl Node {
    /// Panic-safe version of literal indexing
    pub fn lit(&self, index: usize) -> Option<&Lit> {
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
    pub fn unwrap(&mut self) -> &mut INode {
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
    pub(super) depth: usize,
    pub(super) left: NodeCon,
    pub(super) right: NodeCon,
}

impl INode {
    fn new(len: usize, depth: usize, left: NodeCon, right: NodeCon) -> Self {
        // Length of node can never change, therefore make sure that the
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
    /// Generates the encoding to define the positive output literal with index `idx`, if it is not
    /// already defined. Recurses down the tree. The returned literal is the output literal and the
    /// encoding is added to the [`Cnf`]. The encoding is not returned in order to save on memory
    /// allocations.
    pub fn define_pos(
        &mut self,
        id: NodeId,
        idx: usize,
        encoding: &mut Cnf,
        var_manager: &mut dyn ManageVars,
    ) -> Lit {
        let node = &self[id];
        debug_assert!(idx < node.len());
        if node.is_leaf() {
            debug_assert_eq!(idx, 0);
            return node[0];
        }
        let lcon = node.left().unwrap();
        let rcon = node.right().unwrap();
        let node = match node {
            Node::Leaf(_) => panic!(),
            Node::Internal(node) => node,
        };

        // Check if already encoded
        if let LitData::Lit { lit, enc_pos, .. } = node.lits[idx] {
            if enc_pos {
                return lit;
            }
        }

        let con_idx = |idx: usize, con: NodeCon| ((idx + 1) * con.divisor) - 1 + con.offset;

        // The maximum indices of left and right that influence the current literal (ignoring
        // offset and divisor)
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
            self.define_pos(lcon.id, con_idx(lidx, lcon), encoding, var_manager);
        }
        for ridx in r_min_idx..=r_max_idx {
            self.define_pos(rcon.id, con_idx(ridx, rcon), encoding, var_manager);
        }

        // Reserve variable for this node, if needed
        let olit = if let Some(&olit) = self[id].lit(idx) {
            olit
        } else {
            let olit = var_manager.new_var().pos_lit();
            self[id].unwrap().lits[idx] = LitData::new_lit(olit);
            olit
        };

        // Get reference to literals of children
        let tmp_olit_l;
        let llits = match &self[lcon.id] {
            Node::Leaf(lit) => {
                tmp_olit_l = LitData::new_lit(*lit);
                std::slice::from_ref(&tmp_olit_l)
            }
            Node::Internal(INode { lits, .. }) => lits,
        };
        let tmp_olit_r;
        let rlits = match &self[rcon.id] {
            Node::Leaf(lit) => {
                tmp_olit_r = LitData::new_lit(*lit);
                std::slice::from_ref(&tmp_olit_r)
            }
            Node::Internal(INode { lits, .. }) => lits,
        };

        // Encode this node
        if l_max_idx == idx {
            encoding.add_lit_impl_lit(*llits[con_idx(idx, lcon)].lit().unwrap(), olit);
        }
        if r_max_idx == idx {
            encoding.add_lit_impl_lit(*rlits[con_idx(idx, rcon)].lit().unwrap(), olit);
        }
        for lidx in l_min_idx..cmp::min(l_max_idx + 1, idx) {
            let ridx = idx - lidx - 1;
            debug_assert!(ridx <= r_max_idx);
            let llit = *llits[con_idx(lidx, lcon)].lit().unwrap();
            let rlit = *rlits[con_idx(ridx, rcon)].lit().unwrap();
            encoding.add_cube_impl_lit(vec![llit, rlit], olit);
        }

        // Mark positive literal as encoded
        match &mut self[id].unwrap().lits[idx] {
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

        for olit in &mut self[id].unwrap().lits {
            if let LitData::None = olit {
                *olit = LitData::new_lit(var_manager.new_var().pos_lit())
            }
        }
    }

    /// Resets the status of what has already been encoded
    pub fn reset_encoded(&mut self) {
        for node in &mut self.nodes {
            if let Node::Internal(INode { lits, .. }) = node {
                for lit in lits {
                    if let LitData::Lit { enc_pos, .. } = lit {
                        *enc_pos = false;
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{DbTotalizer, TotDb};
    use crate::{
        encodings::{
            card::{BoundUpper, BoundUpperIncremental},
            nodedb::{NodeById, NodeLike},
            EncodeStats, Error,
        },
        instances::{BasicVarManager, Cnf, ManageVars},
        lit,
        types::{Lit, Var},
        var,
    };

    #[test]
    fn tot_db() {
        let mut db = TotDb::default();
        let root = db.lit_tree(&[lit![0], lit![1], lit![2], lit![3]]);
        debug_assert_eq!(db[root].depth(), 3);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);

        let mut cnf = Cnf::new();
        db.define_pos(root, 0, &mut cnf, &mut var_manager);
        debug_assert_eq!(cnf.len(), 6);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos(root, 1, &mut cnf, &mut var_manager);
        debug_assert_eq!(cnf.len(), 9);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos(root, 2, &mut cnf, &mut var_manager);
        debug_assert_eq!(cnf.len(), 8);

        db.reset_encoded();
        let mut cnf = Cnf::new();
        db.define_pos(root, 3, &mut cnf, &mut var_manager);
        debug_assert_eq!(cnf.len(), 3);
    }

    #[test]
    fn functions() {
        let mut tot = DbTotalizer::default();
        tot.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        assert_eq!(tot.enforce_ub(2), Err(Error::NotEncoded));
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);
        let cnf = tot.encode_ub(0..5, &mut var_manager);
        assert_eq!(tot.depth(), 3);
        println!("len: {}, {:?}", cnf.len(), cnf);
        assert_eq!(cnf.n_clauses(), 14);
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
        let cnf = tot.encode_ub(3..4, &mut var_manager);
        assert_eq!(tot.depth(), 3);
        assert_eq!(cnf.n_clauses(), 3);
        assert_eq!(cnf.n_clauses(), tot.n_clauses());
    }

    #[test]
    fn incremental_building_ub() {
        let mut tot1 = DbTotalizer::default();
        tot1.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);
        let cnf1 = tot1.encode_ub(0..5, &mut var_manager);
        let mut tot2 = DbTotalizer::default();
        tot2.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);
        let mut cnf2 = tot2.encode_ub(0..3, &mut var_manager);
        cnf2.extend(tot2.encode_ub_change(0..5, &mut var_manager));
        assert_eq!(cnf1.n_clauses(), cnf2.n_clauses());
        assert_eq!(cnf1.n_clauses(), tot1.n_clauses());
        assert_eq!(cnf2.n_clauses(), tot2.n_clauses());
    }
}
