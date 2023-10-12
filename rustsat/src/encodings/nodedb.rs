//! # Node Database Functionality For Universal Tree-Like Encodings
//!
//! Encodings with a tree-like structure where each node contains a sorted
//! version of its childrens' literals. The leafs are input literals.
//!
//! This is used as the basis for the dynamic polynomial watchdog encoding.
//! (Note that the DPW encoding is not technically tree-like since it might
//! share substructures, but close enough.)

use std::ops::{IndexMut, RangeBounds};

use crate::types::Lit;

/// An ID of a [`NodeLike`] in a database. The usize is typically the index in a
/// vector of nodes.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(transparent)]
pub struct NodeId(pub usize);

/// Trait for nodes in the tree
#[allow(clippy::len_without_is_empty)]
pub trait NodeLike {
    type ValIter: DoubleEndedIterator<Item = usize>;

    /// Returns true if the node is a leaf
    fn is_leaf(&self) -> bool {
        self.len() == 1
    }

    /// Gets the maximum value of the node
    fn max_val(&self) -> usize;

    /// Gets the length (number of outputs) of the node
    fn len(&self) -> usize;

    /// Gets the output values of the node in a given range
    fn vals<R>(&self, range: R) -> Self::ValIter
    where
        R: RangeBounds<usize>;

    /// Gets the connection to the right child
    fn right(&self) -> Option<NodeCon>;

    /// Gets the connection to the left child
    fn left(&self) -> Option<NodeCon>;

    /// Gets the distance to the leaf furthest away in the subtree
    fn depth(&self) -> usize;

    /// Creates a new internal node
    fn internal<Db>(left: NodeCon, right: NodeCon, db: &Db) -> Self
    where
        Db: NodeById<Node = Self>;

    /// Creates a new leaf with weight one
    fn leaf(lit: Lit) -> Self;
}

/// A connection to another node.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct NodeCon {
    /// The child node
    pub id: NodeId,
    /// How much the node is offset. The parent will include `(val - offset) /
    /// divisor * multiplier` in its sum. Negative offsets would be required for
    /// the static polynomial watchdog encoding, but we don't support them as of
    /// now.
    pub offset: u8,
    /// The divisor of the connection. The parent will include `(val - offset) /
    /// divisor * multiplier` in its sum.
    pub divisor: u8,
    /// The multiplier/weight of the connection. The parent will include `(val -
    /// offset) / divisor * multiplier` in its sum.
    pub multiplier: usize,
}

impl NodeCon {
    /// Creates a node connection without any offset or divisor
    pub fn full(id: NodeId) -> NodeCon {
        NodeCon {
            id,
            offset: 0,
            divisor: 1,
            multiplier: 1,
        }
    }

    /// Creates a node connection with a specified weight
    pub fn weighted(id: NodeId, weight: usize) -> NodeCon {
        debug_assert_ne!(weight, 0);
        NodeCon {
            id,
            offset: 0,
            divisor: 1,
            multiplier: weight,
        }
    }

    #[inline]
    pub fn offset(&self) -> usize {
        self.offset.into()
    }

    #[inline]
    pub fn divisor(&self) -> usize {
        self.divisor.into()
    }

    #[inline]
    pub fn multiplier(&self) -> usize {
        self.multiplier
    }

    /// Maps an input value of the connection to its output value
    #[inline]
    pub fn map(&self, val: usize) -> usize {
        (val - self.offset()) / self.divisor() * self.multiplier()
    }

    /// Maps an output value of the connection to its input value
    #[inline]
    pub fn rev_map(&self, val: usize) -> usize {
        val / self.multiplier() * self.divisor() + self.offset()
    }

    #[inline]
    pub fn rev_map_round_up(&self, mut val: usize) -> usize {
        if val % self.multiplier() > 0 {
            val += self.multiplier();
        }
        val / self.multiplier() * self.divisor() + self.offset()
    }

    /// Checks if a value is a possible output value of this connection
    #[inline]
    pub fn is_possible(&self, val: usize) -> bool {
        val % self.multiplier() == 0
    }
}

/// Trait for a database managing [`NodeLike`]s by their [`NodeId`]s
pub trait NodeById: IndexMut<NodeId, Output = Self::Node> {
    /// The type of node in the database
    type Node: NodeLike;

    /// Inserts a new node in the database and gets its ID
    fn insert(&mut self, node: Self::Node) -> NodeId;

    /// An iterator over nodes in order of [`NodeId`]
    type Iter<'own>: Iterator<Item = &'own Self::Node>
    where
        Self: 'own;

    /// Gets an iterator over references to the nodes. The nodes are iterated in
    /// order of [`NodeId`].    
    fn iter(&self) -> Self::Iter<'_>;

    /// Gets the number of node in the database
    fn len(&self) -> usize;

    /// Checks if the database is empty
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Gets the number of literals that a [`NodeCon`] transmits.
    fn con_len(&self, con: NodeCon) -> usize {
        (self[con.id].len() - con.offset()) / con.divisor()
    }

    /// Recursively builds a balanced tree of nodes over literals and returns the
    /// ID of the root
    fn lit_tree(&mut self, lits: &[Lit]) -> NodeId
    where
        Self: Sized,
    {
        debug_assert!(!lits.is_empty());

        if lits.len() == 1 {
            return self.insert(Self::Node::leaf(lits[0]));
        }

        let split = lits.len() / 2;
        let lid = self.lit_tree(&lits[..split]);
        let rid = self.lit_tree(&lits[split..]);

        self.insert(Self::Node::internal(
            NodeCon::full(lid),
            NodeCon::full(rid),
            self,
        ))
    }

    /// Recursively builds a balanced tree of nodes over weighted literals and
    /// returns a [`NodeCon`] to the root (that will be a fill connection,
    /// except for if all input literals have equal weight). Works best if
    /// literals are sorted by weight.
    fn weighted_lit_tree(&mut self, lits: &[(Lit, usize)]) -> NodeCon
    where
        Self: Sized,
    {
        debug_assert!(!lits.is_empty());

        // Detect sequences of literals of equal weight and merge them
        let mut seg_begin = 0;
        let mut seg_end = 0;
        let mut cons = vec![];
        loop {
            seg_end += 1;
            if seg_end < lits.len() && lits[seg_end].1 == lits[seg_begin].1 {
                continue;
            }
            // merge lits of equal weight
            let seg: Vec<_> = lits[seg_begin..seg_end]
                .iter()
                .map(|(lit, _)| *lit)
                .collect();
            let id = self.lit_tree(&seg);
            cons.push(NodeCon::weighted(id, lits[seg_begin].1));
            seg_begin = seg_end;
            if seg_end >= lits.len() {
                break;
            }
        }
        // Merge totalizers
        self.merge_balanced(&cons)
    }

    /// Recursively merges the given [`NodeCon`]s and returns a [`NodeCon`] to
    /// the root (that will be a full connection, except for if the input is a
    /// single connection). While the merging subtree will be balanced in terms
    /// of nodes, the overall tree might not be.
    fn merge(&mut self, cons: &[NodeCon]) -> NodeCon
    where
        Self: Sized,
    {
        debug_assert!(!cons.is_empty());

        if cons.len() == 1 {
            return cons[0];
        }

        let split = cons.len() / 2;
        let lcon = self.merge(&cons[..split]);
        let rcon = self.merge(&cons[split..]);

        NodeCon::full(self.insert(Self::Node::internal(lcon, rcon, self)))
    }

    /// Recursively merges the given [`NodeCon`]s and returns a [`NodeCon`] to
    /// the root (that will be a full connection, except for if the input is a
    /// single connection). Instead of splitting over the number of nodes, this
    /// splits based on the total value. This results in a tree that is overall
    /// more balanced at the expense of more computation while merging. For a
    /// maximally balanced tree, the input connections should be sorted by
    /// [`NodeById::max_value`].
    fn merge_balanced(&mut self, cons: &[NodeCon]) -> NodeCon
    where
        Self: Sized,
    {
        debug_assert!(!cons.is_empty());

        if cons.len() == 1 {
            return cons[0];
        }

        let total_sum = cons.iter().fold(0, |sum, &con| sum + self.con_len(con));
        let mut split = 1;
        let mut lsum = self.con_len(cons[0]);
        while lsum + self.con_len(cons[split]) < total_sum / 2 {
            lsum += self.con_len(cons[split]);
            split += 1;
        }

        let lcon = self.merge(&cons[..split]);
        let rcon = self.merge(&cons[split..]);

        NodeCon::full(self.insert(Self::Node::internal(lcon, rcon, self)))
    }
}
