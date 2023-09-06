//! # Node Database Functionality For Universal Tree-Like Encodings
//!
//! Encodings with a tree-like structure where each node contains a sorted
//! version of its childrens' literals. The leafs are input literals.
//!
//! This is used as the basis for the dynamic polynomial watchdog encoding.
//! (Note that the DPW encoding is not technically tree-like since it might
//! share substructures, but close enough.)

use std::ops::IndexMut;

use crate::types::Lit;

/// An ID of a [`NodeLike`] in a database. The usize is typically the index in a
/// vector of nodes.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(transparent)]
pub struct NodeId(pub usize);

/// Trait for nodes in the tree
pub trait NodeLike {
    /// Returns true if the node is a leaf
    fn is_leaf(&self) -> bool {
        self.len() == 1
    }

    /// Gets the size of the node
    fn len(&self) -> usize;

    /// Gets the connection to the right child
    fn right(&self) -> Option<NodeCon>;

    /// Gets the connection to the left child
    fn left(&self) -> Option<NodeCon>;

    /// Creates a new internal node
    fn internal(len: usize, left: NodeCon, right: NodeCon) -> Self;

    /// Creates a new leaf
    fn leaf(lit: Lit) -> Self;
}

/// A connection to another node.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct NodeCon {
    /// The child node
    pub id: NodeId,
    /// How much the node is offset. The parent will include `(val - offset) /
    /// divisor` in its sum. Negative offsets would be required for the static
    /// polynomial watchdog encoding, but we don't support them as of now.
    pub offset: usize,
    /// The divisor of the connection. The parent will include `(val - offset) /
    /// divisor` in its sum.
    pub divisor: usize,
}

impl NodeCon {
    /// Creates a node connection without any offset or divisor
    pub fn full(id: NodeId) -> NodeCon {
        NodeCon {
            id,
            offset: 0,
            divisor: 1,
        }
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

    /// Getss the number of node in the database
    fn len(&self) -> usize;

    /// Gets the maximum value that a [`NodeCon`] can transmit
    fn max_value(&self, con: NodeCon) -> usize {
        (self[con.id].len() - con.offset) / con.divisor
    }

    /// Recursively build a balanced tree of nodes over literals and returns the
    /// ID of the root
    fn lit_tree(&mut self, lits: &[Lit]) -> NodeId {
        debug_assert!(!lits.is_empty());

        if lits.len() == 1 {
            return self.insert(Self::Node::leaf(lits[0]));
        }

        let split = lits.len() / 2;
        let lid = self.lit_tree(&lits[..split]);
        let rid = self.lit_tree(&lits[split..]);

        self.insert(Self::Node::internal(
            lits.len(),
            NodeCon::full(lid),
            NodeCon::full(rid),
        ))
    }

    /// Recursively merges the given [`NodeCon`]s and returns a [`NodeCon`] to
    /// the root (that will be a full connection, except for if the input is a
    /// single connection). While the merging subtree will be balanced in terms
    /// of nodes, the overall tree might not be.
    fn merge(&mut self, cons: &[NodeCon]) -> NodeCon {
        debug_assert!(!cons.is_empty());

        if cons.len() == 1 {
            return cons[0];
        }

        let split = cons.len() / 2;
        let lcon = self.merge(&cons[..split]);
        let rcon = self.merge(&cons[split..]);

        let len = self.max_value(lcon) + self.max_value(rcon);

        NodeCon::full(self.insert(Self::Node::internal(len, lcon, rcon)))
    }

    /// Recursively merges the given [`NodeCon`]s and returns a [`NodeCon`] to
    /// the root (that will be a full connection, except for if the input is a
    /// single connection). Instead of splitting over the number of nodes, this
    /// splits based on the total value. This results in a tree that is overall
    /// more balanced at the expense of more computation while merging. For a
    /// maximally balanced tree, the input connections should be sorted by
    /// [`NodeById::max_value`].
    fn merge_balanced(&mut self, cons: &[NodeCon]) -> NodeCon {
        debug_assert!(!cons.is_empty());

        if cons.len() == 1 {
            return cons[0];
        }

        let total_sum = cons.iter().fold(0, |sum, &con| sum + self.max_value(con));
        let mut split = 1;
        let mut lsum = self.max_value(cons[0]);
        while lsum + self.max_value(cons[split]) < total_sum / 2 {
            lsum += self.max_value(cons[split]);
            split += 1;
        }

        let lcon = self.merge(&cons[..split]);
        let rcon = self.merge(&cons[split..]);

        let len = self.max_value(lcon) + self.max_value(rcon);

        NodeCon::full(self.insert(Self::Node::internal(len, lcon, rcon)))
    }
}
