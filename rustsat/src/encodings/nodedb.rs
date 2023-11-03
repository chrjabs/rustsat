//! # Node Database Functionality For Universal Tree-Like Encodings
//!
//! Encodings with a tree-like structure where each node contains a sorted
//! version of its childrens' literals. The leafs are input literals.
//!
//! This is used as the basis for the dynamic polynomial watchdog encoding.
//! (Note that the DPW encoding is not technically tree-like since it might
//! share substructures, but close enough.)

use std::{
    num::{NonZeroU8, NonZeroUsize},
    ops::{Add, AddAssign, IndexMut, RangeBounds, Sub, SubAssign},
};

use crate::types::Lit;

/// An ID of a [`NodeLike`] in a database. The usize is typically the index in a
/// vector of nodes.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
#[repr(transparent)]
pub struct NodeId(pub usize);

impl Add<usize> for NodeId {
    type Output = NodeId;

    fn add(self, rhs: usize) -> Self::Output {
        NodeId(self.0 + rhs)
    }
}

impl Add for &NodeId {
    type Output = NodeId;

    fn add(self, rhs: Self) -> Self::Output {
        NodeId(self.0 + rhs.0)
    }
}

impl Add<usize> for &NodeId {
    type Output = NodeId;

    fn add(self, rhs: usize) -> Self::Output {
        NodeId(self.0 + rhs)
    }
}

impl AddAssign for NodeId {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
    }
}

impl AddAssign<usize> for NodeId {
    fn add_assign(&mut self, rhs: usize) {
        self.0 += rhs;
    }
}

impl Sub for NodeId {
    type Output = usize;

    fn sub(self, rhs: Self) -> Self::Output {
        self.0 - rhs.0
    }
}

impl Sub<usize> for NodeId {
    type Output = NodeId;

    fn sub(self, rhs: usize) -> Self::Output {
        NodeId(self.0 - rhs)
    }
}

impl Sub for &NodeId {
    type Output = NodeId;

    fn sub(self, rhs: Self) -> Self::Output {
        NodeId(self.0 - rhs.0)
    }
}

impl Sub<usize> for &NodeId {
    type Output = NodeId;

    fn sub(self, rhs: usize) -> Self::Output {
        NodeId(self.0 - rhs)
    }
}

impl SubAssign for NodeId {
    fn sub_assign(&mut self, rhs: Self) {
        self.0 -= rhs.0;
    }
}

impl SubAssign<usize> for NodeId {
    fn sub_assign(&mut self, rhs: usize) {
        self.0 -= rhs;
    }
}

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
    pub(crate) offset: usize,
    /// The divisor of the connection. The parent will include `(val - offset) /
    /// divisor * multiplier` in its sum.
    pub(crate) divisor: NonZeroU8,
    /// The multiplier/weight of the connection. The parent will include `(val -
    /// offset) / divisor * multiplier` in its sum.
    pub(crate) multiplier: NonZeroUsize,
    /// Transmit a single literal
    pub(crate) single_lit: bool,
}

impl NodeCon {
    /// Creates a node connection without any offset or divisor
    pub fn full(id: NodeId) -> NodeCon {
        NodeCon {
            id,
            offset: 0,
            divisor: NonZeroU8::new(1).unwrap(),
            multiplier: NonZeroUsize::new(1).unwrap(),
            single_lit: false,
        }
    }

    /// Creates a node connection with a specified weight
    pub fn weighted(id: NodeId, weight: usize) -> NodeCon {
        NodeCon {
            id,
            offset: 0,
            divisor: NonZeroU8::new(1).unwrap(),
            multiplier: weight.try_into().unwrap(),
            single_lit: false,
        }
    }

    #[cfg(feature = "internals")]
    pub fn offset_weighted(id: NodeId, offset: usize, weight: usize) -> NodeCon {
        NodeCon {
            id,
            offset,
            divisor: NonZeroU8::new(1).unwrap(),
            multiplier: weight.try_into().unwrap(),
            single_lit: false,
        }
    }

    /// Creates a connection transmitting a single output literal
    #[cfg(feature = "internals")]
    pub fn single(id: NodeId, output: usize, weight: usize) -> NodeCon {
        NodeCon {
            id,
            offset: output - 1,
            divisor: NonZeroU8::new(1).unwrap(),
            multiplier: weight.try_into().unwrap(),
            single_lit: true,
        }
    }

    #[inline]
    #[cfg(feature = "internals")]
    pub fn reweight(self, weight: usize) -> NodeCon {
        NodeCon {
            multiplier: weight.try_into().unwrap(),
            ..self
        }
    }

    #[inline]
    pub fn offset(&self) -> usize {
        self.offset.into()
    }

    #[inline]
    pub fn divisor(&self) -> usize {
        let div: u8 = self.divisor.into();
        div.into()
    }

    #[inline]
    pub fn multiplier(&self) -> usize {
        self.multiplier.into()
    }

    /// Maps an input value of the connection to its output value
    #[inline]
    pub fn map(&self, val: usize) -> usize {
        if self.single_lit {
            return self.multiplier();
        }
        (val - self.offset()) / self.divisor() * self.multiplier()
    }

    /// Maps an output value of the connection to its input value, rounding down
    #[inline]
    pub fn rev_map(&self, val: usize) -> usize {
        if self.single_lit {
            return self.offset() + 1;
        }
        val / self.multiplier() * self.divisor() + self.offset()
    }

    #[inline]
    pub fn rev_map_round_up(&self, mut val: usize) -> usize {
        if self.single_lit {
            if val < self.multiplier() {
                return self.offset() + 1;
            }
            return self.offset() + 2;
        }
        if val % self.multiplier() > 0 {
            val += self.multiplier();
        }
        self.rev_map(val)
    }

    /// Checks if a value is a possible output value of this connection
    #[inline]
    pub fn is_possible(&self, val: usize) -> bool {
        if self.single_lit {
            return val == self.multiplier();
        }
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
        if con.single_lit {
            return 1;
        }
        (self[con.id].len() - con.offset()) / con.divisor()
    }

    /// The drain iterator for the database
    type Drain<'own>: Iterator<Item = Self::Node>
    where
        Self: 'own;

    /// Drains a range of nodes from the database.
    /// Errors if a node from after the range (first [`Err`] parameter)
    /// references a node in the range (second [`Err`] parameter).
    ///
    /// **Warning**: For this function to preserve a valid database, the
    /// database is not allowed to contain any backwards references from before
    /// the range to the range start or higher.
    fn drain<R: RangeBounds<NodeId>>(
        &mut self,
        range: R,
    ) -> Result<Self::Drain<'_>, (NodeId, NodeId)>;

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
    /// [`NodeById::con_len`].
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
