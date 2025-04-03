//! # Node Database Functionality For Universal Tree-Like Encodings
//!
//! Encodings with a tree-like structure where each node contains a sorted
//! version of its children's literals. The leaves are input literals.
//!
//! This is used as the basis for the dynamic polynomial watchdog encoding.
//! (Note that the DPW encoding is not technically tree-like since it might
//! share substructures, but close enough.)

use std::{
    cmp, fmt,
    num::{NonZeroU8, NonZeroUsize},
    ops::{self, Add, AddAssign, IndexMut, Range, RangeBounds, Sub, SubAssign},
};

use crate::{types::Lit, utils::unreachable_none};

/// An ID of a [`NodeLike`] in a database. The [`usize`] is typically the index in a
/// vector of nodes.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[repr(transparent)]
pub struct NodeId(pub usize);

impl fmt::Display for NodeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{}", self.0)
    }
}

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
pub trait NodeLike: ops::Index<usize, Output = Lit> {
    /// The type of iterator over the node's values
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

    /// Gets the distance to the leaf furthest away in the sub-tree
    fn depth(&self) -> usize;

    /// Gets the number of leaves in the sub-tree rooted at this node
    fn n_leaves(&self) -> usize;

    /// Creates a new internal node
    fn internal<Db>(left: NodeCon, right: NodeCon, db: &Db) -> Self
    where
        Db: NodeById<Node = Self>;

    /// Creates a new leaf with weight one
    fn leaf(lit: Lit) -> Self;
}

/// A connection to another node.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
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
    /// Transmit a limited number of literals
    pub(crate) len_limit: Option<NonZeroUsize>,
}

impl NodeCon {
    /// Creates a node connection without any offset or divisor
    #[must_use]
    pub fn full(id: NodeId) -> NodeCon {
        NodeCon {
            id,
            offset: 0,
            divisor: unreachable_none!(NonZeroU8::new(1)),
            multiplier: unreachable_none!(NonZeroUsize::new(1)),
            len_limit: None,
        }
    }

    /// Creates a node connection with a specified weight
    ///
    /// # Panics
    ///
    /// If `weight` is 0.
    #[must_use]
    pub fn weighted(id: NodeId, weight: usize) -> NodeCon {
        NodeCon {
            id,
            offset: 0,
            divisor: unreachable_none!(NonZeroU8::new(1)),
            multiplier: weight.try_into().unwrap(),
            len_limit: None,
        }
    }

    /// Creates a node connection that is offset and weighted
    ///
    /// # Panics
    ///
    /// If `weight` is 0.
    #[cfg(any(test, feature = "internals"))]
    #[must_use]
    pub fn offset_weighted(id: NodeId, offset: usize, weight: usize) -> NodeCon {
        NodeCon {
            id,
            offset,
            divisor: unreachable_none!(NonZeroU8::new(1)),
            multiplier: weight.try_into().unwrap(),
            len_limit: None,
        }
    }

    /// Creates a connection transmitting a single output literal
    ///
    /// # Panics
    ///
    /// If `weight` is 0.
    #[cfg(any(test, feature = "internals"))]
    #[must_use]
    pub fn single(id: NodeId, output: usize, weight: usize) -> NodeCon {
        NodeCon {
            id,
            offset: output - 1,
            divisor: unreachable_none!(NonZeroU8::new(1)),
            multiplier: weight.try_into().unwrap(),
            len_limit: NonZeroUsize::new(1),
        }
    }

    /// Creates a connection transmitting a limited number of literals
    ///
    /// # Panics
    ///
    /// - If `weight` is 0
    /// - If `n_lits` is 0
    #[cfg(any(test, feature = "internals"))]
    #[must_use]
    pub fn limited(id: NodeId, offset: usize, n_lits: usize, weight: usize) -> NodeCon {
        assert_ne!(n_lits, 0);
        NodeCon {
            id,
            offset,
            divisor: unreachable_none!(NonZeroU8::new(1)),
            multiplier: weight.try_into().unwrap(),
            len_limit: NonZeroUsize::new(n_lits),
        }
    }

    /// Changes the weight of a node connection
    ///
    /// # Panics
    ///
    /// If `weight` is 0.
    #[inline]
    #[cfg(feature = "internals")]
    #[must_use]
    pub fn reweight(self, weight: usize) -> NodeCon {
        NodeCon {
            multiplier: weight.try_into().unwrap(),
            ..self
        }
    }

    /// Gets the offset of the connection
    #[inline]
    #[must_use]
    pub fn offset(&self) -> usize {
        self.offset
    }

    /// Gets the divisor of the connection
    #[inline]
    #[must_use]
    pub fn divisor(&self) -> usize {
        let div: u8 = self.divisor.into();
        div.into()
    }

    /// Gets the multiplier of the connection
    #[inline]
    #[must_use]
    pub fn multiplier(&self) -> usize {
        self.multiplier.into()
    }

    /// Maps an input value of the connection to its output value
    #[inline]
    #[must_use]
    pub fn map(&self, val: usize) -> usize {
        if val <= self.offset() {
            0
        } else if let Some(limit) = self.len_limit {
            // TODO: this might be incorrect for weighted nodes
            cmp::min((val - self.offset()) / self.divisor(), limit.into()) * self.multiplier()
        } else {
            (val - self.offset()) / self.divisor() * self.multiplier()
        }
    }

    /// Maps an output value of the connection to its input value, rounding down
    #[inline]
    #[must_use]
    pub fn rev_map(&self, val: usize) -> usize {
        if let Some(limit) = self.len_limit {
            // TODO: this might be incorrect for weighted nodes
            match cmp::min(val / self.multiplier(), limit.into()) * self.divisor() {
                0 => 0,
                x => x + self.offset(),
            }
        } else {
            val / self.multiplier() * self.divisor() + self.offset()
        }
    }

    /// Maps an output value of the connection to its input value, ignore the connection length
    /// limit
    #[inline]
    #[must_use]
    #[cfg(any(feature = "internals", feature = "proof-logging"))]
    pub fn rev_map_no_limit(&self, val: usize) -> usize {
        val / self.multiplier() * self.divisor() + self.offset()
    }

    /// Maps an output value of the connection to its input value, rounding up
    #[inline]
    #[must_use]
    pub fn rev_map_round_up(&self, mut val: usize) -> usize {
        if let Some(limit) = self.len_limit {
            if (val - 1) / self.multiplier() >= limit.into() {
                return (Into::<usize>::into(limit) + 1) * self.divisor() + self.offset();
            }
        }
        if val % self.multiplier() > 0 {
            val += self.multiplier();
        }
        self.rev_map(val)
    }

    /// Checks if a value is a possible output value of this connection
    #[inline]
    #[must_use]
    pub fn is_possible(&self, val: usize) -> bool {
        if let Some(limit) = self.len_limit {
            val % self.multiplier() == 0 && val / self.multiplier() <= limit.into()
        } else {
            val % self.multiplier() == 0
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error(
    "node {referencing} from after the drain range references node {referenced} in the drain range"
)]
pub struct DrainError {
    pub referencing: NodeId,
    pub referenced: NodeId,
}

/// Trait for a database managing [`NodeLike`]s by their [`NodeId`]s
#[allow(dead_code)]
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
        let len = (self[con.id].len() - con.offset()) / con.divisor();
        if let Some(limit) = con.len_limit {
            cmp::min(len, limit.into())
        } else {
            len
        }
    }

    /// The drain iterator for the database
    type Drain<'own>: Iterator<Item = Self::Node>
    where
        Self: 'own;

    /// Drains a range of nodes from the database.
    ///
    /// **Warning**: For this function to preserve a valid database, the
    /// database is not allowed to contain any backwards references from before
    /// the range to the range start or higher.
    ///
    /// # Errors
    ///
    /// If a node from after the range references a node in the range.
    fn drain<R: RangeBounds<NodeId>>(&mut self, range: R) -> Result<Self::Drain<'_>, DrainError>;

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
    /// single connection). While the merging sub-tree will be balanced in terms
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

    /// Merges the given connections according to the following strategy: sort
    /// the connections by multiplier, then merge connections with equal
    /// multiplier, then merge resulting connections with
    /// [`NodeById::merge_balanced`].
    #[cfg(feature = "internals")]
    fn merge_thorough(&mut self, cons: &mut [NodeCon]) -> NodeCon
    where
        Self: Sized,
    {
        debug_assert!(!cons.is_empty());
        cons.sort_unstable_by_key(NodeCon::multiplier);

        // Detect sequences of connections of equal weight and merge them
        let mut seg_begin = 0;
        let mut seg_end = 0;
        let mut merged_cons = vec![];
        loop {
            seg_end += 1;
            if seg_end < cons.len() && cons[seg_end].multiplier() == cons[seg_begin].multiplier() {
                continue;
            }
            if seg_end > seg_begin + 1 {
                // merge lits of equal weight
                let mut seg: Vec<_> = cons[seg_begin..seg_end]
                    .iter()
                    .map(|&con| con.reweight(1))
                    .collect();
                seg.sort_unstable_by_key(|&con| self.con_len(con));
                let con = self.merge_balanced(&seg);
                debug_assert_eq!(con.multiplier(), 1);
                merged_cons.push(con.reweight(cons[seg_begin].multiplier()));
            } else {
                merged_cons.push(cons[seg_begin]);
            }
            seg_begin = seg_end;
            if seg_end >= cons.len() {
                break;
            }
        }

        merged_cons.sort_unstable_by_key(|&con| self.con_len(con));
        self.merge_balanced(&merged_cons)
    }

    /// Gets an iterator over the literals at the leaves of the sub-tree rooted at a given node and
    /// the weight with which they appear at the given node
    ///
    /// For connections with an offset or limited length, the output literals of the child are
    /// treated as leaves, in order for certification to work.
    ///
    /// This iterator can not be used if the sub-tree contains connections with a divisor greater
    /// than one.
    fn leaf_iter(&self, node: NodeId) -> LeafIter<'_, Self>
    where
        Self: Sized,
    {
        LeafIter::new(self, node)
    }
}

/// An iterator over the leaves in a given sub-tree
#[derive(Debug)]
pub struct LeafIter<'db, Db> {
    /// The database that the tree is in
    db: &'db Db,
    /// The trace of the iterator. Everything left of the last node in the trace has already been
    /// explored.
    trace: Vec<(NodeId, bool, usize)>,
    /// The range of literals to return as leaves from the current node
    lit_range: Range<usize>,
    /// The weight of the last literal returned from this node
    last_val: usize,
}

impl<'db, Db> LeafIter<'db, Db>
where
    Db: NodeById,
{
    /// Creates a new leaf iterator
    pub fn new(db: &'db Db, root: NodeId) -> Self {
        let mut trace = vec![(root, false, 1)];
        let mut current = root;
        let mut mult = 1;
        let mut lit_range = 1..2;
        let mut last_val = 0;
        while let Some(con) = db[current].left() {
            debug_assert_eq!(con.divisor(), 1);
            mult *= con.multiplier();
            trace.push((con.id, false, mult));
            if con.offset() > 0 || con.len_limit.is_some() {
                lit_range = con.offset() + 1
                    ..con
                        .len_limit
                        .map_or(db[con.id].max_val() + 1, |lim| lim.get() + con.offset() + 1);
                last_val = con.offset();
                break;
            }
            current = con.id;
        }
        Self {
            db,
            trace,
            lit_range,
            last_val,
        }
    }

    fn find_next_leaf_node(&mut self) {
        // find last element in trace to which we moved left
        let mut last = self.trace.len();
        while last > 0 && self.trace[last - 1].1 {
            last -= 1;
        }
        last -= 1;
        // cut of tail from trace
        self.trace.drain(last..);
        if last == 0 {
            // done iterating
            return;
        }
        // Extend trace to next leaf
        let con = unreachable_none!(self.db[self.trace.last().unwrap().0].right());
        let mut mult = unreachable_none!(self.trace.last()).2 * con.multiplier();
        self.trace.push((con.id, true, mult));
        if con.offset() > 0 || con.len_limit.is_some() {
            self.lit_range = con.offset() + 1
                ..con.len_limit.map_or(self.db[con.id].max_val() + 1, |lim| {
                    lim.get() + con.offset() + 1
                });
            self.last_val = con.offset();
            return;
        }
        let mut current = con.id;
        while let Some(con) = self.db[current].left() {
            mult *= con.multiplier();
            self.trace.push((con.id, false, mult));
            if con.offset() > 0 || con.len_limit.is_some() {
                self.lit_range = con.offset() + 1
                    ..con.len_limit.map_or(self.db[con.id].max_val() + 1, |lim| {
                        lim.get() + con.offset() + 1
                    });
                self.last_val = con.offset();
                return;
            }
            current = con.id;
        }
        self.lit_range = 1..2;
        self.last_val = 0;
    }
}

impl<Db> Iterator for LeafIter<'_, Db>
where
    Db: NodeById,
{
    type Item = (Lit, usize);

    fn next(&mut self) -> Option<Self::Item> {
        // get item to yield
        let elem = *self.trace.last()?;

        let (val, elem) = if let Some(val) = self.db[elem.0].vals(self.lit_range.clone()).next() {
            (val, elem)
        } else {
            self.find_next_leaf_node();
            let elem = *self.trace.last()?;
            (
                self.db[elem.0]
                    .vals(self.lit_range.clone())
                    .next()
                    .expect("just progressed to new node, should have next val"),
                elem,
            )
        };
        let lit = self.db[elem.0][val];
        let weight = elem.2 * (val - self.last_val);
        self.lit_range.start = val + 1;
        self.last_val = val;

        Some((lit, weight))
    }
}

#[cfg(test)]
mod tests {
    use super::{NodeCon, NodeId};

    #[test]
    fn node_con_map_full() {
        let id = NodeId(0);
        let nc = NodeCon::full(id);
        for val in 1..=10 {
            debug_assert_eq!(nc.map(val), val);
            debug_assert_eq!(nc.rev_map(val), val);
            debug_assert_eq!(nc.rev_map_round_up(val), val);
        }
    }

    #[test]
    fn node_con_map_mult() {
        let id = NodeId(0);
        let weight = 3;
        let nc = NodeCon::weighted(id, weight);
        for val in 1..=10 {
            debug_assert_eq!(nc.map(val), weight * val);
            debug_assert_eq!(nc.rev_map(val), val / weight);
            debug_assert_eq!(
                nc.rev_map_round_up(val),
                if val % weight == 0 {
                    val / weight
                } else {
                    val / weight + 1
                }
            );
        }
    }

    #[test]
    fn node_con_map_div() {
        let id = NodeId(0);
        let div = 2;
        let nc = NodeCon {
            id,
            offset: 0,
            divisor: div.try_into().unwrap(),
            multiplier: 1.try_into().unwrap(),
            len_limit: None,
        };
        let div: usize = div.into();
        for val in 1..=10 {
            debug_assert_eq!(nc.map(val), val / div);
            debug_assert_eq!(nc.rev_map(val), val * div);
            debug_assert_eq!(nc.rev_map_round_up(val), val * div);
        }
    }

    #[test]
    fn node_con_map_offset_weighted() {
        let id = NodeId(0);
        let offset = 3;
        let weight = 5;
        let nc = NodeCon::offset_weighted(id, offset, weight);
        for val in offset..=10 {
            debug_assert_eq!(nc.map(val), (val - offset) * weight);
            debug_assert_eq!(nc.rev_map(val), val / weight + offset);
            debug_assert_eq!(
                nc.rev_map_round_up(val),
                if val % weight == 0 {
                    val / weight + offset
                } else {
                    val / weight + offset + 1
                }
            );
        }
    }

    #[test]
    fn node_con_map_single() {
        let id = NodeId(0);
        let output = 5;
        let weight = 7;
        let nc = NodeCon::single(id, output, weight);
        for val in output - 1..=20 {
            println!("{val}");
            debug_assert_eq!(nc.map(val), if val >= output { weight } else { 0 });
            debug_assert_eq!(nc.rev_map(val), if val >= weight { output } else { 0 });
            debug_assert_eq!(
                nc.rev_map_round_up(val),
                if val > weight { output + 1 } else { output }
            );
        }
    }

    #[test]
    fn node_con_map_limited() {
        let id = NodeId(0);
        let offset = 2;
        let weight = 3;
        let limit = 5;
        let nc = NodeCon::limited(id, offset, limit, weight);
        for val in offset..=20 {
            println!("{val}");
            debug_assert_eq!(nc.map(val), std::cmp::min(val - offset, limit) * weight);
            debug_assert_eq!(
                nc.rev_map(val),
                if val >= weight {
                    std::cmp::min(val / weight, limit) + offset
                } else {
                    0
                }
            );
            debug_assert_eq!(
                nc.rev_map_round_up(val),
                if val > weight * limit {
                    limit + offset + 1
                } else if val % weight == 0 {
                    val / weight + offset
                } else {
                    val / weight + offset + 1
                }
            );
        }
    }
}
