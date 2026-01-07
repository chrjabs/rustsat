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
    ops::{self, Add, AddAssign, IndexMut, RangeBounds, Sub, SubAssign},
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
    #[cfg_attr(feature = "_internals", visibility::make(pub))]
    #[must_use]
    pub(crate) fn offset_weighted(id: NodeId, offset: usize, weight: usize) -> NodeCon {
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
    #[cfg(any(test, feature = "_internals"))]
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
    #[cfg(any(test, feature = "_internals"))]
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
    #[cfg(feature = "_internals")]
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
    #[cfg(any(feature = "_internals", feature = "proof-logging"))]
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

    /// Builds a balanced tree of nodes over literals and returns the
    /// ID of the root
    fn lit_tree<I>(&mut self, lits: I) -> Option<NodeId>
    where
        I: IntoIterator<Item = Lit>,
        Self: Sized,
    {
        // binextend-style non-recursive building of the tree
        // https://github.com/Froleyks/binextend

        let mut cons: Vec<_> = lits
            .into_iter()
            .map(|l| NodeCon::full(self.insert(Self::Node::leaf(l))))
            .collect();

        let con = self.merge(&mut cons)?;

        debug_assert_eq!(con.offset(), 0);
        debug_assert_eq!(con.divisor(), 1);
        debug_assert_eq!(con.multiplier(), 1);

        Some(con.id)
    }

    /// Builds a balanced tree of nodes over weighted literals and
    /// returns a [`NodeCon`] to the root (that will be a fill connection,
    /// except for if all input literals have equal weight). Works best if
    /// literals are sorted by weight.
    fn weighted_lit_tree(&mut self, lits: &[(Lit, usize)]) -> Option<NodeCon>
    where
        Self: Sized,
    {
        debug_assert!(!lits.is_empty());

        // Detect sequences of literals of equal weight and merge them
        let mut seg_begin = 0;
        let mut cons = vec![];
        for seg_end in 1..lits.len() {
            if lits[seg_end].1 == lits[seg_begin].1 {
                continue;
            }
            // merge lits of equal weight
            let seg = lits[seg_begin..seg_end].iter().map(|&(lit, _)| lit);
            let id = self.lit_tree(seg).unwrap();
            cons.push(NodeCon::weighted(id, lits[seg_begin].1));
            seg_begin = seg_end;
        }
        let seg = lits[seg_begin..].iter().map(|&(lit, _)| lit);
        let id = self.lit_tree(seg).unwrap();
        cons.push(NodeCon::weighted(id, lits[seg_begin].1));
        // Merge totalizers
        self.merge_balanced(&cons)
    }

    /// Merges the given [`NodeCon`]s and returns a [`NodeCon`] to
    /// the root (that will be a full connection, except for if the input is a
    /// single connection). While the merging sub-tree will be balanced in terms
    /// of nodes, the overall tree might not be.
    ///
    /// For efficiency reasons, this modifies the slice in place.
    fn merge(&mut self, cons: &mut [NodeCon]) -> Option<NodeCon>
    where
        Self: Sized,
    {
        // binextend-style non-recursive building of the tree
        // https://github.com/Froleyks/binextend

        if cons.is_empty() {
            return None;
        }
        assert!(
            cons.len() < isize::MAX.unsigned_abs(),
            "due to bit operations the number of literals must be at most `isize::MAX`"
        );

        let mut reverse_width = 0;
        let mut width = cons.len();
        while width > 1 {
            reverse_width = (reverse_width << 1) | (width & 1);
            width /= 2;
        }

        debug_assert_eq!(width, 1);
        #[allow(clippy::cast_possible_wrap)]
        let mut reverse_width = reverse_width as isize;
        let mut last_reverse_width = reverse_width << 1;

        while width <= cons.len() {
            let mut start = 0;
            let mut split_idx = 1;
            while start < cons.len() {
                let extend = (split_idx & -split_idx & reverse_width) != 0;
                let true_width = width + usize::from(extend);
                if true_width == 1 {
                    split_idx += 1;
                    start += 1;
                    continue;
                }
                if true_width % 2 == 0 {
                    let lcon = cons[start];
                    let rcon = cons[start + true_width / 2];
                    cons[start] = if lcon.multiplier() > 1 && lcon.multiplier() == rcon.multiplier()
                    {
                        let weight = lcon.multiplier();
                        let lcon = NodeCon {
                            multiplier: unreachable_none!(NonZeroUsize::new(1)),
                            ..lcon
                        };
                        let rcon = NodeCon {
                            multiplier: unreachable_none!(NonZeroUsize::new(1)),
                            ..rcon
                        };
                        NodeCon::weighted(
                            self.insert(Self::Node::internal(lcon, rcon, self)),
                            weight,
                        )
                    } else {
                        NodeCon::full(self.insert(Self::Node::internal(lcon, rcon, self)))
                    };
                } else {
                    let left_child_split_idx = (split_idx - 1) * 2 + 1;
                    let left_child_extend =
                        (left_child_split_idx & -left_child_split_idx & last_reverse_width) != 0;
                    let lcon = cons[start];
                    let rcon = cons[start + true_width / 2 + usize::from(left_child_extend)];
                    cons[start] = if lcon.multiplier() > 1 && lcon.multiplier() == rcon.multiplier()
                    {
                        let weight = lcon.multiplier();
                        let lcon = NodeCon {
                            multiplier: unreachable_none!(NonZeroUsize::new(1)),
                            ..lcon
                        };
                        let rcon = NodeCon {
                            multiplier: unreachable_none!(NonZeroUsize::new(1)),
                            ..rcon
                        };
                        NodeCon::weighted(
                            self.insert(Self::Node::internal(lcon, rcon, self)),
                            weight,
                        )
                    } else {
                        NodeCon::full(self.insert(Self::Node::internal(lcon, rcon, self)))
                    };
                }
                split_idx += 1;
                start += true_width;
            }
            #[allow(clippy::cast_sign_loss)]
            {
                width = (width << 1) | (reverse_width as usize & 1);
            }
            reverse_width >>= 1;
            last_reverse_width >>= 1;
        }

        debug_assert_eq!(width, cons.len() * 2);

        Some(cons[0])
    }

    /// Recursively merges the given [`NodeCon`]s and returns a [`NodeCon`] to
    /// the root (that will be a full connection, except for if the input is a
    /// single connection). Instead of splitting over the number of nodes, this
    /// splits based on the total value. This results in a tree that is overall
    /// more balanced at the expense of more computation while merging. For a
    /// maximally balanced tree, the input connections should be sorted by
    /// [`NodeById::con_len`].
    fn merge_balanced(&mut self, cons: &[NodeCon]) -> Option<NodeCon>
    where
        Self: Sized,
    {
        if cons.is_empty() {
            return None;
        }

        let cum_weight = cons
            .iter()
            .fold(Vec::with_capacity(cons.len()), |mut cum_weight, con| {
                cum_weight.push(cum_weight.last().copied().unwrap_or(0) + self.con_len(*con));
                cum_weight
            });
        Some(merge_balanced_recursive(self, cons, &cum_weight, 0))
    }

    /// Merges the given connections according to the following strategy: sort
    /// the connections by multiplier, then merge connections with equal
    /// multiplier, then merge resulting connections with
    /// [`NodeById::merge_balanced`].
    #[cfg(feature = "_internals")]
    fn merge_thorough(&mut self, cons: &mut [NodeCon]) -> Option<NodeCon>
    where
        Self: Sized,
    {
        if cons.is_empty() {
            return None;
        }
        cons.sort_unstable_by_key(NodeCon::multiplier);

        // Detect sequences of connections of equal weight and merge them
        let mut seg_begin = 0;
        let mut merged_cons = vec![];
        for seg_end in 1..cons.len() {
            if cons[seg_end].multiplier() == cons[seg_begin].multiplier() {
                continue;
            }
            if seg_end > seg_begin + 1 {
                // merge lits of equal weight
                let mut seg: Vec<_> = cons[seg_begin..seg_end]
                    .iter()
                    .map(|&con| con.reweight(1))
                    .collect();
                seg.sort_unstable_by_key(|&con| self.con_len(con));
                let con = self.merge_balanced(&seg).unwrap();
                debug_assert_eq!(con.multiplier(), 1);
                merged_cons.push(con.reweight(cons[seg_begin].multiplier()));
            } else {
                merged_cons.push(cons[seg_begin]);
            }
            seg_begin = seg_end;
        }
        if cons.len() > seg_begin + 1 {
            // merge lits of equal weight
            let mut seg: Vec<_> = cons[seg_begin..]
                .iter()
                .map(|&con| con.reweight(1))
                .collect();
            seg.sort_unstable_by_key(|&con| self.con_len(con));
            let con = self.merge_balanced(&seg).unwrap();
            debug_assert_eq!(con.multiplier(), 1);
            merged_cons.push(con.reweight(cons[seg_begin].multiplier()));
        } else {
            merged_cons.push(cons[seg_begin]);
        }

        merged_cons.sort_unstable_by_key(|&con| self.con_len(con));
        self.merge_balanced(&merged_cons)
    }

    /// Gets an iterator over the leaf nodes of the sub-tree rooted at a given node. For each leaf
    /// node, the [`NodeId`], the weight, offset, and length limit are returned.
    ///
    /// Nodes that are connected with an offset or limited length are considered as leaves, in
    /// order for certification to work.
    ///
    /// This iterator can not be used if the sub-tree contains connections with a divisor greater
    /// than one.
    #[cfg(any(feature = "_internals", feature = "proof-logging"))]
    fn leaf_iter(&self, node: NodeId) -> LeafIter<'_, Self>
    where
        Self: Sized,
    {
        LeafIter::new(self, node)
    }
}

fn merge_balanced_recursive<NDb>(
    db: &mut NDb,
    cons: &[NodeCon],
    cum_weight: &[usize],
    offset: usize,
) -> NodeCon
where
    NDb: NodeById,
{
    debug_assert!(!cons.is_empty());

    if cons.len() == 1 {
        return cons[0];
    }

    let threshold = (cum_weight[cum_weight.len() - 1] - offset) / 2 + offset;
    let (split, _) = cum_weight
        .iter()
        .enumerate()
        .skip(1)
        .find(|&(_, &val)| val >= threshold)
        .unwrap();

    let lcon = merge_balanced_recursive(db, &cons[..split], &cum_weight[..split], offset);
    let rcon = merge_balanced_recursive(
        db,
        &cons[split..],
        &cum_weight[split..],
        cum_weight[split - 1],
    );

    if lcon.multiplier() > 1 && lcon.multiplier() == rcon.multiplier() {
        let weight = lcon.multiplier();
        let lcon = NodeCon {
            multiplier: unreachable_none!(NonZeroUsize::new(1)),
            ..lcon
        };
        let rcon = NodeCon {
            multiplier: unreachable_none!(NonZeroUsize::new(1)),
            ..rcon
        };
        NodeCon::weighted(db.insert(NDb::Node::internal(lcon, rcon, db)), weight)
    } else {
        NodeCon::full(db.insert(NDb::Node::internal(lcon, rcon, db)))
    }
}

/// An iterator over the leaves in a given sub-tree
#[derive(Debug)]
#[cfg(any(feature = "_internals", feature = "proof-logging"))]
pub struct LeafIter<'db, Db> {
    /// The database that the tree is in
    db: &'db Db,
    /// The trace of the iterator. Everything left of the last node in the trace has already been
    /// explored.
    trace: Vec<(NodeId, bool, usize)>,
    /// The range of values to consider for the current node
    val_range: std::ops::Range<usize>,
}

#[cfg(any(feature = "_internals", feature = "proof-logging"))]
impl<'db, Db> LeafIter<'db, Db>
where
    Db: NodeById,
{
    /// Creates a new leaf iterator
    pub fn new(db: &'db Db, root: NodeId) -> Self {
        let mut trace = vec![(root, false, 1)];
        let mut current = root;
        let mut mult = 1;
        let mut val_range = 1..2;
        while let Some(con) = db[current].left() {
            debug_assert_eq!(con.divisor(), 1);
            mult *= con.multiplier();
            trace.push((con.id, false, mult));
            if con.offset() > 0 || con.len_limit.is_some() {
                val_range = con.offset() + 1
                    ..con
                        .len_limit
                        .map_or(db[con.id].max_val() + 1, |lim| lim.get() + con.offset() + 1);
                break;
            }
            current = con.id;
        }
        Self {
            db,
            trace,
            val_range,
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
            self.val_range = con.offset() + 1
                ..con.len_limit.map_or(self.db[con.id].max_val() + 1, |lim| {
                    lim.get() + con.offset() + 1
                });
            return;
        }
        let mut current = con.id;
        while let Some(con) = self.db[current].left() {
            mult *= con.multiplier();
            self.trace.push((con.id, false, mult));
            if con.offset() > 0 || con.len_limit.is_some() {
                self.val_range = con.offset() + 1
                    ..con.len_limit.map_or(self.db[con.id].max_val() + 1, |lim| {
                        lim.get() + con.offset() + 1
                    });
                return;
            }
            current = con.id;
        }
        self.val_range = 1..2;
    }

    /// Gets an iterator over the weighted literals at the leaf nodes
    pub fn lits(self) -> LeafLitIter<'db, Db> {
        LeafLitIter::new(self)
    }
}

/// Information about a (pseudo) leaf for a sub-tree
#[derive(Debug, Clone)]
#[cfg(any(feature = "_internals", feature = "proof-logging"))]
pub struct LeafInfo {
    /// The id of the leaf
    pub id: NodeId,
    /// The multiplier for the leaf
    pub weight: usize,
    /// The value range considered for the given leaf node
    pub val_range: std::ops::Range<usize>,
}

#[cfg(any(feature = "_internals", feature = "proof-logging"))]
impl<Db> Iterator for LeafIter<'_, Db>
where
    Db: NodeById,
{
    type Item = LeafInfo;

    fn next(&mut self) -> Option<Self::Item> {
        // get item to yield
        let elem = *self.trace.last()?;

        let info = LeafInfo {
            id: elem.0,
            weight: elem.2,
            val_range: self.val_range.clone(),
        };

        self.find_next_leaf_node();

        Some(info)
    }
}

#[derive(Debug)]
#[cfg(any(feature = "_internals", feature = "proof-logging"))]
pub struct LeafLitIter<'db, Db> {
    leaves: LeafIter<'db, Db>,
    current: LeafInfo,
    last_val: usize,
}

#[cfg(any(feature = "_internals", feature = "proof-logging"))]
impl<'db, Db> LeafLitIter<'db, Db>
where
    Db: NodeById,
{
    fn new(leaves: LeafIter<'db, Db>) -> Self {
        Self {
            leaves,
            current: LeafInfo {
                id: NodeId(0),
                weight: 0,
                val_range: 0..0,
            },
            last_val: 0,
        }
    }
}

#[cfg(any(feature = "_internals", feature = "proof-logging"))]
impl<Db> Iterator for LeafLitIter<'_, Db>
where
    Db: NodeById,
{
    type Item = (Lit, usize);

    fn next(&mut self) -> Option<Self::Item> {
        if self.current.val_range.is_empty() {
            self.current = self.leaves.next()?;
            self.last_val = self.current.val_range.start - 1;
        }
        let val = loop {
            let Some(val) = self.leaves.db[self.current.id]
                .vals(self.current.val_range.clone())
                .next()
            else {
                self.current = self.leaves.next()?;
                self.last_val = self.current.val_range.start - 1;
                continue;
            };
            break val;
        };
        let lit = self.leaves.db[self.current.id][val];
        let weight = self.current.weight * (val - self.last_val);
        self.current.val_range.start = val + 1;
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
