//! # Totalizer Encoding
//!
//! Implementation of the binary adder tree totalizer encoding [1].
//! The implementation is incremental as extended in [2].
//!
//! The implementation is recursive.
//!
//! ## References
//!
//! [1] Olivier Bailleux and Yacine Boufkhad: _Efficient CNF Encoding of Boolean Cardinality Constraints_, CP 2003.
//! [2] Ruben Martins and Saurabh Joshi and Vasco Manquinho and Ines Lynce: _Incremental Cardinality Constraints for MaxSAT_, CP 2014.

use crate::{encodings::BoundType, instances::SatInstance, types::Lit};

pub struct Totalizer {
    /// Input literals already in the tree
    in_lits: Vec<Lit>,
    /// Input literals not yet in the tree
    lit_buffer: Vec<Lit>,
    /// The root of the tree, if constructed
    root: Option<TotNode>,
}

impl Totalizer {
    /// Recursively builds the tree data structure
    fn build_tree(in_lits: &[Lit]) -> TotNode {
        assert_ne!(in_lits.len(), 0);

        if in_lits.len() == 1 {
            return TotNode::new_leaf(in_lits[0]);
        };

        let split = in_lits.len() / 2;
        let left = Totalizer::build_tree(&in_lits[..split]);
        let right = Totalizer::build_tree(&in_lits[split..]);

        TotNode::new_internal(left, right)
    }
}

enum TotNode {
    Leaf {
        /// The input literal to the tree
        lit: Lit,
    },
    Internal {
        /// The output literals of this node
        out_lits: Vec<Lit>,
        /// The path length to leaf furthest away in the subtree
        depth: u64,
        /// The number of clauses this node produced
        n_clauses: u64,
        /// The maximum output this node can have
        max_val: u64,
        /// The maximum right hand side encoded by this node
        max_rhs: u64,
        /// The left child
        left: Box<TotNode>,
        /// The right child
        right: Box<TotNode>,
    },
}

impl TotNode {
    /// Constructs a new leaf node
    fn new_leaf(lit: Lit) -> TotNode {
        TotNode::Leaf { lit }
    }

    /// Constructs a new internal node
    fn new_internal(left: TotNode, right: TotNode) -> TotNode {
        let left_depth = match left {
            TotNode::Leaf { .. } => 0,
            TotNode::Internal { depth, .. } => depth,
        };
        let right_depth = match right {
            TotNode::Leaf { .. } => 0,
            TotNode::Internal { depth, .. } => depth,
        };
        TotNode::Internal {
            out_lits: vec![],
            depth: if left_depth > right_depth {
                left_depth + 1
            } else {
                right_depth + 1
            },
            n_clauses: 0,
            max_rhs: 0,
            max_val: match left {
                TotNode::Leaf { .. } => 1,
                TotNode::Internal { max_val, .. } => max_val,
            } + match right {
                TotNode::Leaf { .. } => 1,
                TotNode::Internal { max_val, .. } => max_val,
            },
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// Encodes the adder from the children to this node up to a given maximum
    /// right hand side. Recurses depth first. Returns the new `next_idx` and
    /// the number of newly added clauses. Always encodes the full totalizer.
    fn encode(&mut self, max_rhs: u64, mut next_idx: usize, bound_type: BoundType) -> SatInstance {
        match self {
            TotNode::Leaf { .. } => return SatInstance::new(),
            TotNode::Internal {
                out_lits,
                max_rhs: smax_rhs,
                max_val,
                n_clauses,
                left,
                right,
                ..
            } => {
                // Ignore all previous encoding and encode from scratch
                *smax_rhs = if max_rhs < *max_val {
                    max_rhs
                } else {
                    *max_val
                };
                // Recurse
                let inst = left.encode(max_rhs, next_idx, bound_type);
                next_idx = inst.next_free_index();
                inst.extend(right.encode(max_rhs, next_idx, bound_type));
                // Reserve vars if needed
                if (out_lits.len() as u64) < *smax_rhs {
                    let max_val = *max_val as usize;
                    out_lits.reserve(max_val - out_lits.len());
                    for _ in out_lits.len()..max_val {
                        let new_lit = Lit::positive(next_idx);
                        next_idx += 1;
                        out_lits.push(new_lit);
                    }
                }
                // Encode adder for current node
                let left_lits = match **left {
                    TotNode::Leaf { lit } => &vec![lit][..],
                    TotNode::Internal { out_lits: lits, .. } => &lits[..],
                };
                let right_lits = match **right {
                    TotNode::Leaf { lit } => &vec![lit][..],
                    TotNode::Internal { out_lits: lits, .. } => &lits[..],
                };
                // Iterate through all value combinations
                for left_val in 0..=left_lits.len() {
                    for right_val in 0..=right_lits.len() {
                        let sum_val = left_val + right_val;
                        if sum_val as u64 > max_rhs + 1 {
                            continue;
                        }
                        // Upper bounding
                        match bound_type {
                            BoundType::UB | BoundType::EQ => {
                                let mut lhs = vec![];
                                if left_val != 0 {
                                    lhs.push(left_lits[left_val - 1]);
                                }
                                if right_val != 0 {
                                    lhs.push(right_lits[right_val - 1]);
                                }
                                if lhs.len() > 0 {
                                    // (left > x) & (right > y) -> (out > x+y)
                                    inst.add_and_impl_lit(lhs, out_lits[sum_val - 1]);
                                    *n_clauses += 1;
                                }
                            }
                            _ => (),
                        };
                        // Lower bounding
                        match bound_type {
                            BoundType::LB | BoundType::EQ => {
                                let mut lhs = vec![];
                                if left_val < left_lits.len() {
                                    lhs.push(!left_lits[left_val]);
                                }
                                if right_val < left_lits.len() {
                                    lhs.push(!right_lits[right_val]);
                                }
                                if lhs.len() > 0 {
                                    // (left <= x) & (right <= y) -> (out <= x+y)
                                    inst.add_and_impl_lit(lhs, !out_lits[sum_val]);
                                    *n_clauses += 1;
                                }
                            }
                            _ => (),
                        };
                    }
                }
                inst
            }
        }
    }

    /// Encodes the adder from the children to this node up to a given maximum
    /// right hand side. Recurses depth first. Returns the new `next_idx` and
    /// the number of newly added clauses. Incrementally only encodes new
    /// clauses.
    fn encode_change(
        &mut self,
        max_rhs: u64,
        next_idx: usize,
        bound_type: BoundType,
    ) -> SatInstance {
    }

    /// Reserves all variables this node might need. This is used if variables
    /// in the totalizer should have consecutive indices. Returns the new
    /// `next_idx`.
    fn reserve_vars(&mut self, mut next_idx: usize) -> usize {
        match self {
            TotNode::Leaf { .. } => next_idx,
            TotNode::Internal {
                out_lits, max_val, ..
            } => {
                let max_val = *max_val as usize;
                out_lits.reserve(max_val - out_lits.len());
                for _ in out_lits.len()..max_val {
                    let new_lit = Lit::positive(next_idx);
                    next_idx += 1;
                    out_lits.push(new_lit);
                }
                next_idx
            }
        }
    }

    /// Reserves all variables this node and the lower subtree might need. This
    /// is used if variables in the totalizer should have consecutive indices.
    /// Returns the new `next_idx`.
    fn reserve_vars_rec(&mut self, mut next_idx: usize) -> usize {
        match self {
            TotNode::Leaf { .. } => return next_idx,
            TotNode::Internal { left, right, .. } => {
                // Recursion
                next_idx = left.reserve_vars_rec(next_idx);
                next_idx = right.reserve_vars_rec(next_idx);
            }
        };
        self.reserve_vars(next_idx)
    }
}
