//! # Totalizer Encoding
//!
//! Implementation of the binary adder tree totalizer encoding \[1\].
//! The implementation is incremental as extended in \[2\].
//! The implementation is recursive.
//!
//! ## References
//!
//! - \[1\] Olivier Bailleux and Yacine Boufkhad: _Efficient CNF Encoding of Boolean Cardinality Constraints_, CP 2003.
//! - \[2\] Ruben Martins and Saurabh Joshi and Vasco Manquinho and Ines Lynce: _Incremental Cardinality Constraints for MaxSAT_, CP 2014.

use super::{BoundType, EncodeCard, EncodingError, IncEncodeCard};
use crate::{
    instances::{ManageVars, CNF},
    types::Lit,
};
use std::slice;

/// Implementation of the binary adder tree totalizer encoding \[1\].
/// The implementation is incremental as extended in \[2\].
/// The implementation is recursive.
///
/// # References
///
/// - \[1\] Olivier Bailleux and Yacine Boufkhad: _Efficient CNF Encoding of Boolean Cardinality Constraints_, CP 2003.
/// - \[2\] Ruben Martins and Saurabh Joshi and Vasco Manquinho and Ines Lynce: _Incremental Cardinality Constraints for MaxSAT_, CP 2014.
pub struct Totalizer {
    /// Input literals already in the tree
    in_lits: Vec<Lit>,
    /// Input literals not yet in the tree
    lit_buffer: Vec<Lit>,
    /// The root of the tree, if constructed
    root: Option<Box<Node>>,
    /// The bound type that the totalizer encodes
    bound_type: BoundType,
    /// Whether or not to reserve all variables when constructing the tree
    reserve_vars: bool,
}

impl Totalizer {
    /// Recursively builds the tree data structure
    fn build_tree(lits: &[Lit]) -> Node {
        assert_ne!(lits.len(), 0);

        if lits.len() == 1 {
            return Node::new_leaf(lits[0]);
        };

        let split = lits.len() / 2;
        let left = Totalizer::build_tree(&lits[..split]);
        let right = Totalizer::build_tree(&lits[split..]);

        Node::new_internal(left, right)
    }

    /// Extends the tree at the root node with added literals
    fn extend_tree<VM: ManageVars>(&mut self, var_manager: &mut VM) {
        if !self.lit_buffer.is_empty() {
            let n_in_tree = self.in_lits.len();
            self.in_lits.extend(&self.lit_buffer);
            let mut subtree = Totalizer::build_tree(&self.in_lits[n_in_tree..]);
            if self.reserve_vars {
                subtree.reserve_all_vars_rec(var_manager, &self.bound_type);
            }
            self.root = match self.root.take() {
                None => Some(Box::new(subtree)),
                Some(old_root) => {
                    let mut new_root = Node::new_internal(*old_root, subtree);
                    if self.reserve_vars {
                        new_root.reserve_all_vars(var_manager, &self.bound_type)
                    };
                    Some(Box::new(new_root))
                }
            };
            self.lit_buffer.clear();
        }
    }

    /// Gets the maximum depth of the tree
    pub fn get_depth(&mut self) -> usize {
        match &self.root {
            None => 0,
            Some(root_node) => root_node.get_depth(),
        }
    }
}

impl EncodeCard for Totalizer {
    fn new(bound_type: BoundType) -> Result<Self, EncodingError> {
        Ok(Totalizer {
            in_lits: vec![],
            lit_buffer: vec![],
            root: None,
            bound_type,
            reserve_vars: false,
        })
    }

    fn add(&mut self, lits: Vec<Lit>) {
        self.lit_buffer.extend(lits);
    }

    fn encode<VM: ManageVars>(&mut self, max_rhs: usize, var_manager: &mut VM) -> CNF {
        self.extend_tree(var_manager);
        match &mut self.root {
            None => CNF::new(),
            Some(root) => root.encode_rec(max_rhs, var_manager, &self.bound_type),
        }
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, EncodingError> {
        match self.bound_type {
            BoundType::LB => Err(EncodingError::NoObjectSupport),
            _ => {
                if !self.lit_buffer.is_empty() {
                    return Err(EncodingError::NotEncoded);
                };
                if ub >= self.in_lits.len() {
                    return Ok(vec![]);
                };
                match &self.root {
                    None => Err(EncodingError::NotEncoded),
                    Some(root_node) => match &**root_node {
                        Node::Leaf { lit } => Ok(vec![!*lit]),
                        Node::Internal {
                            out_lits, max_rhs, ..
                        } => {
                            if let Some(mr) = max_rhs {
                                if *mr < ub {
                                    Err(EncodingError::NotEncoded)
                                } else {
                                    Ok(vec![!out_lits[ub]])
                                }
                            } else {
                                Err(EncodingError::NotEncoded)
                            }
                        }
                    },
                }
            }
        }
    }

    fn enforce_lb(&self, lb: usize) -> Result<Vec<Lit>, EncodingError> {
        match self.bound_type {
            BoundType::UB => Err(EncodingError::NoObjectSupport),
            _ => {
                if !self.lit_buffer.is_empty() {
                    return Err(EncodingError::NotEncoded);
                };
                if lb > self.in_lits.len() {
                    return Err(EncodingError::Unsat);
                } else if lb == 0 {
                    return Ok(vec![]);
                };
                match &self.root {
                    None => Err(EncodingError::NotEncoded),
                    Some(root_node) => match &**root_node {
                        Node::Leaf { lit } => Ok(vec![*lit]),
                        Node::Internal {
                            out_lits, max_rhs, ..
                        } => {
                            if let Some(mr) = max_rhs {
                                if *mr < lb {
                                    Err(EncodingError::NotEncoded)
                                } else {
                                    Ok(vec![out_lits[lb - 1]])
                                }
                            } else {
                                Err(EncodingError::NotEncoded)
                            }
                        }
                    },
                }
            }
        }
    }
}

impl IncEncodeCard for Totalizer {
    fn new_reserving(bound_type: BoundType) -> Result<Self, EncodingError> {
        Ok(Totalizer {
            in_lits: vec![],
            lit_buffer: vec![],
            root: None,
            bound_type,
            reserve_vars: true,
        })
    }

    fn encode_change<VM: ManageVars>(&mut self, max_rhs: usize, var_manager: &mut VM) -> CNF {
        self.extend_tree(var_manager);
        match &mut self.root {
            None => CNF::new(),
            Some(root) => root.encode_change_rec(max_rhs, var_manager, &self.bound_type),
        }
    }
}

enum Node {
    Leaf {
        /// The input literal to the tree
        lit: Lit,
    },
    Internal {
        /// The output literals of this node
        out_lits: Vec<Lit>,
        /// The path length to the leaf furthest away in the subtree
        depth: usize,
        /// The number of clauses this node produced
        n_clauses: usize,
        /// The maximum output this node can have
        max_val: usize,
        /// The maximum right hand side encoded by this node
        max_rhs: Option<usize>,
        /// The left child
        left: Box<Node>,
        /// The right child
        right: Box<Node>,
    },
}

impl Node {
    /// Constructs a new leaf node
    fn new_leaf(lit: Lit) -> Node {
        Node::Leaf { lit }
    }

    /// Constructs a new internal node
    fn new_internal(left: Node, right: Node) -> Node {
        let left_depth = match left {
            Node::Leaf { .. } => 1,
            Node::Internal { depth, .. } => depth,
        };
        let right_depth = match right {
            Node::Leaf { .. } => 1,
            Node::Internal { depth, .. } => depth,
        };
        Node::Internal {
            out_lits: vec![],
            depth: if left_depth > right_depth {
                left_depth + 1
            } else {
                right_depth + 1
            },
            n_clauses: 0,
            max_rhs: None,
            max_val: match left {
                Node::Leaf { .. } => 1,
                Node::Internal { max_val, .. } => max_val,
            } + match right {
                Node::Leaf { .. } => 1,
                Node::Internal { max_val, .. } => max_val,
            },
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// Gets the maximum depth of the subtree rooted in this node
    fn get_depth(&self) -> usize {
        match self {
            Node::Leaf { .. } => 1,
            Node::Internal { depth, .. } => *depth,
        }
    }

    /// Encodes the adder for this node from right hand side values `min` to `max`.
    /// This method only produces the encoding and does _not_ change any of the stats of the node.
    fn encode_from_till<VM: ManageVars>(
        &mut self,
        min_rhs: usize,
        max_rhs: usize,
        var_manager: &mut VM,
        bound_type: &BoundType,
    ) -> CNF {
        // Reserve vars if needed
        self.reserve_vars_till(max_rhs, var_manager, bound_type);
        match self {
            Node::Leaf { .. } => return CNF::new(),
            Node::Internal {
                out_lits,
                max_val,
                left,
                right,
                ..
            } => {
                if min_rhs > *max_val {
                    return CNF::new();
                };
                let max_rhs = if max_rhs > *max_val {
                    *max_val
                } else {
                    max_rhs
                };
                // Encode adder for current node
                let mut cnf = CNF::new();
                let left_lits = match &**left {
                    Node::Leaf { lit } => slice::from_ref(lit),
                    Node::Internal { out_lits, .. } => &out_lits[..],
                };
                let right_lits = match &**right {
                    Node::Leaf { lit } => slice::from_ref(lit),
                    Node::Internal { out_lits, .. } => &out_lits[..],
                };
                // Iterate through all value combinations
                for left_val in 0..=left_lits.len() {
                    for right_val in 0..=right_lits.len() {
                        let sum_val = left_val + right_val;
                        if sum_val > max_rhs + 1 || sum_val + 1 < min_rhs {
                            continue;
                        }
                        // Upper bounding
                        match bound_type {
                            BoundType::UB | BoundType::BOTH => {
                                let mut lhs = vec![];
                                if left_val != 0 {
                                    lhs.push(left_lits[left_val - 1]);
                                }
                                if right_val != 0 {
                                    lhs.push(right_lits[right_val - 1]);
                                }
                                if lhs.len() > 0 && sum_val > min_rhs {
                                    // (left > x) & (right > y) -> (out > x+y)
                                    cnf.add_cube_impl_lit(lhs, out_lits[sum_val - 1]);
                                }
                            }
                            _ => (),
                        };
                        // Lower bounding
                        match bound_type {
                            BoundType::LB | BoundType::BOTH => {
                                let mut lhs = vec![];
                                if left_val < left_lits.len() {
                                    lhs.push(!left_lits[left_val]);
                                }
                                if right_val < right_lits.len() {
                                    lhs.push(!right_lits[right_val]);
                                }
                                if lhs.len() > 0 && sum_val < max_rhs {
                                    // (left <= x) & (right <= y) -> (out <= x+y)
                                    cnf.add_cube_impl_lit(lhs, !out_lits[sum_val]);
                                }
                            }
                            _ => (),
                        };
                    }
                }
                cnf
            }
        }
    }

    /// Encodes the adder from the children to this node up to a given maximum
    /// right hand side. Recurses depth first. Returns  the number of newly
    /// added clauses. Always encodes the full totalizer.
    fn encode_rec<VM: ManageVars>(
        &mut self,
        new_max_rhs: usize,
        var_manager: &mut VM,
        bound_type: &BoundType,
    ) -> CNF {
        let mut cnf = match self {
            Node::Leaf { .. } => CNF::new(),
            Node::Internal { left, right, .. } => {
                // Ignore all previous encoding and encode from scratch
                // Recurse
                let mut cnf = left.encode_rec(new_max_rhs, var_manager, bound_type);
                cnf.extend(right.encode_rec(new_max_rhs, var_manager, bound_type));
                cnf
            }
        };
        let local_cnf = self.encode_from_till(0, new_max_rhs, var_manager, bound_type);
        match self {
            Node::Leaf { .. } => local_cnf,
            Node::Internal {
                max_rhs,
                max_val,
                n_clauses,
                ..
            } => {
                // Update stats
                *max_rhs = if new_max_rhs < *max_val {
                    Some(new_max_rhs)
                } else {
                    Some(*max_val)
                };
                *n_clauses += local_cnf.n_clauses();
                cnf.extend(local_cnf);
                cnf
            }
        }
    }

    /// Encodes the adder from the children to this node up to a given maximum
    /// right hand side. Recurses depth first. Returns the new `next_idx` and
    /// the number of newly added clauses. Incrementally only encodes new
    /// clauses.
    fn encode_change_rec<VM: ManageVars>(
        &mut self,
        new_max_rhs: usize,
        var_manager: &mut VM,
        bound_type: &BoundType,
    ) -> CNF {
        let (mut cnf, min_enc) = match self {
            Node::Leaf { .. } => (CNF::new(), 0),
            Node::Internal {
                left,
                right,
                max_rhs,
                ..
            } => {
                // Ignore all previous encoding and encode from scratch
                // Recurse
                let mut cnf = left.encode_change_rec(new_max_rhs, var_manager, bound_type);
                cnf.extend(right.encode_change_rec(new_max_rhs, var_manager, bound_type));
                (cnf, if let Some(mr) = max_rhs { *mr + 1 } else { 0 })
            }
        };
        // Encode adder for current node
        let local_cnf = self.encode_from_till(min_enc, new_max_rhs, var_manager, bound_type);
        match self {
            Node::Leaf { .. } => local_cnf,
            Node::Internal {
                max_rhs,
                max_val,
                n_clauses,
                ..
            } => {
                // Update stats
                *n_clauses += local_cnf.n_clauses();
                *max_rhs = if new_max_rhs < *max_val {
                    Some(new_max_rhs)
                } else {
                    Some(*max_val)
                };
                cnf.extend(local_cnf);
                cnf
            }
        }
    }

    /// Reserves variables this node might need for enforcing bounds up to `max_rhs`.
    fn reserve_vars_till<VM: ManageVars>(
        &mut self,
        max_rhs: usize,
        var_manager: &mut VM,
        bound_type: &BoundType,
    ) {
        match self {
            Node::Leaf { .. } => (),
            Node::Internal {
                out_lits, max_val, ..
            } => {
                let max_idx = if max_rhs >= *max_val {
                    *max_val - 1
                } else {
                    match bound_type {
                        BoundType::LB => max_rhs - 1,
                        _ => max_rhs,
                    }
                };
                out_lits.reserve(max_idx + 1 - out_lits.len());
                for _ in out_lits.len()..=max_idx {
                    out_lits.push(var_manager.next_free().pos_lit());
                }
                assert!(out_lits.len() <= *max_val);
            }
        }
    }

    /// Reserves all variables this node might need. This is used if variables
    /// in the totalizer should have consecutive indices.
    fn reserve_all_vars<VM: ManageVars>(&mut self, var_manager: &mut VM, bound_type: &BoundType) {
        let max_enc = match self {
            Node::Leaf { .. } => 0,
            Node::Internal { max_val, .. } => *max_val,
        };
        self.reserve_vars_till(max_enc, var_manager, bound_type);
    }

    /// Reserves all variables this node and the lower subtree might need. This
    /// is used if variables in the totalizer should have consecutive indices.
    fn reserve_all_vars_rec<VM: ManageVars>(
        &mut self,
        var_manager: &mut VM,
        bound_type: &BoundType,
    ) {
        match self {
            Node::Leaf { .. } => (),
            Node::Internal { left, right, .. } => {
                // Recursion
                left.reserve_all_vars_rec(var_manager, bound_type);
                right.reserve_all_vars_rec(var_manager, bound_type);
            }
        };
        self.reserve_all_vars(var_manager, bound_type)
    }
}

#[cfg(test)]
mod tests {
    use super::{Node, Totalizer};
    use crate::{
        encodings::{
            card::{EncodeCard, IncEncodeCard},
            BoundType, EncodingError,
        },
        instances::{BasicVarManager, ManageVars},
        lit,
        types::Lit,
    };

    #[test]
    fn adder_1() {
        // Child nodes
        let child1 = Node::new_leaf(lit![0]);
        let child2 = Node::new_leaf(lit![1]);
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::new();
        let cnf = node.encode_from_till(0, 2, &mut var_manager, &BoundType::BOTH);
        match &node {
            Node::Leaf { .. } => panic!(),
            Node::Internal { out_lits, .. } => assert_eq!(out_lits.len(), 2),
        };
        assert_eq!(cnf.n_clauses(), 6);
    }

    #[test]
    fn adder_2() {
        // (Inconsistent) child nodes
        let child1 = Node::Internal {
            out_lits: vec![lit![1], lit![2]],
            depth: 1,
            n_clauses: 0,
            max_val: 2,
            max_rhs: Some(2),
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0])),
            right: Box::new(Node::new_leaf(lit![0])),
        };
        let child2 = Node::Internal {
            out_lits: vec![lit![3], lit![4]],
            depth: 1,
            n_clauses: 0,
            max_val: 2,
            max_rhs: Some(2),
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0])),
            right: Box::new(Node::new_leaf(lit![0])),
        };
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::new();
        let cnf = node.encode_from_till(0, 4, &mut var_manager, &BoundType::BOTH);
        match &node {
            Node::Leaf { .. } => panic!(),
            Node::Internal { out_lits, .. } => assert_eq!(out_lits.len(), 4),
        };
        assert_eq!(cnf.n_clauses(), 16);
    }

    #[test]
    fn adder_3() {
        // Child nodes
        let child1 = Node::new_leaf(lit![0]);
        let child2 = Node::new_leaf(lit![1]);
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::new();
        let cnf = node.encode_from_till(0, 1, &mut var_manager, &BoundType::LB);
        match &node {
            Node::Leaf { .. } => panic!(),
            Node::Internal { out_lits, .. } => assert_eq!(out_lits.len(), 1),
        };
        assert_eq!(cnf.n_clauses(), 1);
    }

    #[test]
    fn partial_adder_1() {
        // (Inconsistent) child nodes
        let child1 = Node::Internal {
            out_lits: vec![lit![1], lit![2], lit![3]],
            depth: 1,
            n_clauses: 0,
            max_val: 2,
            max_rhs: Some(2),
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0])),
            right: Box::new(Node::new_leaf(lit![0])),
        };
        let child2 = Node::Internal {
            out_lits: vec![lit![4], lit![5], lit![6]],
            depth: 1,
            n_clauses: 0,
            max_val: 2,
            max_rhs: Some(2),
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0])),
            right: Box::new(Node::new_leaf(lit![0])),
        };
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::new();
        let cnf = node.encode_from_till(0, 3, &mut var_manager, &BoundType::BOTH);
        match &node {
            Node::Leaf { .. } => panic!(),
            Node::Internal { out_lits, .. } => assert_eq!(out_lits.len(), 4),
        };
        assert_eq!(cnf.n_clauses(), 18);
    }

    #[test]
    fn partial_adder_2() {
        // (Inconsistent) child nodes
        let child1 = Node::Internal {
            out_lits: vec![lit![1], lit![2], lit![3]],
            depth: 1,
            n_clauses: 0,
            max_val: 2,
            max_rhs: Some(2),
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0])),
            right: Box::new(Node::new_leaf(lit![0])),
        };
        let child2 = Node::Internal {
            out_lits: vec![lit![4], lit![5], lit![6]],
            depth: 1,
            n_clauses: 0,
            max_val: 2,
            max_rhs: Some(2),
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0])),
            right: Box::new(Node::new_leaf(lit![0])),
        };
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::new();
        let cnf = node.encode_from_till(2, 3, &mut var_manager, &BoundType::BOTH);
        match &node {
            Node::Leaf { .. } => panic!(),
            Node::Internal { out_lits, .. } => assert_eq!(out_lits.len(), 4),
        };
        assert_eq!(cnf.n_clauses(), 12);
    }

    #[test]
    fn tot_functions() {
        let mut tot = Totalizer::new(BoundType::BOTH).unwrap();
        tot.add(vec![lit![0], lit![1], lit![2], lit![3]]);
        assert_eq!(tot.enforce_ub(2), Err(EncodingError::NotEncoded));
        assert_eq!(tot.enforce_lb(2), Err(EncodingError::NotEncoded));
        let mut var_manager = BasicVarManager::new();
        let cnf = tot.encode(4, &mut var_manager);
        assert_eq!(tot.get_depth(), 3);
        assert_eq!(cnf.n_clauses(), 28);
        assert_eq!(tot.enforce_ub(2).unwrap().len(), 1);
        assert_eq!(tot.enforce_lb(2).unwrap().len(), 1);
    }

    #[test]
    fn tot_incremental_building_ub() {
        let mut tot1 = Totalizer::new(BoundType::UB).unwrap();
        tot1.add(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::new();
        let cnf1 = tot1.encode(4, &mut var_manager);
        let mut tot2 = Totalizer::new(BoundType::UB).unwrap();
        tot2.add(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::new();
        let mut cnf2 = tot2.encode(2, &mut var_manager);
        cnf2.extend(tot2.encode_change(4, &mut var_manager));
        assert_eq!(cnf1.n_clauses(), cnf2.n_clauses());
    }

    #[test]
    fn tot_incremental_building_lb() {
        let mut tot1 = Totalizer::new(BoundType::LB).unwrap();
        tot1.add(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::new();
        let cnf1 = tot1.encode(4, &mut var_manager);
        let mut tot2 = Totalizer::new(BoundType::LB).unwrap();
        tot2.add(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::new();
        let mut cnf2 = tot2.encode(2, &mut var_manager);
        cnf2.extend(tot2.encode_change(4, &mut var_manager));
        assert_eq!(cnf1.n_clauses(), cnf2.n_clauses());
    }

    #[test]
    fn tot_lb_and_ub_is_eq() {
        let mut tot1 = Totalizer::new(BoundType::BOTH).unwrap();
        tot1.add(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::new();
        let cnf1 = tot1.encode(4, &mut var_manager);
        let mut tot2 = Totalizer::new(BoundType::LB).unwrap();
        tot2.add(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::new();
        let mut cnf2 = tot2.encode(4, &mut var_manager);
        let mut tot3 = Totalizer::new(BoundType::UB).unwrap();
        tot3.add(vec![lit![0], lit![1], lit![2], lit![3]]);
        cnf2.extend(tot3.encode(4, &mut var_manager));
        assert_eq!(cnf1.n_clauses(), cnf2.n_clauses());
    }

    #[test]
    fn invalid_useage() {
        let mut tot = Totalizer::new(BoundType::LB).unwrap();
        tot.add(vec![lit![0], lit![1]]);
        assert_eq!(tot.enforce_ub(1), Err(EncodingError::NoObjectSupport));
        let mut tot = Totalizer::new(BoundType::UB).unwrap();
        tot.add(vec![lit![0], lit![1]]);
        assert_eq!(tot.enforce_lb(1), Err(EncodingError::NoObjectSupport));
    }
}
