//! # Dynamic Polynomial Watchdog Encoding
//!
//! Implementation of the dynamic polynomial watchdog (DPW) encoding \[1\].
//!
//! **Note**:
//! This implementation of the  DPW encoding only supports incrementally
//! changing the bound, but not adding new input literals. Calling extend after
//! encoding resets the entire encoding and with the next encode and entirely
//! new encoding will be returned.
//!
//! ## References
//!
//! - \[1\] Tobias Paxian and Sven Reimer and Bernd Becker: _Dynamic Polynomial
//!   Watchdog Encoding for Solving Weighted MaxSAT_, SAT 2018.

use std::{collections::BTreeMap, ops::Range};

use crate::{
    encodings::{
        card::dbtotalizer::{Node, TotDb},
        nodedb::{NodeById, NodeCon, NodeId, NodeLike},
        EncodeStats, Error,
    },
    instances::{Cnf, ManageVars},
    types::{Lit, RsHashMap},
    utils,
};

use super::{BoundUpper, BoundUpperIncremental, Encode, EncodeIncremental};

/// Implementation of the dynamic polynomial watchdog (DPW) encoding \[1\].
///
/// **Note**:
/// This implementation of the  DPW encoding only supports incrementally
/// changing the bound, but not adding new input literals. Calling extend after
/// encoding resets the entire encoding and with the next encode and entirely
/// new encoding will be returned.
///
/// ## References
///
/// - \[1\] Tobias Paxian and Sven Reimer and Bernd Becker: _Dynamic Polynomial
///   Watchdog Encoding for Solving Weighted MaxSAT_, SAT 2018.
#[derive(Default)]
pub struct DynamicPolyWatchdog {
    /// Input literals and weights for the encoding
    in_lits: RsHashMap<Lit, usize>,
    /// Flag to know when new literals where added and the encoding needs to be reconstructed
    lits_added: bool,
    /// The encoding root and the tares
    structure: Option<Structure>,
    /// Sum of all input weight
    weight_sum: usize,
    /// The number of variables
    n_vars: usize,
    /// The number of clauses
    n_clauses: usize,
    /// The node database of the totalizer
    db: TotDb,
}

impl DynamicPolyWatchdog {
    /// Gets the maximum depth of the tree
    pub fn depth(&self) -> usize {
        match &self.structure {
            Some(Structure { root, .. }) => self.db[*root].depth(),
            None => 0,
        }
    }
}

#[cfg_attr(feature = "internals", visibility::make(pub))]
struct Structure {
    /// The root of the structure
    pub root: NodeId,
    /// The tare variables needed to enforce specific bounds. First in vector is
    /// the tare to the second largest top bucket, then decreasing.
    pub tares: Vec<Lit>,
}

impl Structure {
    /// Gets the power of the output literals (they represent a weight of
    /// 2^power)
    pub fn output_power(&self) -> usize {
        self.tares.len()
    }
}

impl Encode for DynamicPolyWatchdog {
    type Iter<'a> = DpwIter<'a>;

    fn iter(&self) -> Self::Iter<'_> {
        self.in_lits.iter().map(copy_key_val)
    }

    fn weight_sum(&self) -> usize {
        self.weight_sum
    }

    fn next_higher(&self, val: usize) -> usize {
        val + 1
    }

    fn next_lower(&self, val: usize) -> usize {
        val - 1
    }
}

impl EncodeIncremental for DynamicPolyWatchdog {
    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        if let Some(Structure { root, .. }) = &self.structure {
            self.db.reserve_vars(*root, var_manager);
        }
    }
}

impl BoundUpper for DynamicPolyWatchdog {
    fn encode_ub(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> Cnf {
        self.db.reset_encoded();
        self.encode_ub_change(range, var_manager)
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, Error> {
        match &self.structure {
            Some(structure) => enforce_ub(structure, ub, &self.db),
            None => Ok(vec![]),
        }
    }
}

impl BoundUpperIncremental for DynamicPolyWatchdog {
    fn encode_ub_change(&mut self, range: Range<usize>, var_manager: &mut dyn ManageVars) -> Cnf {
        if range.is_empty() {
            return Cnf::new();
        }
        if self.lits_added {
            // reset current totalizer database
            self.db = Default::default();
            self.structure = Some(build_structure(
                self.in_lits.iter().map(|(&l, &w)| (l, w)),
                &mut self.db,
                var_manager,
            ));
        }
        match &self.structure {
            Some(structure) => {
                let n_vars_before = var_manager.n_used();
                let output_weight = 1 << (structure.output_power());
                let output_range = range.start / output_weight..(range.end - 1) / output_weight + 1;
                let mut cnf = Cnf::new();
                for oidx in output_range {
                    encode_output(&structure, oidx, &mut self.db, var_manager, &mut cnf);
                }
                self.n_clauses += cnf.len();
                self.n_vars += var_manager.n_used() - n_vars_before;
                cnf
            }
            None => Cnf::new(),
        }
    }
}

impl EncodeStats for DynamicPolyWatchdog {
    fn n_clauses(&self) -> usize {
        self.n_clauses
    }

    fn n_vars(&self) -> usize {
        self.n_vars
    }
}

impl From<RsHashMap<Lit, usize>> for DynamicPolyWatchdog {
    fn from(lits: RsHashMap<Lit, usize>) -> Self {
        let weight_sum = lits.iter().fold(0, |sum, (_, w)| sum + *w);
        Self {
            in_lits: lits.clone(),
            lits_added: true,
            structure: Default::default(),
            weight_sum,
            n_vars: Default::default(),
            n_clauses: Default::default(),
            db: Default::default(),
        }
    }
}

impl FromIterator<(Lit, usize)> for DynamicPolyWatchdog {
    fn from_iter<T: IntoIterator<Item = (Lit, usize)>>(iter: T) -> Self {
        let lits: RsHashMap<Lit, usize> = RsHashMap::from_iter(iter);
        Self::from(lits)
    }
}

impl Extend<(Lit, usize)> for DynamicPolyWatchdog {
    fn extend<T: IntoIterator<Item = (Lit, usize)>>(&mut self, iter: T) {
        iter.into_iter().for_each(|(l, w)| {
            self.weight_sum += w;
            // Insert into map of input literals
            match self.in_lits.get_mut(&l) {
                Some(old_w) => *old_w += w,
                None => {
                    self.in_lits.insert(l, w);
                }
            };
        });
        self.lits_added = true;
    }
}

fn copy_key_val(key_val_refs: (&Lit, &usize)) -> (Lit, usize) {
    (*key_val_refs.0, *key_val_refs.1)
}
type DpwIter<'a> = std::iter::Map<
    std::collections::hash_map::Iter<'a, Lit, usize>,
    fn((&Lit, &usize)) -> (Lit, usize),
>;

#[cfg_attr(feature = "internals", visibility::make(pub))]
fn build_structure<LI: Iterator<Item = (Lit, usize)>>(
    lits: LI,
    tot_db: &mut TotDb,
    var_manager: &mut dyn ManageVars,
) -> Structure {
    // Initialize weight queue
    let mut weight_queue: BTreeMap<usize, Vec<NodeCon>> = BTreeMap::new();
    for (lit, weight) in lits {
        let node = tot_db.insert(Node::Leaf(lit));
        if let Some(cons) = weight_queue.get_mut(&weight) {
            cons.push(NodeCon::full(node));
        } else {
            weight_queue.insert(weight, vec![NodeCon::full(node)]);
        }
    }
    let basis_len = utils::digits(*weight_queue.iter().next_back().unwrap().0, 2) as usize;

    // Children to be merged to a given top bucket
    let mut top_buckets = vec![vec![]; basis_len];
    // Converts a digit number to a corresponding index in the
    // `top_buckets`. Top buckets are ordered from smallest to highest.
    let tb_idx = |digits: u32| (digits - 1) as usize;

    // Loop while there are new weights that need to be added and distribute
    // them to relevant top buckets
    while !weight_queue.is_empty() {
        let (weight, cons) = weight_queue.pop_last().unwrap();
        let merged = tot_db.merge_balanced(&cons);
        let digits = utils::digits(weight, 2);
        let current_weight = 1 << (digits - 1);
        top_buckets[tb_idx(digits)].push(merged);
        // Insert remainder of totalizer as new child
        let remaining_weight = weight & !current_weight;
        if remaining_weight > 0 {
            if let Some(cons) = weight_queue.get_mut(&remaining_weight) {
                cons.push(merged);
            } else {
                weight_queue.insert(remaining_weight, vec![merged]);
            }
        }
    }

    if basis_len == 1 {
        debug_assert_eq!(top_buckets[0].len(), 1);
        return Structure {
            root: top_buckets[0][0].id,
            tares: vec![],
        };
    }

    // Prepare tares
    let tares: Vec<_> = (0..basis_len - 1)
        .map(|_| var_manager.new_var().pos_lit())
        .collect();
    let tare_nodes: Vec<_> = tares
        .iter()
        .map(|&lit| tot_db.insert(Node::Leaf(lit)))
        .collect();

    // Merge top buckets and merge with bottom buckets
    let mut last_bottom_bucket = None;
    for (idx, mut cons) in top_buckets.into_iter().enumerate() {
        if idx != basis_len - 1 {
            // Merge top bucket (except for last) with tare
            cons.push(NodeCon::full(tare_nodes[idx]));
        }
        cons.sort_unstable_by_key(|&con| tot_db.con_len(con));
        let top_bucket = tot_db.merge_balanced(&cons);
        if last_bottom_bucket.is_none() {
            // special case: lowest bucket does not need bottom buckets
            if tot_db.con_len(top_bucket) == 1 {
                // top bucket is empty (except for tare), tare can be
                // omitted: shift to next layer
                continue;
            }
            debug_assert_eq!(top_bucket.divisor, 1);
            last_bottom_bucket = Some(NodeCon {
                id: top_bucket.id,
                offset: top_bucket.offset,
                divisor: 2,
            });
            continue;
        }

        let right = last_bottom_bucket.unwrap();
        let len = tot_db.con_len(top_bucket) + tot_db.con_len(right);
        let depth = std::cmp::max(tot_db[top_bucket.id].depth(), tot_db[right.id].depth()) + 1;
        let bottom = tot_db.insert(Node::internal(len, depth, top_bucket, right));
        last_bottom_bucket = Some(NodeCon {
            id: bottom,
            offset: 0,
            divisor: 2,
        });
    }

    let root = last_bottom_bucket.unwrap();
    debug_assert_eq!(root.offset, 0);
    debug_assert_eq!(root.divisor, 2);
    Structure {
        root: root.id,
        tares,
    }
}

#[cfg_attr(feature = "internals", visibility::make(pub))]
fn encode_output(
    dpw: &Structure,
    oidx: usize,
    tot_db: &mut TotDb,
    var_manager: &mut dyn ManageVars,
    encoding: &mut Cnf,
) {
    if oidx >= tot_db[dpw.root].len() {
        return;
    }
    tot_db.define_pos(dpw.root, oidx, encoding, var_manager);
}

#[cfg_attr(feature = "internals", visibility::make(pub))]
fn enforce_ub(dpw: &Structure, ub: usize, tot_db: &TotDb) -> Result<Vec<Lit>, Error> {
    let output_weight = 1 << (dpw.output_power());
    let oidx = ub / output_weight;
    if oidx >= tot_db[dpw.root].len() {
        return Ok(vec![]);
    }
    let olit = match tot_db[dpw.root].lit(oidx) {
        Some(&lit) => lit,
        None => return Err(Error::NotEncoded),
    };
    let mut assumps = vec![!olit];
    // inputs <= enforced_weight at this stage
    let mut enforced_weight = (oidx + 1) * output_weight - 1;
    // Set needed tares
    for power in (0..dpw.output_power()).rev() {
        let weight = 1 << power;
        if ub + weight <= enforced_weight {
            enforced_weight -= weight;
            assumps.push(dpw.tares[power]);
        }
        if ub == enforced_weight {
            break;
        }
    }
    debug_assert!(ub == enforced_weight);

    Ok(assumps)
}
