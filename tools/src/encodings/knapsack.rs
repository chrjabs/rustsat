//! # (Multi-Criteria) Knapsack Encoding

use std::ops::Range;

use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use rustsat::{
    clause,
    encodings::pb,
    instances::{fio::dimacs, BasicVarManager, Cnf, ManageVars},
    types::{constraints::PBConstraint, Lit},
};

/// An instance of the (multi-criteria 0-1) knapsack problem
pub struct Knapsack {
    items: Vec<ItemData>,
    capacity: usize,
}

/// Data associated with one knapsack item
struct ItemData {
    weight: usize,
    values: Vec<usize>,
}

pub enum Capacity {
    /// A fixed knapsack capacity
    Fixed(usize),
    /// Calculate the capacity as the total weight divided by the given value
    FractionTotalWeight(usize),
}

impl Knapsack {
    pub fn random(
        n_items: usize,
        n_objectives: usize,
        value_range: Range<usize>,
        weight_range: Range<usize>,
        capacity: Capacity,
        seed: u64,
    ) -> Self {
        let mut rng = ChaCha8Rng::seed_from_u64(seed);
        let items: Vec<_> = (0..n_items)
            .map(|_| {
                let weight = rng.gen_range(weight_range.clone());
                let values = (0..n_objectives)
                    .map(|_| rng.gen_range(value_range.clone()))
                    .collect();
                ItemData { weight, values }
            })
            .collect();
        let capacity = match capacity {
            Capacity::Fixed(cap) => cap,
            Capacity::FractionTotalWeight(div) => {
                items.iter().fold(0, |sum, item| sum + item.weight) / div
            }
        };
        Self { items, capacity }
    }
}

enum Clause {
    /// Clause of the capacity encoding
    Capacity(<Cnf as IntoIterator>::IntoIter),
    /// Soft clause for item and objective
    Soft(usize, usize),
}

pub struct Encoding {
    data: Knapsack,
    next_clause: Clause,
}

impl Encoding {
    pub fn new<PBE>(data: Knapsack) -> Self
    where
        PBE: pb::BoundUpper + FromIterator<(Lit, usize)>,
    {
        let mut vm = BasicVarManager::default();
        let cap_constr = match PBConstraint::new_ub(
            data.items
                .iter()
                .map(|item| (vm.new_var().pos_lit(), item.weight as isize)),
            data.capacity as isize,
        ) {
            PBConstraint::UB(constr) => constr,
            _ => panic!(),
        };
        let mut cap_cnf = Cnf::new();
        PBE::encode_ub_constr(cap_constr, &mut cap_cnf, &mut vm).unwrap();
        Self {
            data,
            next_clause: Clause::Capacity(cap_cnf.into_iter()),
        }
    }
}

impl Iterator for Encoding {
    type Item = dimacs::McnfLine;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match &mut self.next_clause {
                Clause::Capacity(iter) => {
                    let next = iter.next();
                    if next.is_some() {
                        return next.map(dimacs::McnfLine::Hard);
                    }
                    self.next_clause = Clause::Soft(0, 0);
                }
                Clause::Soft(iidx, oidx) => {
                    let iidx = *iidx;
                    let oidx = *oidx;
                    if iidx >= self.data.items.len() {
                        return None;
                    }
                    if oidx >= self.data.items[iidx].values.len() {
                        self.next_clause = Clause::Soft(iidx + 1, 0);
                        continue;
                    }
                    self.next_clause = Clause::Soft(iidx, oidx + 1);
                    return Some(dimacs::McnfLine::Soft(
                        clause![Lit::positive(iidx as u32)],
                        self.data.items[iidx].values[oidx],
                        oidx,
                    ));
                }
            }
        }
    }
}
