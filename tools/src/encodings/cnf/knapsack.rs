//! # CNF (Multi-Criteria) Knapsack Encoding

use rustsat::{
    clause,
    encodings::pb,
    instances::{fio::dimacs, BasicVarManager, Cnf, ManageVars},
    types::{constraints::PbConstraint, Lit},
};

use crate::encodings::knapsack::Knapsack;

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
        let cap_constr = match PbConstraint::new_ub(
            data.items
                .iter()
                .map(|item| (vm.new_var().pos_lit(), item.weight as isize)),
            data.capacity as isize,
        ) {
            PbConstraint::Ub(constr) => constr,
            _ => unreachable!(),
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
