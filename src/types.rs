use core::ops::Not;
use std::os::raw::c_int;

use crate::solvers::{ipasir::IpasirError, SolverState};

#[derive(Hash, Eq, PartialEq, Clone, Copy)]
pub struct Var {
    idx: usize,
}

impl Var {
    pub fn new(idx: usize) -> Var {
        Var { idx }
    }

    pub fn pos_lit(self) -> Lit {
        Lit {
            v: self,
            negated: false,
        }
    }

    pub fn neg_lit(self) -> Lit {
        Lit {
            v: self,
            negated: true,
        }
    }

    pub fn index(self) -> usize {
        self.idx
    }
}

#[derive(Hash, Eq, PartialEq, Clone, Copy)]
pub struct Lit {
    v: Var,
    negated: bool,
}

impl Lit {
    pub fn new(v: usize, negated: bool) -> Lit {
        let var = Var::new(v);
        Lit {
            v: var,
            negated,
        }
    }

    pub fn var(&self) -> &Var {
        &self.v
    }

    pub fn is_pos(&self) -> bool {
        !self.negated
    }

    pub fn is_neg(&self) -> bool {
        self.negated
    }

    pub fn to_ipasir(self) -> c_int {
        let idx: i32 = (self.v.idx + 1)
            .try_into()
            .expect("Variable index too high to fit in int32_t");
        if self.negated {
            -idx
        } else {
            idx
        }
    }
}

impl Not for Lit {
    type Output = Lit;

    fn not(self) -> Lit {
        Lit {
            v: self.v,
            negated: !self.negated,
        }
    }
}

pub enum LitVal {
    True,
    False,
    DontCare,
}

pub struct Solution {
    assignment: Vec<LitVal>,
}

impl Solution {
    pub fn from_vec(assignment: Vec<LitVal>) -> Solution {
        Solution { assignment }
    }

    pub fn var_value(&self, var: &Var) -> Option<&LitVal> {
        if var.idx >= self.assignment.len() {
            None
        } else {
            Some(&self.assignment[var.idx])
        }
    }

    pub fn lit_value(&self, lit: &Lit) -> Option<&LitVal> {
        if lit.negated {
            match self.var_value(lit.var())? {
                LitVal::DontCare => Some(&LitVal::DontCare),
                LitVal::True => Some(&LitVal::False),
                LitVal::False => Some(&LitVal::True),
            }
        } else {
            self.var_value(lit.var())
        }
    }
}

pub enum Error {
    Ipasir(IpasirError),
    StateError(SolverState),
}
