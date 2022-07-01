use core::ops::Not;
use std::collections::HashMap;

#[derive(Hash, Eq, PartialEq, Clone, Copy)]
pub struct Var {
    v: u32,
}

impl Var {
    pub fn new(v: u32) -> Var {
        Var { v }
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
}

#[derive(Hash, Eq, PartialEq, Clone, Copy)]
pub struct Lit {
    v: Var,
    negated: bool,
}

impl Lit {
    pub fn new(v: u32, sign: bool) -> Lit {
        let var = Var::new(v);
        Lit {
            v: var,
            negated: sign,
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

pub struct Solution {
    assignment: HashMap<Var, bool>,
}

impl Solution {
    pub fn var_value(&self, var: &Var) -> Option<bool> {
        match self.assignment.get(var) {
            Some(val) => Some(*val),
            None => None,
        }
    }
}
