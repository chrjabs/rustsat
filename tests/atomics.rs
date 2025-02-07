use rustsat::{
    encodings::atomics,
    lit,
    types::{
        constraints::{CardConstraint, PbConstraint},
        Assignment, Lit, TernaryVal,
    },
};

/// Tests wether the `lit -> card` reification for the given constraint (over variables 0-3) is correct
fn test_lit_impl_card(constr: &CardConstraint) {
    let reif = atomics::lit_impl_card(lit![4], constr);
    println!("reification: {reif:?}");
    for idx in 0..32 {
        let mut assign = Assignment::default();
        for v in 0..5 {
            let lit = if idx & (1 << v) > 0 {
                Lit::positive(v)
            } else {
                Lit::negative(v)
            };
            assign.assign_lit(lit);
        }
        println!("assignment: {assign}");
        if assign.lit_value(lit![4]) == TernaryVal::False {
            assert_eq!(reif.evaluate(&assign), TernaryVal::True);
        } else {
            assert_eq!(constr.evaluate(&assign), reif.evaluate(&assign));
        }
    }
}

#[test]
fn lit_impl_card() {
    let lits = vec![lit![0], lit![1], lit![2], lit![3]];
    for b in 0..4 {
        let constr = CardConstraint::new_ub(lits.clone(), b);
        println!("constraint: {constr:?}");
        test_lit_impl_card(&constr);
    }
    for b in 1..=4 {
        let constr = CardConstraint::new_lb(lits.clone(), b);
        println!("constraint: {constr:?}");
        test_lit_impl_card(&constr);
    }
}

/// Tests wether the `card -> lit` reification for the given constraint (over variables 0-3) is correct
fn test_card_impl_lit(constr: &CardConstraint) {
    let reif = atomics::card_impl_lit(constr, lit![4]);
    println!("reification: {reif:?}");
    for idx in 0..32 {
        let mut assign = Assignment::default();
        for v in 0..5 {
            let lit = if idx & (1 << v) > 0 {
                Lit::positive(v)
            } else {
                Lit::negative(v)
            };
            assign.assign_lit(lit);
        }
        println!("assignment: {assign}");
        if assign.lit_value(lit![4]) == TernaryVal::True {
            assert_eq!(reif.evaluate(&assign), TernaryVal::True);
        } else {
            assert_ne!(constr.evaluate(&assign), reif.evaluate(&assign));
        }
    }
}

#[test]
fn card_impl_lit() {
    let lits = vec![lit![0], lit![1], lit![2], lit![3]];
    for b in 0..4 {
        let constr = CardConstraint::new_ub(lits.clone(), b);
        println!("constraint: {constr:?}");
        test_card_impl_lit(&constr);
    }
    for b in 1..=4 {
        let constr = CardConstraint::new_lb(lits.clone(), b);
        println!("constraint: {constr:?}");
        test_card_impl_lit(&constr);
    }
}

/// Tests wether the `lit -> pb` reification for the given constraint (over variables 0-3) is correct
fn test_lit_impl_pb(constr: &PbConstraint) {
    let reif = atomics::lit_impl_pb(lit![4], constr);
    println!("reification: {reif:?}");
    for idx in 0..32 {
        let mut assign = Assignment::default();
        for v in 0..5 {
            let lit = if idx & (1 << v) > 0 {
                Lit::positive(v)
            } else {
                Lit::negative(v)
            };
            assign.assign_lit(lit);
        }
        println!("assignment: {assign}");
        if assign.lit_value(lit![4]) == TernaryVal::False {
            assert_eq!(reif.evaluate(&assign), TernaryVal::True);
        } else {
            assert_eq!(constr.evaluate(&assign), reif.evaluate(&assign));
        }
    }
}

#[test]
fn lit_impl_pb() {
    let lits = vec![(lit![0], 1), (lit![1], 2), (lit![2], 1), (lit![3], 2)];
    for b in 0..6 {
        let constr = PbConstraint::new_ub(lits.clone(), b);
        println!("constraint: {constr:?}");
        test_lit_impl_pb(&constr);
    }
    for b in 1..=6 {
        let constr = PbConstraint::new_lb(lits.clone(), b);
        println!("constraint: {constr:?}");
        test_lit_impl_pb(&constr);
    }
}

/// Tests wether the `pb -> lit` reification for the given constraint (over variables 0-3) is correct
fn test_pb_impl_lit(constr: &PbConstraint) {
    let reif = atomics::pb_impl_lit(constr, lit![4]);
    println!("reification: {reif:?}");
    for idx in 0..32 {
        let mut assign = Assignment::default();
        for v in 0..5 {
            let lit = if idx & (1 << v) > 0 {
                Lit::positive(v)
            } else {
                Lit::negative(v)
            };
            assign.assign_lit(lit);
        }
        println!("assignment: {assign}");
        if assign.lit_value(lit![4]) == TernaryVal::True {
            assert_eq!(reif.evaluate(&assign), TernaryVal::True);
        } else {
            assert_ne!(constr.evaluate(&assign), reif.evaluate(&assign));
        }
    }
}

#[test]
fn pb_impl_lit() {
    let lits = vec![(lit![0], 1), (lit![1], 2), (lit![2], 1), (lit![3], 2)];
    for b in 0..6 {
        let constr = PbConstraint::new_ub(lits.clone(), b);
        println!("constraint: {constr:?}");
        test_pb_impl_lit(&constr);
    }
    for b in 1..=6 {
        let constr = PbConstraint::new_lb(lits.clone(), b);
        println!("constraint: {constr:?}");
        test_pb_impl_lit(&constr);
    }
}
