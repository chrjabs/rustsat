extern crate proc_macro;

use proc_macro2::TokenStream;
use quote::quote;
use syn::{parse_quote, Attribute};

use super::MacroInput;

pub fn base(input: MacroInput) -> TokenStream {
    let slv = input.slv;
    let ignoretok = |idx: usize| -> Option<Attribute> {
        if input.bools.len() > idx && input.bools[idx] {
            Some(parse_quote! {#[ignore]})
        } else {
            None
        }
    };
    let mut ts = quote! {
        macro_rules! test_inst {
            ($slv:ty, $inst:expr, $res:expr) => {{
                let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
                let mut solver = <$slv>::default();
                let inst = rustsat::instances::SatInstance::<rustsat::instances::BasicVarManager>::from_dimacs_path(format!("{manifest}/{}", $inst))
                    .expect("failed to parse instance");
                rustsat::solvers::Solve::add_cnf_ref(&mut solver, inst.cnf())
                    .expect("failed to add cnf to solver");
                let res = rustsat::solvers::Solve::solve(&mut solver).expect("failed solving");
                assert_eq!(res, $res);
                if $res == rustsat::solvers::SolverResult::Sat {
                    let sol = rustsat::solvers::Solve::solution(&solver, inst.max_var().expect("no variables in instance"))
                        .expect("failed to get solution from solver");
                    assert!(inst.is_sat(&sol));
                }
            }};
            ($init:expr, $inst:expr, $res:expr) => {{
                let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
                let mut solver = $init;
                let inst = rustsat::instances::SatInstance::<rustsat::instances::BasicVarManager>::from_dimacs_path(format!("{manifest}/{}", $inst))
                    .expect("failed to parse instance");
                rustsat::solvers::Solve::add_cnf_ref(&mut solver, inst.cnf())
                    .expect("failed to add cnf to solver");
                let res = rustsat::solvers::Solve::solve(&mut solver).expect("failed solving");
                assert_eq!(res, $res);
                if $res == rustsat::solvers::SolverResult::Sat {
                    let sol = rustsat::solvers::Solve::solution(&solver, inst.max_var().expect("no variables in instance"))
                        .expect("failed to get solution from solver");
                    assert!(inst.is_sat(&sol));
                }
            }};
        }
    };
    let ignore = ignoretok(0);
    ts.extend(quote! {
        #[test]
        #ignore
        fn small_sat() {
            test_inst!(#slv, "data/AProVE11-12.cnf", rustsat::solvers::SolverResult::Sat);
        }
    });
    let ignore = ignoretok(1);
    ts.extend(quote! {
        #[test]
        #ignore
        fn small_unsat() {
            test_inst!(#slv, "data/smtlib-qfbv-aigs-ext_con_032_008_0256-tseitin.cnf", rustsat::solvers::SolverResult::Unsat);
        }
    });
    let ignore = ignoretok(2);
    ts.extend(quote! {
        #[test]
        #ignore
        fn minisat_segfault() {
            test_inst!(#slv, "data/minisat-segfault.cnf", rustsat::solvers::SolverResult::Unsat);
        }
    });
    ts
}

pub fn incremental(input: MacroInput) -> TokenStream {
    let slv = input.slv;
    let ignoretok = |idx: usize| -> Option<Attribute> {
        if input.bools.len() > idx && input.bools[idx] {
            Some(parse_quote! {#[ignore]})
        } else {
            None
        }
    };
    let mut ts = quote! {
        macro_rules! init_slv {
            ($slv:ty) => {
                <$slv>::default()
            };
            ($init:expr) => {
                $init
            };
        }
    };
    let ignore = ignoretok(0);
    ts.extend(quote! {
        #[test]
        #ignore
        fn assumption_sequence() {
            use rustsat::{
                instances::{SatInstance},
                lit,
                solvers::{Solve, SolveIncremental, SolverResult::{Sat, Unsat}},
            };

            let mut solver = init_slv!(#slv);
            let inst: SatInstance =
                SatInstance::from_dimacs_path("data/small.cnf").unwrap();
            solver.add_cnf(inst.into_cnf().0).unwrap();
            let res = solver.solve().unwrap();
            assert_eq!(res, Sat);
            let res = solver.solve_assumps(&[!lit![0], !lit![1]]).unwrap();
            assert_eq!(res, Unsat);
            let res = solver
                .solve_assumps(&[lit![0], lit![1], lit![2], lit![3]])
                .unwrap();
            assert_eq!(res, Unsat);
            let res = solver
                .solve_assumps(&[lit![0], lit![1], lit![2], !lit![3]])
                .unwrap();
            assert_eq!(res, Unsat);
            let res = solver
                .solve_assumps(&[lit![0], lit![1], !lit![2], lit![3]])
                .unwrap();
            assert_eq!(res, Unsat);
            let res = solver
                .solve_assumps(&[lit![0], lit![1], !lit![2], !lit![3]])
                .unwrap();
            assert_eq!(res, Sat);
            let res = solver
                .solve_assumps(&[lit![0], !lit![1], lit![2], lit![3]])
                .unwrap();
            assert_eq!(res, Unsat);
            let res = solver
                .solve_assumps(&[lit![0], !lit![1], lit![2], !lit![3]])
                .unwrap();
            assert_eq!(res, Sat);
            let res = solver
                .solve_assumps(&[lit![0], !lit![1], !lit![2], lit![3]])
                .unwrap();
            assert_eq!(res, Unsat);
            let res = solver
                .solve_assumps(&[lit![0], !lit![1], !lit![2], !lit![3]])
                .unwrap();
            assert_eq!(res, Unsat);
            let res = solver
                .solve_assumps(&[!lit![0], lit![1], lit![2], lit![3]])
                .unwrap();
            assert_eq!(res, Unsat);
            let res = solver
                .solve_assumps(&[!lit![0], lit![1], lit![2], !lit![3]])
                .unwrap();
            assert_eq!(res, Unsat);
            let res = solver
                .solve_assumps(&[!lit![0], lit![1], !lit![2], lit![3]])
                .unwrap();
            assert_eq!(res, Sat);
            let res = solver
                .solve_assumps(&[!lit![0], lit![1], !lit![2], !lit![3]])
                .unwrap();
            assert_eq!(res, Sat);
            let res = solver
                .solve_assumps(&[!lit![0], !lit![1], lit![2], lit![3]])
                .unwrap();
            assert_eq!(res, Unsat);
            let res = solver
                .solve_assumps(&[!lit![0], !lit![1], lit![2], !lit![3]])
                .unwrap();
            assert_eq!(res, Unsat);
            let res = solver
                .solve_assumps(&[!lit![0], !lit![1], !lit![2], lit![3]])
                .unwrap();
            assert_eq!(res, Unsat);
            let res = solver
                .solve_assumps(&[!lit![0], !lit![1], !lit![2], !lit![3]])
                .unwrap();
            assert_eq!(res, Unsat);
        }
    });
    ts
}

pub fn phasing(input: MacroInput) -> TokenStream {
    let slv = input.slv;
    let ignoretok = |idx: usize| -> Option<Attribute> {
        if input.bools.len() > idx && input.bools[idx] {
            Some(parse_quote! {#[ignore]})
        } else {
            None
        }
    };
    let mut ts = quote! {
        macro_rules! init_slv {
            ($slv:ty) => {
                <$slv>::default()
            };
            ($init:expr) => {
                $init
            };
        }
    };
    let ignore = ignoretok(0);
    ts.extend(quote! {
        #[test]
        #ignore
        fn user_phases() {
            use rustsat::{
                instances::{SatInstance},
                lit,
                solvers::{PhaseLit, Solve, SolverResult::Sat},
                types::TernaryVal::{True, False},
                var,
            };
            let mut solver = init_slv!(#slv);
            let inst: SatInstance =
                SatInstance::from_dimacs_path("data/small.cnf").unwrap();
            solver.add_cnf(inst.into_cnf().0).unwrap();
            solver.phase_lit(lit![0]).unwrap();
            solver.phase_lit(!lit![1]).unwrap();
            solver.phase_lit(lit![2]).unwrap();
            solver.phase_lit(!lit![3]).unwrap();
            let res = solver.solve().unwrap();
            assert_eq!(res, Sat);
            let sol = solver.solution(var![3]).unwrap();
            assert_eq!(sol.lit_value(lit![0]), True);
            assert_eq!(sol.lit_value(lit![1]), False);
            assert_eq!(sol.lit_value(lit![2]), True);
            assert_eq!(sol.lit_value(lit![3]), False);
            solver.unphase_var(var![1]).unwrap();
            solver.unphase_var(var![0]).unwrap();
        }
    });
    ts
}
