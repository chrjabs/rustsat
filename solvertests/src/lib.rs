extern crate proc_macro;

use proc_macro::TokenStream;
use quote::{quote, ToTokens};
use syn::{
    parse::Parse, parse_macro_input, parse_quote, punctuated::Punctuated, Attribute, Expr, LitBool,
    Token, Type,
};

enum InitBy {
    Default(Type),
    Expr(Expr),
}

impl Parse for InitBy {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let typr: syn::Result<Type> = input.parse();
        Ok(if let Ok(typ) = typr {
            Self::Default(typ)
        } else {
            Self::Expr(input.parse()?)
        })
    }
}

impl ToTokens for InitBy {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        match self {
            InitBy::Default(typ) => typ.to_tokens(tokens),
            InitBy::Expr(expr) => expr.to_tokens(tokens),
        }
    }
}

struct MacroInput {
    slv: InitBy,
    bools: Vec<bool>,
}

impl Parse for MacroInput {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let slv: InitBy = input.parse()?;
        if input.is_empty() {
            return Ok(Self { slv, bools: vec![] });
        }
        let _: Token![,] = input.parse()?;
        let bools = Punctuated::<LitBool, Token![,]>::parse_terminated(input)?;
        let bools: Vec<_> = bools.into_iter().map(|lit| lit.value).collect();
        Ok(Self { slv, bools })
    }
}

#[proc_macro]
pub fn base_tests(tokens: TokenStream) -> TokenStream {
    let input = parse_macro_input!(tokens as MacroInput);
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
                let mut solver = <$slv>::default();
                let inst = rustsat::instances::SatInstance::<rustsat::instances::BasicVarManager>::from_dimacs_path($inst)
                    .expect("failed to parse instance");
                rustsat::solvers::Solve::add_cnf(&mut solver, inst.as_cnf().0)
                    .expect("failed to add cnf to solver");
                let res = rustsat::solvers::Solve::solve(&mut solver).expect("failed solving");
                assert_eq!(res, $res);
            }};
            ($init:expr, $inst:expr, $res:expr) => {{
                let mut solver = $init;
                let inst = rustsat::instances::SatInstance::<rustsat::instances::BasicVarManager>::from_dimacs_path($inst)
                    .expect("failed to parse instance");
                rustsat::solvers::Solve::add_cnf(&mut solver, inst.as_cnf().0)
                    .expect("failed to add cnf to solver");
                let res = rustsat::solvers::Solve::solve(&mut solver).expect("failed solving");
                assert_eq!(res, $res);
            }};
        }
    };
    let ignore = ignoretok(0);
    ts.extend(quote! {
        #[test]
        #ignore
        fn small_sat() {
            test_inst!(#slv, "./data/AProVE11-12.cnf", rustsat::solvers::SolverResult::Sat);
        }
    });
    let ignore = ignoretok(1);
    ts.extend(quote! {
        #[test]
        #ignore
        fn small_unsat() {
            test_inst!(#slv, "./data/smtlib-qfbv-aigs-ext_con_032_008_0256-tseitin.cnf", rustsat::solvers::SolverResult::Unsat);
        }
    });
    let ignore = ignoretok(2);
    ts.extend(quote! {
        #[test]
        #ignore
        fn minisat_segfault() {
            test_inst!(#slv, "./data/minisat-segfault.cnf", rustsat::solvers::SolverResult::Unsat);
        }
    });
    ts.into()
}

#[proc_macro]
pub fn incremental_tests(tokens: TokenStream) -> TokenStream {
    let input = parse_macro_input!(tokens as MacroInput);
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
                SatInstance::from_dimacs_path("./data/small.cnf").unwrap();
            solver.add_cnf(inst.as_cnf().0).unwrap();
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
    ts.into()
}

#[proc_macro]
pub fn phasing_tests(tokens: TokenStream) -> TokenStream {
    let input = parse_macro_input!(tokens as MacroInput);
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
                solvers::{PhaseLit, Solve, SolverResult::Sat},
                types::TernaryVal::{True, False},
                var,
            };
            let mut solver = init_slv!(#slv);
            let inst: SatInstance =
                SatInstance::from_dimacs_path("./data/small.cnf").unwrap();
            solver.add_cnf(inst.as_cnf().0).unwrap();
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
    ts.into()
}
