extern crate proc_macro;

use proc_macro2::TokenStream;
use quote::quote;
use syn::{LitStr, Type};

pub fn basic(slv: Type, signature: LitStr, multi_threaded: bool) -> TokenStream {
    let mut ts = quote! {
        #[test]
        fn build_destroy() {
            let _solver = #slv::default();
        }

        #[test]
        fn build_two() {
            let _solver1 = #slv::default();
            let _solver2 = #slv::default();
        }

        #[test]
        fn signature() {
            use rustsat::solvers::Solve;
            let pat = #signature;
            let sig = #slv::default().signature();
            let mut pat_chars = pat.chars();
            let mut sig_chars = sig.chars().peekable();
            let mut alt_depth = 0;
            while sig_chars.peek().is_some() {
                let pat_char = pat_chars
                    .next()
                    .unwrap_or_else(|| panic!("signature `{sig}` does not match pattern `{pat}`"));
                if pat_char == '(' {
                    // patterns of form `(alt1|alt2)` represent alternatives
                    // NOTE: the matcher does not backtrack, so the above example pattern will actually
                    // match `aalt2`
                    alt_depth += 1;
                    continue;
                }
                if pat_char == ')' {
                    assert!(alt_depth > 0, "malformed pattern `{pat}`");
                    alt_depth -= 1;
                    continue;
                }
                if pat_char == '[' {
                    // blocks in square brackets match any sequence of numeric digits
                    loop {
                        match pat_chars.next() {
                            Some(']') => break,
                            None => panic!("signature `{sig}` does not match pattern `{pat}`"),
                            _ => (),
                        }
                    }
                    assert!(
                        sig_chars.next().is_some_and(char::is_numeric),
                        "signature `{sig}` does not match pattern `{pat}`"
                    );
                    loop {
                        match sig_chars.peek() {
                            Some(c) if !c.is_numeric() => break,
                            Some(_) => pat_chars.next(),
                            None => break,
                        };
                    }
                    continue;
                }
                if sig_chars.peek().is_some_and(|c| *c == pat_char) {
                    sig_chars.next().unwrap();
                } else {
                    assert!(
                        alt_depth > 0,
                        "signature `{sig}` does not match pattern `{pat}`"
                    );
                    // find next alternative
                    let mut children = 0;
                    loop {
                        match pat_chars.next() {
                            Some('|') => {
                                if children == 0 {
                                    break;
                                }
                            }
                            Some('(') => children += 1,
                            Some(')') => {
                                assert!(
                                    children > 0,
                                    "signature `{sig}` does not match pattern `{pat}`"
                                );
                                children -= 1;
                            }
                            None => panic!("malformed pattern `{pat}`"),
                            _ => (),
                        }
                    }
                }
            }
            for _ in 0..alt_depth {
                match pat_chars.next() {
                    None => panic!("malformed pattern `{pat}`"),
                    Some(')') => (),
                    Some('|') => loop {
                        match pat_chars.next() {
                            Some(')') => break,
                            None => panic!("malformed pattern `{pat}`"),
                            _ => (),
                        }
                    },
                    _ => panic!("signature `{sig}` does not match pattern `{pat}`"),
                }
            }
            assert!(
                pat_chars.next().is_none(),
                "signature `{sig}` does not match pattern `{pat}`"
            );
        }

        #[test]
        fn stats() {
            use rustsat::{lit, var, solvers::{Solve, SolveStats}};

            let mut solver = #slv::default();

            assert_eq!(solver.n_clauses(), 0);
            assert_eq!(solver.max_var(), None);
            assert_eq!(solver.n_vars(), 0);

            solver.add_binary(lit![0], !lit![1]).unwrap();
            solver.add_binary(lit![1], !lit![2]).unwrap();
            solver.add_binary(lit![2], !lit![3]).unwrap();
            solver.add_binary(lit![3], !lit![4]).unwrap();
            solver.add_binary(lit![4], !lit![5]).unwrap();
            solver.add_binary(lit![5], !lit![6]).unwrap();
            solver.add_binary(lit![6], !lit![7]).unwrap();
            solver.add_binary(lit![7], !lit![8]).unwrap();
            solver.add_binary(lit![8], !lit![9]).unwrap();

            assert_eq!(solver.n_sat_solves(), 0);
            assert_eq!(solver.n_unsat_solves(), 0);
            assert_eq!(solver.n_terminated(), 0);
            assert_eq!(solver.n_solves(), 0);
            assert_eq!(solver.n_clauses(), 9);
            assert_eq!(solver.max_var(), Some(var![9]));
            assert_eq!(solver.n_vars(), 10);
            assert!((solver.avg_clause_len() - 2.).abs() < f32::EPSILON);

            solver.solve().unwrap();

            assert_eq!(solver.n_sat_solves(), 1);
            assert_eq!(solver.n_unsat_solves(), 0);
            assert_eq!(solver.n_terminated(), 0);
            assert_eq!(solver.n_solves(), 1);
        }

        #[test]
        fn tiny_instance_sat() {
            use rustsat::{lit, solvers::{Solve, SolverResult}};

            let mut solver = #slv::default();
            solver.add_binary(lit![0], !lit![1]).unwrap();
            solver.add_binary(lit![1], !lit![2]).unwrap();
            let ret = solver.solve();
            match ret {
                Err(e) => panic!("got error when solving: {}", e),
                Ok(res) => assert_eq!(res, SolverResult::Sat),
            }
            solver.full_solution().unwrap();
        }

        #[test]
        fn tiny_instance_unsat() {
            use rustsat::{lit, solvers::{Solve, SolverResult}};

            let mut solver = #slv::default();
            solver.add_unit(!lit![0]).unwrap();
            solver.add_binary(lit![0], !lit![1]).unwrap();
            solver.add_binary(lit![1], !lit![2]).unwrap();
            solver.add_unit(lit![2]).unwrap();
            let ret = solver.solve();
            match ret {
                Err(e) => panic!("got error when solving: {}", e),
                Ok(res) => assert_eq!(res, SolverResult::Unsat),
            }
            assert!(solver.full_solution().is_err());
        }
    };
    if multi_threaded {
        ts.extend(quote! {
            #[test]
            fn tiny_instance_multithreaded_sat() {
                use std::{sync::{Arc, Mutex}, thread};
                use rustsat::{lit, var, types::TernaryVal, solvers::{Solve, SolverResult}};

                let mutex_solver = Arc::new(Mutex::new(#slv::default()));

                {
                    // Build in one thread
                    let mut solver = mutex_solver.lock().unwrap();
                    solver.add_binary(lit![0], !lit![1]).unwrap();
                    solver.add_unit(lit![0]).unwrap();
                    solver.add_binary(lit![1], !lit![2]).unwrap();
                }

                // Now in another thread
                let s = mutex_solver.clone();
                let ret = thread::spawn(move || {
                    let mut solver = s.lock().unwrap();
                    solver.solve()
                })
                .join()
                .unwrap();
                match ret {
                    Err(e) => panic!("got error when solving: {}", e),
                    Ok(res) => assert_eq!(res, SolverResult::Sat),
                }

                // Finally, back in the main thread
                let ret = {
                    let solver = mutex_solver.lock().unwrap();
                    solver.full_solution()
                };

                match ret {
                    Err(e) => panic!("got error when solving: {}", e),
                    Ok(res) => assert_eq!(res.var_value(var![0]), TernaryVal::True),
                }
            }
        });
    };
    ts
}

pub fn termination(slv: Type) -> TokenStream {
    quote! {
        #[test]
        fn termination_callback() {
            use rustsat::{lit, solvers::{Solve, SolverResult, Terminate, ControlSignal}};

            let mut solver = #slv::default();
            solver.add_binary(lit![0], !lit![1]).unwrap();
            solver.add_binary(lit![1], !lit![2]).unwrap();
            solver.add_binary(lit![2], !lit![3]).unwrap();
            solver.add_binary(lit![3], !lit![4]).unwrap();
            solver.add_binary(lit![4], !lit![5]).unwrap();
            solver.add_binary(lit![5], !lit![6]).unwrap();
            solver.add_binary(lit![6], !lit![7]).unwrap();
            solver.add_binary(lit![7], !lit![8]).unwrap();
            solver.add_binary(lit![8], !lit![9]).unwrap();

            solver.attach_terminator(|| ControlSignal::Terminate);

            let ret = solver.solve();

            match ret {
                Err(e) => panic!("got error when solving: {}", e),
                Ok(res) => assert_eq!(res, SolverResult::Interrupted),
            }

            // Note: since IPASIR doesn't specify _when_ the terminator callback needs
            // to be called, there is no guarantee that the callback is actually
            // called during solving. This might cause this test to fail with some solvers.
        }
    }
}

pub fn learn(slv: Type) -> TokenStream {
    quote! {
        #[test]
        fn learner_callback() {
            use rustsat::{lit, solvers::{Solve, SolverResult, Learn}};

            let mut solver = #slv::default();
            solver.add_binary(lit![0], !lit![1]).unwrap();
            solver.add_binary(lit![1], !lit![2]).unwrap();
            solver.add_binary(lit![2], !lit![3]).unwrap();
            solver.add_binary(lit![3], !lit![4]).unwrap();
            solver.add_binary(lit![4], !lit![5]).unwrap();
            solver.add_binary(lit![5], !lit![6]).unwrap();
            solver.add_binary(lit![6], !lit![7]).unwrap();
            solver.add_binary(lit![7], !lit![8]).unwrap();
            solver.add_binary(lit![8], !lit![9]).unwrap();
            solver.add_unit(lit![9]).unwrap();
            solver.add_unit(!lit![0]).unwrap();

            let mut cl_len = 0;

            solver.attach_learner(
                |clause| {
                    cl_len = clause.len();
                },
                10,
            );

            let ret = solver.solve();

            drop(solver);

            // Note: it is hard to create a testing instance on which clause learning
            // actually happens and therefore it is not actually tested if the
            // callback is called

            match ret {
                Err(e) => panic!("got error when solving: {}", e),
                Ok(res) => assert_eq!(res, SolverResult::Unsat),
            }
        }
    }
}

pub fn freezing(slv: Type) -> TokenStream {
    quote! {
        #[test]
        fn freezing() {
            use rustsat::{lit, var, solvers::{Solve, FreezeVar}};
            let mut solver = #slv::default();
            solver.add_binary(lit![0], !lit![1]).unwrap();

            solver.freeze_var(var![0]).unwrap();

            assert!(solver.is_frozen(var![0]).unwrap());

            solver.melt_var(var![0]).unwrap();

            assert!(!solver.is_frozen(var![0]).unwrap());
        }
    }
}

pub fn propagate(slv: Type) -> TokenStream {
    quote! {
        #[test]
        fn propagate() {
            use rustsat::{lit, solvers::{Solve, Propagate}};
            let mut solver = #slv::default();
            solver.add_binary(!lit![0], lit![1]).unwrap();
            solver.add_binary(!lit![1], lit![2]).unwrap();
            solver.add_binary(!lit![2], lit![3]).unwrap();

            let res = solver.propagate(&[], false).unwrap();

            assert!(!res.conflict);
            assert!(res.propagated.is_empty());

            let res = solver.propagate(&[lit![0]], false).unwrap();

            assert!(!res.conflict);
            assert_eq!(res.propagated.len(), 4);

            solver.add_unit(!lit![3]).unwrap();

            let res = solver.propagate(&[lit![0]], false).unwrap();
            assert!(res.conflict);
        }
    }
}
