#[macro_export]
macro_rules! integration {
    (base: $solver:block, $ignore_small_sat:literal, $ignore_small_unsat:literal, $ignore_minisat_segfault:literal) => {
        #[test]
        #[cfg_attr($ignore_small_sat, ignore)]
        fn small_sat() {
            $crate::test_inst!(
                $solver,
                "data/AProVE11-12.cnf",
                rustsat::solvers::SolverResult::Sat
            );
        }

        #[test]
        #[cfg_attr($ignore_small_unsat, ignore)]
        fn small_unsat() {
            $crate::test_inst!(
                $solver,
                "data/smtlib-qfbv-aigs-ext_con_032_008_0256-tseitin.cnf",
                rustsat::solvers::SolverResult::Unsat
            );
        }

        #[test]
        #[cfg_attr($ignore_minisat_segfault, ignore)]
        fn minisat_segfault() {
            $crate::test_inst!(
                $solver,
                "data/minisat-segfault.cnf",
                rustsat::solvers::SolverResult::Unsat
            );
        }
    };
    (base: $solver:block, $ignore1:literal, $ignore2:literal) => {
        $crate::integration!(base: $solver, $ignore1, $ignore2, false);
    };
    (base: $solver:block, $ignore1:literal) => {
        $crate::integration!(base: $solver, $ignore1, false, false);
    };
    (base: $solver:block) => {
        $crate::integration!(base: $solver, false, false, false);
    };
    (base: $solver:ty, $ignore1:literal, $ignore2:literal, $ignore3:literal) => {
        $crate::integration!(base: {<$solver>::default()}, $ignore1, $ignore2, $ignore3);
    };
    (base: $solver:ty, $ignore1:literal, $ignore2:literal) => {
        $crate::integration!(base: {<$solver>::default()}, $ignore1, $ignore2, false);
    };
    (base: $solver:ty, $ignore1:literal) => {
        $crate::integration!(base: {<$solver>::default()}, $ignore1, false, false);
    };
    (base: $solver:ty) => {
        $crate::integration!(base: {<$solver>::default()}, false, false, false);
    };

    (incremental: $solver:block, $ignore_assumption_sequence:literal, $ignore_core_implied:literal, $ignore_assumption_empty:literal, $ignore_solution_caching:literal) => {
        #[test]
        #[cfg_attr($ignore_assumption_sequence, ignore)]
        fn assumption_sequence() {
            use rustsat::instances::SatInstance;
            use rustsat::lit;
            use rustsat::solvers::Solve;
            use rustsat::solvers::SolveIncremental;
            use rustsat::solvers::SolverResult;

            let mut solver = $solver;
            let inst: SatInstance =
                SatInstance::from_dimacs_path("data/small.cnf").unwrap();
            solver.add_cnf(inst.into_cnf().0).unwrap();
            let res = solver.solve().unwrap();
            assert_eq!(res, SolverResult::Sat);
            let res = solver.solve_assumps(&[!lit![0], !lit![1]]).unwrap();
            assert_eq!(res, SolverResult::Unsat);
            let mut core = solver.core().unwrap();
            core.sort_unstable();
            assert_eq!(core, vec![lit![0], lit![1]]);
            let res = solver
                .solve_assumps(&[lit![0], lit![1], lit![2], lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Unsat);
            assert!(solver.core().unwrap().len() >= 2);
            let res = solver
                .solve_assumps(&[lit![0], lit![1], lit![2], !lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Unsat);
            assert!(solver.core().unwrap().len() >= 2);
            let res = solver
                .solve_assumps(&[lit![0], lit![1], !lit![2], lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Unsat);
            assert!(solver.core().unwrap().len() >= 2);
            let res = solver
                .solve_assumps(&[lit![0], lit![1], !lit![2], !lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Sat);
            assert!(solver.core().is_err());
            let res = solver
                .solve_assumps(&[lit![0], !lit![1], lit![2], lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Unsat);
            assert!(solver.core().unwrap().len() >= 2);
            let res = solver
                .solve_assumps(&[lit![0], !lit![1], lit![2], !lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Sat);
            assert!(solver.core().is_err());
            let res = solver
                .solve_assumps(&[lit![0], !lit![1], !lit![2], lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Unsat);
            assert!(solver.core().unwrap().len() >= 2);
            let res = solver
                .solve_assumps(&[lit![0], !lit![1], !lit![2], !lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Unsat);
            assert!(solver.core().unwrap().len() >= 2);
            let res = solver
                .solve_assumps(&[!lit![0], lit![1], lit![2], lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Unsat);
            assert!(solver.core().unwrap().len() >= 2);
            let res = solver
                .solve_assumps(&[!lit![0], lit![1], lit![2], !lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Unsat);
            assert!(solver.core().unwrap().len() >= 2);
            let res = solver
                .solve_assumps(&[!lit![0], lit![1], !lit![2], lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Sat);
            assert!(solver.core().is_err());
            let res = solver
                .solve_assumps(&[!lit![0], lit![1], !lit![2], !lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Sat);
            assert!(solver.core().is_err());
            let res = solver
                .solve_assumps(&[!lit![0], !lit![1], lit![2], lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Unsat);
            assert!(solver.core().unwrap().len() >= 2);
            let res = solver
                .solve_assumps(&[!lit![0], !lit![1], lit![2], !lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Unsat);
            assert!(solver.core().unwrap().len() >= 2);
            let res = solver
                .solve_assumps(&[!lit![0], !lit![1], !lit![2], lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Unsat);
            assert!(solver.core().unwrap().len() >= 2);
            let res = solver
                .solve_assumps(&[!lit![0], !lit![1], !lit![2], !lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Unsat);
            assert!(solver.core().unwrap().len() >= 2);
        }

        #[test]
        #[cfg_attr($ignore_core_implied, ignore)]
        fn core_implied() {
            use rustsat::instances::SatInstance;
            use rustsat::lit;
            use rustsat::solvers::Solve;
            use rustsat::solvers::SolveIncremental;
            use rustsat::solvers::SolverResult;

            let mut solver = $solver;
            let inst: SatInstance =
                SatInstance::from_dimacs_path("data/small.cnf").unwrap();
            solver.add_cnf(inst.into_cnf().0).unwrap();
            let res = solver
                .solve_assumps(&[!lit![0], !lit![1], !lit![2], lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Unsat);
            let core = solver.core().unwrap();
            solver.add_clause_ref(&core[..]).unwrap();
            let res = solver
                .solve_assumps(&[lit![0], lit![1], lit![2], lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Unsat);
            let res = solver
                .solve_assumps(&[lit![0], lit![1], lit![2], !lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Unsat);
            let res = solver
                .solve_assumps(&[lit![0], lit![1], !lit![2], lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Unsat);
            let res = solver
                .solve_assumps(&[lit![0], lit![1], !lit![2], !lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Sat);
            let res = solver
                .solve_assumps(&[lit![0], !lit![1], lit![2], lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Unsat);
            let res = solver
                .solve_assumps(&[lit![0], !lit![1], lit![2], !lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Sat);
            let res = solver
                .solve_assumps(&[lit![0], !lit![1], !lit![2], lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Unsat);
            let res = solver
                .solve_assumps(&[lit![0], !lit![1], !lit![2], !lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Unsat);
            let res = solver
                .solve_assumps(&[!lit![0], lit![1], lit![2], lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Unsat);
            let res = solver
                .solve_assumps(&[!lit![0], lit![1], lit![2], !lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Unsat);
            let res = solver
                .solve_assumps(&[!lit![0], lit![1], !lit![2], lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Sat);
            let res = solver
                .solve_assumps(&[!lit![0], lit![1], !lit![2], !lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Sat);
            let res = solver
                .solve_assumps(&[!lit![0], !lit![1], lit![2], lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Unsat);
            let res = solver
                .solve_assumps(&[!lit![0], !lit![1], lit![2], !lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Unsat);
            let res = solver
                .solve_assumps(&[!lit![0], !lit![1], !lit![2], lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Unsat);
            let res = solver
                .solve_assumps(&[!lit![0], !lit![1], !lit![2], !lit![3]])
                .unwrap();
            assert_eq!(res, SolverResult::Unsat);
        }

        #[test]
        #[cfg_attr($ignore_assumption_empty, ignore)]
        fn assumption_empty() {
            use rustsat::instances::SatInstance;
            use rustsat::lit;
            use rustsat::solvers::Solve;
            use rustsat::solvers::SolveIncremental;
            use rustsat::solvers::SolverResult;

            let mut solver = $solver;
            let mut instance: SatInstance = SatInstance::new();
            let l1 = instance.new_lit();
            let l2 = instance.new_lit();
            instance.add_binary(l1, l2);
            instance.add_binary(!l1, l2);
            instance.add_binary(l1, !l2);
            instance.add_binary(!l1, !l2);
            solver.add_cnf(instance.into_cnf().0).unwrap();
            let res = solver.solve().unwrap();
            assert_eq!(res, SolverResult::Unsat);
            let res = solver.solve_assumps(&[]).unwrap();
            assert_eq!(res, SolverResult::Unsat);
            let mut core = solver.core().unwrap();
            assert_eq!(core, &[]);
        }

        #[test]
        #[cfg_attr($ignore_solution_caching, ignore)]
        fn solution_caching() {
            use rustsat::instances::SatInstance;
            use rustsat::lit;
            use rustsat::solvers::Solve;
            use rustsat::solvers::SolveIncremental;
            use rustsat::solvers::SolverResult;

            let mut solver = $solver;
            let res = solver.solve().unwrap();
            assert_eq!(res, SolverResult::Sat);
            solver.add_binary(lit![0], lit![1]).unwrap();
            let res = solver.solve().unwrap();
            assert_eq!(res, SolverResult::Sat);
            solver.add_binary(!lit![0], !lit![1]).unwrap();
            let res = solver.solve().unwrap();
            assert_eq!(res, SolverResult::Sat);
            solver.add_unit(!lit![0]).unwrap();
            let res = solver.solve().unwrap();
            assert_eq!(res, SolverResult::Sat);
            solver.add_unit(!lit![1]).unwrap();
            let res = solver.solve().unwrap();
            assert_eq!(res, SolverResult::Unsat);
        }
    };
    (incremental: $solver:block, $ignore1:literal, $ignore2:literal, $ignore3:literal) => {
        $crate::integration!(incremental: $solver, $ignore1, $ignore2, $ignore3, false);
    };
    (incremental: $solver:block, $ignore1:literal, $ignore2:literal) => {
        $crate::integration!(incremental: $solver, $ignore1, $ignore2, false, false);
    };
    (incremental: $solver:block, $ignore1:literal) => {
        $crate::integration!(incremental: $solver, $ignore1, false, false, false);
    };
    (incremental: $solver:block) => {
        $crate::integration!(incremental: $solver, false, false, false, false);
    };
    (incremental: $solver:ty, $ignore1:literal, $ignore2:literal, $ignore3:literal, $ignore4:literal) => {
        $crate::integration!(incremental: {<$solver>::default()}, $ignore1, $ignore2, $ignore3, $ignore4);
    };
    (incremental: $solver:ty, $ignore1:literal, $ignore2:literal, $ignore_assumption_empty:literal) => {
        $crate::integration!(incremental: {<$solver>::default()}, $ignore1, $ignore2, $ignore3, false);
    };
    (incremental: $solver:ty, $ignore1:literal, $ignore2:literal) => {
        $crate::integration!(incremental: {<$solver>::default()}, $ignore1, $ignore2, false, false);
    };
    (incremental: $solver:ty, $ignore1:literal) => {
        $crate::integration!(incremental: {<$solver>::default()}, $ignore1, false, false, false);
    };
    (incremental: $solver:ty) => {
        $crate::integration!(incremental: {<$solver>::default()}, false, false, false, false);
    };

    (learning: $solver:block, $ignore_learner_callback:literal) => {
        #[test]
        #[cfg_attr($ignore_learner_callback, ignore)]
        fn learner_callback() {
            use rustsat::instances::SatInstance;
            use rustsat::solvers::Learn;
            use rustsat::solvers::Solve;
            use rustsat::solvers::SolverResult;

            let mut n_learned = 0;
            {
                let mut solver = $solver;
                let inst: SatInstance =
                    SatInstance::from_dimacs_path("data/smtlib-qfbv-aigs-ext_con_032_008_0256-tseitin.cnf").unwrap();
                solver.add_cnf(inst.into_cnf().0).unwrap();
                solver.attach_learner(|_| {n_learned += 1;}, 42);
                let res = solver.solve().unwrap();
                assert_eq!(res, SolverResult::Unsat);
            }
            assert!(n_learned > 0);
        }
    };
    (learning: $solver:block) => {
        $crate::integration!(learning: $solver, false);
    };
    (learning: $solver:ty, $ignore1:literal) => {
        $crate::integration!(learning: {<$solver>::default()}, $ignore1);
    };
    (learning: $solver:ty) => {
        $crate::integration!(learning: {<$solver>::default()}, false);
    };

    (phasing: $solver:block, $ignore_user_phases:literal) => {
        #[test]
        #[cfg_attr($ignore_user_phases, ignore)]
        fn user_phases() {
            use rustsat::instances::SatInstance;
            use rustsat::lit;
            use rustsat::solvers::PhaseLit;
            use rustsat::solvers::Solve;
            use rustsat::solvers::SolverResult;
            use rustsat::types::TernaryVal;
            use rustsat::var;

            let mut solver = $solver;
            let inst: SatInstance =
                SatInstance::from_dimacs_path("data/small.cnf").unwrap();
            solver.add_cnf(inst.into_cnf().0).unwrap();
            solver.phase_lit(lit![0]).unwrap();
            solver.phase_lit(!lit![1]).unwrap();
            solver.phase_lit(lit![2]).unwrap();
            solver.phase_lit(!lit![3]).unwrap();
            let res = solver.solve().unwrap();
            assert_eq!(res, SolverResult::Sat);
            let sol = solver.solution(var![3]).unwrap();
            assert_eq!(sol.lit_value(lit![0]), TernaryVal::True);
            assert_eq!(sol.lit_value(lit![1]), TernaryVal::False);
            assert_eq!(sol.lit_value(lit![2]), TernaryVal::True);
            assert_eq!(sol.lit_value(lit![3]), TernaryVal::False);
            solver.unphase_var(var![1]).unwrap();
            solver.unphase_var(var![0]).unwrap();
        }
    };
    (phasing: $solver:block) => {
        $crate::integration!(phasing: $solver, false);
    };
    (phasing: $solver:ty, $ignore1:literal) => {
        $crate::integration!(phasing: {<$solver>::default()}, $ignore1);
    };
    (phasing: $solver:ty) => {
        $crate::integration!(phasing: {<$solver>::default()}, false);
    };

    (flipping: $solver:block, $ignore_flipping_lits:literal) => {
        #[test]
        #[cfg_attr($ignore_flipping_lits, ignore)]
        fn flipping_lits() {
            use rustsat::clause;
            use rustsat::lit;
            use rustsat::solvers::FlipLit;
            use rustsat::solvers::Solve;
            use rustsat::solvers::SolveIncremental;
            use rustsat::solvers::SolverResult;

            let mut solver = $solver;
            solver.add_clause(clause![lit![0]]).unwrap();
            solver.add_clause(clause![lit![1], lit![2]]).unwrap();
            assert_eq!(
                solver.solve_assumps(&[lit![1], lit![2]]).unwrap(),
                SolverResult::Sat
            );
            assert!(!solver.is_flippable(!lit![0]).unwrap());
            assert!(solver.is_flippable(!lit![1]).unwrap());
            assert!(solver.is_flippable(!lit![2]).unwrap());
            assert!(solver.flip_lit(!lit![1]).unwrap());
            assert!(!solver.is_flippable(!lit![2]).unwrap());
        }
    };
    (flipping: $solver:block) => {
        $crate::integration!(flipping: $solver, false);
    };
    (flipping: $solver:ty, $ignore1:literal) => {
        $crate::integration!(flipping: {<$solver>::default()}, $ignore1);
    };
    (flipping: $solver:ty) => {
        $crate::integration!(flipping: {<$solver>::default()}, false);
    };

    (internal-stats: $solver:block, $ignore_internal_stats:literal) => {
        #[test]
        #[cfg_attr($ignore_internal_stats, ignore)]
        fn internal_stats() {
            use rustsat::instances::SatInstance;
            use rustsat::solvers::GetInternalStats;
            use rustsat::solvers::Solve;
            use rustsat::solvers::SolverResult;

            let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
            let mut solver = $solver;
            assert_eq!(solver.propagations(), 0);
            assert_eq!(solver.decisions(), 0);
            assert_eq!(solver.conflicts(), 0);
            let inst: SatInstance = SatInstance::from_dimacs_path(format!("{manifest}/data/AProVE11-12.cnf"))
                .expect("failed to parse instance");
            solver.add_cnf_ref(inst.cnf()).expect("failed to add cnf to solver");
            let res = solver.solve().expect("failed solving");
            assert_eq!(res, SolverResult::Sat);
            assert!(solver.propagations() > 0);
            assert!(solver.decisions() > 0);
            assert!(solver.conflicts() > 0);
        }
    };
    (internal-stats: $solver:block) => {
        $crate::integration!(internal-stats: $solver, false);
    };
    (internal-stats: $solver:ty, $ignore1:literal) => {
        $crate::integration!(internal-stats: {<$solver>::default()}, $ignore1);
    };
    (internal-stats: $solver:ty) => {
        $crate::integration!(internal-stats: {<$solver>::default()}, false);
    };
}
