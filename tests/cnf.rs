use rustsat::instances::Cnf;
use rustsat::lit;
use rustsat::solvers::Solve;
use rustsat::solvers::SolveIncremental;
use rustsat::solvers::SolverResult;
use rustsat::types::Lit;
use rustsat_tools::test_all;

#[test]
fn cnf_implications() {
    let mut cnf = Cnf::new();
    cnf.add_lit_impl_lit(lit![0], lit![1]);
    let mut solver = rustsat_minisat::core::Minisat::default();
    solver.add_cnf(cnf).unwrap();
    test_all!(
        solver,
        Vec::<Lit>::new(),
        SolverResult::Sat,
        SolverResult::Unsat,
        SolverResult::Sat,
        SolverResult::Sat
    );

    let mut cnf = Cnf::new();
    cnf.add_lit_impl_clause(lit![0], &[lit![1], lit![2]]);
    let mut solver = rustsat_minisat::core::Minisat::default();
    solver.add_cnf(cnf).unwrap();
    test_all!(
        solver,
        Vec::<Lit>::new(),
        SolverResult::Sat,
        SolverResult::Sat,
        SolverResult::Sat,
        SolverResult::Unsat,
        SolverResult::Sat,
        SolverResult::Sat,
        SolverResult::Sat,
        SolverResult::Sat
    );

    let mut cnf = Cnf::new();
    cnf.add_lit_impl_cube(lit![0], &[lit![1], lit![2]]);
    let mut solver = rustsat_minisat::core::Minisat::default();
    solver.add_cnf(cnf).unwrap();
    test_all!(
        solver,
        Vec::<Lit>::new(),
        SolverResult::Sat,
        SolverResult::Unsat,
        SolverResult::Unsat,
        SolverResult::Unsat,
        SolverResult::Sat,
        SolverResult::Sat,
        SolverResult::Sat,
        SolverResult::Sat
    );

    let mut cnf = Cnf::new();
    cnf.add_cube_impl_lit(&[lit![0], lit![1]], lit![2]);
    let mut solver = rustsat_minisat::core::Minisat::default();
    solver.add_cnf(cnf).unwrap();
    test_all!(
        solver,
        Vec::<Lit>::new(),
        SolverResult::Sat,
        SolverResult::Unsat,
        SolverResult::Sat,
        SolverResult::Sat,
        SolverResult::Sat,
        SolverResult::Sat,
        SolverResult::Sat,
        SolverResult::Sat
    );

    let mut cnf = Cnf::new();
    cnf.add_clause_impl_lit(&[lit![0], lit![1]], lit![2]);
    let mut solver = rustsat_minisat::core::Minisat::default();
    solver.add_cnf(cnf).unwrap();
    test_all!(
        solver,
        Vec::<Lit>::new(),
        SolverResult::Sat,
        SolverResult::Unsat,
        SolverResult::Sat,
        SolverResult::Unsat,
        SolverResult::Sat,
        SolverResult::Unsat,
        SolverResult::Sat,
        SolverResult::Sat
    );

    let mut cnf = Cnf::new();
    cnf.add_cube_impl_clause(&[lit![0], lit![1]], &[lit![2], lit![3]]);
    let mut solver = rustsat_minisat::core::Minisat::default();
    solver.add_cnf(cnf).unwrap();
    test_all!(
        solver,
        Vec::<Lit>::new(),
        SolverResult::Sat,   // 1111
        SolverResult::Sat,   // 1110
        SolverResult::Sat,   // 1101
        SolverResult::Unsat, // 1100
        SolverResult::Sat,   // 1011
        SolverResult::Sat,   // 1010
        SolverResult::Sat,   // 1001
        SolverResult::Sat,   // 1000
        SolverResult::Sat,   // 0111
        SolverResult::Sat,   // 0110
        SolverResult::Sat,   // 0101
        SolverResult::Sat,   // 0100
        SolverResult::Sat,   // 0011
        SolverResult::Sat,   // 0010
        SolverResult::Sat,   // 0001
        SolverResult::Sat    // 0000
    );

    let mut cnf = Cnf::new();
    cnf.add_clause_impl_clause(&[lit![0], lit![1]], &[lit![2], lit![3]]);
    let mut solver = rustsat_minisat::core::Minisat::default();
    solver.add_cnf(cnf).unwrap();
    test_all!(
        solver,
        Vec::<Lit>::new(),
        SolverResult::Sat,   // 1111
        SolverResult::Sat,   // 1110
        SolverResult::Sat,   // 1101
        SolverResult::Unsat, // 1100
        SolverResult::Sat,   // 1011
        SolverResult::Sat,   // 1010
        SolverResult::Sat,   // 1001
        SolverResult::Unsat, // 1000
        SolverResult::Sat,   // 0111
        SolverResult::Sat,   // 0110
        SolverResult::Sat,   // 0101
        SolverResult::Unsat, // 0100
        SolverResult::Sat,   // 0011
        SolverResult::Sat,   // 0010
        SolverResult::Sat,   // 0001
        SolverResult::Sat    // 0000
    );

    let mut cnf = Cnf::new();
    cnf.add_clause_impl_cube(&[lit![0], lit![1]], &[lit![2], lit![3]]);
    let mut solver = rustsat_minisat::core::Minisat::default();
    solver.add_cnf(cnf).unwrap();
    test_all!(
        solver,
        Vec::<Lit>::new(),
        SolverResult::Sat,   // 1111
        SolverResult::Unsat, // 1110
        SolverResult::Unsat, // 1101
        SolverResult::Unsat, // 1100
        SolverResult::Sat,   // 1011
        SolverResult::Unsat, // 1010
        SolverResult::Unsat, // 1001
        SolverResult::Unsat, // 1000
        SolverResult::Sat,   // 0111
        SolverResult::Unsat, // 0110
        SolverResult::Unsat, // 0101
        SolverResult::Unsat, // 0100
        SolverResult::Sat,   // 0011
        SolverResult::Sat,   // 0010
        SolverResult::Sat,   // 0001
        SolverResult::Sat    // 0000
    );

    let mut cnf = Cnf::new();
    cnf.add_cube_impl_cube(&[lit![0], lit![1]], &[lit![2], lit![3]]);
    let mut solver = rustsat_minisat::core::Minisat::default();
    solver.add_cnf(cnf).unwrap();
    test_all!(
        solver,
        Vec::<Lit>::new(),
        SolverResult::Sat,   // 1111
        SolverResult::Unsat, // 1110
        SolverResult::Unsat, // 1101
        SolverResult::Unsat, // 1100
        SolverResult::Sat,   // 1011
        SolverResult::Sat,   // 1010
        SolverResult::Sat,   // 1001
        SolverResult::Sat,   // 1000
        SolverResult::Sat,   // 0111
        SolverResult::Sat,   // 0110
        SolverResult::Sat,   // 0101
        SolverResult::Sat,   // 0100
        SolverResult::Sat,   // 0011
        SolverResult::Sat,   // 0010
        SolverResult::Sat,   // 0001
        SolverResult::Sat    // 0000
    );
}
