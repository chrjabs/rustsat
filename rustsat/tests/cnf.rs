use rustsat::{
    instances::Cnf,
    lit,
    solvers::{
        Solve, SolveIncremental,
        SolverResult::{Sat, Unsat},
    },
    types::Lit,
};
use rustsat_tools::{test_all, test_assignment};

#[test]
fn cnf_implications() {
    let mut cnf = Cnf::new();
    cnf.add_lit_impl_lit(lit![0], lit![1]);
    let mut solver = rustsat_minisat::core::Minisat::default();
    solver.add_cnf(cnf).unwrap();
    test_all!(solver, Vec::<Lit>::new(), Sat, Unsat, Sat, Sat);

    let mut cnf = Cnf::new();
    cnf.add_lit_impl_clause(lit![0], &[lit![1], lit![2]]);
    let mut solver = rustsat_minisat::core::Minisat::default();
    solver.add_cnf(cnf).unwrap();
    test_all!(
        solver,
        Vec::<Lit>::new(),
        Sat,
        Sat,
        Sat,
        Unsat,
        Sat,
        Sat,
        Sat,
        Sat
    );

    let mut cnf = Cnf::new();
    cnf.add_lit_impl_cube(lit![0], &[lit![1], lit![2]]);
    let mut solver = rustsat_minisat::core::Minisat::default();
    solver.add_cnf(cnf).unwrap();
    test_all!(
        solver,
        Vec::<Lit>::new(),
        Sat,
        Unsat,
        Unsat,
        Unsat,
        Sat,
        Sat,
        Sat,
        Sat
    );

    let mut cnf = Cnf::new();
    cnf.add_cube_impl_lit(&[lit![0], lit![1]], lit![2]);
    let mut solver = rustsat_minisat::core::Minisat::default();
    solver.add_cnf(cnf).unwrap();
    test_all!(
        solver,
        Vec::<Lit>::new(),
        Sat,
        Unsat,
        Sat,
        Sat,
        Sat,
        Sat,
        Sat,
        Sat
    );

    let mut cnf = Cnf::new();
    cnf.add_clause_impl_lit(&[lit![0], lit![1]], lit![2]);
    let mut solver = rustsat_minisat::core::Minisat::default();
    solver.add_cnf(cnf).unwrap();
    test_all!(
        solver,
        Vec::<Lit>::new(),
        Sat,
        Unsat,
        Sat,
        Unsat,
        Sat,
        Unsat,
        Sat,
        Sat
    );

    let mut cnf = Cnf::new();
    cnf.add_cube_impl_clause(&[lit![0], lit![1]], &[lit![2], lit![3]]);
    let mut solver = rustsat_minisat::core::Minisat::default();
    solver.add_cnf(cnf).unwrap();
    test_all!(
        solver,
        Vec::<Lit>::new(), //
        Sat,               // 1111
        Sat,               // 1110
        Sat,               // 1101
        Unsat,             // 1100
        Sat,               // 1011
        Sat,               // 1010
        Sat,               // 1001
        Sat,               // 1000
        Sat,               // 0111
        Sat,               // 0110
        Sat,               // 0101
        Sat,               // 0100
        Sat,               // 0011
        Sat,               // 0010
        Sat,               // 0001
        Sat                // 0000
    );

    let mut cnf = Cnf::new();
    cnf.add_clause_impl_clause(&[lit![0], lit![1]], &[lit![2], lit![3]]);
    let mut solver = rustsat_minisat::core::Minisat::default();
    solver.add_cnf(cnf).unwrap();
    test_all!(
        solver,
        Vec::<Lit>::new(), //
        Sat,               // 1111
        Sat,               // 1110
        Sat,               // 1101
        Unsat,             // 1100
        Sat,               // 1011
        Sat,               // 1010
        Sat,               // 1001
        Unsat,             // 1000
        Sat,               // 0111
        Sat,               // 0110
        Sat,               // 0101
        Unsat,             // 0100
        Sat,               // 0011
        Sat,               // 0010
        Sat,               // 0001
        Sat                // 0000
    );

    let mut cnf = Cnf::new();
    cnf.add_clause_impl_cube(&[lit![0], lit![1]], &[lit![2], lit![3]]);
    let mut solver = rustsat_minisat::core::Minisat::default();
    solver.add_cnf(cnf).unwrap();
    test_all!(
        solver,
        Vec::<Lit>::new(), //
        Sat,               // 1111
        Unsat,             // 1110
        Unsat,             // 1101
        Unsat,             // 1100
        Sat,               // 1011
        Unsat,             // 1010
        Unsat,             // 1001
        Unsat,             // 1000
        Sat,               // 0111
        Unsat,             // 0110
        Unsat,             // 0101
        Unsat,             // 0100
        Sat,               // 0011
        Sat,               // 0010
        Sat,               // 0001
        Sat                // 0000
    );

    let mut cnf = Cnf::new();
    cnf.add_cube_impl_cube(&[lit![0], lit![1]], &[lit![2], lit![3]]);
    let mut solver = rustsat_minisat::core::Minisat::default();
    solver.add_cnf(cnf).unwrap();
    test_all!(
        solver,
        Vec::<Lit>::new(), //
        Sat,               // 1111
        Unsat,             // 1110
        Unsat,             // 1101
        Unsat,             // 1100
        Sat,               // 1011
        Sat,               // 1010
        Sat,               // 1001
        Sat,               // 1000
        Sat,               // 0111
        Sat,               // 0110
        Sat,               // 0101
        Sat,               // 0100
        Sat,               // 0011
        Sat,               // 0010
        Sat,               // 0001
        Sat                // 0000
    );
}
