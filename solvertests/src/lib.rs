mod integration;
mod unit;

#[macro_export]
macro_rules! test_inst {
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
            assert_eq!(inst.evaluate(&sol), rustsat::types::TernaryVal::True);
        }
    }};
}
