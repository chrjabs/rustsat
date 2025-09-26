mod file_file {
    use rustsat::solvers::{external, ExternalSolver};
    use std::process::Command;

    rustsat_solvertests::base_tests!(
        {
            let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
            let slv = std::env::var("RS_EXT_SOLVER").expect(
                "please set the `RS_EXT_SOLVER` environment variable to run tests for external solvers",
            );
            ExternalSolver::new(
                Command::new(slv),
                external::InputVia::file_last(format!(
                    "{manifest}/target/extsolver_file_file_{testid}.cnf"
                )),
                external::OutputVia::file(format!(
                    "{manifest}/target/extsolver_file_file_{testid}.log"
                )),
                "extsolver",
            )
        },
        true,
        true,
        true
    );
}

mod file_pipe {
    use rustsat::solvers::{external, ExternalSolver};
    use std::process::Command;

    rustsat_solvertests::base_tests!(
        {
            let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
            let slv = std::env::var("RS_EXT_SOLVER").expect(
                "please set the `RS_EXT_SOLVER` environment variable to run tests for external solvers",
            );
            ExternalSolver::new(
                Command::new(slv),
                external::InputVia::file_last(format!(
                    "{manifest}/target/extsolver_file_pipe_{testid}.cnf"
                )),
                external::OutputVia::pipe(),
                "extsolver",
            )
        },
        true,
        true,
        true
    );
}

mod tempfile_pipe {
    use rustsat::solvers::{external, ExternalSolver};
    use std::process::Command;

    rustsat_solvertests::base_tests!(
        {
            let slv = std::env::var("RS_EXT_SOLVER").expect(
                "please set the `RS_EXT_SOLVER` environment variable to run tests for external solvers",
            );
            ExternalSolver::new(
                Command::new(slv),
                external::InputVia::tempfile_last(),
                external::OutputVia::pipe(),
                "extsolver",
            )
        },
        true,
        true,
        true
    );
}

mod pipe_pipe {
    use rustsat::solvers::{external, ExternalSolver};
    use std::process::Command;

    rustsat_solvertests::base_tests!(
        {
            let slv = std::env::var("RS_EXT_SOLVER").expect(
                "please set the `RS_EXT_SOLVER` environment variable to run tests for external solvers",
            );
            ExternalSolver::new(
                Command::new(slv),
                external::InputVia::pipe(),
                external::OutputVia::pipe(),
                "extsolver",
            )
        },
        true,
        true,
        true
    );
}

mod pipe_file {
    use rustsat::solvers::{external, ExternalSolver};
    use std::process::Command;

    rustsat_solvertests::base_tests!(
        {
            let slv = std::env::var("RS_EXT_SOLVER").expect(
                "please set the `RS_EXT_SOLVER` environment variable to run tests for external solvers",
            );
            let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
            ExternalSolver::new(
                Command::new(slv),
                external::InputVia::pipe(),
                external::OutputVia::file(format!(
                    "{manifest}/target/extsolver_pipe_file_{testid}.log"
                )),
                "extsolver",
            )
        },
        true,
        true,
        true
    );
}

mod simulator {
    use rustsat::solvers::{external, simulators, ExternalSolver, Initialize};
    use std::process::Command;

    struct Init;

    impl Initialize<ExternalSolver> for Init {
        fn init() -> ExternalSolver {
            let slv = std::env::var("RS_EXT_SOLVER").expect(
                "please set the `RS_EXT_SOLVER` environment variable to run tests for external solvers",
            );
            ExternalSolver::new(
                Command::new(slv),
                external::InputVia::pipe(),
                external::OutputVia::pipe(),
                "extsolver",
            )
        }
    }

    rustsat_solvertests::base_tests!(
        simulators::Incremental<ExternalSolver, Init>,
        true,
        true,
        true
    );

    rustsat_solvertests::incremental_tests!(
        simulators::Incremental<ExternalSolver, Init>,
        true,
        true,
        true
    );
}
