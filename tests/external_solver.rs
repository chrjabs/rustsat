mod file_file {
    use rustsat::solvers::ExternalSolver;
    use rustsat::solvers::external;

    rustsat_solvertests::integration!(base:
        {
            let slv = std::env::var("RS_EXT_SOLVER").expect(
                "please set the `RS_EXT_SOLVER` environment variable to run tests for external solvers",
            );
            let infile = tempfile::NamedTempFile::new().unwrap();
            let outfile = tempfile::NamedTempFile::new().unwrap();
            ExternalSolver::new(
                std::process::Command::new(slv),
                external::InputVia::file_last(infile.path()),
                external::OutputVia::file(outfile.path()),
                "extsolver",
            )
        },
        true,
        true,
        true
    );
}

mod file_pipe {
    use rustsat::solvers::ExternalSolver;
    use rustsat::solvers::external;

    rustsat_solvertests::integration!(base:
        {
            let slv = std::env::var("RS_EXT_SOLVER").expect(
                "please set the `RS_EXT_SOLVER` environment variable to run tests for external solvers",
            );
            let infile = tempfile::NamedTempFile::new().unwrap();
            ExternalSolver::new(
                std::process::Command::new(slv),
                external::InputVia::file_last(infile.path()),
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
    use rustsat::solvers::ExternalSolver;
    use rustsat::solvers::external;

    rustsat_solvertests::integration!(base:
        {
            let slv = std::env::var("RS_EXT_SOLVER").expect(
                "please set the `RS_EXT_SOLVER` environment variable to run tests for external solvers",
            );
            ExternalSolver::new(
                std::process::Command::new(slv),
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
    use rustsat::solvers::ExternalSolver;
    use rustsat::solvers::external;

    rustsat_solvertests::integration!(base:
        {
            let slv = std::env::var("RS_EXT_SOLVER").expect(
                "please set the `RS_EXT_SOLVER` environment variable to run tests for external solvers",
            );
            ExternalSolver::new(
                std::process::Command::new(slv),
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
    use rustsat::solvers::ExternalSolver;
    use rustsat::solvers::external;

    rustsat_solvertests::integration!(base:
        {
            let slv = std::env::var("RS_EXT_SOLVER").expect(
                "please set the `RS_EXT_SOLVER` environment variable to run tests for external solvers",
            );
            let outfile = tempfile::NamedTempFile::new().unwrap();
            ExternalSolver::new(
                std::process::Command::new(slv),
                external::InputVia::pipe(),
                external::OutputVia::file(outfile.path()),
                "extsolver",
            )
        },
        true,
        true,
        true
    );
}

mod simulator {
    use rustsat::solvers::ExternalSolver;
    use rustsat::solvers::Initialize;
    use rustsat::solvers::external;
    use rustsat::solvers::simulators;

    struct Init;

    impl Initialize<ExternalSolver> for Init {
        fn init() -> ExternalSolver {
            let slv = std::env::var("RS_EXT_SOLVER").expect(
                "please set the `RS_EXT_SOLVER` environment variable to run tests for external solvers",
            );
            ExternalSolver::new(
                std::process::Command::new(slv),
                external::InputVia::pipe(),
                external::OutputVia::pipe(),
                "extsolver",
            )
        }
    }

    rustsat_solvertests::integration!(base:
        simulators::Incremental<ExternalSolver, Init>,
        true,
        true,
        true
    );

    rustsat_solvertests::integration!(incremental:
        simulators::Incremental<ExternalSolver, Init>,
        true,
        true,
        true,
        true
    );
}

#[test]
#[ignore]
fn gimsatul_deadlock() {
    let slv = std::env::var("RS_EXT_SOLVER").expect(
        "please set the `RS_EXT_SOLVER` environment variable to run tests for external solvers",
    );
    if AsRef::<std::path::Path>::as_ref(&slv)
        .file_name()
        .is_none_or(|slv_name| slv_name != std::ffi::OsStr::new("gimsatul"))
    {
        print!("skipping because not using gimsatul");
        return;
    }
    let mut cmd = std::process::Command::new(slv);
    cmd.arg("--threads=20");
    let mut slv = rustsat::solvers::ExternalSolver::new_default(cmd, "gimsatul-20");
    let inst =
        rustsat::instances::SatInstance::<rustsat::instances::BasicVarManager>::from_dimacs_path(
            format!(
                "{}/data/gimsatul-deadlock.cnf",
                std::env::var("CARGO_MANIFEST_DIR").unwrap()
            ),
        )
        .expect("failed to parse instance");
    rustsat::solvers::Solve::add_cnf_ref(&mut slv, inst.cnf())
        .expect("failed to add cnf to solver");
    let res = rustsat::solvers::Solve::solve(&mut slv).expect("failed solving");
    assert_eq!(res, rustsat::solvers::SolverResult::Unsat);
}
