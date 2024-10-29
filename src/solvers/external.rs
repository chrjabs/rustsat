//! # Solver Interface for External Executables

use std::{
    fs, io,
    path::{Path, PathBuf},
    process::{self, Command},
};

use crate::{
    instances::{
        fio::{self, SolverOutput},
        Cnf,
    },
    types::{Assignment, Cl, Clause},
};

use super::Solve;

/// Specifies what argument position the instance is passed to the solver at
///
/// Most solvers expect the instance as the last argument
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
enum InstanceArg {
    /// Pass the instance file path as the first solver argument
    First,
    /// Pass the instance file path as the last argument
    #[default]
    Last,
}

/// Options for how the input instance should be passed to the external solver
#[derive(Debug, Clone)]
pub struct InputVia(InputViaInt);

#[derive(Debug, Clone)]
enum InputViaInt {
    /// Passes the instance by writing it to a file at the specified path
    ///
    /// The file will _not_ be removed afterwards
    File(PathBuf, InstanceArg),
    /// Passes the instance by writing it to a temporary file that will automatically be removed
    TempFile(InstanceArg),
    /// Passes the instance through a pipe to `stdin`
    ///
    /// Note, not all solvers support reading input from `stdin`
    Pipe,
}

impl InputVia {
    /// Pass the input via a persistent file at `path`, passed to the solver as the last argument
    #[must_use]
    pub fn file_last<P: AsRef<Path>>(path: P) -> Self {
        InputVia(InputViaInt::File(
            path.as_ref().to_path_buf(),
            InstanceArg::Last,
        ))
    }

    /// Pass the input via a persistent file at `path`, passed to the solver as the first argument
    #[must_use]
    pub fn file_first<P: AsRef<Path>>(path: P) -> Self {
        InputVia(InputViaInt::File(
            path.as_ref().to_path_buf(),
            InstanceArg::First,
        ))
    }

    /// Pass the input via a temporary file, passed to the solver as the last argument
    #[must_use]
    pub fn tempfile_last() -> Self {
        InputVia(InputViaInt::TempFile(InstanceArg::Last))
    }

    /// Pass the input via a temporary file, passed to the solver as the first argument
    #[must_use]
    pub fn tempfile_first() -> Self {
        InputVia(InputViaInt::TempFile(InstanceArg::First))
    }

    /// Pass the input via a pipe to `<stdin>`
    #[must_use]
    pub fn pipe() -> Self {
        InputVia(InputViaInt::Pipe)
    }
}

impl Default for InputVia {
    fn default() -> Self {
        InputVia(InputViaInt::TempFile(InstanceArg::default()))
    }
}

/// Options for how the output of the solver is read by RustSAT
#[derive(Debug, Clone, Default)]
pub struct OutputVia(OutputViaInt);

#[derive(Debug, Clone, Default)]
enum OutputViaInt {
    /// The solver output is written to a file at the given path that is not automatically deleted
    File(PathBuf),
    /// The solver output is read directly through a pipe
    #[default]
    Pipe,
}

impl OutputVia {
    /// Process the solver output via a persistent file at `path`
    #[must_use]
    pub fn file<P: AsRef<Path>>(path: P) -> Self {
        OutputVia(OutputViaInt::File(path.as_ref().to_path_buf()))
    }

    /// Process the solver output via a pipe from `<stdout>`
    #[must_use]
    pub fn pipe() -> Self {
        OutputVia(OutputViaInt::Pipe)
    }
}

/// A solver called via an external executable
///
/// This solver will perform a call to the solver executable via [`Command`] and parse the solver
/// output via [`fio::parse_sat_solver_output`]
#[derive(Debug)]
pub struct Solver {
    signature: &'static str,
    state: SolverState,
}

#[derive(Debug)]
enum SolverState {
    Pre(SolverPre),
    Post(fio::SolverOutput),
}

/// State before calling the external solver
#[derive(Debug)]
struct SolverPre {
    cmd: Command,
    input: InputVia,
    output: OutputVia,
    cnf: Cnf,
    n_vars: u32,
}

impl Solver {
    /// Initializes a solver with a [`Command`] that is fully set up, except for the input instance
    ///
    /// # Notes
    ///
    /// - If input is passed via a file with a path that ends in a compression extension, RustSAT
    ///     will write a compressed file
    /// - If the solver output is processed via a file, compression is _not_ supported
    /// - If [`Command::env_clear`] was called on the command and the input is passed via a
    ///     file as the first argument, the fact that the environment has been cleared might be
    ///     forgotten
    ///
    /// # Example
    ///
    /// ```
    /// use std::process::Command;
    /// use rustsat::solvers::{ExternalSolver, external};
    /// let solver = ExternalSolver::new(
    ///     Command::new("<path to solver binary>"),
    ///     external::InputVia::tempfile_last(),
    ///     external::OutputVia::pipe(),
    ///     "solver-signature",
    /// );
    /// ```
    /// After this initialization, the `solver` instance can be used with the [`Solve`] trait.
    #[must_use]
    pub fn new(cmd: Command, input: InputVia, output: OutputVia, signature: &'static str) -> Self {
        Solver {
            signature,
            state: SolverState::Pre(SolverPre {
                cmd,
                input,
                output,
                cnf: Cnf::default(),
                n_vars: 0,
            }),
        }
    }

    /// Initializes a solver with default values for [`InputVia`] and [`OutputVia`]
    ///
    /// The default values are passing the input via a temporary file and processing the output via
    /// a pipe.
    ///
    /// # Example
    ///
    /// ```
    /// use std::process::Command;
    /// use rustsat::solvers::{ExternalSolver, external};
    /// let solver = ExternalSolver::new_default(
    ///     Command::new("<path to solver binary>"),
    ///     "solver-signature",
    /// );
    /// ```
    /// After this initialization, the `solver` instance can be used with the [`Solve`] trait.
    #[must_use]
    pub fn new_default(cmd: Command, signature: &'static str) -> Self {
        Solver::new(cmd, InputVia::default(), OutputVia::default(), signature)
    }
}

impl Solve for Solver {
    fn signature(&self) -> &'static str {
        self.signature
    }

    fn solve(&mut self) -> anyhow::Result<super::SolverResult> {
        if let SolverState::Post(state) = &self.state {
            anyhow::bail!(super::StateError {
                required_state: super::SolverState::Input,
                actual_state: match state {
                    fio::SolverOutput::Sat(_) => super::SolverState::Sat,
                    fio::SolverOutput::Unsat => super::SolverState::Unsat,
                    fio::SolverOutput::Unknown => super::SolverState::Unknown,
                }
            });
        }
        let SolverState::Pre(config) =
            std::mem::replace(&mut self.state, SolverState::Post(SolverOutput::Unknown))
        else {
            unreachable!()
        };
        let post = call_external(config)?;
        let res = post.result();
        self.state = SolverState::Post(post);
        Ok(res)
    }

    fn lit_val(&self, lit: crate::types::Lit) -> anyhow::Result<crate::types::TernaryVal> {
        match &self.state {
            SolverState::Pre(_) => anyhow::bail!(super::StateError {
                required_state: super::SolverState::Sat,
                actual_state: super::SolverState::Input
            }),
            SolverState::Post(SolverOutput::Sat(sol)) => Ok(sol.lit_value(lit)),
            SolverState::Post(state) => anyhow::bail!(super::StateError {
                required_state: super::SolverState::Sat,
                actual_state: state.state()
            }),
        }
    }

    fn add_clause_ref<C>(&mut self, clause: &C) -> anyhow::Result<()>
    where
        C: AsRef<Cl> + ?Sized,
    {
        self.add_clause(clause.as_ref().iter().copied().collect())
    }

    fn solution(&self, high_var: crate::types::Var) -> anyhow::Result<Assignment> {
        match &self.state {
            SolverState::Pre(_) => anyhow::bail!(super::StateError {
                required_state: super::SolverState::Sat,
                actual_state: super::SolverState::Input
            }),
            SolverState::Post(SolverOutput::Sat(sol)) => Ok(sol.clone().truncate(high_var)),
            SolverState::Post(state) => anyhow::bail!(super::StateError {
                required_state: super::SolverState::Sat,
                actual_state: state.state()
            }),
        }
    }

    fn add_clause(&mut self, clause: Clause) -> anyhow::Result<()> {
        let state = match &mut self.state {
            SolverState::Pre(state) => state,
            SolverState::Post(state) => anyhow::bail!(super::StateError {
                required_state: super::SolverState::Input,
                actual_state: state.state()
            }),
        };
        for lit in &clause {
            state.n_vars = std::cmp::max(lit.var().idx32() + 1, state.n_vars);
        }
        state.cnf.add_clause(clause);
        Ok(())
    }
}

impl Extend<Clause> for Solver {
    fn extend<T: IntoIterator<Item = Clause>>(&mut self, iter: T) {
        iter.into_iter().for_each(|cl| {
            self.add_clause(cl).expect("Error adding clause in extend");
        });
    }
}

impl<'a> Extend<&'a Clause> for Solver {
    fn extend<T: IntoIterator<Item = &'a Clause>>(&mut self, iter: T) {
        iter.into_iter().for_each(|cl| {
            self.add_clause_ref(cl)
                .expect("Error adding clause in extend");
        });
    }
}

macro_rules! check_exit_code {
    ($status:expr) => {
        match $status.code() {
            // these are the expected return codes for SAT solvers
            // we don't check them against the ouput though
            Some(0 | 10 | 20) => (),
            Some(x) => anyhow::bail!("solver returned unexpected code {x}"),
            None => anyhow::bail!("solver process terminated by signal"),
        };
    };
}

fn call_external(config: SolverPre) -> anyhow::Result<SolverOutput> {
    // when writing to a temporary file, this needs to be explicitly closed at the end
    let mut temppath = None;
    // build the final command
    let mut cmd = match config.input.0 {
        InputViaInt::File(in_path, argpos) => {
            // write input to file
            fio::dimacs::write_cnf_annotated(
                &mut fio::open_compressed_uncompressed_write(&in_path)?,
                &config.cnf,
                config.n_vars,
            )?;
            construct_command_path(config.cmd, in_path, argpos)
        }
        InputViaInt::TempFile(argpos) => {
            let mut writer = io::BufWriter::new(tempfile::NamedTempFile::new()?);
            // write input to file
            fio::dimacs::write_cnf_annotated(&mut writer, &config.cnf, config.n_vars)?;
            let path = writer.into_inner()?.into_temp_path();
            let cmd = construct_command_path(config.cmd, path.to_path_buf(), argpos);
            temppath = Some(path);
            cmd
        }
        InputViaInt::Pipe => {
            let mut cmd = config.cmd;
            cmd.stdin(process::Stdio::piped());
            match config.output.0 {
                OutputViaInt::File(path) => {
                    // pipe output into file and spawn
                    // NOTE: this currently does not support compression
                    let mut child = cmd.stdout(fs::File::create(&path)?).spawn()?;
                    // write input to stdin
                    let mut stdin = io::BufWriter::new(child.stdin.take().unwrap());
                    fio::dimacs::write_cnf_annotated(&mut stdin, &config.cnf, config.n_vars)?;
                    drop(stdin);
                    let exit = child.wait()?;
                    // parse output from file
                    let output = fio::parse_sat_solver_output(&mut io::BufReader::new(
                        fs::File::open(&path)?,
                    ))?;
                    check_exit_code!(exit);
                    return Ok(output);
                }
                OutputViaInt::Pipe => {
                    let mut child = cmd.stdout(process::Stdio::piped()).spawn()?;
                    let mut stdin = io::BufWriter::new(child.stdin.take().unwrap());
                    // second thread for processing stdout to avoid blocking
                    let mut stdout = io::BufReader::new(child.stdout.take().unwrap());
                    let output_handle =
                        std::thread::spawn(move || -> anyhow::Result<(fio::SolverOutput, io::BufReader<process::ChildStdout>)> {
                            // this thread passes stdout back to ensure that it remains open long
                            // enough for the solver to terminate
                            let output = fio::parse_sat_solver_output(&mut stdout)?;
                            Ok((output, stdout))
                        });
                    // main thread writes input to stdin
                    fio::dimacs::write_cnf_annotated(&mut stdin, &config.cnf, config.n_vars)?;
                    drop(stdin);
                    let exit = child.wait()?;
                    let (output, stdout) = output_handle
                        .join()
                        .expect("could not join output parsing thread")?;
                    drop(stdout);
                    check_exit_code!(exit);
                    return Ok(output);
                }
            }
        }
    };
    // case input pipe handeled above
    let output = match config.output.0 {
        OutputViaInt::File(path) => {
            // pipe output into file
            // NOTE: this currently does not support compression
            cmd.stdout(fs::File::create(&path)?);
            let exit = cmd.status()?;
            let output =
                fio::parse_sat_solver_output(&mut io::BufReader::new(fs::File::open(&path)?))?;
            check_exit_code!(exit);
            output
        }
        OutputViaInt::Pipe => {
            let mut child = cmd.stdout(process::Stdio::piped()).spawn()?;
            let mut stdout = io::BufReader::new(child.stdout.take().unwrap());
            let output = fio::parse_sat_solver_output(&mut stdout)?;
            check_exit_code!(child.wait()?);
            // keep pipe open till after child has terminated
            drop(stdout);
            output
        }
    };
    if let Some(temppath) = temppath {
        temppath.close()?;
    }
    Ok(output)
}

fn construct_command_path(mut cmd: Command, path: PathBuf, argpos: InstanceArg) -> Command {
    match argpos {
        InstanceArg::First => {
            // reconstruct command with argument at the beginning
            let mut new_cmd = Command::new(cmd.get_program());
            new_cmd.arg(path).args(cmd.get_args());
            for (key, val) in cmd.get_envs() {
                if let Some(val) = val {
                    new_cmd.env(key, val);
                } else {
                    new_cmd.env_remove(key);
                }
            }
            if let Some(dir) = cmd.get_current_dir() {
                new_cmd.current_dir(dir);
            }
            new_cmd
        }
        InstanceArg::Last => {
            cmd.arg(path);
            cmd
        }
    }
}
