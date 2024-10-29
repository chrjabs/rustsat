//! # `opb2wcnf`
//!
//! A small tool for converting OPB files to DIMACS WCNF.

use anyhow::Context;
use clap::Parser;
use rustsat::instances::{fio::opb::Options as OpbOptions, OptInstance};
use std::{io, path::PathBuf};

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The OPB input file. Reads from `stdin` if not given.
    in_path: Option<PathBuf>,
    /// The DIMACS WCNF output path. Writes to `stdout` if not given.
    out_path: Option<PathBuf>,
    /// The index in the OPB file to treat as the lowest variable
    #[arg(long, default_value_t = 1)]
    first_var_idx: usize,
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    let opb_opts = OpbOptions {
        first_var_idx: 0,
        ..Default::default()
    };

    let inst: OptInstance = if let Some(in_path) = args.in_path {
        OptInstance::from_opb_path(in_path, opb_opts).context("error parsing the input file")?
    } else {
        OptInstance::from_opb(&mut io::BufReader::new(io::stdin()), opb_opts)
            .context("error parsing input")?
    };

    let (constrs, obj) = inst.decompose();
    let mut constrs = constrs.sanitize();

    println!("c {} clauses", constrs.n_clauses());
    println!("c {} cards", constrs.n_cards());
    println!("c {} pbs", constrs.n_pbs());

    constrs.convert_to_cnf();
    let inst = OptInstance::compose(constrs, obj);

    if let Some(out_path) = args.out_path {
        inst.write_dimacs_path(out_path)
            .context("io error writing the output file")?;
    } else {
        inst.write_dimacs(&mut io::stdout())
            .context("io error writing to stdout")?;
    }
    Ok(())
}
