//! # `cnf2opb`
//!
//! A small tool for converting DIMACS CNF files to OPB.

use anyhow::Context;
use clap::Parser;
use rustsat::instances::{fio::opb::Options as OpbOptions, SatInstance};
use std::{io, path::PathBuf};

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The DIMACS CNF input file. Reads from `stdin` if not given.
    in_path: Option<PathBuf>,
    /// The OPB output path. Writes to `stdout` if not given.
    out_path: Option<PathBuf>,
    /// The index in the OPB file to treat as the lowest variable
    #[arg(long, default_value_t = 1)]
    first_var_idx: u32,
    /// Avoid negated literals in the OPB file by transforming constraints
    #[arg(long)]
    avoid_negated_lits: bool,
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    let opb_opts = OpbOptions {
        first_var_idx: args.first_var_idx,
        no_negated_lits: args.avoid_negated_lits,
    };

    let inst: SatInstance = if let Some(in_path) = args.in_path {
        SatInstance::from_dimacs_path(in_path).context("error parsing the input file")?
    } else {
        SatInstance::from_dimacs(&mut io::BufReader::new(io::stdin()))
            .context("error parsing input")?
    };

    if let Some(out_path) = args.out_path {
        inst.write_opb_path(out_path, opb_opts)
            .context("error writing the output file")?;
    } else {
        inst.write_opb(&mut io::stdout(), opb_opts)
            .context("error writing the output file")?;
    }
    Ok(())
}
