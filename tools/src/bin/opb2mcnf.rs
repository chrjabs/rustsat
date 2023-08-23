//! # opb2mcnf
//!
//! A small tool for converting OPB files to DIMACS MCNF.

use clap::Parser;
use rustsat::instances::{fio::opb::Options as OpbOptions, MultiOptInstance};
use std::{io, path::PathBuf};

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The OPB input file. Reads from `stdin` if not given.
    in_path: Option<PathBuf>,
    /// The DIMACS MCNF output path. Writes to `stdout` if not given.
    out_path: Option<PathBuf>,
    /// The index in the OPB file to treat as the lowest variable
    #[arg(long, default_value_t = 0)]
    first_var_idx: usize,
}

fn main() {
    let args = Args::parse();
    let opb_opts = OpbOptions {
        first_var_idx: 0,
        ..Default::default()
    };

    let inst: MultiOptInstance = if let Some(in_path) = args.in_path {
        MultiOptInstance::from_opb_path(in_path, opb_opts).expect("error parsing the input file")
    } else {
        MultiOptInstance::from_opb(io::stdin(), opb_opts).expect("error parsing input")
    };

    let (constrs, objs) = inst.decompose();
    let constrs = constrs.sanitize();

    println!("c {} clauses", constrs.n_clauses());
    println!("c {} cards", constrs.n_cards());
    println!("c {} pbs", constrs.n_pbs());
    println!("c {} objectives", objs.len());

    let inst = MultiOptInstance::compose(constrs, objs);

    if let Some(out_path) = args.out_path {
        inst.to_dimacs_path(out_path)
            .expect("io error writing the output file");
    } else {
        inst.to_dimacs(&mut io::stdout())
            .expect("io error writing to stdout");
    }
}
