//! # mcnf2opb
//!
//! A small tool for converting DIMACS MCNF files to OPB.
//!
//! Usage: wcnf2opb [dimacs mcnf file] [opb output path]

use rustsat::instances::MultiOptInstance;

macro_rules! print_usage {
    () => {{
        eprintln!("Usage: mcnf2opb [dimacs mcnf file] [opb output path]");
        panic!()
    }};
}

fn main() {
    let in_path = std::env::args().nth(1).unwrap_or_else(|| print_usage!());
    let out_path = std::env::args().nth(2).unwrap_or_else(|| print_usage!());

    let inst: MultiOptInstance =
        MultiOptInstance::from_dimacs_path(in_path).expect("error parsing the input file");

    inst.to_opb_path(out_path)
        .expect("io error writing the output file");
}
