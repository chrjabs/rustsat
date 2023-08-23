//! # shuffledimacs
//!
//! A small tool for shuffling the order of constraints and the variable
//! indexing in a DIMACS file.
//!
//! Usage: shuffledimacs [dimacs [m,w]cnf file] [output path]

use std::path::{Path, PathBuf};

use rustsat::instances::{self, BasicVarManager, ManageVars, RandReindVarManager};

macro_rules! print_usage {
    () => {{
        eprintln!("Usage: shuffledimacs [dimacs [m,w]cnf file] [output path]");
        panic!()
    }};
}

enum FileType {
    Cnf,
    Wcnf,
    Mcnf,
}

fn main() {
    let in_path = PathBuf::from(&std::env::args().nth(1).unwrap_or_else(|| print_usage!()));
    let out_path = PathBuf::from(&std::env::args().nth(2).unwrap_or_else(|| print_usage!()));

    match determine_file_type(&in_path) {
        FileType::Cnf => {
            let mut inst = instances::SatInstance::<BasicVarManager>::from_dimacs_path(in_path)
                .expect("Could not parse CNF");
            let n_vars = inst.var_manager().n_used();
            let rand_reindexer = RandReindVarManager::init(n_vars);
            inst.reindex(rand_reindexer)
                .shuffle()
                .to_dimacs_path(out_path)
                .expect("Could not write CNF");
        }
        FileType::Wcnf => {
            let mut inst = instances::OptInstance::<BasicVarManager>::from_dimacs_path(in_path)
                .expect("Could not parse WCNF");
            let n_vars = inst.get_constraints().var_manager().n_used();
            let rand_reindexer = RandReindVarManager::init(n_vars);
            inst.reindex(rand_reindexer)
                .shuffle()
                .to_dimacs_path(out_path)
                .expect("Could not write WCNF");
        }
        FileType::Mcnf => {
            let mut inst =
                instances::MultiOptInstance::<BasicVarManager>::from_dimacs_path(in_path)
                    .expect("Could not parse MCNF");
            let n_vars = inst.get_constraints().var_manager().n_used();
            let rand_reindexer = RandReindVarManager::init(n_vars);
            inst.reindex(rand_reindexer)
                .shuffle()
                .to_dimacs_path(out_path)
                .expect("Could not write MCNF");
        }
    }
}

macro_rules! is_one_of {
    ($a:expr, $($b:expr),*) => {
        $( $a == $b || )* false
    }
}

fn determine_file_type(in_path: &Path) -> FileType {
    if let Some(ext) = in_path.extension() {
        let path_without_compr = in_path.with_extension("");
        let ext = if is_one_of!(ext, "gz", "bz2") {
            // Strip compression extension
            match path_without_compr.extension() {
                Some(ext) => ext,
                None => return FileType::Cnf, // Fallback default
            }
        } else {
            ext
        };
        if "wcnf" == ext {
            return FileType::Wcnf;
        };
        if "mcnf" == ext {
            return FileType::Mcnf;
        };
        return FileType::Cnf; // Fallback default
    };
    FileType::Cnf // Fallback default
}
