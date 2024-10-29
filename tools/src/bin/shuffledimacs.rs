//! # `shuffledimacs`
//!
//! A small tool for shuffling the order of constraints and the variable
//! indexing in a DIMACS file.
//!
//! Usage: `shuffledimacs [dimacs [m,w]cnf file] [output path]`

use std::path::{Path, PathBuf};

use anyhow::Context;
use rustsat::instances::{self, BasicVarManager, RandReindVarManager};

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

fn main() -> anyhow::Result<()> {
    let in_path = PathBuf::from(&std::env::args().nth(1).unwrap_or_else(|| print_usage!()));
    let out_path = PathBuf::from(&std::env::args().nth(2).unwrap_or_else(|| print_usage!()));

    match determine_file_type(&in_path) {
        FileType::Cnf => {
            let inst = instances::SatInstance::<BasicVarManager>::from_dimacs_path(in_path)
                .context("Could not parse CNF")?;
            let n_vars = inst.n_vars();
            let rand_reindexer = RandReindVarManager::init(n_vars);
            inst.reindex(rand_reindexer)
                .shuffle()
                .write_dimacs_path(out_path)
                .context("Could not write CNF")?;
        }
        FileType::Wcnf => {
            let inst = instances::OptInstance::<BasicVarManager>::from_dimacs_path(in_path)
                .context("Could not parse WCNF")?;
            let n_vars = inst.constraints_ref().n_vars();
            let rand_reindexer = RandReindVarManager::init(n_vars);
            inst.reindex(rand_reindexer)
                .shuffle()
                .write_dimacs_path(out_path)
                .context("Could not write WCNF")?;
        }
        FileType::Mcnf => {
            let inst = instances::MultiOptInstance::<BasicVarManager>::from_dimacs_path(in_path)
                .context("Could not parse MCNF")?;
            let n_vars = inst.constraints_ref().n_vars();
            let rand_reindexer = RandReindVarManager::init(n_vars);
            inst.reindex(rand_reindexer)
                .shuffle()
                .write_dimacs_path(out_path)
                .context("Could not write MCNF")?;
        }
    }
    Ok(())
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
