mod ffi;

use super::SolverState;
use ffi::IpasirHandle;

pub struct IpasirSolver {
    handle: IpasirHandle,
    state: SolverState,
    n_sat: u32,
    n_unsat: u32,
    n_clauses: u32,
    n_vars: u32,
    avg_clause_len: f32,
}
