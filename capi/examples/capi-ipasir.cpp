#include <cassert>

#include "ipasir.h"
#include "rustsat.h"

// Example clause collector using the IPASIR solver interface
void ipasir_clause_collector(int lit, void *solver) { ipasir_add(solver, lit); }

// Example assumption collector using the IPASIR solver interface
void ipasir_assump_collector(int lit, void *solver) {
  ipasir_assume(solver, lit);
}

int main() {
  // Initialize solver
  void *solver = ipasir_init();

  // Load potential instance here
  int n_vars_used = 50;

  // Setup dynamic poly watchdog
  RustSAT::DynamicPolyWatchdog *dpw = RustSAT::dpw_new();
  // Some example input literals
  RustSAT::dpw_add(dpw, 1, 5);
  RustSAT::dpw_add(dpw, 2, 3);
  RustSAT::dpw_add(dpw, 3, 14);
  RustSAT::dpw_add(dpw, 4, 42);

  // Encode dynamic poly watchdog and add encoding to the solver
  RustSAT::dpw_encode_ub(dpw, 10, 40, &n_vars_used, ipasir_clause_collector,
                         solver);

  // Enforce bound and solve
  RustSAT::MaybeError ret =
      RustSAT::dpw_enforce_ub(dpw, 30, ipasir_assump_collector, solver);
  assert(ret == RustSAT::MaybeError::Ok);
  ipasir_solve(solver);
  
  ipasir_release(solver);
  
  return 0;
}