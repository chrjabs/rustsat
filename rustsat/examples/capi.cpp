#include <cassert>
#include <vector>

#include "rustsat.h"

// A dummy solver type for the example
class Solver {
public:
  void add_clause(std::vector<int> clause){};
  int solve_assumps(std::vector<int> assumps) { return 0; };
};

struct SolverWithBuffer {
  Solver *solver;
  std::vector<int> buffer;
};

// Example clause collector using the IPASIR-like solver interface
void clause_collector(int lit, void *ptr) {
  SolverWithBuffer *solver_with_buffer = (SolverWithBuffer *)ptr;
  if (lit) {
    solver_with_buffer->buffer.push_back(lit);
    return;
  }
  solver_with_buffer->solver->add_clause(solver_with_buffer->buffer);
  solver_with_buffer->buffer.clear();
}

void assump_collector(int lit, void *assumps) {
  ((std::vector<int> *)assumps)->push_back(lit);
}

int main() {
  // Initialize solver
  Solver solver{};

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
  SolverWithBuffer solver_with_buffer{.solver = &solver};
  RustSAT::dpw_encode_ub(dpw, 10, 40, &n_vars_used, clause_collector,
                         &solver_with_buffer);

  // Enforce bound and solve
  std::vector<int> assumps{};
  RustSAT::MaybeError ret =
      RustSAT::dpw_enforce_ub(dpw, 30, assump_collector, &assumps);
  assert(ret == RustSAT::MaybeError::Ok);
  solver.solve_assumps(assumps);
  
  return 0;
}
