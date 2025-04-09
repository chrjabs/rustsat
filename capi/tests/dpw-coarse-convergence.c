#include <assert.h>

#include "rustsat.h"

void assump_counter(int lit, void *data) {
  assert(lit);
  int *cnt = (int *)data;
  (*cnt)++;
}

void clause_counter(int lit, void *data) {
  if (!lit) {
    int *cnt = (int *)data;
    (*cnt)++;
  }
}

int main() {
  DynamicPolyWatchdog *dpw = dpw_new();
  assert(dpw_add(dpw, 1, 5) == Ok);
  assert(dpw_add(dpw, 2, 3) == Ok);
  assert(dpw_add(dpw, 3, 8) == Ok);
  assert(dpw_add(dpw, 4, 7) == Ok);
  uint32_t n_used = 4;
  uint32_t n_clauses = 0;
  dpw_encode_ub(dpw, 0, 23, &n_used, &clause_counter, &n_clauses);
  for (size_t ub = 7; ub < 23; ub++) {
    size_t coarse_ub = dpw_coarse_ub(dpw, ub);
    assert(coarse_ub <= ub);
    if (ub % 8 == 7)
      assert(coarse_ub == ub);
    int n_assumps = 0;
    assert(dpw_enforce_ub(dpw, coarse_ub, &assump_counter, &n_assumps) == Ok);
    assert(n_assumps == 1);
  }
}
