// !!! Auto-generated by codegen, do not edit manually !!!

#include <assert.h>

#include "rustsat.h"

void clause_counter(int lit, void *data) {
  if (!lit) {
    int *cnt = (int *)data;
    (*cnt)++;
  }
}

int main() {
  DynamicPolyWatchdog *dpw = dpw_new();
  assert(dpw_add(dpw, 1, 1) == Ok);
  assert(dpw_add(dpw, 2, 2) == Ok);
  assert(dpw_add(dpw, 3, 3) == Ok);
  assert(dpw_add(dpw, 4, 4) == Ok);
  uint32_t n_used = 4;
  uint32_t n_clauses = 0;
  dpw_encode_ub(dpw, 0, 10, &n_used, &clause_counter, &n_clauses);
  dpw_drop(dpw);
  assert(n_used == 19);
  assert(n_clauses == 21);
  return 0;
}
