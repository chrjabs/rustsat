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
  Totalizer *tot = tot_new();
  assert(tot_add(tot, 1) == Ok);
  assert(tot_add(tot, 2) == Ok);
  assert(tot_add(tot, 3) == Ok);
  assert(tot_add(tot, 4) == Ok);
  uint32_t n_used = 4;
  uint32_t n_clauses = 0;
  tot_encode_ub(tot, 0, 4, &n_used, &clause_counter, &n_clauses);
  tot_encode_lb(tot, 0, 4, &n_used, &clause_counter, &n_clauses);
  tot_drop(tot);
  assert(n_used == 12);
  assert(n_clauses == 28);
  return 0;
}
