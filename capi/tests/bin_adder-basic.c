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
  BinaryAdder *bin_adder = bin_adder_new();
  assert(bin_adder_add(bin_adder, 1, 1) == Ok);
  assert(bin_adder_add(bin_adder, 2, 2) == Ok);
  assert(bin_adder_add(bin_adder, 3, 3) == Ok);
  assert(bin_adder_add(bin_adder, 4, 4) == Ok);
  uint32_t n_used = 4;
  uint32_t n_clauses = 0;
  bin_adder_encode_ub(bin_adder, 0, 10, &n_used, &clause_counter, &n_clauses);
  bin_adder_encode_lb(bin_adder, 0, 10, &n_used, &clause_counter, &n_clauses);
  bin_adder_drop(bin_adder);
  assert(n_used == 20);
  assert(n_clauses == 53);
  return 0;
}
