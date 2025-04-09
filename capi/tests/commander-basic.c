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
  Commander *commander = commander_new();
  assert(commander_add(commander, 1) == Ok);
  assert(commander_add(commander, 2) == Ok);
  assert(commander_add(commander, 3) == Ok);
  assert(commander_add(commander, 4) == Ok);
  uint32_t n_used = 4;
  uint32_t n_clauses = 0;
  commander_encode(commander, &n_used, &clause_counter, &n_clauses);
  commander_drop(commander);
  assert(n_used == 5);
  assert(n_clauses == 10);
  return 0;
}
