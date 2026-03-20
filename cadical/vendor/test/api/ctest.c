#include "../../src/ccadical.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>

int main (void) {
  struct CCaDiCaL *solver = ccadical_init ();
  int res = ccadical_solve (solver);
  assert (res == 10);
  const int var1 = ccadical_declare_one_more_variable (solver);
  const int var2 = ccadical_declare_one_more_variable (solver);
  ccadical_add (solver, -var1);
  ccadical_add (solver, var2);
  ccadical_add (solver, 0);
  ccadical_add (solver, var1);
  ccadical_add (solver, var2);
  ccadical_add (solver, 0);
  ccadical_add (solver, -var1);
  ccadical_add (solver, -var2);
  ccadical_add (solver, 0);
  res = ccadical_solve (solver);
  assert (res == 10);
  res = ccadical_val (solver, var1);
  assert (res == -1);
  res = ccadical_val (solver, var2);
  assert (res == 2);
  res = ccadical_val (solver, -var1);
  assert (res == -1);
  res = ccadical_val (solver, -var2);
  assert (res == 2);
  ccadical_release (solver);
  return 0;
}
