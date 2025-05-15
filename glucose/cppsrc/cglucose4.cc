/*
 * Author: Christoph Jabs - christoph.jabs@helsinki.fi
 *
 * Copyright © 2022 Christoph Jabs, University of Helsinki
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the “Software”), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 */

#include "core/Solver.h"
#include "mtl/XAlloc.h"
#include "simp/SimpSolver.h"
#include <new>

using namespace Glucose;

extern "C" {

#include "cglucose4.h"

const char *cglucose4_signature(void) { return "Glucose 4.2.1"; }

CGlucose4 *cglucose4_init(void) {
  try {
    return (CGlucose4 *)new Solver();
  } catch (std::bad_alloc &) {
    return nullptr;
  } catch (OutOfMemoryException &) {
    return nullptr;
  }
}

CGlucoseSimp4 *cglucosesimp4_init(void) {
  try {
    return (CGlucoseSimp4 *)new SimpSolver();
  } catch (std::bad_alloc &) {
    return nullptr;
  } catch (OutOfMemoryException &) {
    return nullptr;
  }
}

void cglucose4_release(CGlucose4 *handle) { delete (Solver *)handle; }

void cglucosesimp4_release(CGlucoseSimp4 *handle) {
  delete (SimpSolver *)handle;
}

void cglucose4_ensure_vars(Solver *solver, const Lit *lits, size_t n_lits) {
  // find max variable in clause
  Var max_v = 0;
  for (size_t i = 0; i < n_lits; i++) {
    if (var(lits[i]) > max_v) {
      max_v = var(lits[i]);
    }
  }
  // reserve variables in solver
  while (max_v >= solver->nVars())
    solver->newVar();
}

int cglucose4_reserve(CGlucose4 *handle, c_Var var) {
  Solver *solver = (Solver *)handle;
  try {
    while (var >= solver->nVars())
      solver->newVar();
    return 0;
  } catch (OutOfMemoryException &) {
    return OUT_OF_MEM;
  }
}

int cglucosesimp4_reserve(CGlucoseSimp4 *handle, c_Var var) {
  return cglucose4_reserve((CGlucose4 *)handle, var);
}

int cglucose4_add_clause(CGlucose4 *handle, const c_Lit *c_lits,
                         size_t n_lits) {
  Lit *lits = (Lit *)c_lits;
  Solver *solver = (Solver *)handle;
  try {
    cglucose4_ensure_vars(solver, lits, n_lits);
    solver->addClause(lits, (int)n_lits);
    return 0;
  } catch (OutOfMemoryException &) {
    return OUT_OF_MEM;
  }
}

int cglucosesimp4_add_clause(CGlucoseSimp4 *handle, const c_Lit *lits,
                             size_t n_lits) {
  return cglucose4_add_clause((CGlucose4 *)handle, lits, n_lits);
}

int cglucose4_solve(CGlucose4 *handle, const c_Lit *c_assumps,
                    size_t n_assumps) {
  Lit *assumps = (Lit *)c_assumps;
  Solver *solver = (Solver *)handle;
  lbool res;
  try {
    cglucose4_ensure_vars(solver, assumps, n_assumps);
    res = solver->solveLimited(assumps, (int)n_assumps);
  } catch (OutOfMemoryException &) {
    return OUT_OF_MEM;
  }
  if (res == l_True) {
    return 10;
  }
  if (res == l_False) {
    return 20;
  }
  return 0;
}

int cglucosesimp4_solve(CGlucoseSimp4 *handle, const c_Lit *assumps,
                        size_t n_assumps) {
  return cglucose4_solve((CGlucose4 *)handle, assumps, n_assumps);
}

int cglucose4_val(CGlucose4 *handle, c_Lit lit) {
  Solver *solver = (Solver *)handle;
  Var v = var(Lit{lit.x});
  lbool val = solver->modelValue(v);
  if (val == l_True) {
    return T_TRUE;
  }
  if (val == l_False) {
    return T_FALSE;
  }
  return T_UNASSIGNED;
}

int cglucosesimp4_val(CGlucoseSimp4 *handle, c_Lit lit) {
  return cglucose4_val((CGlucose4 *)handle, lit);
}

void cglucose4_conflict(CGlucose4 *handle, const c_Lit **conflict,
                        size_t *conflict_len) {
  Solver *solver = (Solver *)handle;
  *conflict = (const c_Lit *)solver->conflict.ptr();
  *conflict_len = solver->conflict.size();
}

void cglucosesimp4_conflict(CGlucoseSimp4 *handle, const c_Lit **conflict,
                            size_t *conflict_len) {
  return cglucose4_conflict((CGlucose4 *)handle, conflict, conflict_len);
}

int cglucose4_phase(CGlucose4 *handle, c_Lit lit) {
  try {
    ((Solver *)handle)->phase(Lit{lit.x});
    return 0;
  } catch (OutOfMemoryException &) {
    return OUT_OF_MEM;
  }
}

int cglucosesimp4_phase(CGlucoseSimp4 *handle, c_Lit lit) {
  try {
    ((SimpSolver *)handle)->phase(Lit{lit.x});
    return 0;
  } catch (OutOfMemoryException &) {
    return OUT_OF_MEM;
  }
}

void cglucose4_unphase(CGlucose4 *handle, c_Var var) {
  return ((Solver *)handle)->unphase(var);
}

void cglucosesimp4_unphase(CGlucoseSimp4 *handle, c_Var var) {
  return ((SimpSolver *)handle)->unphase(var);
}

int cglucose4_n_assigns(CGlucose4 *handle) {
  return ((Solver *)handle)->nAssigns();
}

int cglucosesimp4_n_assigns(CGlucoseSimp4 *handle) {
  return ((SimpSolver *)handle)->nAssigns();
}

int cglucose4_n_clauses(CGlucose4 *handle) {
  return ((Solver *)handle)->nClauses();
}

int cglucosesimp4_n_clauses(CGlucoseSimp4 *handle) {
  return ((SimpSolver *)handle)->nClauses();
}

int cglucose4_n_learnts(CGlucose4 *handle) {
  return ((Solver *)handle)->nLearnts();
}

int cglucosesimp4_n_learnts(CGlucoseSimp4 *handle) {
  return ((SimpSolver *)handle)->nLearnts();
}

int cglucose4_n_vars(CGlucose4 *handle) { return ((Solver *)handle)->nVars(); }

int cglucosesimp4_n_vars(CGlucoseSimp4 *handle) {
  return ((SimpSolver *)handle)->nVars();
}

void cglucose4_set_conf_limit(CGlucose4 *handle, int64_t limit) {
  ((Solver *)handle)->setConfBudget(limit);
}

void cglucosesimp4_set_conf_limit(CGlucoseSimp4 *handle, int64_t limit) {
  ((SimpSolver *)handle)->setConfBudget(limit);
}

void cglucose4_set_prop_limit(CGlucose4 *handle, int64_t limit) {
  ((Solver *)handle)->setPropBudget(limit);
}

void cglucosesimp4_set_prop_limit(CGlucoseSimp4 *handle, int64_t limit) {
  ((SimpSolver *)handle)->setPropBudget(limit);
}

void cglucose4_set_no_limit(CGlucose4 *handle) {
  ((Solver *)handle)->budgetOff();
}

void cglucosesimp4_set_no_limit(CGlucoseSimp4 *handle) {
  ((SimpSolver *)handle)->budgetOff();
}

void cglucose4_interrupt(CGlucose4 *handle) { ((Solver *)handle)->interrupt(); }

void cglucosesimp4_interrupt(CGlucoseSimp4 *handle) {
  ((SimpSolver *)handle)->interrupt();
}

uint64_t cglucose4_decisions(CGlucose4 *handle) {
  return ((Solver *)handle)->decisions;
}

uint64_t cglucosesimp4_decisions(CGlucoseSimp4 *handle) {
  return ((SimpSolver *)handle)->decisions;
}

uint64_t cglucose4_propagations(CGlucose4 *handle) {
  return ((Solver *)handle)->propagations;
}

uint64_t cglucosesimp4_propagations(CGlucoseSimp4 *handle) {
  return ((SimpSolver *)handle)->propagations;
}

uint64_t cglucose4_conflicts(CGlucose4 *handle) {
  return ((Solver *)handle)->conflicts;
}

uint64_t cglucosesimp4_conflicts(CGlucoseSimp4 *handle) {
  return ((SimpSolver *)handle)->conflicts;
}

void cglucosesimp4_set_frozen(CGlucoseSimp4 *handle, c_Var var, int frozen) {
  ((SimpSolver *)handle)->setFrozen(var, frozen);
}

int cglucosesimp4_is_frozen(CGlucoseSimp4 *handle, c_Var var) {
  return ((SimpSolver *)handle)->isFrozen(var);
}

int cglucosesimp4_is_eliminated(CGlucoseSimp4 *handle, c_Var var) {
  return ((SimpSolver *)handle)->isEliminated(var);
}

int cglucose4_propcheck(CGlucose4 *handle, const c_Lit *assumps,
                        size_t n_assumps, int psaving,
                        void (*prop_cb)(void *, c_Lit), void *cb_data) {
  Solver *solver = (Solver *)handle;
  bool res;
  try {
    res = solver->propCheck((Lit *)assumps, n_assumps, psaving,
                            (void (*)(void *, Lit))prop_cb, cb_data);
  } catch (OutOfMemoryException &) {
    return OUT_OF_MEM;
  }
  return res ? 10 : 20;
}

int cglucosesimp4_propcheck(CGlucoseSimp4 *handle, const c_Lit *assumps,
                            size_t n_assumps, int psaving,
                            void (*prop_cb)(void *, c_Lit), void *cb_data) {
  return cglucose4_propcheck((CGlucose4 *)handle, assumps, n_assumps, psaving,
                             prop_cb, cb_data);
}
}
