/*
 * Author: Christoph Jabs - christoph.jabs@helsinki.fi
 *
 * Copyright © 2023 Christoph Jabs, University of Helsinki
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

using namespace Minisat;

extern "C" {

#include "cminisat.h"

const char *cminisat_signature(void) { return "Minisat 2.2.0"; }

CMinisat *cminisat_init(void) {
  try {
    return (CMinisat *)new Solver();
  } catch (std::bad_alloc &) {
    return nullptr;
  } catch (OutOfMemoryException &) {
    return nullptr;
  }
}

CMinisatSimp *cminisatsimp_init(void) {
  try {
    return (CMinisatSimp *)new SimpSolver();
  } catch (std::bad_alloc &) {
    return nullptr;
  } catch (OutOfMemoryException &) {
    return nullptr;
  }
}

void cminisat_release(CMinisat *handle) { delete (Solver *)handle; }

void cminisatsimp_release(CMinisatSimp *handle) { delete (SimpSolver *)handle; }

void cminisat_ensure_vars(Solver *solver, const Lit *lits, size_t n_lits) {
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

int cminisat_reserve(CMinisat *handle, c_Var var) {
  Solver *solver = (Solver *)handle;
  try {
    while (var >= solver->nVars())
      solver->newVar();
    return 0;
  } catch (OutOfMemoryException &) {
    return OUT_OF_MEM;
  }
}

int cminisatsimp_reserve(CMinisatSimp *handle, c_Var var) {
  return cminisat_reserve((CMinisat *)handle, var);
}

int cminisat_add_clause(CMinisat *handle, const c_Lit *c_lits, size_t n_lits) {
  Lit *lits = (Lit *)c_lits;
  Solver *solver = (Solver *)handle;
  try {
    cminisat_ensure_vars(solver, lits, n_lits);
    solver->addClause(lits, (int)n_lits);
    return 0;
  } catch (OutOfMemoryException &) {
    return OUT_OF_MEM;
  }
}

int cminisatsimp_add_clause(CMinisatSimp *handle, const c_Lit *lits,
                            size_t n_lits) {
  return cminisat_add_clause((CMinisat *)handle, lits, n_lits);
}

int cminisat_solve(CMinisat *handle, const c_Lit *c_assumps, size_t n_assumps) {
  Lit *assumps = (Lit *)c_assumps;
  Solver *solver = (Solver *)handle;
  lbool res;
  try {
    cminisat_ensure_vars(solver, assumps, n_assumps);
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

int cminisatsimp_solve(CMinisatSimp *handle, const c_Lit *assumps,
                       size_t n_assumps) {
  return cminisat_solve((CMinisat *)handle, assumps, n_assumps);
}

int cminisat_val(CMinisat *handle, c_Lit lit) {
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

int cminisatsimp_val(CMinisatSimp *handle, c_Lit lit) {
  return cminisat_val((CMinisat *)handle, lit);
}

void cminisat_conflict(CMinisat *handle, const c_Lit **conflict,
                       size_t *conflict_len) {
  Solver *solver = (Solver *)handle;
  *conflict = (const c_Lit *)solver->conflict.toVec().ptr();
  *conflict_len = solver->conflict.size();
}

void cminisatsimp_conflict(CMinisatSimp *handle, const c_Lit **conflict,
                           size_t *conflict_len) {
  return cminisat_conflict((CMinisat *)handle, conflict, conflict_len);
}

int cminisat_phase(CMinisat *handle, c_Lit lit) {
  try {
    ((Solver *)handle)->phase(Lit{lit.x});
    return 0;
  } catch (OutOfMemoryException &) {
    return OUT_OF_MEM;
  }
}

int cminisatsimp_phase(CMinisatSimp *handle, c_Lit lit) {
  try {
    ((SimpSolver *)handle)->phase(Lit{lit.x});
    return 0;
  } catch (OutOfMemoryException &) {
    return OUT_OF_MEM;
  }
}

void cminisat_unphase(CMinisat *handle, c_Var var) {
  return ((Solver *)handle)->unphase(var);
}

void cminisatsimp_unphase(CMinisatSimp *handle, c_Var var) {
  return ((SimpSolver *)handle)->unphase(var);
}

int cminisat_n_assigns(CMinisat *handle) {
  return ((Solver *)handle)->nAssigns();
}

int cminisatsimp_n_assigns(CMinisatSimp *handle) {
  return ((SimpSolver *)handle)->nAssigns();
}

int cminisat_n_clauses(CMinisat *handle) {
  return ((Solver *)handle)->nClauses();
}

int cminisatsimp_n_clauses(CMinisatSimp *handle) {
  return ((SimpSolver *)handle)->nClauses();
}

int cminisat_n_learnts(CMinisat *handle) {
  return ((Solver *)handle)->nLearnts();
}

int cminisatsimp_n_learnts(CMinisatSimp *handle) {
  return ((SimpSolver *)handle)->nLearnts();
}

int cminisat_n_vars(CMinisat *handle) { return ((Solver *)handle)->nVars(); }

int cminisatsimp_n_vars(CMinisatSimp *handle) {
  return ((SimpSolver *)handle)->nVars();
}

void cminisat_set_conf_limit(CMinisat *handle, int64_t limit) {
  ((Solver *)handle)->setConfBudget(limit);
}

void cminisatsimp_set_conf_limit(CMinisatSimp *handle, int64_t limit) {
  ((SimpSolver *)handle)->setConfBudget(limit);
}

void cminisat_set_prop_limit(CMinisat *handle, int64_t limit) {
  ((Solver *)handle)->setPropBudget(limit);
}

void cminisatsimp_set_prop_limit(CMinisatSimp *handle, int64_t limit) {
  ((SimpSolver *)handle)->setPropBudget(limit);
}

void cminisat_set_no_limit(CMinisat *handle) {
  ((Solver *)handle)->budgetOff();
}

void cminisatsimp_set_no_limit(CMinisatSimp *handle) {
  ((SimpSolver *)handle)->budgetOff();
}

void cminisat_interrupt(CMinisat *handle) { ((Solver *)handle)->interrupt(); }

void cminisatsimp_interrupt(CMinisatSimp *handle) {
  ((SimpSolver *)handle)->interrupt();
}

uint64_t cminisat_decisions(CMinisat *handle) {
  return ((Solver *)handle)->decisions;
}

uint64_t cminisatsimp_decisions(CMinisatSimp *handle) {
  return ((SimpSolver *)handle)->decisions;
}

uint64_t cminisat_propagations(CMinisat *handle) {
  return ((Solver *)handle)->propagations;
}

uint64_t cminisatsimp_propagations(CMinisatSimp *handle) {
  return ((SimpSolver *)handle)->propagations;
}

uint64_t cminisat_conflicts(CMinisat *handle) {
  return ((Solver *)handle)->conflicts;
}

uint64_t cminisatsimp_conflicts(CMinisatSimp *handle) {
  return ((SimpSolver *)handle)->conflicts;
}

void cminisatsimp_set_frozen(CMinisatSimp *handle, c_Var var, int frozen) {
  ((SimpSolver *)handle)->setFrozen(var, frozen);
}

int cminisatsimp_is_frozen(CMinisatSimp *handle, c_Var var) {
  return ((SimpSolver *)handle)->isFrozen(var);
}

int cminisatsimp_is_eliminated(CMinisatSimp *handle, c_Var var) {
  return ((SimpSolver *)handle)->isEliminated(var);
}

int cminisat_propcheck(CMinisat *handle, const c_Lit *assumps, size_t n_assumps,
                       int psaving, void (*prop_cb)(void *, c_Lit),
                       void *cb_data) {
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

int cminisatsimp_propcheck(CMinisatSimp *handle, const c_Lit *assumps,
                           size_t n_assumps, int psaving,
                           void (*prop_cb)(void *, c_Lit), void *cb_data) {
  return cminisat_propcheck((CMinisat *)handle, assumps, n_assumps, psaving,
                            prop_cb, cb_data);
}
}
