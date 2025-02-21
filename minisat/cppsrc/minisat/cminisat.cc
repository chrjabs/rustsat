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

#define IPASIR2MS(il) (mkLit(abs(il) - 1, il < 0))

namespace Minisat {

// Note: the memory layout of Wrapper and SimpWrapper needs to be the same
// because we are casting SimpWrapper into Wrapper

struct Wrapper {
  Solver *solver;
  vec<Lit> clause;
  vec<Lit> assumps;

  Wrapper() : solver(new Solver()), clause(), assumps() {}

  ~Wrapper() { delete solver; }
};

struct SimpWrapper {
  SimpSolver *solver;
  vec<Lit> clause;
  vec<Lit> assumps;

  SimpWrapper() : solver(new SimpSolver()), clause(), assumps() {}

  ~SimpWrapper() { delete solver; }
};

} // namespace Minisat

using namespace Minisat;

extern "C" {

#include "cminisat.h"

const char *cminisat_signature(void) { return "Minisat 2.2.0"; }

CMinisat *cminisat_init(void) {
  try {
    return (CMinisat *)new Wrapper();
  } catch (std::bad_alloc &) {
    return nullptr;
  } catch (OutOfMemoryException &) {
    return nullptr;
  }
}

CMinisatSimp *cminisatsimp_init(void) {
  try {
    return (CMinisatSimp *)new SimpWrapper();
  } catch (std::bad_alloc &) {
    return nullptr;
  } catch (OutOfMemoryException &) {
    return nullptr;
  }
}

void cminisat_release(CMinisat *handle) { delete (Wrapper *)handle; }

void cminisatsimp_release(CMinisatSimp *handle) {
  delete (SimpWrapper *)handle;
}

int cminisat_add(CMinisat *handle, int lit) {
  Wrapper *wrapper = (Wrapper *)handle;
  try {
    if (lit) {
      int var = abs(lit) - 1;
      while (var >= wrapper->solver->nVars())
        wrapper->solver->newVar();
      wrapper->clause.push(IPASIR2MS(lit));
      return 0;
    }
    wrapper->solver->addClause_(wrapper->clause);
    wrapper->clause.clear();
    return 0;
  } catch (OutOfMemoryException &) {
    return OUT_OF_MEM;
  }
}

int cminisatsimp_add(CMinisatSimp *handle, int lit) {
  return cminisat_add((CMinisat *)handle, lit);
}

void cminisat_assume(CMinisat *handle, int lit) {
  Wrapper *wrapper = (Wrapper *)handle;
  int var = abs(lit) - 1;
  while (var >= wrapper->solver->nVars())
    wrapper->solver->newVar();
  wrapper->assumps.push(IPASIR2MS(lit));
}

void cminisatsimp_assume(CMinisatSimp *handle, int lit) {
  cminisat_assume((CMinisat *)handle, lit);
}

int cminisat_solve(CMinisat *handle) {
  Wrapper *wrapper = (Wrapper *)handle;
  lbool res;
  try {
    res = wrapper->solver->solveLimited(wrapper->assumps);
    wrapper->assumps.clear();
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

int cminisatsimp_solve(CMinisatSimp *handle) {
  return cminisat_solve((CMinisat *)handle);
}

int cminisat_val(CMinisat *handle, int lit) {
  Wrapper *wrapper = (Wrapper *)handle;
  Var v = abs(lit) - 1;
  lbool val = wrapper->solver->modelValue(v);
  if (val == l_True) {
    return v + 1;
  }
  if (val == l_False) {
    return -(v + 1);
  }
  return 0;
}

int cminisatsimp_val(CMinisatSimp *handle, int lit) {
  return cminisat_val((CMinisat *)handle, lit);
}

int cminisat_failed(CMinisat *handle, int lit) {
  Wrapper *wrapper = (Wrapper *)handle;
  Lit ms_lit = IPASIR2MS(-lit);
  for (int i = 0; i < wrapper->solver->conflict.size(); ++i) {
    if (wrapper->solver->conflict[i] == ms_lit) {
      return 1;
    }
  }
  return 0;
}

int cminisatsimp_failed(CMinisatSimp *handle, int lit) {
  return cminisat_failed((CMinisat *)handle, lit);
}

int cminisat_phase(CMinisat *handle, int lit) {
  try {
    ((Wrapper *)handle)->solver->phase(IPASIR2MS(lit));
    return 0;
  } catch (OutOfMemoryException &) {
    return OUT_OF_MEM;
  }
}

int cminisatsimp_phase(CMinisatSimp *handle, int lit) {
  try {
    ((SimpWrapper *)handle)->solver->phase(IPASIR2MS(lit));
    return 0;
  } catch (OutOfMemoryException &) {
    return OUT_OF_MEM;
  }
}

void cminisat_unphase(CMinisat *handle, int lit) {
  return ((Wrapper *)handle)->solver->unphase(var(IPASIR2MS(lit)));
}

void cminisatsimp_unphase(CMinisatSimp *handle, int lit) {
  return ((SimpWrapper *)handle)->solver->unphase(var(IPASIR2MS(lit)));
}

int cminisat_n_assigns(CMinisat *handle) {
  return ((Wrapper *)handle)->solver->nAssigns();
}

int cminisatsimp_n_assigns(CMinisatSimp *handle) {
  return ((SimpWrapper *)handle)->solver->nAssigns();
}

int cminisat_n_clauses(CMinisat *handle) {
  return ((Wrapper *)handle)->solver->nClauses();
}

int cminisatsimp_n_clauses(CMinisatSimp *handle) {
  return ((SimpWrapper *)handle)->solver->nClauses();
}

int cminisat_n_learnts(CMinisat *handle) {
  return ((Wrapper *)handle)->solver->nLearnts();
}

int cminisatsimp_n_learnts(CMinisatSimp *handle) {
  return ((SimpWrapper *)handle)->solver->nLearnts();
}

int cminisat_n_vars(CMinisat *handle) {
  return ((Wrapper *)handle)->solver->nVars();
}

int cminisatsimp_n_vars(CMinisatSimp *handle) {
  return ((SimpWrapper *)handle)->solver->nVars();
}

void cminisat_set_conf_limit(CMinisat *handle, int64_t limit) {
  ((Wrapper *)handle)->solver->setConfBudget(limit);
}

void cminisatsimp_set_conf_limit(CMinisatSimp *handle, int64_t limit) {
  ((SimpWrapper *)handle)->solver->setConfBudget(limit);
}

void cminisat_set_prop_limit(CMinisat *handle, int64_t limit) {
  ((Wrapper *)handle)->solver->setPropBudget(limit);
}

void cminisatsimp_set_prop_limit(CMinisatSimp *handle, int64_t limit) {
  ((SimpWrapper *)handle)->solver->setPropBudget(limit);
}

void cminisat_set_no_limit(CMinisat *handle) {
  ((Wrapper *)handle)->solver->budgetOff();
}

void cminisatsimp_set_no_limit(CMinisatSimp *handle) {
  ((SimpWrapper *)handle)->solver->budgetOff();
}

void cminisat_interrupt(CMinisat *handle) {
  ((Wrapper *)handle)->solver->interrupt();
}

void cminisatsimp_interrupt(CMinisatSimp *handle) {
  ((SimpWrapper *)handle)->solver->interrupt();
}

uint64_t cminisat_decisions(CMinisat *handle) {
  return ((Wrapper *)handle)->solver->decisions;
}

uint64_t cminisatsimp_decisions(CMinisatSimp *handle) {
  return ((SimpWrapper *)handle)->solver->decisions;
}

uint64_t cminisat_propagations(CMinisat *handle) {
  return ((Wrapper *)handle)->solver->propagations;
}

uint64_t cminisatsimp_propagations(CMinisatSimp *handle) {
  return ((SimpWrapper *)handle)->solver->propagations;
}

uint64_t cminisat_conflicts(CMinisat *handle) {
  return ((Wrapper *)handle)->solver->conflicts;
}

uint64_t cminisatsimp_conflicts(CMinisatSimp *handle) {
  return ((SimpWrapper *)handle)->solver->conflicts;
}

void cminisatsimp_set_frozen(CMinisatSimp *handle, int var, int frozen) {
  ((SimpWrapper *)handle)->solver->setFrozen(var - 1, frozen);
}

int cminisatsimp_is_frozen(CMinisatSimp *handle, int var) {
  return ((SimpWrapper *)handle)->solver->isFrozen(var - 1);
}

int cminisatsimp_is_eliminated(CMinisatSimp *handle, int var) {
  return ((SimpWrapper *)handle)->solver->isEliminated(var - 1);
}

int cminisat_propcheck(CMinisat *handle, int psaving,
                       void (*prop_cb)(void *, int), void *cb_data) {
  Wrapper *wrapper = (Wrapper *)handle;
  bool res;
  try {
    res =
        wrapper->solver->propCheck(wrapper->assumps, psaving, prop_cb, cb_data);
    wrapper->assumps.clear();
  } catch (OutOfMemoryException &) {
    return OUT_OF_MEM;
  }
  return res ? 10 : 20;
}

int cminisatsimp_propcheck(CMinisatSimp *handle, int psaving,
                           void (*prop_cb)(void *, int), void *cb_data) {
  return cminisat_propcheck((CMinisat *)handle, psaving, prop_cb, cb_data);
}
}
