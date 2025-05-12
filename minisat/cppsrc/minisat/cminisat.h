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

#ifndef Minisat_CMinisat_h
#define Minisat_CMinisat_h

#ifdef __cplusplus
extern "C" {
#endif

#include <stddef.h>
#include <stdint.h>

// Same as the internal literal representation
typedef struct c_Lit {
  int x;
} c_Lit;
// Same as the internal variable representation
typedef int c_Var;

// Minisat C API
// The API is roughly IPASIR-like

const char *cminisat_signature(void);

// These values are returned from _val
const int T_FALSE = -1;
const int T_UNASSIGNED = 0;
const int T_TRUE = 1;

// This value is returned from _solve, _add, and _phase if the solver runs out
// of memory
const int OUT_OF_MEM = 50;

// -----------------------------------------------------------------------------
// API for the solver without preprocessing
typedef struct CMinisat CMinisat;
CMinisat *cminisat_init(void);
void cminisat_release(CMinisat *);

int cminisat_reserve(CMinisat *, c_Var var);
int cminisat_add_clause(CMinisat *, const c_Lit *lits, size_t n_lits);
int cminisat_solve(CMinisat *, const c_Lit *assumps, size_t n_assumps);
int cminisat_val(CMinisat *, c_Lit lit);
void cminisat_conflict(CMinisat *, const c_Lit **conflict,
                       size_t *conflict_len);

int cminisat_phase(CMinisat *, c_Lit lit);
void cminisat_unphase(CMinisat *, c_Var var);

int cminisat_n_assigns(CMinisat *);
int cminisat_n_clauses(CMinisat *);
int cminisat_n_learnts(CMinisat *);
int cminisat_n_vars(CMinisat *);

void cminisat_set_conf_limit(CMinisat *, int64_t limit);
void cminisat_set_prop_limit(CMinisat *, int64_t limit);
void cminisat_set_no_limit(CMinisat *);
void cminisat_interrupt(CMinisat *);

uint64_t cminisat_decisions(CMinisat *);
uint64_t cminisat_propagations(CMinisat *);
uint64_t cminisat_conflicts(CMinisat *);

// Propagates the assumptions, returns 20 if a
// conflict was encountered, 10 if not. The list of propagated literals is
// returned via the `prop_cb`. If the solver runs out of memory, returns
// `OUT_OF_MEM`.
int cminisat_propcheck(CMinisat *, const c_Lit *assumps, size_t n_assumps,
                       int psaving, void (*prop_cb)(void *, c_Lit),
                       void *cb_data);
// -----------------------------------------------------------------------------

// -----------------------------------------------------------------------------
// API for the solver with preprocessing
typedef struct CMinisatSimp CMinisatSimp;
CMinisatSimp *cminisatsimp_init(void);
void cminisatsimp_release(CMinisatSimp *);

int cminisatsimp_reserve(CMinisatSimp *, c_Var var);
int cminisatsimp_add_clause(CMinisatSimp *, const c_Lit *lits, size_t n_lits);
int cminisatsimp_solve(CMinisatSimp *, const c_Lit *assumps, size_t n_assumps);
int cminisatsimp_val(CMinisatSimp *, c_Lit lit);
void cminisatsimp_conflict(CMinisatSimp *, const c_Lit **conflict,
                           size_t *conflict_len);

int cminisatsimp_phase(CMinisatSimp *, c_Lit lit);
void cminisatsimp_unphase(CMinisatSimp *, c_Var var);

int cminisatsimp_n_assigns(CMinisatSimp *);
int cminisatsimp_n_clauses(CMinisatSimp *);
int cminisatsimp_n_learnts(CMinisatSimp *);
int cminisatsimp_n_vars(CMinisatSimp *);

void cminisatsimp_set_conf_limit(CMinisatSimp *, int64_t limit);
void cminisatsimp_set_prop_limit(CMinisatSimp *, int64_t limit);
void cminisatsimp_set_no_limit(CMinisatSimp *);
void cminisatsimp_interrupt(CMinisatSimp *);

uint64_t cminisatsimp_decisions(CMinisatSimp *);
uint64_t cminisatsimp_propagations(CMinisatSimp *);
uint64_t cminisatsimp_conflicts(CMinisatSimp *);

// Propagates the assumptions, returns 20 if a
// conflict was encountered, 10 if not. The list of propagated literals is
// returned via the `prop_cb`. If the solver runs out of memory, returns
// `OUT_OF_MEM`.
int cminisatsimp_propcheck(CMinisatSimp *, const c_Lit *assumps,
                           size_t n_assumps, int psaving,
                           void (*prop_cb)(void *, c_Lit), void *cb_data);

// Simplification-specific functions
void cminisatsimp_set_frozen(CMinisatSimp *, c_Var var, int frozen);
int cminisatsimp_is_frozen(CMinisatSimp *, c_Var var);
int cminisatsimp_is_eliminated(CMinisatSimp *, c_Var var);
// -----------------------------------------------------------------------------

#ifdef __cplusplus
}
#endif

#endif
