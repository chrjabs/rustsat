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

// Minisat C API
// The API is roughly IPASIR-like

const char *cminisat_signature(void);

// This value is returned from _solve, _add, and _phase if the solver runs out
// of memory
const int OUT_OF_MEM = 50;

// -----------------------------------------------------------------------------
// API for the solver without preprocessing
typedef struct CMinisat CMinisat;
CMinisat *cminisat_init(void);
void cminisat_release(CMinisat *);

int cminisat_add(CMinisat *, int lit);
void cminisat_assume(CMinisat *, int lit);
int cminisat_solve(CMinisat *);
int cminisat_val(CMinisat *, int lit);
int cminisat_failed(CMinisat *, int lit);

int cminisat_phase(CMinisat *, int lit);
void cminisat_unphase(CMinisat *, int lit);

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

// Propagates the assumptions set via `cminisat_assume`, returns 20 if a
// conflict was encountered, 10 if not. The list of propagated literals is
// returned via the `prop_cb`. If the solver runs out of memory, returns
// `OUT_OF_MEM`.
int cminisat_propcheck(CMinisat *, int psaving, void (*prop_cb)(void *, int),
                       void *cb_data);
// -----------------------------------------------------------------------------

// -----------------------------------------------------------------------------
// API for the solver with preprocessing
typedef struct CMinisatSimp CMinisatSimp;
CMinisatSimp *cminisatsimp_init(void);
void cminisatsimp_release(CMinisatSimp *);

int cminisatsimp_add(CMinisatSimp *, int lit);
void cminisatsimp_assume(CMinisatSimp *, int lit);
int cminisatsimp_solve(CMinisatSimp *);
int cminisatsimp_val(CMinisatSimp *, int lit);
int cminisatsimp_failed(CMinisatSimp *, int lit);

int cminisatsimp_phase(CMinisatSimp *, int lit);
void cminisatsimp_unphase(CMinisatSimp *, int lit);

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

// Propagates the assumptions set via `cminisatsimp_assume`, returns 20 if a
// conflict was encountered, 10 if not. The list of propagated literals is
// returned via the `prop_cb`. If the solver runs out of memory, returns
// `OUT_OF_MEM`.
int cminisatsimp_propcheck(CMinisatSimp *, int psaving,
                           void (*prop_cb)(void *, int), void *cb_data);

// Simplification-specific functions
void cminisatsimp_set_frozen(CMinisatSimp *, int var, int frozen);
int cminisatsimp_is_frozen(CMinisatSimp *, int var);
int cminisatsimp_is_eliminated(CMinisatSimp *, int var);
// -----------------------------------------------------------------------------

#ifdef __cplusplus
}
#endif

#endif
