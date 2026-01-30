// CaDiCaL C API Extension (Christoph Jabs)
// To be included at the bottom of `ccadical.h`

#include <stddef.h>

const int OUT_OF_MEM = 50;

int ccadical_add_mem(CCaDiCaL *wrapper, int lit);
int ccadical_assume_mem(CCaDiCaL *wrapper, int lit);
int ccadical_constrain_mem(CCaDiCaL *wrapper, int lit);
int ccadical_solve_mem(CCaDiCaL *wrapper);
int ccadical_configure(CCaDiCaL *ptr, const char *name);
#ifndef V2_2
void ccadical_phase(CCaDiCaL *ptr, int lit);
void ccadical_unphase(CCaDiCaL *ptr, int lit);
int ccadical_vars(CCaDiCaL *ptr);
#endif
int ccadical_set_option_ret(CCaDiCaL *wrapper, const char *name, int val);
int ccadical_limit_ret(CCaDiCaL *wrapper, const char *name, int val);
int64_t ccadical_redundant(CCaDiCaL *wrapper);
int ccadical_simplify_rounds(CCaDiCaL *wrapper, int rounds);
int ccadical_resize(CCaDiCaL *wrapper, int min_max_var);
#ifndef V2_2
int64_t ccadical_propagations(CCaDiCaL *wrapper);
int64_t ccadical_decisions(CCaDiCaL *wrapper);
int64_t ccadical_conflicts(CCaDiCaL *wrapper);
#endif
#ifdef V1_5
int ccadical_flip(CCaDiCaL *wrapper, int lit);
int ccadical_flippable(CCaDiCaL *wrapper, int lit);
#endif
#ifndef V2_1
int ccadical_propcheck(CCaDiCaL *wrapper, const int *assumps,
                       size_t assumps_len, int psaving,
                       void (*prop_cb)(void *, int), void *cb_data);
#else
int ccadical_propagate(CCaDiCaL *wrapper);
void ccadical_implied(CCaDiCaL *wrapper, void (*implied_cb)(void *, int),
                      void *cb_data);
#endif
#ifndef NTRACING
int ccadical_trace_api_calls(CCaDiCaL *wrapper, const char *const path);
#endif
int ccadical_trace_proof_path(CCaDiCaL *wrapper, const char *const path);
#ifdef V2_2
int64_t ccadical_get_statistic_value(const CCaDiCaL *wrapper,
                                     const char *const);
void ccadical_force_backtrack(const CCaDiCaL *wrapper, int new_level);
#endif
