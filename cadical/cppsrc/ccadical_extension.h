// CaDiCaL C API Extension (Christoph Jabs)
// To be included at the bottom of `ccadical.h`

#include <stddef.h>

const int OUT_OF_MEM = 50;

int ccadical_add_mem(CCaDiCaL *wrapper, int lit);
int ccadical_assume_mem(CCaDiCaL *wrapper, int lit);
int ccadical_constrain_mem(CCaDiCaL *wrapper, int lit);
int ccadical_solve_mem(CCaDiCaL *wrapper);
int ccadical_configure(CCaDiCaL *ptr, const char *name);
void ccadical_phase(CCaDiCaL *ptr, int lit);
void ccadical_unphase(CCaDiCaL *ptr, int lit);
int ccadical_vars(CCaDiCaL *ptr);
int ccadical_set_option_ret(CCaDiCaL *wrapper, const char *name, int val);
int ccadical_limit_ret(CCaDiCaL *wrapper, const char *name, int val);
int64_t ccadical_redundant(CCaDiCaL *wrapper);
int ccadical_simplify_rounds(CCaDiCaL *wrapper, int rounds);
int ccadical_reserve(CCaDiCaL *wrapper, int min_max_var);
int64_t ccadical_propagations(CCaDiCaL *wrapper);
int64_t ccadical_decisions(CCaDiCaL *wrapper);
int64_t ccadical_conflicts(CCaDiCaL *wrapper);
#ifdef FLIP
int ccadical_flip(CCaDiCaL *wrapper, int lit);
int ccadical_flippable(CCaDiCaL *wrapper, int lit);
#endif
int ccadical_propcheck(CCaDiCaL *wrapper, const int *assumps,
                       size_t assumps_len, int psaving,
                       void (*prop_cb)(void *, int), void *cb_data);
int ccadical_trace_api_calls(CCaDiCaL *wrapper, const char *path);
int ccadical_trace_proof_path(CCaDiCaL *wrapper, const char *path);
