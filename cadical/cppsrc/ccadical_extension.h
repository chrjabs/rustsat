// CaDiCaL C API Extension (Christoph Jabs)
// To be included at the bottom of `ccadical.h`

#include <stdbool.h>

const int OUT_OF_MEM = 50;

int ccadical_add_mem(CCaDiCaL *wrapper, int lit);
int ccadical_assume_mem(CCaDiCaL *wrapper, int lit);
int ccadical_constrain_mem(CCaDiCaL *wrapper, int lit);
int ccadical_solve_mem(CCaDiCaL *wrapper);
bool ccadical_configure(CCaDiCaL *ptr, const char *name);
void ccadical_phase(CCaDiCaL *ptr, int lit);
void ccadical_unphase(CCaDiCaL *ptr, int lit);
int ccadical_vars(CCaDiCaL *ptr);
bool ccadical_set_option_ret(CCaDiCaL *wrapper, const char *name, int val);
bool ccadical_limit_ret(CCaDiCaL *wrapper, const char *name, int val);
int64_t ccadical_redundant(CCaDiCaL *wrapper);
int ccadical_simplify_rounds(CCaDiCaL *wrapper, int rounds);
int ccadical_reserve(CCaDiCaL *wrapper, int min_max_var);
int64_t ccadical_propagations(CCaDiCaL *wrapper);
int64_t ccadical_decisions(CCaDiCaL *wrapper);
int64_t ccadical_conflicts(CCaDiCaL *wrapper);
#ifdef FLIP
bool ccadical_flip(CCaDiCaL *wrapper, int lit);
bool ccadical_flippable(CCaDiCaL *wrapper, int lit);
#endif
