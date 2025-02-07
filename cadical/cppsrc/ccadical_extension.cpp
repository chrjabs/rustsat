// CaDiCaL C API Extension (Christoph Jabs)
// To be included at the bottom of `ccadical.cpp`

extern "C" {

int ccadical_add_mem(CCaDiCaL *wrapper, int lit) {
  try {
    ((Wrapper *)wrapper)->solver->add(lit);
    return 0;
  } catch (std::bad_alloc &) {
    return OUT_OF_MEM;
  }
}

int ccadical_assume_mem(CCaDiCaL *wrapper, int lit) {
  try {
    ((Wrapper *)wrapper)->solver->assume(lit);
    return 0;
  } catch (std::bad_alloc &) {
    return OUT_OF_MEM;
  }
}

int ccadical_constrain_mem(CCaDiCaL *wrapper, int lit) {
  try {
    ((Wrapper *)wrapper)->solver->constrain(lit);
    return 0;
  } catch (std::bad_alloc &) {
    return OUT_OF_MEM;
  }
}

int ccadical_solve_mem(CCaDiCaL *wrapper) {
  try {
    return ((Wrapper *)wrapper)->solver->solve();
  } catch (std::bad_alloc &) {
    return OUT_OF_MEM;
  }
}

int ccadical_configure(CCaDiCaL *ptr, const char *name) {
  return ((Wrapper *)ptr)->solver->configure(name);
}

void ccadical_phase(CCaDiCaL *ptr, int lit) {
  ((Wrapper *)ptr)->solver->phase(lit);
}

void ccadical_unphase(CCaDiCaL *ptr, int lit) {
  ((Wrapper *)ptr)->solver->unphase(lit);
}

int ccadical_vars(CCaDiCaL *ptr) { return ((Wrapper *)ptr)->solver->vars(); }

int ccadical_set_option_ret(CCaDiCaL *wrapper, const char *name, int val) {
  return ((Wrapper *)wrapper)->solver->set(name, val);
}

int ccadical_limit_ret(CCaDiCaL *wrapper, const char *name, int val) {
  return ((Wrapper *)wrapper)->solver->limit(name, val);
}

int64_t ccadical_redundant(CCaDiCaL *wrapper) {
  return ((Wrapper *)wrapper)->solver->redundant();
}

int ccadical_simplify_rounds(CCaDiCaL *wrapper, int rounds) {
  return ((Wrapper *)wrapper)->solver->simplify(rounds);
}

int ccadical_reserve(CCaDiCaL *wrapper, int min_max_var) {
  try {
    ((Wrapper *)wrapper)->solver->reserve(min_max_var);
    return 0;
  } catch (std::bad_alloc &) {
    return OUT_OF_MEM;
  }
}

int64_t ccadical_propagations(CCaDiCaL *wrapper) {
  return ((Wrapper *)wrapper)->solver->propagations();
}

int64_t ccadical_decisions(CCaDiCaL *wrapper) {
  return ((Wrapper *)wrapper)->solver->decisions();
}

int64_t ccadical_conflicts(CCaDiCaL *wrapper) {
  return ((Wrapper *)wrapper)->solver->conflicts();
}

#ifdef FLIP
int ccadical_flip(CCaDiCaL *wrapper, int lit) {
  return ((Wrapper *)wrapper)->solver->flip(lit);
}

int ccadical_flippable(CCaDiCaL *wrapper, int lit) {
  return ((Wrapper *)wrapper)->solver->flippable(lit);
}
#endif

int ccadical_propcheck(CCaDiCaL *wrapper, const int *assumps,
                       size_t assumps_len, int psaving,
                       void (*prop_cb)(void *, int), void *cb_data) {
  try {
    if (((Wrapper *)wrapper)
            ->solver->prop_check(assumps, assumps_len, psaving, prop_cb,
                                 cb_data)) {
      return 10;
    }
    return 20;
  } catch (std::bad_alloc &) {
    return OUT_OF_MEM;
  }
}

int ccadical_trace_api_calls(CCaDiCaL *wrapper, const char *path) {
  FILE *trace_file = fopen(path, "w");
  if (!trace_file)
    return 1;
  ((Wrapper *)wrapper)->solver->trace_api_calls(trace_file);
  return 0;
}

int ccadical_trace_proof_path(CCaDiCaL *wrapper, const char *path) {
  return ((Wrapper *)wrapper)->solver->trace_proof(path);
}
}

#ifdef TRACER
#include "ctracer.cpp"
#endif
