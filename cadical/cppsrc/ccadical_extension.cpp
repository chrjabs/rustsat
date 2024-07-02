// CaDiCaL C API Extension (Christoph Jabs)
// To be included at the bottom of `ccadical.cpp`

extern "C" {

const int OUT_OF_MEM = 50;

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

bool ccadical_configure(CCaDiCaL *ptr, const char *name) {
  return ((Wrapper *)ptr)->solver->configure(name);
}

void ccadical_phase(CCaDiCaL *ptr, int lit) {
  ((Wrapper *)ptr)->solver->phase(lit);
}

void ccadical_unphase(CCaDiCaL *ptr, int lit) {
  ((Wrapper *)ptr)->solver->unphase(lit);
}

int ccadical_vars(CCaDiCaL *ptr) { return ((Wrapper *)ptr)->solver->vars(); }

bool ccadical_set_option_ret(CCaDiCaL *wrapper, const char *name, int val) {
  return ((Wrapper *)wrapper)->solver->set(name, val);
}

bool ccadical_limit_ret(CCaDiCaL *wrapper, const char *name, int val) {
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
bool ccadical_flip(CCaDiCaL *wrapper, int lit) {
  return ((Wrapper *)wrapper)->solver->flip(lit);
}

bool ccadical_flippable(CCaDiCaL *wrapper, int lit) {
  return ((Wrapper *)wrapper)->solver->flippable(lit);
}
#endif
}
