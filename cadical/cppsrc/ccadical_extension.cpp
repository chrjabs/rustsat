// CaDiCaL C API Extension (Christoph Jabs)
// To be included at the bottom of `ccadical.cpp`

#ifdef TRACER
#include "tracer.hpp"

extern "C" {

#include <stddef.h>
#include <stdint.h>

// Struct defining all necessary callbacks for a tracer
// If any of the callback is set to `NULL`, it will be ignored
// For all callbacks, the first void pointer argument is what was passed to the
// init function
// All clauses and other vectors are passed as a length and a read-only array of
// integers
struct CCaDiCaLTraceCallbacks {
  /*------------------------------------------------------------------------*/
  /*                                                                        */
  /*                            Basic Events                                */
  /*                                                                        */
  /*------------------------------------------------------------------------*/

  // Notify the tracer that a original clause has been added.
  // Includes ID and wether the clause is redundant or irredundant
  // Arguments: Data, ID, redundant, length, clause, restored
  void (*add_original_clause)(void *, uint64_t, bool, size_t, const int *,
                              bool);

  // Notify the observer that a new clause has been derived.
  // Includes ID and wether the clause is redundant or irredundant
  // If antecedents are derived they will be included here.
  // Arguments: Data, ID, redundant, clause length, clause, antecedents length,
  // antecedents
  void (*add_derived_clause)(void *, uint64_t, bool, size_t, const int *,
                             size_t, const uint64_t *);

  // Notify the observer that a clause is deleted.
  // Includes ID and redundant/irredundant
  // Arguments: Data, ID, redundant, length, clause
  void (*delete_clause)(void *, uint64_t, bool, size_t, const int *);

  // Notify the observer to remember that the clause might be restored later
  // Arguments: Data, ID, length, clause
  void (*weaken_minus)(void *, uint64_t, size_t, const int *);

  // Notify the observer that a clause is strengthened
  // Arguments: Data, ID
  void (*strengthen)(void *, uint64_t);

  // Notify the observer that the solve call ends with status StatusType
  // If the status is UNSAT and an empty clause has been derived, the second
  // argument will contain its id.
  // Note that the empty clause is already added through add_derived_clause
  // and finalized with finalize_clause
  // Arguments: Data, int, ID
  void (*report_status)(void *, int, uint64_t);

  /*------------------------------------------------------------------------*/
  /*                                                                        */
  /*                   Specifically non-incremental                         */
  /*                                                                        */
  /*------------------------------------------------------------------------*/

  // Notify the observer that a clause is finalized.
  // Arguments: Data, ID, length, clause
  void (*finalize_clause)(void *, uint64_t, size_t, const int *);

  // Notify the observer that the proof begins with a set of reserved ids
  // for original clauses. Given ID is the first derived clause ID.
  // Arguments: Data, ID
  void (*begin_proof)(void *, uint64_t);

  /*------------------------------------------------------------------------*/
  /*                                                                        */
  /*                      Specifically incremental                          */
  /*                                                                        */
  /*------------------------------------------------------------------------*/

  // Notify the observer that an assumption has been added
  // Arguments: Data
  void (*solve_query)(void *);

  // Notify the observer that an assumption has been added
  // Arguments: Data, assumption_literal
  void (*add_assumption)(void *, int);

  // Notify the observer that a constraint has been added
  // Arguments: Data, length, constraint_clause
  void (*add_constraint)(void *, size_t, const int *);

  // Notify the observer that assumptions and constraints are reset
  // Arguments: Data
  void (*reset_assumptions)(void *);

  // Notify the observer that this clause could be derived, which
  // is the negation of a core of failing assumptions/constraints.
  // If antecedents are derived they will be included here.
  // Arguments: Data, ID, clause length, clause, antecedents length, antecedents
  void (*add_assumption_clause)(void *, uint64_t, size_t, const int *, size_t,
                                const uint64_t *);

  // Notify the observer that conclude unsat was requested.
  // will give either the id of the empty clause, the id of a failing
  // assumption clause or the ids of the failing constrain clauses
  // Arguments: Data, conclusion_type, length, clause_ids
  void (*conclude_unsat)(void *, ConclusionType, size_t, const uint64_t *);

  // Notify the observer that conclude sat was requested.
  // will give the complete model as a vector.
  // Arguments: Data, model length, model
  void (*conclude_sat)(void *, size_t, const int *);
};
}

namespace CaDiCaL {

class CTracer : public Tracer {
  void *data;
  CCaDiCaLTraceCallbacks callbacks;

public:
  CTracer(void *data, CCaDiCaLTraceCallbacks callbacks)
      : data(data), callbacks(callbacks) {}
  ~CTracer();

  void add_original_clause(uint64_t id, bool redundant,
                           const std::vector<int> &clause,
                           bool restored = false) override {
    if (!callbacks.add_original_clause)
      return;
    callbacks.add_original_clause(data, id, redundant, clause.size(),
                                  clause.data(), restored);
  }

  void add_derived_clause(uint64_t id, bool redundant,
                          const std::vector<int> &clause,
                          const std::vector<uint64_t> &antecedents) override {
    if (!callbacks.add_derived_clause)
      return;
    callbacks.add_derived_clause(data, id, redundant, clause.size(),
                                 clause.data(), antecedents.size(),
                                 antecedents.data());
  }

  void delete_clause(uint64_t id, bool redundant,
                     const std::vector<int> &clause) override {
    if (!callbacks.delete_clause)
      return;
    callbacks.delete_clause(data, id, redundant, clause.size(), clause.data());
  }

  void weaken_minus(uint64_t id, const std::vector<int> &clause) override {
    if (!callbacks.weaken_minus)
      return;
    callbacks.weaken_minus(data, id, clause.size(), clause.data());
  }

  void strengthen(uint64_t id) override {
    if (!callbacks.strengthen)
      return;
    callbacks.strengthen(data, id);
  }

  void report_status(int status, uint64_t id) override {
    if (!callbacks.report_status)
      return;
    callbacks.report_status(data, status, id);
  }

  void finalize_clause(uint64_t id, const std::vector<int> &clause) override {
    if (!callbacks.finalize_clause)
      return;
    callbacks.finalize_clause(data, id, clause.size(), clause.data());
  }

  void begin_proof(uint64_t id) override {
    if (!callbacks.begin_proof)
      return;
    callbacks.begin_proof(data, id);
  }

  void solve_query() override {
    if (!callbacks.solve_query)
      return;
    callbacks.solve_query(data);
  }

  void add_assumption(int assumption_literal) override {
    if (!callbacks.add_assumption)
      return;
    callbacks.add_assumption(data, assumption_literal);
  }

  void add_constraint(const std::vector<int> &constraint_clause) override {
    if (!callbacks.add_constraint)
      return;
    callbacks.add_constraint(data, constraint_clause.size(),
                             constraint_clause.data());
  }

  void reset_assumptions() override {
    if (!callbacks.reset_assumptions)
      return;
    callbacks.reset_assumptions(data);
  }

  void
  add_assumption_clause(uint64_t id, const std::vector<int> &clause,
                        const std::vector<uint64_t> &antecedents) override {
    if (!callbacks.add_assumption_clause)
      return;
    callbacks.add_assumption_clause(data, id, clause.size(), clause.data(),
                                    antecedents.size(), antecedents.data());
  }

  void conclude_unsat(ConclusionType conclusion_type,
                      const std::vector<uint64_t> &clause_ids) override {
    if (!callbacks.conclude_unsat)
      return;
    callbacks.conclude_unsat(data, conclusion_type, clause_ids.size(),
                             clause_ids.data());
  }

  void conclude_sat(const std::vector<int> &model) override {
    if (!callbacks.conclude_sat)
      return;
    callbacks.conclude_sat(data, model.size(), model.data());
  }
};

} // namespace CaDiCaL
#endif

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

#ifdef TRACER
CTracer *ccadical_connect_proof_tracer(CCaDiCaL *wrapper, void *data,
                                       CCaDiCaLTraceCallbacks callbacks,
                                       bool antecedents) {
  CTracer *tracer = new CTracer(data, callbacks);
  ((Wrapper *)wrapper)
      ->solver->connect_proof_tracer((Tracer *)tracer, antecedents);
  return tracer;
}

bool ccadical_disconnect_proof_tracer(CCaDiCaL *wrapper, CTracer *tracer) {
  return ((Wrapper *)wrapper)
      ->solver->disconnect_proof_tracer((Tracer *)tracer);
}
#endif
}
