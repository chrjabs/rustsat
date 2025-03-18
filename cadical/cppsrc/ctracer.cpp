// CaDiCaL C API Extension For Proof Tracing (Christoph Jabs)

#include <cassert>

#include "ctracer.h"
#include "tracer.hpp"

namespace CaDiCaL {

class CTracer : public Tracer {
  void *data;
  CCaDiCaLTraceCallbacks callbacks;

public:
  CTracer(void *data, CCaDiCaLTraceCallbacks callbacks)
      : data(data), callbacks(callbacks) {
    assert(callbacks.add_original_clause);
    assert(callbacks.add_derived_clause);
    assert(callbacks.delete_clause);
    assert(callbacks.weaken_minus);
    assert(callbacks.strengthen);
    assert(callbacks.report_status);
    assert(callbacks.finalize_clause);
    assert(callbacks.begin_proof);
    assert(callbacks.solve_query);
    assert(callbacks.add_assumption);
    assert(callbacks.add_constraint);
    assert(callbacks.reset_assumptions);
    assert(callbacks.add_assumption_clause);
    assert(callbacks.conclude_unsat);
    assert(callbacks.conclude_sat);
  }
  ~CTracer() {};

  void add_original_clause(uint64_t id, bool redundant,
                           const std::vector<int> &clause,
                           bool restored = false) override {
    callbacks.add_original_clause(data, id, redundant, clause.size(),
                                  clause.data(), restored);
  }

  void add_derived_clause(uint64_t id, bool redundant,
                          const std::vector<int> &clause,
                          const std::vector<uint64_t> &antecedents) override {
    callbacks.add_derived_clause(data, id, redundant, clause.size(),
                                 clause.data(), antecedents.size(),
                                 antecedents.data());
  }

  void delete_clause(uint64_t id, bool redundant,
                     const std::vector<int> &clause) override {
    callbacks.delete_clause(data, id, redundant, clause.size(), clause.data());
  }

  void weaken_minus(uint64_t id, const std::vector<int> &clause) override {
    callbacks.weaken_minus(data, id, clause.size(), clause.data());
  }

  void strengthen(uint64_t id) override { callbacks.strengthen(data, id); }

  void report_status(int status, uint64_t id) override {
    callbacks.report_status(data, status, id);
  }

  void finalize_clause(uint64_t id, const std::vector<int> &clause) override {
    callbacks.finalize_clause(data, id, clause.size(), clause.data());
  }

  void begin_proof(uint64_t id) override { callbacks.begin_proof(data, id); }

  void solve_query() override { callbacks.solve_query(data); }

  void add_assumption(int assumption_literal) override {
    callbacks.add_assumption(data, assumption_literal);
  }

  void add_constraint(const std::vector<int> &constraint_clause) override {
    callbacks.add_constraint(data, constraint_clause.size(),
                             constraint_clause.data());
  }

  void reset_assumptions() override { callbacks.reset_assumptions(data); }

  void
  add_assumption_clause(uint64_t id, const std::vector<int> &clause,
                        const std::vector<uint64_t> &antecedents) override {
    callbacks.add_assumption_clause(data, id, clause.size(), clause.data(),
                                    antecedents.size(), antecedents.data());
  }

  void conclude_unsat(ConclusionType conclusion_type,
                      const std::vector<uint64_t> &clause_ids) override {
    CCaDiCaLConclusionType conclusion_out;
    switch (conclusion_type) {
    case ConclusionType::CONFLICT:
      conclusion_out = CCaDiCaLConclusionType::CONFLICT;
      break;
    case ConclusionType::ASSUMPTIONS:
      conclusion_out = CCaDiCaLConclusionType::ASSUMPTIONS;
      break;
    case ConclusionType::CONSTRAINT:
      conclusion_out = CCaDiCaLConclusionType::CONSTRAINT;
      break;
    }
    callbacks.conclude_unsat(data, conclusion_out, clause_ids.size(),
                             clause_ids.data());
  }

  void conclude_sat(const std::vector<int> &model) override {
    callbacks.conclude_sat(data, model.size(), model.data());
  }

  void *get_data() { return data; }
};

} // namespace CaDiCaL

extern "C" {

CCaDiCaLTracer *ccadical_connect_proof_tracer(CCaDiCaL *wrapper, void *data,
                                              CCaDiCaLTraceCallbacks callbacks,
                                              bool antecedents) {
  CaDiCaL::CTracer *tracer = new CaDiCaL::CTracer(data, callbacks);
  ((Wrapper *)wrapper)
      ->solver->connect_proof_tracer((Tracer *)tracer, antecedents);
  return (CCaDiCaLTracer *)tracer;
}

bool ccadical_disconnect_proof_tracer(CCaDiCaL *wrapper,
                                      CCaDiCaLTracer *tracer) {
  bool ret =
      ((Wrapper *)wrapper)->solver->disconnect_proof_tracer((Tracer *)tracer);
  delete (CaDiCaL::CTracer *)tracer;
  return ret;
}
}
