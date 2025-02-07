#ifdef __cplusplus
extern "C" {
#endif

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "ccadical.h"

typedef struct CCaDiCaLTracer CCaDiCaLTracer;
typedef enum {
  CONFLICT = 1,
  ASSUMPTIONS = 2,
  CONSTRAINT = 4
} CCaDiCaLConclusionType;

// Struct defining all necessary callbacks for a tracer
// If any of the callback is set to `NULL`, it will be ignored
// For all callbacks, the first void pointer argument is what was passed to the
// init function
// All clauses and other vectors are passed as a length and a read-only array of
// integers
typedef struct {
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
  void (*conclude_unsat)(void *, CCaDiCaLConclusionType, size_t,
                         const uint64_t *);

  // Notify the observer that conclude sat was requested.
  // will give the complete model as a vector.
  // Arguments: Data, model length, model
  void (*conclude_sat)(void *, size_t, const int *);
} CCaDiCaLTraceCallbacks;

// Connects a proof tracer to an instance of CaDiCaL
// Arguments: CaDiCaL, data, callbacks (all non-null), antecedents
CCaDiCaLTracer *ccadical_connect_proof_tracer(CCaDiCaL *, void *,
                                              CCaDiCaLTraceCallbacks, bool);

// Disconnects a proof tracer from an instance of CaDiCaL
// Arguments: CaDiCaL, tracer
// Returns false if the tracer was not found to be connected
bool ccadical_disconnect_proof_tracer(CCaDiCaL *, CCaDiCaLTracer *);

#ifdef __cplusplus
}
#endif
