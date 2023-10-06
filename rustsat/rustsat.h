#ifndef rustsat_h
#define rustsat_h

/* Generated with cbindgen:0.26.0 */

#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>


#ifdef __cplusplus
namespace RustSAT {
#endif // __cplusplus

typedef enum MaybeError {
  /**
   * No error
   */
  Ok,
  /**
   * Encode was not called before using the encoding
   */
  NotEncoded,
  /**
   * The requested encoding is unsatisfiable
   */
  Unsat,
  /**
   * The encoding is in an invalid state to perform this action
   */
  InvalidState,
} MaybeError;

/**
 * Implementation of the binary adder tree totalizer encoding \[1\].
 * The implementation is incremental as extended in \[2\].
 * The implementation is based on a node database.
 * For now, this implementation only supports upper bounding.
 *
 * # References
 *
 * - \[1\] Olivier Bailleux and Yacine Boufkhad: _Efficient CNF Encoding of Boolean Cardinality Constraints_, CP 2003.
 * - \[2\] Ruben Martins and Saurabh Joshi and Vasco Manquinho and Ines Lynce: _Incremental Cardinality Constraints for MaxSAT_, CP 2014.
 */
typedef struct DbTotalizer DbTotalizer;

/**
 * Implementation of the dynamic polynomial watchdog (DPW) encoding \[1\].
 *
 * **Note**:
 * This implementation of the  DPW encoding only supports incrementally
 * changing the bound, but not adding new input literals. Calling extend after
 * encoding resets the entire encoding and with the next encode and entirely
 * new encoding will be returned.
 *
 * ## References
 *
 * - \[1\] Tobias Paxian and Sven Reimer and Bernd Becker: _Dynamic Polynomial
 *   Watchdog Encoding for Solving Weighted MaxSAT_, SAT 2018.
 */
typedef struct DynamicPolyWatchdog DynamicPolyWatchdog;

typedef void (*CClauseCollector)(int lit, void *data);

typedef void (*CAssumpCollector)(int lit, void *data);

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/**
 * Adds a new input literal to a [`DynamicPolyWatchdog`]. Input
 * literals can only be added _before_ the encoding is built for the
 * first time. Otherwise [`MaybeError::InvalidState`] is returned.
 *
 * # Safety
 *
 * `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has
 * not yet been called on.
 */
enum MaybeError dpw_add(struct DynamicPolyWatchdog *dpw, int lit, size_t weight);

/**
 * Gets the next smaller upper bound value that can be encoded without
 * setting tares. This is used for coarse convergence.
 *
 * # Safety
 *
 * `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has
 * not yet been called on.
 */
size_t dpw_coarse_ub(struct DynamicPolyWatchdog *dpw, size_t ub);

/**
 * Frees the memory associated with a [`DynamicPolyWatchdog`]
 *
 * # Safety
 *
 * `dpw` must be a return value of [`dpw_new`] and cannot be used
 * afterwards again.
 */
void dpw_drop(struct DynamicPolyWatchdog *dpw);

/**
 * Lazily builds the _change in_ pseudo-boolean encoding to enable
 * upper bounds from within the range. A change might only be a change
 * in bounds, the [`DynamicPolyWatchdog`] does not support adding
 * literals at the moment.
 *
 * The min and max bounds are inclusive. After a call to
 * [`dpw_encode_ub`] with `min_bound=2` and `max_bound=4` bound
 * including `<= 2` and `<= 4` can be enforced.
 *
 * A call to `var_manager` must yield a new variable. The
 * encoding will be returned via the given callback function as
 * 0-terminated clauses (in the same way as IPASIR's `add`).
 *
 * # Safety
 *
 * `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has
 * not yet been called on.
 */
void dpw_encode_ub(struct DynamicPolyWatchdog *dpw,
                   size_t min_bound,
                   size_t max_bound,
                   int *n_vars_used,
                   CClauseCollector collector,
                   void *collector_data);

/**
 * Returns assumptions/units for enforcing an upper bound (`sum of lits
 * <= ub`). Make sure that [`dpw_encode_ub`] has been called adequately
 * and nothing has been called afterwards, otherwise
 * [`MaybeError::NotEncoded`] will be returned.
 *
 * Assumptions are returned via the collector callback. There is _no_
 * terminating zero, all assumptions are passed when [`dpw_enforce_ub`]
 * returns.
 *
 * # Safety
 *
 * `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has
 * not yet been called on.
 */
enum MaybeError dpw_enforce_ub(struct DynamicPolyWatchdog *dpw,
                               size_t ub,
                               CAssumpCollector collector,
                               void *collector_data);

/**
 * Creates a new [`DynamicPolyWatchdog`] cardinality encoding
 */
struct DynamicPolyWatchdog *dpw_new(void);

/**
 * Adds a new input literal to a [`DbTotalizer`]
 *
 * # Safety
 *
 * `tot` must be a return value of [`tot_new`] that [`tot_drop`] has
 * not yet been called on.
 */
void tot_add(struct DbTotalizer *tot, int lit);

/**
 * Frees the memory associated with a [`DbTotalizer`]
 *
 * # Safety
 *
 * `tot` must be a return value of [`tot_new`] and cannot be used
 * afterwards again.
 */
void tot_drop(struct DbTotalizer *tot);

/**
 * Lazily builds the _change in_ cardinality encoding to enable upper
 * bounds in a given range. A change might be added literals or changed
 * bounds.
 *
 * The min and max bounds are inclusive. After a call to
 * [`tot_encode_ub`] with `min_bound=2` and `max_bound=4` bound
 * including `<= 2` and `<= 4` can be enforced.
 *
 * A call to `var_manager` must yield a new variable. The
 * encoding will be returned via the given callback function as
 * 0-terminated clauses (in the same way as IPASIR's `add`).
 *
 * # Safety
 *
 * `tot` must be a return value of [`tot_new`] that [`tot_drop`] has
 * not yet been called on.
 */
void tot_encode_ub(struct DbTotalizer *tot,
                   size_t min_bound,
                   size_t max_bound,
                   int *n_vars_used,
                   CClauseCollector collector,
                   void *collector_data);

/**
 * Returns an assumption/unit for enforcing an upper bound (`sum of
 * lits <= ub`). Make sure that [`tot_encode_ub`] has been called
 * adequately and nothing has been called afterwards, otherwise
 * [`MaybeError::NotEncoded`] will be returned.
 *
 * # Safety
 *
 * `tot` must be a return value of [`tot_new`] that [`tot_drop`] has
 * not yet been called on.
 */
enum MaybeError tot_enforce_ub(struct DbTotalizer *tot, size_t ub, int *assump);

/**
 * Creates a new [`DbTotalizer`] cardinality encoding
 */
struct DbTotalizer *tot_new(void);

#ifdef __cplusplus
} // extern "C"
#endif // __cplusplus

#ifdef __cplusplus
} // namespace RustSAT
#endif // __cplusplus

#endif /* rustsat_h */
