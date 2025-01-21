#ifndef rustsat_h
#define rustsat_h

#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#define RUSTSAT_VERSION 0.6.3
#define RUSTSAT_VERSION_MAJOR 0
#define RUSTSAT_VERSION_MINOR 6
#define RUSTSAT_VERSION_PATCH 3

#ifdef __cplusplus
namespace RustSAT {
#endif  // __cplusplus

typedef enum MaybeError {
  /**
   * No error
   */
  Ok = 0,
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
  /**
   * Invalid IPASIR-style literal
   */
  InvalidLiteral,
  /**
   * Precision divisor is not a power of 2
   */
  PrecisionNotPow2,
  /**
   * Attempting to decrease precision
   */
  PrecisionDecreased,
} MaybeError;

/**
 * Implementation of the binary adder encoding first described in \[1\].
 * The implementation follows the description in \[2\].
 *
 * ## References
 *
 * - \[1\] Joose P. Warners: _A linear-time transformation of linear inequalities into conjunctive
 *     normal form_, Inf. Process. Lett. 1998.
 * - \[2\] Niklas Eén and Niklas Sörensson: _Translating Pseudo-Boolean Constraints into SAT_,
 *     JSAT 2006.
 */
typedef struct BinaryAdder BinaryAdder;

/**
 * Implementation of the binary adder tree generalized totalizer encoding
 * \[1\]. The implementation is incremental. The implementation is recursive.
 * This encoding only support upper bounding. Lower bounding can be achieved by
 * negating the input literals. This is implemented in
 * [`super::simulators::Inverted`].
 * The implementation is based on a node database.
 *
 * # References
 *
 * - \[1\] Saurabh Joshi and Ruben Martins and Vasco Manquinho: _Generalized
 *     Totalizer Encoding for Pseudo-Boolean Constraints_, CP 2015.
 */
typedef struct DbGte DbGte;

/**
 * Implementation of the binary adder tree totalizer encoding \[1\].
 * The implementation is incremental as extended in \[2\].
 * The implementation is based on a node database.
 * For now, this implementation only supports upper bounding.
 *
 * # References
 *
 * - \[1\] Olivier Bailleux and Yacine Boufkhad: _Efficient CNF Encoding of Boolean Cardinality
 *     Constraints_, CP 2003.
 * - \[2\] Ruben Martins and Saurabh Joshi and Vasco Manquinho and Ines Lynce: _Incremental
 *     Cardinality Constraints for MaxSAT_, CP 2014.
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
 *     Watchdog Encoding for Solving Weighted MaxSAT_, SAT 2018.
 */
typedef struct DynamicPolyWatchdog DynamicPolyWatchdog;

typedef void (*CClauseCollector)(int lit, void *data);

typedef void (*CAssumpCollector)(int lit, void *data);

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/**
 * Adds a new input literal to a [`BinaryAdder`].
 *
 * # Errors
 *
 * - If `lit` is not a valid IPASIR-style literal (e.g., `lit = 0`),
 *     [`MaybeError::InvalidLiteral`] is returned
 *
 * # Safety
 *
 * `adder` must be a return value of [`bin_adder_new`] that [`bin_adder_drop`] has not yet been
 * called on.
 */
enum MaybeError bin_adder_add(struct BinaryAdder *adder, int lit, size_t weight);

/**
 * Frees the memory associated with a [`BinaryAdder`]
 *
 * # Safety
 *
 * `adder` must be a return value of [`bin_adder_new`] and cannot be used
 * afterwards again.
 */
void bin_adder_drop(struct BinaryAdder *adder);

/**
 * Lazily builds the _change in_ pseudo-boolean encoding to enable lower bounds from within the
 * range.
 *
 * The min and max bounds are inclusive. After a call to [`bin_adder_encode_lb`] with
 * `min_bound=2` and `max_bound=4`, bounds satisfying `2 <= bound <= 4` can be enforced.
 *
 * Clauses are returned via the `collector`. The `collector` function should expect clauses to be
 * passed similarly to `ipasir_add`, as a 0-terminated sequence of literals where the literals are
 * passed as the first argument and the `collector_data` as a second.
 *
 * `n_vars_used` must be the number of variables already used and will be incremented by the
 * number of variables used up in the encoding.
 *
 * # Safety
 *
 * `adder` must be a return value of [`bin_adder_new`] that [`bin_adder_drop`] has not yet been
 * called on.
 *
 * # Panics
 *
 * If `min_bound > max_bound`.
 */
void bin_adder_encode_lb(struct BinaryAdder *adder,
                         size_t min_bound,
                         size_t max_bound,
                         uint32_t *n_vars_used,
                         CClauseCollector collector,
                         void *collector_data);

/**
 * Lazily builds the _change in_ pseudo-boolean encoding to enable upper bounds from within the
 * range.
 *
 * The min and max bounds are inclusive. After a call to [`bin_adder_encode_ub`] with
 * `min_bound=2` and `max_bound=4`, bounds satisfying `2 <= bound <= 4` can be enforced.
 *
 * Clauses are returned via the `collector`. The `collector` function should expect clauses to be
 * passed similarly to `ipasir_add`, as a 0-terminated sequence of literals where the literals are
 * passed as the first argument and the `collector_data` as a second.
 *
 * `n_vars_used` must be the number of variables already used and will be incremented by the
 * number of variables used up in the encoding.
 *
 * # Safety
 *
 * `adder` must be a return value of [`bin_adder_new`] that [`bin_adder_drop`] has not yet been
 * called on.
 *
 * # Panics
 *
 * - If `min_bound > max_bound`.
 * - If the encoding ran out of memory
 */
void bin_adder_encode_ub(struct BinaryAdder *adder,
                         size_t min_bound,
                         size_t max_bound,
                         uint32_t *n_vars_used,
                         CClauseCollector collector,
                         void *collector_data);

/**
 * Returns assumptions/units for enforcing an upper bound (`sum of lits >= lb`). Make sure that
 * [`bin_adder_encode_lb`] has been called adequately and nothing has been called afterwards,
 * otherwise [`MaybeError::NotEncoded`] will be returned.
 *
 * Assumptions are returned via the collector callback. There is _no_ terminating zero, all
 * assumptions are passed when [`bin_adder_enforce_lb`] returns.
 *
 * # Safety
 *
 * `adder` must be a return value of [`bin_adder_new`] that [`bin_adder_drop`] has not yet been
 * called on.
 */
enum MaybeError bin_adder_enforce_lb(struct BinaryAdder *adder,
                                     size_t ub,
                                     CAssumpCollector collector,
                                     void *collector_data);

/**
 * Returns assumptions/units for enforcing an upper bound (`sum of lits <= ub`). Make sure that
 * [`bin_adder_encode_ub`] has been called adequately and nothing has been called afterwards,
 * otherwise [`MaybeError::NotEncoded`] will be returned.
 *
 * Assumptions are returned via the collector callback. There is _no_ terminating zero, all
 * assumptions are passed when [`bin_adder_enforce_ub`] returns.
 *
 * # Safety
 *
 * `adder` must be a return value of [`bin_adder_new`] that [`bin_adder_drop`] has not yet been
 * called on.
 */
enum MaybeError bin_adder_enforce_ub(struct BinaryAdder *adder,
                                     size_t ub,
                                     CAssumpCollector collector,
                                     void *collector_data);

/**
 * Creates a new [`BinaryAdder`] cardinality encoding
 */
struct BinaryAdder *bin_adder_new(void);

/**
 * Reserves all auxiliary variables that the encoding might need
 *
 * All calls to [`bin_adder_encode_ub`] or [`bin_adder_encode_lb`] following a call to this
 * function are guaranteed to not increase the value of `n_vars_used`. This does _not_ hold if
 * [`bin_adder_add`] is called in between
 *
 * # Safety
 *
 * `adder` must be a return value of [`bin_adder_new`] that [`bin_adder_drop`] has not yet been
 * called on.
 */
void bin_adder_reserve(struct BinaryAdder *adder, uint32_t *n_vars_used);

/**
 * Adds a new input literal to a [`DynamicPolyWatchdog`].
 *
 * # Errors
 *
 * - If `lit` is not a valid IPASIR-style literal (e.g., `lit = 0`),
 *     [`MaybeError::InvalidLiteral`] is returned
 * - If a literal is added _after_ the encoding is build, [`MaybeError::InvalidState`] is returned
 *
 * # Safety
 *
 * `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
 */
enum MaybeError dpw_add(struct DynamicPolyWatchdog *dpw, int lit, size_t weight);

/**
 * Gets the next smaller upper bound value that can be encoded without setting tares. This is used
 * for coarse convergence.
 *
 * # Safety
 *
 * `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
 */
size_t dpw_coarse_ub(struct DynamicPolyWatchdog *dpw, size_t ub);

/**
 * Frees the memory associated with a [`DynamicPolyWatchdog`]
 *
 * # Safety
 *
 * `dpw` must be a return value of [`dpw_new`] and cannot be used afterwards again.
 */
void dpw_drop(struct DynamicPolyWatchdog *dpw);

/**
 * Lazily builds the _change in_ pseudo-boolean encoding to enable upper bounds from within the
 * range. A change might only be a change in bounds, the [`DynamicPolyWatchdog`] does not support
 * adding literals at the moment.
 *
 * The min and max bounds are inclusive. After a call to [`dpw_encode_ub`] with `min_bound=2` and
 * `max_bound=4`, bounds satisfying `2 <= bound <= 4` can be enforced.
 *
 * Clauses are returned via the `collector`. The `collector` function should expect clauses to be
 * passed similarly to `ipasir_add`, as a 0-terminated sequence of literals where the literals are
 * passed as the first argument and the `collector_data` as a second.
 *
 * `n_vars_used` must be the number of variables already used and will be incremented by the
 * number of variables used up in the encoding.
 *
 * # Safety
 *
 * `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
 *
 * # Panics
 *
 * - If `min_bound > max_bound`.
 * - If the encoding ran out of memory
 */
void dpw_encode_ub(struct DynamicPolyWatchdog *dpw,
                   size_t min_bound,
                   size_t max_bound,
                   uint32_t *n_vars_used,
                   CClauseCollector collector,
                   void *collector_data);

/**
 * Returns assumptions/units for enforcing an upper bound (`sum of lits <= ub`). Make sure that
 * [`dpw_encode_ub`] has been called adequately and nothing has been called afterwards, otherwise
 * [`MaybeError::NotEncoded`] will be returned.
 *
 * Assumptions are returned via the collector callback. There is _no_ terminating zero, all
 * assumptions are passed when [`dpw_enforce_ub`] returns.
 *
 * # Safety
 *
 * `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
 */
enum MaybeError dpw_enforce_ub(struct DynamicPolyWatchdog *dpw,
                               size_t ub,
                               CAssumpCollector collector,
                               void *collector_data);

/**
 * Checks whether the encoding is already at the maximum precision
 *
 * # Safety
 *
 * `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
 */
bool dpw_is_max_precision(struct DynamicPolyWatchdog *dpw);

/**
 * Given a range of output values to limit the encoding to, returns additional clauses that
 * "shrink" the encoding through hardening
 *
 * The output value range must be a range considering _all_ input literals, not only the encoded
 * ones.
 *
 * This is intended for, e.g., a MaxSAT solving application where a global lower bound is derived
 * and parts of the encoding can be hardened.
 *
 * The min and max bounds are inclusive. After a call to [`dpw_limit_range`] with `min_value=2`
 * and `max_value=4`, the encoding is valid for the value range `2 <= range <= 4`.
 *
 * To not specify a bound, pass `0` for the lower bound or `SIZE_MAX` for the upper bound.
 *
 * Clauses are returned via the `collector`. The `collector` function should expect clauses to be
 * passed similarly to `ipasir_add`, as a 0-terminated sequence of literals where the literals are
 * passed as the first argument and the `collector_data` as a second.
 *
 * # Safety
 *
 * `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
 *
 * # Panics
 *
 * - If `min_bound <= max_bound`.
 * - If the encoding ran out of memory
 */
void dpw_limit_range(struct DynamicPolyWatchdog *dpw,
                     size_t min_value,
                     size_t max_value,
                     CClauseCollector collector,
                     void *collector_data);

/**
 * Creates a new [`DynamicPolyWatchdog`] cardinality encoding
 */
struct DynamicPolyWatchdog *dpw_new(void);

/**
 * Gets the next possible precision divisor value
 *
 * Note that this is not the next possible precision value from the last _set_ precision but from
 * the last _encoded_ precision. The divisor value will always be a power of two so that calling
 * `set_precision` and then encoding will produce the smallest non-empty next segment of the
 * encoding.
 *
 * # Safety
 *
 * `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
 */
size_t dpw_next_precision(struct DynamicPolyWatchdog *dpw);

/**
 * Reserves all auxiliary variables that the encoding might need
 *
 * All calls to [`dpw_encode_ub`] following a call to this function are guaranteed to not increase
 * the value of `n_vars_used`. This does _not_ hold if [`dpw_add`] is called in between
 *
 * # Safety
 *
 * `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
 */
void dpw_reserve(struct DynamicPolyWatchdog *dpw, uint32_t *n_vars_used);

/**
 * Set the precision at which to build the encoding at. With `divisor = 8` the encoding will
 * effectively be built such that the weight of every input literal is divided by `divisor`
 * (integer division, rounding down). Divisor values must be powers of 2. After building the
 * encoding, the precision can only be increased, i.e., only call this function with _decreasing_
 * divisor values.
 *
 * # Errors
 *
 * - If `divisor` is not a power of 2, [`MaybeError::PrecisionNotPow2`] is returned
 * - If `divisor` is larger than the last divisor, i.e., precision is attempted to be decreased,
 *     [`MaybeError::PrecisionDecreased`] is returned
 *
 * # Safety
 *
 * `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
 */
enum MaybeError dpw_set_precision(struct DynamicPolyWatchdog *dpw, size_t divisor);

/**
 * Adds a new input literal to a [`DbGte`].
 *
 * # Errors
 *
 * - If `lit` is not a valid IPASIR-style literal (e.g., `lit = 0`),
 *     [`MaybeError::InvalidLiteral`] is returned
 *
 * # Safety
 *
 * `gte` must be a return value of [`gte_new`] that [`gte_drop`] has not yet been called on.
 */
enum MaybeError gte_add(struct DbGte *gte, int lit, size_t weight);

/**
 * Frees the memory associated with a [`DbGte`]
 *
 * # Safety
 *
 * `gte` must be a return value of [`gte_new`] and cannot be used
 * afterwards again.
 */
void gte_drop(struct DbGte *gte);

/**
 * Lazily builds the _change in_ pseudo-boolean encoding to enable upper bounds from within the
 * range.
 *
 * The min and max bounds are inclusive. After a call to [`gte_encode_ub`] with `min_bound=2` and
 * `max_bound=4`, bounds satisfying `2 <= bound <= 4` can be enforced.
 *
 * Clauses are returned via the `collector`. The `collector` function should expect clauses to be
 * passed similarly to `ipasir_add`, as a 0-terminated sequence of literals where the literals are
 * passed as the first argument and the `collector_data` as a second.
 *
 * `n_vars_used` must be the number of variables already used and will be incremented by the
 * number of variables used up in the encoding.
 *
 * # Safety
 *
 * `gte` must be a return value of [`gte_new`] that [`gte_drop`] has not yet been called on.
 *
 * # Panics
 *
 * - If `min_bound > max_bound`.
 * - If the encoding ran out of memory
 */
void gte_encode_ub(struct DbGte *gte,
                   size_t min_bound,
                   size_t max_bound,
                   uint32_t *n_vars_used,
                   CClauseCollector collector,
                   void *collector_data);

/**
 * Returns assumptions/units for enforcing an upper bound (`sum of lits <= ub`). Make sure that
 * [`gte_encode_ub`] has been called adequately and nothing has been called afterwards, otherwise
 * [`MaybeError::NotEncoded`] will be returned.
 *
 * Assumptions are returned via the collector callback. There is _no_ terminating zero, all
 * assumptions are passed when [`gte_enforce_ub`] returns.
 *
 * # Safety
 *
 * `gte` must be a return value of [`gte_new`] that [`gte_drop`] has not yet been called on.
 */
enum MaybeError gte_enforce_ub(struct DbGte *gte,
                               size_t ub,
                               CAssumpCollector collector,
                               void *collector_data);

/**
 * Creates a new [`DbGte`] cardinality encoding
 */
struct DbGte *gte_new(void);

/**
 * Reserves all auxiliary variables that the encoding might need
 *
 * All calls to [`gte_encode_ub`] following a call to this function are guaranteed to not increase
 * the value of `n_vars_used`. This does _not_ hold if [`gte_add`] is called in between
 *
 * # Safety
 *
 * `gte` must be a return value of [`gte_new`] that [`gte_drop`] has not yet been called on.
 */
void gte_reserve(struct DbGte *gte, uint32_t *n_vars_used);

/**
 * Adds a new input literal to a [`DbTotalizer`]
 *
 * # Errors
 *
 * - If `lit` is not a valid IPASIR-style literal (e.g., `lit = 0`),
 *     [`MaybeError::InvalidLiteral`] is returned
 *
 * # Safety
 *
 * `tot` must be a return value of [`tot_new`] that [`tot_drop`] has not yet been called on.
 *
 * # Panics
 *
 * If the passed `lit` is an invalid IPASIR literal
 */
enum MaybeError tot_add(struct DbTotalizer *tot, int lit);

/**
 * Frees the memory associated with a [`DbTotalizer`]
 *
 * # Safety
 *
 * `tot` must be a return value of [`tot_new`] and cannot be used afterwards again.
 */
void tot_drop(struct DbTotalizer *tot);

/**
 * Lazily builds the _change in_ cardinality encoding to enable upper bounds in a given range. A
 * change might be added literals or changed bounds.
 *
 * The min and max bounds are inclusive. After a call to [`tot_encode_ub`] with `min_bound=2` and
 * `max_bound=4` bound including `<= 2` and `<= 4` can be enforced.
 *
 * Clauses are returned via the `collector`. The `collector` function should expect clauses to be
 * passed similarly to `ipasir_add`, as a 0-terminated sequence of literals where the literals are
 * passed as the first argument and the `collector_data` as a second.
 *
 * `n_vars_used` must be the number of variables already used and will be incremented by the
 * number of variables used up in the encoding.
 *
 * # Safety
 *
 * `tot` must be a return value of [`tot_new`] that [`tot_drop`] has not yet been called on.
 *
 * # Panics
 *
 * - If `min_bound > max_bound`.
 * - If the encoding ran out of memory
 */
void tot_encode_ub(struct DbTotalizer *tot,
                   size_t min_bound,
                   size_t max_bound,
                   uint32_t *n_vars_used,
                   CClauseCollector collector,
                   void *collector_data);

/**
 * Returns an assumption/unit for enforcing an upper bound (`sum of lits <= ub`). Make sure that
 * [`tot_encode_ub`] has been called adequately and nothing has been called afterwards, otherwise
 * [`MaybeError::NotEncoded`] will be returned.
 *
 * # Safety
 *
 * `tot` must be a return value of [`tot_new`] that [`tot_drop`] has not yet been called on.
 */
enum MaybeError tot_enforce_ub(struct DbTotalizer *tot, size_t ub, int *assump);

/**
 * Creates a new [`DbTotalizer`] cardinality encoding
 */
struct DbTotalizer *tot_new(void);

/**
 * Reserves all auxiliary variables that the encoding might need
 *
 * All calls to [`tot_encode_ub`] following a call to this function are guaranteed to not increase
 * the value of `n_vars_used`. This does _not_ hold if [`tot_add`] is called in between
 *
 * # Safety
 *
 * `tot` must be a return value of [`tot_new`] that [`tot_drop`] has not yet been called on.
 */
void tot_reserve(struct DbTotalizer *tot, uint32_t *n_vars_used);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#ifdef __cplusplus
}  // namespace RustSAT
#endif  // __cplusplus

#endif  /* rustsat_h */
