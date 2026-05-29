/*
 * adsmt — C ABI header.
 *
 * v0.19 surface freeze candidate. The surface itself remains
 * subject to change until v1.0 ships; this header documents the
 * current shape so downstream C / C++ / Lean4 binding writers
 * have a stable reference.
 *
 * Compatibility guarantees:
 *   - v0.x: NO compatibility (per the v0.x exclusion policy
 *     adopted 2026-05-29). Both forward and backward breaking
 *     changes may land in any minor bump.
 *   - v1.0+: full semver-bound C ABI. Symbol additions land in
 *     minor bumps; symbol removals or signature changes require
 *     a major bump.
 *
 * License: tri-licensed under BSD-2-Clause OR Apache-2.0 OR
 * LGPL-2.1-or-later (matches the adsmt main project's triple).
 */

#ifndef ADSMT_H
#define ADSMT_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* === Return codes ============================================ */

/* SAT verdict codes returned by adsmt_solver_check_sat. */
#define ADSMT_SAT        0
#define ADSMT_UNSAT      1
#define ADSMT_UNKNOWN    2
#define ADSMT_ABDUCTIVE  3

/* Error codes for command-style operations (always negative). */
#define ADSMT_ERR_NULL    (-1)
#define ADSMT_ERR_INVALID (-2)

/* === Handle type ============================================= */

/*
 * Opaque solver handle. `0` represents null.
 *
 * Allocated by adsmt_solver_new(); freed by adsmt_solver_free().
 * Repeat free() returns ADSMT_ERR_NULL but does not crash.
 */
typedef size_t AdsmtSolverHandle;

/* === Lifecycle ================================================ */

AdsmtSolverHandle adsmt_solver_new(void);
int32_t adsmt_solver_free(AdsmtSolverHandle h);
int32_t adsmt_solver_reset(AdsmtSolverHandle h);

/* === Scope stack ============================================== */

int32_t adsmt_solver_push(AdsmtSolverHandle h);
int32_t adsmt_solver_pop(AdsmtSolverHandle h, uint32_t levels);

/* === Assertions ============================================== */

/*
 * Assert a single SMT-LIB-shaped atom string.
 *
 * `atom` MUST be a NUL-terminated UTF-8 string. The function
 * parses it via adsmt-parser and routes the resulting Term to
 * the engine. Returns 0 on success, negative error codes on
 * parse / type failure.
 */
int32_t adsmt_solver_assert_atom(AdsmtSolverHandle h,
                                 const char *atom);

/*
 * Total number of literals currently asserted (across all push
 * levels). Useful for instrumentation; not stable across pop
 * boundaries beyond the obvious "decreases on pop".
 */
int32_t adsmt_solver_assertion_count(AdsmtSolverHandle h);

/* === Solving ================================================= */

/*
 * Run check-sat. Returns one of ADSMT_SAT, ADSMT_UNSAT,
 * ADSMT_UNKNOWN, ADSMT_ABDUCTIVE (positive) or a negative error
 * code.
 */
int32_t adsmt_solver_check_sat(AdsmtSolverHandle h);

/* === Strings ================================================== */

/*
 * Returns a NUL-terminated UTF-8 string carrying the adsmt
 * version (Cargo workspace version) — caller MUST free via
 * adsmt_string_free().
 */
char *adsmt_version(void);

/*
 * Returns a null string handle (`(char *) NULL` equivalent).
 * Provided for language bindings that need a sentinel.
 */
char *adsmt_null_string(void);

/*
 * Free a string returned by an adsmt_* function. Safe to call
 * with NULL.
 */
void adsmt_string_free(char *s);

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* ADSMT_H */
