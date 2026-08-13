/* trust-cg-sat-host - bindgen input for the vendored MicroSAT solver.
 *
 * Provenance: MicroSAT (Marijn Heule, MIT) ships its entire implementation
 * in a single .c file with no public header. This wrapper forward-declares
 * the symbols we expose through `pub mod sys` and lets bindgen produce
 * Rust signatures without parsing the C body itself.
 */

#ifndef TRUST_CG_SAT_HOST_MICROSAT_WRAPPER_H
#define TRUST_CG_SAT_HOST_MICROSAT_WRAPPER_H

#ifdef __cplusplus
extern "C" {
#endif

/* Mirrors the `struct solver` definition in third_party/vendor/microsat/microsat.c
 * verbatim so bindgen can size the type for stack allocation. Keep in sync
 * if the vendored source is ever updated past commit 26985d9b. */
struct solver {
  int  *DB, nVars, nClauses, mem_used, mem_fixed, mem_max, maxLemmas, nLemmas, *buffer, nConflicts, *model,
       *reason, *falseStack, *false, *first, *forced, *processed, *assigned, *next, *prev, head, res, fast, slow;
};

int  parse    (struct solver* s, char* filename);
int  solve    (struct solver* s);
void initCDCL (struct solver* s, int n, int m);

#ifdef __cplusplus
}
#endif

#endif
