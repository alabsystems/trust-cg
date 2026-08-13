/* trust-cg-sat-host - DRAT trampoline for MicroSAT.
 *
 * Author: Andrew Yates <andrewyates.name@gmail.com>
 * Copyright 2026 Andrew Yates | License: Apache-2.0
 *
 * Purpose
 * -------
 * MicroSAT's `addClause` and `reduceDB` are the two points at which the
 * solver mutates its clause database. DRAT proofs need an event whenever
 * a *learned* clause is added or a *lemma* is deleted. We do not modify
 * the upstream `microsat.c`. The build script renames the upstream
 * symbols to `microsat_native_add_clause` and `microsat_native_reduce_db`
 * via `-D` defines. This translation unit then defines the `addClause`
 * and `reduceDB` symbols that MicroSAT's own code expects, so all
 * internal call sites are routed through the trampoline at link time
 * without source edits.
 *
 * DRAT semantics (why this file is subtle)
 * ----------------------------------------
 * A DRAT proof is stated *relative to* the input CNF. `drat-trim` loads
 * the CNF, then replays the proof. Each proof line is either:
 *
 *   - an *addition* `l1 l2 ... 0`, which the checker must justify by
 *     RUP/RAT against the clauses currently in its database, or
 *   - a *deletion* `d l1 l2 ... 0`, which removes a clause.
 *
 * There are exactly three callers of `addClause` in microsat.c:
 *
 *   1. `parse`   -> `addClause(.., irr=1)`  -- ORIGINAL input clauses.
 *   2. `analyze` -> `addClause(.., irr=0)`  -- a freshly DERIVED lemma.
 *   3. `reduceDB`-> `addClause(.., irr=0)`  -- RE-ADDING a kept lemma.
 *
 * The correct DRAT trace must therefore:
 *
 *   - case (1): an input clause is already in the checker's database, so
 *     restating it as an addition is *redundant but sound* -- a clause
 *     already present is trivially RUP, and `drat-trim` accepts it. We
 *     deliberately keep emitting these so a formula that is UNSAT purely
 *     by parse-time unit propagation (e.g. `(x) and (-x)`, which
 *     short-circuits in `parse` before `solve`/`analyze` ever runs and
 *     thus learns no lemma) still produces a non-empty, well-formed,
 *     drat-trim-accepted proof rather than an empty file.
 *   - case (2): emit an addition -- genuine learned lemmas are the proof.
 *   - case (3): emit NOTHING. A kept lemma is *already present* in the
 *     checker's database and stays present, so re-stating it as a fresh
 *     addition would force the checker to re-derive (by RUP) a clause
 *     whose antecedent lemmas may have just been deleted in the same
 *     `reduceDB` batch -- which is exactly the failure mode that made
 *     `drat-trim` reject the pigeonhole / large-random proofs with
 *     "RAT check failed on all possible pivots".
 *
 * For deletions, `reduceDB` virtually clears every lemma and then
 * re-adds the ones worth keeping (`count < k`). From the DRAT database's
 * point of view only the *dropped* lemmas (`count >= k`) actually leave;
 * the kept ones never go away. So we must emit a `d` line for the
 * dropped lemmas ONLY, mirroring microsat's own keep/drop decision, and
 * leave the kept lemmas untouched in the proof.
 *
 * Implementation: a re-entrancy flag (`g_in_reduce_db`) is raised around
 * the native `reduceDB` so the `addClause` trampoline can recognise the
 * re-add path (caller 3) and suppress its addition. The deletion `d`
 * lines for the genuinely-dropped lemmas are emitted by walking the DB
 * *before* delegating, applying the same `count < k` test microsat uses.
 *
 * Lemma layout in `S->DB` (from MicroSAT's `addClause`):
 *   - allocation: `getMemory(S, size + 3)` returns base `b`.
 *   - watch prefix:   DB[b], DB[b+1]                (linked-list pointers)
 *   - clause body:    DB[b+2], ..., DB[b+2+size-1]  (literals)
 *   - terminator:     DB[b+2+size] = 0
 *
 * `reduceDB` walks lemmas using the same layout from `S->mem_fixed + 2`
 * upward in steps of `i += 3` (after the inner `while (S->DB[i])` loop
 * scans the literals + terminator). We mirror that walk here to enumerate
 * the lemmas about to be dropped before delegating.
 */

#include <stdio.h>
#include <stdlib.h>

/* Mirror of MicroSAT's `struct solver` (microsat.c lines 32-34). Must be
 * kept in sync if the vendored source snapshot is updated. Bindgen already
 * mirrors this struct from `include/microsat_wrapper.h`; the C side here
 * must remain a bit-identical declaration so the field offsets match the
 * upstream layout. We additionally need `model`, `nVars`, `mem_fixed`,
 * and `mem_used` to replicate reduceDB's keep/drop decision so we delete
 * exactly the lemmas microsat drops. */
struct solver {
  int  *DB, nVars, nClauses, mem_used, mem_fixed, mem_max, maxLemmas, nLemmas, *buffer, nConflicts, *model,
       *reason, *falseStack, *false, *first, *forced, *processed, *assigned, *next, *prev, head, res, fast, slow;
};

/* Renamed upstream entry points. Defined in microsat.c, exposed under
 * the renamed symbol thanks to the `-DaddClause=...` / `-DreduceDB=...`
 * build-script defines. */
extern int* microsat_native_add_clause(struct solver* S, int* in, int size, int irr);
extern void microsat_native_reduce_db(struct solver* S, int k);

/* Rust-side recorder hooks. Implemented in `src/drat_recorder.rs`.
 *
 *   - `rs_drat_record_add(lits, size)`: emit `lit1 lit2 ... 0\n`
 *   - `rs_drat_record_delete(lits, size)`: emit `d lit1 lit2 ... 0\n`
 *
 * Both are no-ops when no DRAT recorder is attached. The trampoline
 * always calls them; the recorder is responsible for cheap early-exit
 * when disabled. Literals are passed by raw pointer + count and are
 * read-only on the Rust side. */
extern void rs_drat_record_add(const int* lits, int size);
extern void rs_drat_record_delete(const int* lits, int size);

/* Re-entrancy guard. `reduceDB` re-adds the lemmas it keeps by calling
 * `addClause` again; those re-adds are not new derivations and must NOT
 * be recorded as DRAT additions (the kept lemma never left the checker's
 * database). We raise this flag for the duration of the native
 * `reduceDB` call so the `addClause` trampoline can recognise and
 * suppress the re-add path.
 *
 * MicroSAT is single-threaded per solve and the DRAT recorder is already
 * serialised process-globally by the Rust-side mutex (see
 * `drat_recorder.rs` and the corpus test's `CORPUS_LOCK`), so a plain
 * file-scope flag is sufficient; there is no nested-reduceDB re-entry in
 * microsat. */
static int g_in_reduce_db = 0;

int* addClause(struct solver* S, int* in, int size, int irr) {
  /* Record a DRAT addition for every clause EXCEPT the kept lemmas that
   * `reduceDB` re-adds:
   *
   *   - `g_in_reduce_db != 0` -> a KEPT lemma being re-added by
   *                             `reduceDB`. The clause is *already
   *                             present* in the checker's database (it
   *                             was never deleted -- see `reduceDB`
   *                             below, which now deletes only the
   *                             dropped lemmas), so re-stating it as a
   *                             fresh addition would force the checker to
   *                             re-derive by RUP a clause whose
   *                             antecedent lemmas may have just been
   *                             dropped in the same batch. That is the
   *                             bug that made `drat-trim` fall back to a
   *                             RAT check and reject pigeonhole / large
   *                             random proofs. Emit nothing.
   *
   *   - `irr != 0` (input clause from `parse`) and `irr == 0` (a fresh
   *     conflict lemma from `analyze`) -> emit the addition. Restating an
   *     input clause is redundant but harmless to the checker (a clause
   *     already in its database is trivially RUP), and emitting it keeps
   *     the proof non-empty for instances that are UNSAT purely by
   *     parse-time unit propagation.
   *
   * We pass the input literal buffer directly because that is exactly
   * what gets copied into the DB on the next line by the native
   * implementation. */
  if (!g_in_reduce_db) {
    rs_drat_record_add(in, size);
  }
  return microsat_native_add_clause(S, in, size, irr);
}

void reduceDB(struct solver* S, int k) {
  /* Emit a `d` proof step for every lemma microsat is about to DROP.
   *
   * microsat's reduceDB keeps a lemma iff the number of its literals
   * satisfied by the current model is `< k`, and re-adds the kept ones
   * via `addClause`; the rest are dropped. We must delete exactly the
   * dropped set: deleting a *kept* lemma (the previous implementation's
   * delete-everything behaviour) removes clauses the checker still needs
   * to justify later additions by RUP, which is what caused `drat-trim`
   * to fall back to a RAT check and reject the proof.
   *
   * Lemmas live in `S->DB[S->mem_fixed .. S->mem_used)` in the layout
   * documented in the file header. We mirror microsat's walk and its
   * `count < k` keep test exactly. */
  int* db = S->DB;
  int* model = S->model;
  int mem_used = S->mem_used;
  int mem_fixed = S->mem_fixed;
  int i = mem_fixed + 2;
  while (i < mem_used) {
    int head = i;
    int count = 0;
    /* Scan to the 0 terminator, counting model-satisfied literals using
     * microsat's own test: `(lit > 0) == model[abs(lit)]`. */
    while (db[i]) {
      int lit = db[i++];
      int v = lit < 0 ? -lit : lit;
      if ((lit > 0) == (model[v] != 0)) {
        count++;
      }
    }
    int size = i - head;
    /* Keep iff `count < k` (matches microsat reduceDB). Emit a deletion
     * for the lemmas that are NOT kept. */
    if (size > 0 && count >= k) {
      rs_drat_record_delete(&db[head], size);
    }
    /* Advance past the terminator + the 2-int watch prefix of the next
     * clause, matching `i += 3` after the inner loop in `reduceDB`. */
    i += 3;
  }

  /* Delegate, suppressing DRAT additions for the kept lemmas that
   * microsat re-adds via `addClause` while the guard is raised. */
  g_in_reduce_db = 1;
  microsat_native_reduce_db(S, k);
  g_in_reduce_db = 0;
}
