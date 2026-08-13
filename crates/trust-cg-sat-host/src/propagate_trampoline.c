/* trust-cg-sat-host - C shim that redirects MicroSAT's propagate call site
 * through a Rust-defined replacement.
 *
 * SAFETY / DESIGN NOTES
 * ---------------------
 * Build-time wiring (see build.rs):
 *   - microsat.c is copied to $OUT_DIR with a single-line rewrite of the
 *     `propagate` function-definition signature to
 *     `microsat_native_propagate`. The vendored source stays pristine.
 *     The call site inside `solve()` (line 164 in the upstream sha) is
 *     deliberately *not* rewritten, so it remains a reference to the
 *     external symbol `propagate`.
 *   - This file is compiled alongside the rewritten microsat.c and
 *     defines `propagate` so that MicroSAT's `solve()` calls into this
 *     thunk at link time.
 *   - The thunk delegates to `trust_cg_propagate`, a Rust extern "C"
 *     function that owns the dispatch policy (native shadow / future
 *     trust-cg-JIT'd BCP). Keeping the C shim a single, trivial line of
 *     delegation means the *behaviour* is Rust-defined while the symbol
 *     name lives in C.
 *
 * Opaque-layout choice:
 *   - MicroSAT's `struct solver` is defined inline in microsat.c and is
 *     not exported. Replicating it in a header would couple this shim to
 *     the upstream layout. Instead we treat the pointer as opaque (void*)
 *     in C, and let the Rust side (which has a bindgen-generated
 *     `struct solver`) cast it back when it actually needs to read fields.
 *     A later swap to (b) (shared header) is a 1-line change here.
 *
 * Risk surface:
 *   - If MicroSAT ever takes the address of `propagate` (e.g.
 *     `int (*fn)(struct solver*) = propagate;`), the rename would still
 *     redirect that to `microsat_native_propagate` and bypass our
 *     trampoline silently. A grep at integration time confirmed there
 *     are no taken-address uses in the current vendored source revision
 *     (26985d9b6b9aa5375d345051bd98afd63213043d) - only the direct
 *     call site at microsat.c:164.
 */

/* Forward declaration of the renamed native implementation. We accept
 * the solver as an opaque pointer because (i) we never dereference it
 * here, and (ii) the real struct definition isn't exported by MicroSAT.
 */
int microsat_native_propagate(void* S);

/* Implemented in Rust (lib.rs:trust_cg_propagate). Owns the dispatch
 * policy between the native implementation and the validated JIT BCP path.
 */
extern int trust_cg_propagate(void* S);

/* The symbol MicroSAT's solve() resolves at link time. */
int propagate(void* S) {
    return trust_cg_propagate(S);
}
