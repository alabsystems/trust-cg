// trust-cg-sat-host build script.
//
// Provenance: vendored from upstream MicroSAT at commit
// 26985d9b6b9aa5375d345051bd98afd63213043d (Marijn Heule, MIT, 2022-06-18).
// The release source under `third_party/vendor/microsat/` stays pristine.
//
// Build-time instrumentation strategy
// -----------------------------------
// We do NOT modify the upstream `microsat.c` on disk. Instead the build
// script copies the pristine source into `$OUT_DIR/microsat_renamed.c`
// and applies definition-only text rewrites:
//
//   `int propagate (struct solver* S)`
//       -> `int microsat_native_propagate (struct solver* S)`
//   `int* addClause (...)`
//       -> `int* microsat_native_add_clause (...)`
//   `void reduceDB (...)`
//       -> `void microsat_native_reduce_db (...)`
//   `int main (int argc, char** argv)`
//       -> `int microsat_unused_main (int argc, char** argv)`
//
// Plus a single in-body rewrite to fix the B1-follow-up analyze-driver
// hand-off bug WITHOUT touching the upstream source on disk: line 133
// of microsat.c initialises the top-of-`propagate` `forced` flag as
//
//   int forced = S->reason[abs (*S->processed)];      // Initialize forced flag
//
// which is the "is the next literal forced?" proxy. The unconditional
// `if (forced) return UNSAT;` on line 153 then mis-fires when the JIT's
// analyze-driver returns to `solve()` with the lemma's UIP left
// unprocessed but with `reason[abs(UIP)] != 0`. We rewrite the
// initialiser to call a Rust-side helper that walks the trail and
// returns the canonical decision-level-0 verdict
// (see `propagate.rs::trust_cg_decision_level_is_zero`), so the line-153
// short-circuit fires only at true DL0.
//
// All call sites in microsat.c (e.g. `propagate(S)` inside `solve`,
// `addClause(S, ...)` inside `parse`, `reduceDB(S, 6)` inside `solve`)
// are left intact and resolve at link time to the trampoline symbols
// supplied by `src/propagate_trampoline.c` and `src/drat_trampoline.c`.
//
// Why not `cc::Build::define("propagate", ...)`: a `-D` define rewrites
// every textual occurrence of the identifier in the translation unit,
// including the call sites, so the call site would bypass our trampoline
// entirely. Definition-only line rewrites avoid that pitfall while
// keeping the on-disk source pristine.
//
// We `grep`'d the vendored sha to confirm that `propagate`, `addClause`,
// and `reduceDB` are only called (never taken by address) inside
// microsat.c, so the link-time interception is safe. We also assert each
// substitution match-count to fail loudly if a future vendored-source update
// reshapes the signatures.

use std::env;
use std::fs;
use std::path::PathBuf;

fn main() {
    let manifest_dir =
        PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR"));
    let workspace_root = manifest_dir
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root has two ancestors above CARGO_MANIFEST_DIR")
        .to_path_buf();
    let microsat_src = workspace_root.join("third_party/vendor/microsat/microsat.c");
    let propagate_trampoline = manifest_dir.join("src/propagate_trampoline.c");
    let drat_trampoline = manifest_dir.join("src/drat_trampoline.c");
    let wrapper_header = manifest_dir.join("include/microsat_wrapper.h");
    let out_dir = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR is set by cargo"));
    let microsat_renamed = out_dir.join("microsat_renamed.c");

    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed={}", microsat_src.display());
    println!("cargo:rerun-if-changed={}", propagate_trampoline.display());
    println!("cargo:rerun-if-changed={}", drat_trampoline.display());
    println!("cargo:rerun-if-changed={}", wrapper_header.display());

    let upstream =
        fs::read_to_string(&microsat_src).expect("read third_party/vendor/microsat/microsat.c");
    let rewritten = rewrite_definitions(&upstream);
    fs::write(&microsat_renamed, &rewritten).unwrap_or_else(|e| {
        panic!(
            "write rewritten microsat to {}: {e}",
            microsat_renamed.display()
        )
    });

    // Explicit -O3 + -march=native so the MicroSAT C baseline we ship
    // is built at the same optimisation tier a production-tuned C BCP
    // loop would receive. cc-rs already defaults to `opt-level=3` in
    // the release/bench profile, but cc-rs does NOT add a target-CPU
    // flag of its own. Comparing a verified-JIT against `-O0`/`-O2` C
    // would be misleading; this is the headline-honest configuration.
    //
    // The flag is gated under non-MSVC because MSVC's CL.EXE uses
    // `/O2 /favor:INTEL64` rather than `-O3 -march=native`. The
    // workspace's primary host (Apple Silicon, AArch64) and the
    // SAT-Comp deployment target (x86-64) both reach cc-rs's GCC/Clang
    // driver, which accepts these flags verbatim.
    let mut build = cc::Build::new();
    build
        .file(&microsat_renamed)
        .file(&propagate_trampoline)
        .file(&drat_trampoline)
        .warnings(false)
        .extra_warnings(false)
        .opt_level(3);
    let cc_tool = build.get_compiler();
    if !cc_tool.is_like_msvc() {
        build.flag_if_supported("-O3");
        build.flag_if_supported("-march=native");
    }
    build.compile("microsat");

    let bindings = bindgen::Builder::default()
        .header(wrapper_header.to_string_lossy().into_owned())
        .allowlist_function("parse")
        .allowlist_function("solve")
        .allowlist_function("initCDCL")
        .allowlist_type("solver")
        .layout_tests(false)
        .generate()
        .expect("bindgen generates microsat bindings");

    bindings
        .write_to_file(out_dir.join("microsat_bindings.rs"))
        .expect("bindgen writes microsat_bindings.rs");
}

/// Apply the four definition-only renames to the upstream microsat.c
/// text. Each needle is the full function-definition prologue (return
/// type + name + `(` + params + `) {`) so a call site cannot accidentally
/// match. We assert exactly one occurrence of each so a future upstream
/// bump that changes a signature fails the build loudly rather than
/// silently dropping the trampoline instrumentation.
fn rewrite_definitions(src: &str) -> String {
    let renames: &[(&str, &str)] = &[
        (
            "int propagate (struct solver* S) {",
            "int microsat_native_propagate (struct solver* S) {",
        ),
        (
            "int* addClause (struct solver* S, int* in, int size, int irr) {",
            "int* microsat_native_add_clause (struct solver* S, int* in, int size, int irr) {",
        ),
        (
            "void reduceDB (struct solver* S, int k) {",
            "void microsat_native_reduce_db (struct solver* S, int k) {",
        ),
        (
            "int main (int argc, char** argv) {",
            "int microsat_unused_main (int argc, char** argv) {",
        ),
    ];

    let mut out = src.to_string();
    for (needle, repl) in renames {
        let occurrences = out.matches(needle).count();
        assert_eq!(
            occurrences, 1,
            "expected exactly one occurrence of upstream definition {:?}, found {}; \
             the vendored MicroSAT source may no longer match commit 26985d9b",
            needle, occurrences
        );
        out = out.replace(needle, repl);
    }

    // Forward declarations for the symbols whose definitions now live in
    // trampoline C files. The unchanged call sites inside microsat.c
    // (e.g. `propagate(S)` inside `solve`, `addClause(...)` inside
    // `parse`) would otherwise fail C99's no-implicit-decl check. The
    // declarations reference `struct solver`, so we anchor the injection
    // immediately after the struct definition.
    //
    // The injection also forward-declares
    // `trust_cg_decision_level_is_zero`, the Rust-side helper that
    // replaces line 133's `forced` initialiser (see the in-body
    // rewrite below).
    let injection = "\n\
/* trust-cg-sat-host trampoline forward declarations.\n\
 * `propagate`, `addClause`, and `reduceDB` are now external symbols\n\
 * supplied by src/propagate_trampoline.c and src/drat_trampoline.c.\n\
 * The unchanged call sites further down in this file resolve to those\n\
 * trampolines at link time. */\n\
extern int propagate(struct solver* S);\n\
extern int* addClause(struct solver* S, int* in, int size, int irr);\n\
extern void reduceDB(struct solver* S, int k);\n\
\n\
/* trust-cg-sat-host B1 follow-up: fixes the analyze-driver UIP hand-off\n\
 * bug by replacing propagate's top-of-loop `forced` initialiser\n\
 * (microsat.c:133) with a canonical decision-level-0 walk. See\n\
 * propagate.rs::trust_cg_decision_level_is_zero for the Rust\n\
 * implementation. */\n\
extern int trust_cg_decision_level_is_zero(struct solver* S);\n\
\n";
    let struct_anchor = "       *reason, *falseStack, *false, *first, *forced, *processed, *assigned, *next, *prev, head, res, fast, slow; };";
    let struct_anchor_count = out.matches(struct_anchor).count();
    assert_eq!(
        struct_anchor_count, 1,
        "expected exactly one occurrence of struct solver anchor; upstream may have changed"
    );
    out = out.replace(struct_anchor, &format!("{}{}", struct_anchor, injection));

    // In-body rewrite: replace propagate's line-133 `forced` initialiser
    // with a call to the Rust-side decision-level-0 walk. The proxy
    // (`reason[abs(*processed)] != 0`) is sufficient inside a single
    // propagate-then-analyze step but mis-fires when the JIT's analyze-
    // driver returns to `solve()` mid-conflict-resolution: the lemma's
    // UIP is left unprocessed on the trail with `reason != 0`, and the
    // NEXT propagate call reads `forced = 1` even though decisions are
    // still alive at higher decision levels. The line-153 unconditional
    // `if (forced) return UNSAT;` then mis-terminates a SAT instance as
    // UNSAT (B1 diagnosis; see propagate.rs::try_jit_replace_native's
    // conflict branch for the full story).
    //
    // The replacement preserves the post-loop `if (forced) S->forced =
    // S->processed;` bookkeeping on line 157: at true DL0 it still
    // fires; at DL >= 1 it does not (matching the native semantics —
    // `S->forced` only lifts when the entire trail is unit-propagated).
    let forced_needle =
        "  int forced = S->reason[abs (*S->processed)];      // Initialize forced flag";
    let forced_replacement = "  int forced = trust_cg_decision_level_is_zero(S); // B1: was S->reason[abs(*S->processed)] (mis-fires post-analyze-driver UIP hand-off)";
    let forced_count = out.matches(forced_needle).count();
    assert_eq!(
        forced_count, 1,
        "expected exactly one occurrence of upstream forced-initialiser {:?}, found {}; \
         the vendored MicroSAT source may no longer match commit 26985d9b",
        forced_needle, forced_count
    );
    out = out.replace(forced_needle, forced_replacement);
    out
}
