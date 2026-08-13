// str_const_lowering_slice.rs — R3 stage 1: &'static str CONSTANT lowering.
//
// Regeneration source for the embedded modules in
// crates/trust-cg-codegen/tests/e2e_str_const_lowering.rs. Each #[no_mangle]
// root is emitted as its own module with the R3 str-const frontend change
// (trust-ir branch `r3-str-lowering`, frontend/src/mir_lower.rs):
//
//   S=$HOME/trust/build/aarch64-apple-darwin/stage1
//   cd <r3-worktree>/frontend && env -u RUSTUP_TOOLCHAIN RUSTC=$S/bin/rustc \
//     DYLD_LIBRARY_PATH=$S/lib/rustlib/aarch64-apple-darwin/lib \
//     $S/bin/cargo run --bin trust_ir_mir -- str_const_lowering_slice.rs \
//     --crate-type=lib --mir-emit-closure <root> <out.tir>
//   roots: str_const_ident_root / str_const_pick_root / str_const_local_root /
//          str_const_from_len_root
//
// WHAT THIS EXERCISES (the previously probe-pinned gap (1), "call arg constant
// of non-scalar type ref"): a `&'static str` literal as (a) a call argument to
// an IN-MODULE fat-param callee, (b) two literals selected by a runtime branch,
// (c) a literal assigned into a fat LOCAL first (`let s: &str = "..."`), and
// (d) a literal argument to a real std consumer (`String::from`) that crosses
// an EXTERN shim boundary and copies the bytes into a heap String.
//
// MODELED BOUNDARIES (documented in the frontend change and the test file):
//   * ADDRESS IDENTITY / ALLOCATION COUNT: the lowering materializes each
//     distinct literal as an immortal heap image (one `__rust_alloc` per
//     function invocation, leaked) instead of rodata. Byte values and lengths
//     are exact; literal ADDRESS comparisons / allocator-traffic counts would
//     diverge from native. Nothing here observes either.
//   * `String::from` / `String::len` in root (d) are std (not crate-local), so
//     they lower to extern decls; the test binds FAITHFUL host shims that call
//     the real std fns through the module's synthesized ABI (sret String ptr /
//     pair ptr; thin &String -> u64).
//   * The `String` local's drop is not emitted by the lowering (the landed
//     RUNG-8b purely-deallocating-drop model: the String leaks). Return VALUES
//     are unaffected.
#![allow(dead_code)]

/// Crate-local leaf: consumes a `&str` (fat param, Ptr-to-pair ABI) and returns
/// it (fat sret return) — pure fat-lane plumbing, fully in-module.
fn ident_str(s: &str) -> &str {
    s
}

/// Crate-local leaf: selects one of two `&str`s by a runtime scalar — fat
/// params + branch + fat return.
fn pick_str<'a>(a: &'a str, b: &'a str, which: u64) -> &'a str {
    if which == 0 {
        a
    } else {
        b
    }
}

/// Root (a): a literal as a DIRECT call arg to an in-module fat-param callee.
/// The harness reads the returned (ptr,len) pair through the sret buffer and
/// compares the pointed-to bytes against "Tree.rec".
#[no_mangle]
pub extern "C" fn str_const_ident_root() -> &'static str {
    ident_str("Tree.rec")
}

/// Root (b): TWO literals, runtime-selected. Verifies distinct literals get
/// distinct images and the branch returns the right pair.
#[no_mangle]
pub extern "C" fn str_const_pick_root(which: u64) -> &'static str {
    pick_str("Tree.rec", "Forest.rec", which)
}

/// Root (c): the literal lands in a fat LOCAL first (`Use(Constant)` into a
/// fat destination — the second consumer site of the R3 change), then flows to
/// the callee as an ordinary fat PLACE arg.
#[no_mangle]
pub extern "C" fn str_const_local_root() -> &'static str {
    let s: &str = "Quot.lift";
    ident_str(s)
}

/// Root (d): the original probe (1) shape — `String::from("Tree.rec")` -> len.
/// The literal's pair crosses the extern boundary to the real `String::from`
/// (host shim), which COPIES the image bytes into a real heap String; a wrong
/// image byte / wrong length would change the observed len or the shim's
/// UTF-8 read.
#[no_mangle]
pub extern "C" fn str_const_from_len_root() -> u64 {
    let s = String::from("Tree.rec");
    s.len() as u64
}

/// Root (e): the T3 PROBE A2 shape VERBATIM (String::new + push_str x2 +
/// as_bytes + index-loop byte hash). Before R3 stage 1 this failed at the
/// push_str CONST ARGS (gap (1)); with (1) closed, the whole body lowers —
/// the `as_bytes` fat RETURN crosses as an sret pair (gap (2) fell out
/// naturally for this shape), and the hash loop (PtrMetadata bounds checks,
/// slice indexing through the fat pair, wrapping arithmetic) runs IN-MODULE.
/// std calls (`String::new`/`push_str`/`as_bytes`, `wrapping_mul`/`_add`)
/// stay extern; the test binds faithful host shims.
#[no_mangle]
pub extern "C" fn str_const_hash_root() -> u64 {
    let mut s = String::new();
    s.push_str("Tree");
    s.push_str(".rec");
    let bytes = s.as_bytes();
    let mut h = 0u64;
    let mut i = 0usize;
    while i < bytes.len() {
        h = h.wrapping_mul(31).wrapping_add(bytes[i] as u64);
        i += 1;
    }
    h
}
