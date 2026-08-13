// SipHasher13-derived portions: Copyright (c) The Rust Project Contributors.
// Licensed under MIT; see third_party/vendor/rust-stdlib-SipHasher13-LICENSE.
// trust-cg-specific harness: Copyright 2026 Andrew Yates, Apache-2.0.

//! R7-A — SIPHASH13 DE-MODELING: boundary B7 (the LAST meta-hash model) is
//! CLOSED for the verified compute_meta surfaces. The ExprMeta payload hashes
//! (`hash_to_u64` at the Sort/Const/Lit/Proj arms) now run the PRODUCTION
//! hasher — std's DefaultHasher == SipHasher13 with zero keys — transcribed
//! VERBATIM from the toolchain std source into the slice, JIT-compiled
//! through Trust (Rust -> MIR -> trust-ir -> trust-cg -> machine code), and
//! proven native == JIT over real heap inputs with THREE independent oracles:
//!   1. the REAL `std::hash::DefaultHasher` at runtime (raw byte-string and
//!      integer-write differentials — the native oracle IS std's hasher);
//!   2. a native mirror of the production compute_meta arms whose payload
//!      hashing goes through the REAL std Hash machinery (mem::discriminant,
//!      derive(Hash), <[T]>::hash length prefix) driven into a REAL
//!      DefaultHasher — byte-for-byte the production hash path;
//!   3. META GOLDENS pinned from the REAL clean-kernel binary (scratch crate
//!      over $HOME/clean/crates/clean-kernel, cfg(not(kani)) so DefaultHasher is
//!      LIVE in compute_meta; 2026-07-03): G1..G8 below, plus the round-4
//!      Name cached_hash goldens cross-checked exactly (Tree.rec =
//!      0x293412c406e2a88e).
//!
//! WHAT REMAINS ON KaniHasher (stated precisely): the frozen rounds-1..6 gate
//! fixtures embedded in the older e2e files keep their KaniHasher model —
//! that is a fixture-regen convention, not a verification claim; and clean's
//! own cfg(kani) builds SELECT KaniHasher by design (that IS production
//! behavior under kani). The cfg(not(kani)) production hasher — the one the
//! shipping clean-kernel binary runs — is what this file de-models.
//!
//! Slice (verbatim transcription + [S-*] rewrite ledger + regen recipe):
//!   tests/slices/clean_siphash_slice.rs
//! Emitted at trust-ir 1eb4b56 (NO frontend changes this round; no-drift gate
//! re-run GREEN: whnf gold 115661 bytes byte-identical). All three embedded
//! modules: validate_module = 0, re-parse OK, deterministic re-emit
//! (byte-identical second emit) — re-asserted at test time.
//!
//! REGEN (per module):
//!   S=$HOME/trust/build/aarch64-apple-darwin/stage1
//!   cd $HOME/trust-ir/frontend
//!   env -u RUSTUP_TOOLCHAIN RUSTC=$S/bin/rustc \
//!     DYLD_LIBRARY_PATH=$S/lib/rustlib/aarch64-apple-darwin/lib \
//!     $S/bin/cargo run --bin trust_ir_mir -- \
//!     ../../trust-cg/crates/trust-cg-codegen/tests/slices/clean_siphash_slice.rs \
//!     --crate-type=lib --mir-emit-closure <root> <out.tir>
//!   roots: sip_bytes_root | sip_ints_root | meta_sip_root
//!
//! HANG SAFETY: every JIT compile+execute runs on a WATCHDOG worker thread
//! (180s). Run ONE TEST PER PROCESS:
//!   perl -e 'alarm 300; exec @ARGV' -- cargo test -p trust-cg-codegen \
//!     --test e2e_siphash_meta -- --exact <name> --test-threads=1

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::collections::hash_map::DefaultHasher;
use std::hash::Hasher;
use std::sync::Arc;
use std::sync::mpsc;
use std::time::Duration;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

// ════════════════════════════════════════════════════════════════════════════
// shared harness (the e2e_str_stage2.rs / e2e_universe_realnames.rs discipline)
// ════════════════════════════════════════════════════════════════════════════

fn jit_module(
    text: &str,
    what: &str,
    externs: &HashMap<String, *const u8>,
) -> trust_cg_codegen::jit::ExecutableBuffer {
    let module = trust_ir::parser::parse_module(text)
        .unwrap_or_else(|e| panic!("MIR-emitted `{what}` trust-ir text must parse: {e:?}"));
    let errs = trust_ir_build::validate_module(&module);
    assert!(
        errs.is_empty(),
        "MIR-emitted `{what}` must validate clean (emitted with 0 errors): {errs:?}"
    );
    // FAIL-LOUD completeness: every bodyless (extern) fn must have a shim bound.
    for f in &module.functions {
        if f.blocks.is_empty() {
            assert!(
                externs.contains_key(&f.name),
                "extern `{}` in `{what}` has no host shim bound — harness out of date",
                f.name
            );
        }
    }
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    Compiler::new(config)
        .compile_module_to_jit(&module, externs)
        .unwrap_or_else(|e| panic!("trust-cg JIT compile of MIR-emitted `{what}` failed: {e:?}"))
        .buffer
}

fn bind(buffer: &trust_cg_codegen::jit::ExecutableBuffer, sym: &str) -> *const u8 {
    buffer
        .get_fn_ptr_bound(sym)
        .unwrap_or_else(|| panic!("JIT symbol `{sym}` not found"))
        .as_ptr()
}

fn run_with_watchdog<T: Send + 'static>(what: &str, f: impl FnOnce() -> T + Send + 'static) -> T {
    let (tx, rx) = mpsc::channel();
    let what_owned = what.to_string();
    std::thread::spawn(move || {
        let _ = tx.send(f());
    });
    match rx.recv_timeout(Duration::from_secs(180)) {
        Ok(v) => v,
        Err(_) => panic!("WATCHDOG: `{what_owned}` did not complete within 180s (JIT hang?)"),
    }
}

/// The module-side fat pair layout: [data ptr at +0, byte length at +8].
#[repr(C)]
#[derive(Clone, Copy)]
struct FatPair {
    ptr: *const u8,
    len: u64,
}

/// Opaque 24-byte module-`Level` value (layout read off the emitted IR:
/// `Level::succ` copies three i64 lanes at +0/+8/+16 into the 40-byte
/// ArcInner it heap_allocs — 16B header + 24B data; `Level::param` stores
/// tag 4 @+0 and the cached_hash @+8). The host NEVER interprets these
/// bytes — all Level reads happen in JIT machine code; the host Vec shims
/// only move whole 24-byte values.
#[repr(C)]
#[derive(Clone, Copy)]
struct LevelBlob([u64; 3]);

// ── FAITHFUL host shims (landed conventions) ────────────────────────────────

extern "C" fn shim_rust_alloc(size: usize, align: usize) -> *mut u8 {
    unsafe {
        let layout = std::alloc::Layout::from_size_align(size, align).expect("valid layout");
        std::alloc::alloc(layout)
    }
}

extern "C" fn shim_wrapping_mul_u64(a: u64, b: u64) -> u64 {
    a.wrapping_mul(b)
}

extern "C" fn shim_wrapping_add_u8(a: u8, b: u8) -> u8 {
    a.wrapping_add(b)
}

extern "C" fn shim_ord_min_u32(a: u32, b: u32) -> u32 {
    std::cmp::Ord::min(a, b)
}

/// `core::slice::from_raw_parts::<u8>`: identity fat-pair construction.
extern "C" fn shim_from_raw_parts_u8(out: *mut FatPair, data: *const u8, len: u64) {
    unsafe {
        *out = FatPair { ptr: data, len };
    }
}

/// `core::slice::from_raw_parts::<u64>`: identity fat-pair construction
/// (len is the ELEMENT count; the module's u64 loads read through it).
extern "C" fn shim_from_raw_parts_u64(out: *mut FatPair, data: *const u8, len: u64) {
    unsafe {
        *out = FatPair { ptr: data, len };
    }
}

/// `core::str::from_utf8_unchecked`: the identity cast (&[u8] -> &str).
extern "C" fn shim_from_utf8_unchecked(out: *mut FatPair, inp: *const FatPair) {
    unsafe {
        *out = *inp;
    }
}

/// FAITHFUL `Arc::<str>::from(&str)` (str_stage2's landed shim): builds a
/// REAL Arc<str> (real ArcInner, real refcounts, bytes copied) and moves the
/// 16-byte Arc VALUE into the module slot. Leaks (the landed leak model).
extern "C" fn shim_arc_str_from(sret: *mut u8, pair: *const FatPair) {
    unsafe {
        let p = *pair;
        let s = std::str::from_utf8(std::slice::from_raw_parts(p.ptr, p.len as usize))
            .expect("Arc::<str>::from shim received non-UTF8 bytes");
        let a: Arc<str> = Arc::from(s);
        std::ptr::write(sret as *mut Arc<str>, a);
    }
}

/// FAITHFUL `<Arc<str> as Deref>::deref`: the real deref, as (ptr,len).
extern "C" fn shim_arc_str_deref(sret: *mut FatPair, arc_slot: *const Arc<str>) {
    unsafe {
        let a: &Arc<str> = &*arc_slot;
        let s: &str = a;
        *sret = FatPair {
            ptr: s.as_ptr(),
            len: s.len() as u64,
        };
    }
}

// Vec<Level> (module layout; 24-byte opaque elements) — landed vec-shim shape.
extern "C" fn shim_vec_lvl_new(sret: *mut Vec<LevelBlob>) {
    unsafe {
        std::ptr::write(sret, Vec::new());
    }
}
extern "C" fn shim_vec_lvl_push(v: *mut Vec<LevelBlob>, val: *const LevelBlob) {
    unsafe {
        (*v).push(*val);
    }
}
extern "C" fn shim_vec_lvl_len(v: *const Vec<LevelBlob>) -> u64 {
    unsafe { (*v).len() as u64 }
}
extern "C" fn shim_vec_lvl_index(v: *const Vec<LevelBlob>, j: u64) -> *const LevelBlob {
    unsafe {
        let vr: &Vec<LevelBlob> = &*v;
        &vr[j as usize] as *const LevelBlob
    }
}
extern "C" fn shim_vec_lvl_deref(out: *mut FatPair, v: *const Vec<LevelBlob>) {
    unsafe {
        *out = FatPair {
            ptr: (*v).as_ptr() as *const u8,
            len: (*v).len() as u64,
        };
    }
}

// Vec<u64> — same shape, by-value u64 push, element pointer index.
extern "C" fn shim_vec_u64_new(sret: *mut Vec<u64>) {
    unsafe {
        std::ptr::write(sret, Vec::new());
    }
}
extern "C" fn shim_vec_u64_push(v: *mut Vec<u64>, val: u64) {
    unsafe {
        (*v).push(val);
    }
}
extern "C" fn shim_vec_u64_len(v: *const Vec<u64>) -> u64 {
    unsafe { (*v).len() as u64 }
}
extern "C" fn shim_vec_u64_index(v: *const Vec<u64>, j: u64) -> *const u64 {
    unsafe {
        let vr: &Vec<u64> = &*v;
        &vr[j as usize] as *const u64
    }
}

// Extern symbol names read VERBATIM from the emitted modules (v0 mangling;
// instantiating crate = clean_siphash_slice).
const SYM_FRP_U8: &str =
    "_RINvNtNtCs2EYQwhfuABO_4core5slice3raw14from_raw_partshECs6Skw9Chgdp8_19clean_siphash_slice";
const SYM_FRP_U64: &str =
    "_RINvNtNtCs2EYQwhfuABO_4core5slice3raw14from_raw_partsyECs6Skw9Chgdp8_19clean_siphash_slice";
const SYM_FROM_UTF8_UNCHECKED: &str = "_RNvNtNtCs2EYQwhfuABO_4core3str8converts19from_utf8_uncheckedCs6Skw9Chgdp8_19clean_siphash_slice";
const SYM_ARC_STR_FROM: &str = "_RNvXs17_NtCskTzINo8ZBH9_5alloc4syncINtB6_3ArceEINtNtCs2EYQwhfuABO_4core7convert4FromReE4fromCs6Skw9Chgdp8_19clean_siphash_slice";
const SYM_ARC_STR_DEREF: &str = "_RNvXsw_NtCskTzINo8ZBH9_5alloc4syncINtB5_3ArceENtNtNtCs2EYQwhfuABO_4core3ops5deref5Deref5derefCs6Skw9Chgdp8_19clean_siphash_slice";
const SYM_VEC_LVL_NEW: &str =
    "_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNtCs6Skw9Chgdp8_19clean_siphash_slice5LevelE3newBE_";
const SYM_VEC_LVL_PUSH: &str = "_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6Skw9Chgdp8_19clean_siphash_slice5LevelE4pushBH_";
const SYM_VEC_LVL_LEN: &str = "_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCs6Skw9Chgdp8_19clean_siphash_slice5LevelE3lenBG_";
const SYM_VEC_LVL_INDEX: &str = "_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6Skw9Chgdp8_19clean_siphash_slice5LevelEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_";
const SYM_VEC_LVL_DEREF: &str = "_RNvXs7_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6Skw9Chgdp8_19clean_siphash_slice5LevelENtNtNtCs2EYQwhfuABO_4core3ops5deref5Deref5derefBH_";
const SYM_VEC_U64_NEW: &str =
    "_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecyE3newCs6Skw9Chgdp8_19clean_siphash_slice";
const SYM_VEC_U64_PUSH: &str =
    "_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecyE4pushCs6Skw9Chgdp8_19clean_siphash_slice";
const SYM_VEC_U64_LEN: &str =
    "_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecyE3lenCs6Skw9Chgdp8_19clean_siphash_slice";
const SYM_VEC_U64_INDEX: &str = "_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecyEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexCs6Skw9Chgdp8_19clean_siphash_slice";
const SYM_ORD_MIN_U32: &str =
    "_RNvYmNtNtCs2EYQwhfuABO_4core3cmp3Ord3minCs6Skw9Chgdp8_19clean_siphash_slice";
const SYM_WRAPPING_MUL_U64: &str = "_RNvMs7_NtCs2EYQwhfuABO_4core3numy12wrapping_mul";
const SYM_WRAPPING_ADD_U8: &str = "_RNvMs4_NtCs2EYQwhfuABO_4core3numh12wrapping_add";

fn bytes_externs() -> HashMap<String, *const u8> {
    let mut e: HashMap<String, *const u8> = HashMap::new();
    e.insert("__rust_alloc".to_string(), shim_rust_alloc as *const u8);
    e.insert(SYM_FRP_U8.to_string(), shim_from_raw_parts_u8 as *const u8);
    e
}

fn ints_externs() -> HashMap<String, *const u8> {
    let mut e: HashMap<String, *const u8> = HashMap::new();
    e.insert("__rust_alloc".to_string(), shim_rust_alloc as *const u8);
    e.insert(
        SYM_WRAPPING_ADD_U8.to_string(),
        shim_wrapping_add_u8 as *const u8,
    );
    e
}

fn meta_externs() -> HashMap<String, *const u8> {
    let mut e: HashMap<String, *const u8> = HashMap::new();
    e.insert("__rust_alloc".to_string(), shim_rust_alloc as *const u8);
    e.insert(SYM_FRP_U8.to_string(), shim_from_raw_parts_u8 as *const u8);
    e.insert(
        SYM_FRP_U64.to_string(),
        shim_from_raw_parts_u64 as *const u8,
    );
    e.insert(
        SYM_FROM_UTF8_UNCHECKED.to_string(),
        shim_from_utf8_unchecked as *const u8,
    );
    e.insert(SYM_ARC_STR_FROM.to_string(), shim_arc_str_from as *const u8);
    e.insert(
        SYM_ARC_STR_DEREF.to_string(),
        shim_arc_str_deref as *const u8,
    );
    e.insert(SYM_VEC_LVL_NEW.to_string(), shim_vec_lvl_new as *const u8);
    e.insert(SYM_VEC_LVL_PUSH.to_string(), shim_vec_lvl_push as *const u8);
    e.insert(SYM_VEC_LVL_LEN.to_string(), shim_vec_lvl_len as *const u8);
    e.insert(
        SYM_VEC_LVL_INDEX.to_string(),
        shim_vec_lvl_index as *const u8,
    );
    e.insert(
        SYM_VEC_LVL_DEREF.to_string(),
        shim_vec_lvl_deref as *const u8,
    );
    e.insert(SYM_VEC_U64_NEW.to_string(), shim_vec_u64_new as *const u8);
    e.insert(SYM_VEC_U64_PUSH.to_string(), shim_vec_u64_push as *const u8);
    e.insert(SYM_VEC_U64_LEN.to_string(), shim_vec_u64_len as *const u8);
    e.insert(
        SYM_VEC_U64_INDEX.to_string(),
        shim_vec_u64_index as *const u8,
    );
    e.insert(SYM_ORD_MIN_U32.to_string(), shim_ord_min_u32 as *const u8);
    e.insert(
        SYM_WRAPPING_MUL_U64.to_string(),
        shim_wrapping_mul_u64 as *const u8,
    );
    e
}

// ════════════════════════════════════════════════════════════════════════════
// GOLDENS — pinned 2026-07-03 from the REAL clean-kernel binary (scratch
// crate over $HOME/clean/crates/clean-kernel, release, cfg(not(kani)):
// DefaultHasher LIVE in compute_meta). Meta words reconstructed from the
// PUBLIC accessors (hash_cached / has_*_quick / loose_bvar_range) with the
// KNOWN depth (0 for the leaf kinds, 1 for proj-over-leaf).
// ════════════════════════════════════════════════════════════════════════════

const GOLD_NAME_NAT: u64 = 0x9ecc0d3a68dfdd9b;
const GOLD_NAME_TREE_REC: u64 = 0x293412c406e2a88e; // == the round-4 pin
const GOLD_NAME_U: u64 = 0xae572a66f1f7b2e8;
const GOLD_NAME_V: u64 = 0x486e7075aebc6ca6;
const GOLD_NAME_PROD: u64 = 0xd43076ddcea47779;

const G1_SORT_ZERO: u64 = 0x00000000d83e0b62; // Expr::sort(Level::zero())
const G2_SORT_SUCC_PARAM_U: u64 = 0x0000080064c21ef9; // sort(succ(param u))
const G3_CONST_NAT_EMPTY: u64 = 0x0000000086c5c1a0; // const(Nat, [])
const G4_CONST_TREEREC: u64 = 0x000008004e32e247; // const(Tree.rec,[succ u,0])
const G5_LIT_42: u64 = 0x0000000022aef57c; // nat_lit(42)
const G6_LIT_BIG: u64 = 0x00000000b7d2cf54; // bignat_lit(Big[lo,hi])
const G6_LIMB_LO: u64 = 0xfedc_ba98_7654_3210;
const G6_LIMB_HI: u64 = 0x0123_4567_89ab_cdef;
const G7_LIT_STR_TREEREC: u64 = 0x00000000963529dc; // str_lit("Tree.rec")
const G8_PROJ_PROD_1_LIT7: u64 = 0x00000001f98de6b9; // proj(Prod,1,nat_lit(7))

// Raw DefaultHasher pins (same run; guard the algorithm assumption in BOTH
// toolchains — the native oracle must reproduce these before it is trusted).
const SIP_EMPTY: u64 = 0xd1fba762150c532c;
const SIP_ABC: u64 = 0xc03bc3a0042630f2;
const SIP_U8_7_U64_X: u64 = 0x0465b7c16226984a; // write_u8(7); write_u64(0x0123456789abcdef)
const SIP_LCG40: u64 = 0xda7f53b7fae03d6d; // write(&lcg_bytes(0x5eed, 40))

/// The deterministic content stream the byte sweep uses (LCG, seed fixed).
fn lcg_bytes(seed: u64, n: usize) -> Vec<u8> {
    let mut lcg = seed;
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        lcg = lcg
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        out.push((lcg >> 33) as u8);
    }
    out
}

// ════════════════════════════════════════════════════════════════════════════
// NATIVE MIRROR — the production compute_meta arms with payload hashing done
// by the REAL std Hash machinery (mem::discriminant, derive(Hash), <[T]>::hash
// with its write_length_prefix) into a REAL DefaultHasher. This is
// byte-for-byte the cfg(not(kani)) clean-kernel hash path; the module carries
// the transcription, so agreement proves the transcription.
// ════════════════════════════════════════════════════════════════════════════

mod mirror {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    use std::sync::Arc;

    /// name.rs:233-239 hash surface + name.rs:461-467 Hash (cached_hash only).
    pub struct Name {
        pub cached_hash: u64,
    }

    impl Hash for Name {
        #[inline]
        fn hash<H: Hasher>(&self, state: &mut H) {
            // O(1) hash using cached value
            self.cached_hash.hash(state);
        }
    }

    /// level/mod.rs:81-92.
    pub enum Level {
        Zero,
        Succ(Arc<Level>),
        Max(Arc<Level>, Arc<Level>),
        IMax(Arc<Level>, Arc<Level>),
        Param(Name),
    }

    /// VERBATIM the production cfg(not(kani)) Hash (level/mod.rs:96-110) —
    /// REAL mem::discriminant, REAL default write_* chain.
    impl Hash for Level {
        fn hash<H: Hasher>(&self, state: &mut H) {
            std::mem::discriminant(self).hash(state);
            match self {
                Level::Zero => {}
                Level::Succ(l) => l.hash(state),
                Level::Max(l, r) | Level::IMax(l, r) => {
                    l.hash(state);
                    r.hash(state);
                }
                Level::Param(n) => n.hash(state),
            }
        }
    }

    impl Level {
        pub fn has_params(&self) -> bool {
            match self {
                Level::Zero => false,
                Level::Succ(l) => l.has_params(),
                Level::Max(l1, l2) | Level::IMax(l1, l2) => l1.has_params() || l2.has_params(),
                Level::Param(_) => true,
            }
        }
    }

    /// expr/types.rs:165-171 — REAL derive(Hash) (the production derives).
    #[derive(Hash)]
    pub enum BigNat {
        Small(u64),
        Big(Vec<u64>),
    }

    /// expr/types.rs:399-406 — REAL derive(Hash).
    #[derive(Hash)]
    pub enum Literal {
        Nat(BigNat),
        String(Arc<str>),
    }

    /// VERBATIM production hash_to_u64 (expr/meta.rs:367-374, cfg(not(kani))).
    pub fn hash_to_u64<T: Hash>(value: &T) -> u64 {
        let mut hasher = DefaultHasher::new();
        value.hash(&mut hasher);
        hasher.finish()
    }

    /// expr/meta.rs:264-274 — mix_hash VERBATIM.
    pub fn mix_hash(h: u64, k: u64) -> u64 {
        const M: u64 = 0xc6a4_a793_5bd1_e995;
        const R: u32 = 47;
        let mut k = k.wrapping_mul(M);
        k ^= k >> R;
        k ^= M;
        let mut h = h ^ k;
        h = h.wrapping_mul(M);
        h
    }

    /// expr/meta.rs — ExprMeta::pack VERBATIM (bit layout).
    pub fn pack(
        hash: u32,
        loose_bvar_range: u32,
        approx_depth: u32,
        has_fvar: bool,
        has_expr_mvar: bool,
        has_level_mvar: bool,
        has_level_param: bool,
    ) -> u64 {
        let depth = approx_depth.min(255);
        (hash as u64)
            | ((depth as u64) << 32)
            | ((has_fvar as u64) << 40)
            | ((has_expr_mvar as u64) << 41)
            | ((has_level_mvar as u64) << 42)
            | ((has_level_param as u64) << 43)
            | ((loose_bvar_range as u64) << 44)
    }

    // clean's Level has no MVar constructor: everywhere-false.
    pub fn level_has_mvar(_l: &Level) -> bool {
        false
    }

    /// compute_meta Sort arm (kind.rs:558-566).
    pub fn meta_sort(lvl: &Level) -> u64 {
        pack(
            mix_hash(11, hash_to_u64(lvl)) as u32,
            0,
            0,
            false,
            false,
            level_has_mvar(lvl),
            lvl.has_params(),
        )
    }

    /// compute_meta Const arm (kind.rs:567-581). `levels` hashed as the
    /// Vec (== SmallVec == slice hash sequence).
    pub fn meta_const(name: &Name, levels: &Vec<Level>) -> u64 {
        let name_hash = hash_to_u64(name);
        let levels_hash = hash_to_u64(levels);
        let has_level_param = levels.iter().any(|l| l.has_params());
        let has_level_mvar = levels.iter().any(level_has_mvar);
        pack(
            mix_hash(5, mix_hash(name_hash, levels_hash)) as u32,
            0,
            0,
            false,
            false,
            has_level_mvar,
            has_level_param,
        )
    }

    /// compute_meta Lit arm (kind.rs:588-596).
    pub fn meta_lit(lit: &Literal) -> u64 {
        pack(
            mix_hash(3, hash_to_u64(lit)) as u32,
            0,
            0,
            false,
            false,
            false,
            false,
        )
    }

    /// compute_meta Proj arm (kind.rs:597-616) over an inner meta WORD.
    pub fn meta_proj(name: &Name, idx: u32, inner: u64) -> u64 {
        let inner_depth = ((inner >> 32) & 0xFF) as u32;
        let inner_hash = (inner & 0xFFFF_FFFF) as u32;
        let depth = (inner_depth + 1).min(255);
        let h = mix_hash(
            depth as u64,
            mix_hash(hash_to_u64(name), mix_hash(idx as u64, inner_hash as u64)),
        ) as u32;
        pack(
            h,
            (inner >> 44) as u32,
            depth,
            (inner >> 40) & 1 == 1,
            (inner >> 41) & 1 == 1,
            (inner >> 42) & 1 == 1,
            (inner >> 43) & 1 == 1,
        )
    }

    // ── The OLD B7 KaniHasher MODEL (rounds 1-6) — kept ONLY for the armed
    //    de-modeling control: its meta words must NOT match the production
    //    SipHash13 words (proving B7 was a real boundary, now closed). ──

    pub struct KaniHasher {
        pub state: u64,
    }
    impl Hasher for KaniHasher {
        fn finish(&self) -> u64 {
            self.state
        }
        fn write(&mut self, bytes: &[u8]) {
            for &b in bytes {
                self.state = self.state.wrapping_mul(31).wrapping_add(b as u64);
            }
        }
        fn write_u8(&mut self, i: u8) {
            self.state ^= i as u64;
            self.state = self.state.wrapping_mul(0x517cc1b727220a95);
        }
        fn write_u16(&mut self, i: u16) {
            self.state ^= i as u64;
            self.state = self.state.wrapping_mul(0x517cc1b727220a95);
        }
        fn write_u32(&mut self, i: u32) {
            self.state ^= i as u64;
            self.state = self.state.wrapping_mul(0x517cc1b727220a95);
        }
        fn write_u64(&mut self, i: u64) {
            self.state ^= i;
            self.state = self.state.wrapping_mul(0x517cc1b727220a95);
        }
        fn write_usize(&mut self, i: usize) {
            self.write_u64(i as u64);
        }
    }

    pub fn kani_hash_to_u64<T: Hash>(value: &T) -> u64 {
        let mut hasher = KaniHasher { state: 0 };
        value.hash(&mut hasher);
        hasher.finish()
    }

    pub fn kani_meta_sort(lvl: &Level) -> u64 {
        pack(
            mix_hash(11, kani_hash_to_u64(lvl)) as u32,
            0,
            0,
            false,
            false,
            level_has_mvar(lvl),
            lvl.has_params(),
        )
    }

    pub fn kani_meta_const(name: &Name, levels: &Vec<Level>) -> u64 {
        let name_hash = kani_hash_to_u64(name);
        let levels_hash = kani_hash_to_u64(levels);
        let has_level_param = levels.iter().any(|l| l.has_params());
        pack(
            mix_hash(5, mix_hash(name_hash, levels_hash)) as u32,
            0,
            0,
            false,
            false,
            false,
            has_level_param,
        )
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Root fn types
// ════════════════════════════════════════════════════════════════════════════

type SipBytesFn = extern "C" fn(*const u8, usize, *const u8, usize, *const u8, usize) -> u64;
type SipIntsFn = extern "C" fn(u64, u64, u32, u8) -> u64;
type MetaSipFn = extern "C" fn(u64, u64, u64, u64, *const u8, usize) -> u64;

/// Native oracle for the bytes root: the REAL std DefaultHasher fed the
/// identical three chunks.
fn native_sip_chunks(c1: &[u8], c2: &[u8], c3: &[u8]) -> u64 {
    let mut h = DefaultHasher::new();
    h.write(c1);
    h.write(c2);
    h.write(c3);
    h.finish()
}

/// Native oracle for the ints root: the REAL std DefaultHasher fed the
/// identical write_uN sequence (the mode dispatch mirrors the module root).
fn native_sip_ints(mode: u64, a: u64, b: u32, c: u8) -> u64 {
    let mut h = DefaultHasher::new();
    if mode == 0 {
        h.write_u64(a);
    } else if mode == 1 {
        h.write_u32(b);
    } else if mode == 2 {
        h.write_u8(c);
    } else if mode == 3 {
        h.write_u8(c);
        h.write_u64(a);
    } else if mode == 4 {
        h.write_u32(b);
        h.write_u64(a);
        h.write_u8(c);
    } else if mode == 5 {
        h.write_usize(a as usize);
    } else if mode == 6 {
        h.write_u8(c);
        h.write_u8(c ^ 0xFF);
        h.write_u8(c.wrapping_add(1));
        h.write_u32(b);
        h.write_u64(a);
    } else if mode == 7 {
        h.write_u16((b & 0xFFFF) as u16);
    } else if mode == 8 {
        h.write_u8(c);
        h.write_u16((b & 0xFFFF) as u16);
        h.write_u32(b);
        h.write_u64(a);
    } else if mode == 9 {
        h.write_u64(a);
        h.write_u8(0xFF);
    } else {
        h.write_u64(a);
        h.write_u64(a ^ mode);
    }
    h.finish()
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 1 — RAW SIP over byte strings: lengths 0..=40 (every tail/block shape)
// x 7 chunk-splits (every ntail interplay across sequential write()s: partial
// fill, exact fill, flush+blocks, flush+tail) — native (REAL DefaultHasher)
// == JIT machine code. Plus the pinned scratch-run constants, and THE ARMED
// CORRUPTION DEMO: a single-digit corruption of the v0 SipHash constant in
// the module text must make the differential fail LOUDLY; the pristine text
// (untouched by the corruption, byte-identical by construction) re-passes.
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn sip_raw_bytes_differential_and_armed_corruption() {
    let (jit_result_abc_corrupted, results) = run_with_watchdog(
        "JIT compile+run sip_bytes_root (pristine + armed-corrupt)",
        move || {
            // ── pristine module ──
            let buffer = jit_module(SIP_BYTES_MODULE, "sip_bytes_root", &bytes_externs());
            let f: SipBytesFn = unsafe { std::mem::transmute(bind(&buffer, "sip_bytes_root")) };

            let mut results: Vec<(usize, usize, usize, u64, u64)> = Vec::new();
            let stream = lcg_bytes(0x5eed, 40);
            let stream2 = lcg_bytes(0xc0ffee, 40);
            for len in 0..=40usize {
                for &(pa, pb) in &[
                    (0usize, 0usize),
                    (usize::MAX, usize::MAX), // (len, len) after clamp
                    (1, 9),
                    (7, 8),
                    (8, 23),
                    (3, 3),
                    (usize::MAX / 2, usize::MAX), // (len/2 via clamp trick below, len)
                ] {
                    for msg in [&stream[..len], &stream2[..len]] {
                        let s1 = if pa == usize::MAX / 2 {
                            len / 2
                        } else {
                            pa.min(len)
                        };
                        let s2 = if pb == usize::MAX { len } else { pb.min(len) }.max(s1);
                        let (c1, c2, c3) = (&msg[..s1], &msg[s1..s2], &msg[s2..]);
                        let native = native_sip_chunks(c1, c2, c3);
                        let jit = f(
                            c1.as_ptr(),
                            c1.len(),
                            c2.as_ptr(),
                            c2.len(),
                            c3.as_ptr(),
                            c3.len(),
                        );
                        assert_eq!(
                            jit, native,
                            "SIP BYTES DIVERGENCE len={len} split=({s1},{s2}): \
                             JIT {jit:#018x} != native DefaultHasher {native:#018x}"
                        );
                        results.push((len, s1, s2, jit, native));
                    }
                }
            }

            // Pinned scratch-run constants (guard both toolchains' std).
            let empty = f(stream.as_ptr(), 0, stream.as_ptr(), 0, stream.as_ptr(), 0);
            assert_eq!(empty, SIP_EMPTY, "JIT b\"\" != clean-side scratch pin");
            assert_eq!(
                native_sip_chunks(b"", b"", b""),
                SIP_EMPTY,
                "native b\"\" != scratch pin — harness std drifted from clean's"
            );
            let abc = b"abc";
            let jit_abc = f(abc.as_ptr(), 3, abc.as_ptr(), 0, abc.as_ptr(), 0);
            assert_eq!(jit_abc, SIP_ABC, "JIT b\"abc\" != scratch pin");
            let jit_lcg40 = f(stream.as_ptr(), 40, stream.as_ptr(), 0, stream.as_ptr(), 0);
            assert_eq!(jit_lcg40, SIP_LCG40, "JIT lcg40 != scratch pin");
            drop(buffer);

            // ── ARMED CORRUPTION: v0 init constant 0x736f6d6570736575 ==
            //    8317987319222330741 (must appear EXACTLY once), +1'd. ──
            let needle = "8317987319222330741";
            assert_eq!(
                SIP_BYTES_MODULE.matches(needle).count(),
                1,
                "armed control needs the v0 constant exactly once in the module text"
            );
            let corrupted = SIP_BYTES_MODULE.replace(needle, "8317987319222330742");
            assert_ne!(corrupted, SIP_BYTES_MODULE);
            assert_eq!(corrupted.len(), SIP_BYTES_MODULE.len());
            let cbuffer = jit_module(
                &corrupted,
                "sip_bytes_root[ARMED-CORRUPT-v0]",
                &bytes_externs(),
            );
            let cf: SipBytesFn = unsafe { std::mem::transmute(bind(&cbuffer, "sip_bytes_root")) };
            let corrupted_abc = cf(abc.as_ptr(), 3, abc.as_ptr(), 0, abc.as_ptr(), 0);
            drop(cbuffer);

            // ── RESTORE (the pristine const was never touched — byte-identical
            //    by construction) and RE-PASS. ──
            let buffer2 = jit_module(
                SIP_BYTES_MODULE,
                "sip_bytes_root[restored]",
                &bytes_externs(),
            );
            let f2: SipBytesFn = unsafe { std::mem::transmute(bind(&buffer2, "sip_bytes_root")) };
            let repass = f2(abc.as_ptr(), 3, abc.as_ptr(), 0, abc.as_ptr(), 0);
            assert_eq!(repass, SIP_ABC, "restored pristine module must re-pass");
            drop(buffer2);

            (corrupted_abc, results)
        },
    );

    // THE LOUD FAILURE the corruption causes (asserted OUTSIDE the worker so
    // a corrupted-yet-matching hash cannot hide): one bit of the v0 constant
    // must flip the hash.
    assert_ne!(
        jit_result_abc_corrupted, SIP_ABC,
        "ARMED CONTROL FAILED: the v0-corrupted module still hashed b\"abc\" \
         to the production value — the differential is vacuous"
    );
    assert!(
        results.len() >= 41 * 7,
        "sweep must have covered all lengths x splits"
    );
    println!(
        "sip_raw_bytes: {} native==JIT rows; armed v0-corruption diverged as required \
         ({jit_result_abc_corrupted:#018x} != {SIP_ABC:#018x})",
        results.len()
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 2 — RAW SIP over integer-write sequences: the DEFAULT write_uN trait
// bodies (u8/u16/u32/u64/usize + the write_str 0xFF suffix shape), landing
// 8-byte writes at every tail offset (modes 3/4/6/8 cross the buffer
// boundary at ntail = 1,2,3,4,7). Native (REAL DefaultHasher) == JIT.
// Negative control: the order-swapped sequence must NOT match (armed).
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn sip_raw_int_writes_differential() {
    let rows = run_with_watchdog("JIT compile+run sip_ints_root", move || {
        let buffer = jit_module(SIP_INTS_MODULE, "sip_ints_root", &ints_externs());
        let f: SipIntsFn = unsafe { std::mem::transmute(bind(&buffer, "sip_ints_root")) };

        let a_vals: [u64; 7] = [
            0,
            1,
            0xFF,
            0x0123_4567_89ab_cdef,
            u64::MAX,
            0x8000_0000_0000_0000,
            0xdead_beef_cafe_f00d,
        ];
        let b_vals: [u32; 5] = [0, 1, 0xFFFF, 0xdead_beef, u32::MAX];
        let c_vals: [u8; 5] = [0, 1, 7, 0x7F, 0xFF];

        let mut rows = 0usize;
        for mode in 0..=11u64 {
            for &a in &a_vals {
                for &b in &b_vals {
                    for &c in &c_vals {
                        let native = native_sip_ints(mode, a, b, c);
                        let jit = f(mode, a, b, c);
                        assert_eq!(
                            jit, native,
                            "SIP INTS DIVERGENCE mode={mode} a={a:#x} b={b:#x} c={c:#x}: \
                             JIT {jit:#018x} != native {native:#018x}"
                        );
                        rows += 1;
                    }
                }
            }
        }

        // Pinned scratch-run constant: mode 3 (u8 then u64).
        let pinned = f(3, 0x0123_4567_89ab_cdef, 0, 7);
        assert_eq!(pinned, SIP_U8_7_U64_X, "mode-3 pin != scratch-run constant");

        // ── ARMED ORDER CONTROL: swapping the two writes must change the
        //    hash, and the JIT must match the RIGHT order only. ──
        let correct = native_sip_ints(3, 0x0123_4567_89ab_cdef, 0, 7);
        let swapped = {
            let mut h = DefaultHasher::new();
            h.write_u64(0x0123_4567_89ab_cdef);
            h.write_u8(7);
            h.finish()
        };
        assert_ne!(
            correct, swapped,
            "sanity: order swap must change a SipHash digest"
        );
        assert_ne!(
            pinned, swapped,
            "ARMED CONTROL FAILED: JIT matched the ORDER-SWAPPED sequence — \
             the write path is not order-faithful"
        );
        drop(buffer);
        rows
    });
    println!("sip_raw_ints: {rows} native==JIT rows (modes 0..=11)");
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 3 — THE META DIFFERENTIAL: the four payload-hash compute_meta arms
// (Sort/Const/Lit/Proj) with hash_to_u64 running the PRODUCTION SipHash13
// in JIT machine code, against the native mirror whose payload hashing is
// the REAL std Hash machinery into a REAL DefaultHasher. Raw payload-hash
// cases (20..=26) isolate the hasher from mix_hash. ARMED de-modeling
// control: the OLD KaniHasher-model meta words must NOT match — B7 was a
// real boundary and is now closed.
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn sip_meta_arms_differential_vs_production_defaulthasher() {
    use mirror as m;
    let rows = run_with_watchdog("JIT compile+run meta_sip_root (differential)", move || {
        let buffer = jit_module(META_SIP_MODULE, "meta_sip_root", &meta_externs());
        let f: MetaSipFn = unsafe { std::mem::transmute(bind(&buffer, "meta_sip_root")) };
        let nul: *const u8 = std::ptr::null();

        let name_vals: [u64; 6] = [
            0,
            1,
            GOLD_NAME_NAT,
            GOLD_NAME_TREE_REC,
            GOLD_NAME_U,
            u64::MAX,
        ];
        let mut rows = 0usize;

        for &x in &name_vals {
            for &y in &name_vals[..3] {
                let z = x ^ y ^ 0x1234;

                // case 0: Sort(Zero)
                assert_eq!(
                    f(0, x, y, z, nul, 0),
                    m::meta_sort(&m::Level::Zero),
                    "case 0 Sort(Zero)"
                );
                // case 1: Sort(Succ(Zero))
                assert_eq!(
                    f(1, x, y, z, nul, 0),
                    m::meta_sort(&m::Level::Succ(Arc::new(m::Level::Zero))),
                    "case 1 Sort(Succ(Zero))"
                );
                // case 2: Sort(Param{x})
                assert_eq!(
                    f(2, x, y, z, nul, 0),
                    m::meta_sort(&m::Level::Param(m::Name { cached_hash: x })),
                    "case 2 Sort(Param) x={x:#x}"
                );
                // case 3: Sort(Max(Succ(Zero), Param{x}))
                assert_eq!(
                    f(3, x, y, z, nul, 0),
                    m::meta_sort(&m::Level::Max(
                        Arc::new(m::Level::Succ(Arc::new(m::Level::Zero))),
                        Arc::new(m::Level::Param(m::Name { cached_hash: x })),
                    )),
                    "case 3 Sort(Max) x={x:#x}"
                );
                // case 4: Sort(IMax(Param{x}, Param{y}))
                assert_eq!(
                    f(4, x, y, z, nul, 0),
                    m::meta_sort(&m::Level::IMax(
                        Arc::new(m::Level::Param(m::Name { cached_hash: x })),
                        Arc::new(m::Level::Param(m::Name { cached_hash: y })),
                    )),
                    "case 4 Sort(IMax) x={x:#x} y={y:#x}"
                );
                // case 5: Const({x}, [])
                assert_eq!(
                    f(5, x, y, z, nul, 0),
                    m::meta_const(&m::Name { cached_hash: x }, &vec![]),
                    "case 5 Const empty x={x:#x}"
                );
                // case 6: Const({x}, [Succ(Param{y}), Zero])
                assert_eq!(
                    f(6, x, y, z, nul, 0),
                    m::meta_const(
                        &m::Name { cached_hash: x },
                        &vec![
                            m::Level::Succ(Arc::new(m::Level::Param(m::Name { cached_hash: y }))),
                            m::Level::Zero,
                        ],
                    ),
                    "case 6 Const levels x={x:#x} y={y:#x}"
                );
                // case 7: Lit(Nat(Small(x)))
                assert_eq!(
                    f(7, x, y, z, nul, 0),
                    m::meta_lit(&m::Literal::Nat(m::BigNat::Small(x))),
                    "case 7 Lit Small x={x:#x}"
                );
                // case 10: Proj({x}, y as u32, Lit-Small(z))
                let inner = m::meta_lit(&m::Literal::Nat(m::BigNat::Small(z)));
                assert_eq!(
                    f(10, x, y, z, nul, 0),
                    m::meta_proj(&m::Name { cached_hash: x }, y as u32, inner),
                    "case 10 Proj x={x:#x} idx={y} z={z:#x}"
                );
                // case 11: Sort(Succ(Param{x}))
                assert_eq!(
                    f(11, x, y, z, nul, 0),
                    m::meta_sort(&m::Level::Succ(Arc::new(m::Level::Param(m::Name {
                        cached_hash: x
                    })))),
                    "case 11 Sort(Succ(Param)) x={x:#x}"
                );
                // cases 20..25: raw payload hashes
                assert_eq!(
                    f(20, x, y, z, nul, 0),
                    m::hash_to_u64(&m::Level::Zero),
                    "case 20 raw level Zero"
                );
                assert_eq!(
                    f(21, x, y, z, nul, 0),
                    m::hash_to_u64(&m::Level::Succ(Arc::new(m::Level::Param(m::Name {
                        cached_hash: x
                    })))),
                    "case 21 raw level Succ(Param) x={x:#x}"
                );
                assert_eq!(
                    f(22, x, y, z, nul, 0),
                    m::hash_to_u64(&m::Name { cached_hash: x }),
                    "case 22 raw name x={x:#x}"
                );
                assert_eq!(
                    f(23, x, y, z, nul, 0),
                    m::hash_to_u64::<Vec<m::Level>>(&vec![]),
                    "case 23 raw levels []"
                );
                assert_eq!(
                    f(24, x, y, z, nul, 0),
                    m::hash_to_u64(&vec![
                        m::Level::Succ(Arc::new(m::Level::Param(m::Name { cached_hash: y }))),
                        m::Level::Zero,
                    ]),
                    "case 24 raw levels [Succ(Param),Zero] y={y:#x}"
                );
                assert_eq!(
                    f(25, x, y, z, nul, 0),
                    m::hash_to_u64(&m::Literal::Nat(m::BigNat::Small(x))),
                    "case 25 raw lit Small x={x:#x}"
                );
                rows += 14;
            }
        }

        // case 8: Lit(Nat(Big(limbs))) over several limb vectors [S5 live].
        for limbs in [
            vec![0u64],
            vec![1, 2],
            vec![G6_LIMB_LO, G6_LIMB_HI],
            vec![u64::MAX, u64::MAX, u64::MAX, 7],
            vec![],
        ] {
            let jit = f(8, 0, 0, 0, limbs.as_ptr() as *const u8, limbs.len());
            let native = m::meta_lit(&m::Literal::Nat(m::BigNat::Big(limbs.clone())));
            assert_eq!(jit, native, "case 8 Lit Big {limbs:x?}");
            rows += 1;
        }

        // cases 9 + 26: Lit(String) / raw string-lit hash (write_str's 0xFF
        // suffix + the Arc<str> crossing live).
        for s in [
            "",
            "a",
            "Tree.rec",
            "abcdefgh",
            "abcdefghi",
            "The quick brown fox jumps over the lazy dog",
        ] {
            let jit = f(9, 0, 0, 0, s.as_ptr(), s.len());
            let native = m::meta_lit(&m::Literal::String(Arc::from(s)));
            assert_eq!(jit, native, "case 9 Lit String {s:?}");
            let jit_raw = f(26, 0, 0, 0, s.as_ptr(), s.len());
            let native_raw = m::hash_to_u64(&m::Literal::String(Arc::from(s)));
            assert_eq!(jit_raw, native_raw, "case 26 raw lit String {s:?}");
            rows += 2;
        }

        // ── ARMED B7 DE-MODELING CONTROL: the OLD KaniHasher model must NOT
        //    reproduce the production meta words (else B7 was never a real
        //    boundary and this thread proved nothing new). ──
        let x = GOLD_NAME_TREE_REC;
        let jit_sort_param = f(2, GOLD_NAME_U, 0, 0, nul, 0);
        let kani_sort_param = m::kani_meta_sort(&m::Level::Param(m::Name {
            cached_hash: GOLD_NAME_U,
        }));
        assert_ne!(
            jit_sort_param, kani_sort_param,
            "ARMED CONTROL FAILED: production-SipHash13 Sort(Param) meta == \
             KaniHasher-model meta — B7 was vacuous"
        );
        let jit_const = f(5, x, 0, 0, nul, 0);
        let kani_const = m::kani_meta_const(&m::Name { cached_hash: x }, &vec![]);
        assert_ne!(
            jit_const, kani_const,
            "ARMED CONTROL FAILED: production-SipHash13 Const meta == \
             KaniHasher-model meta — B7 was vacuous"
        );

        // ── Input-sensitivity control: one bit in the name hash flips the
        //    meta word. ──
        assert_ne!(
            f(2, x, 0, 0, nul, 0),
            f(2, x ^ 1, 0, 0, nul, 0),
            "ARMED CONTROL FAILED: meta word insensitive to the Param name hash"
        );

        drop(buffer);
        rows
    });
    println!("sip_meta_arms: {rows} native==JIT meta/payload rows");
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 4 — CLEAN-KERNEL META GOLDENS: 8 meta words pinned from the REAL
// clean-kernel binary (DefaultHasher LIVE in its compute_meta), reproduced
// BIT-IDENTICALLY by the JIT machine code; the native mirror must agree with
// the binary too (mirror self-check). Armed: +1-corrupted and crossed
// goldens must reject.
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn sip_meta_clean_kernel_goldens() {
    use mirror as m;
    run_with_watchdog("JIT compile+run meta_sip_root (goldens)", move || {
        let buffer = jit_module(META_SIP_MODULE, "meta_sip_root", &meta_externs());
        let f: MetaSipFn = unsafe { std::mem::transmute(bind(&buffer, "meta_sip_root")) };
        let nul: *const u8 = std::ptr::null();

        // G1 sort(zero)
        assert_eq!(f(0, 0, 0, 0, nul, 0), G1_SORT_ZERO, "G1 sort(zero)");
        // G2 sort(succ(param u))
        assert_eq!(
            f(11, GOLD_NAME_U, 0, 0, nul, 0),
            G2_SORT_SUCC_PARAM_U,
            "G2 sort(succ(param u))"
        );
        // G3 const(Nat, [])
        assert_eq!(
            f(5, GOLD_NAME_NAT, 0, 0, nul, 0),
            G3_CONST_NAT_EMPTY,
            "G3 const(Nat,[])"
        );
        // G4 const(Tree.rec, [succ(param u), zero])
        assert_eq!(
            f(6, GOLD_NAME_TREE_REC, GOLD_NAME_U, 0, nul, 0),
            G4_CONST_TREEREC,
            "G4 const(Tree.rec,[succ u, 0])"
        );
        // G5 lit(42)
        assert_eq!(f(7, 42, 0, 0, nul, 0), G5_LIT_42, "G5 lit(42)");
        // G6 lit(Big[lo,hi])
        let limbs = [G6_LIMB_LO, G6_LIMB_HI];
        assert_eq!(
            f(8, 0, 0, 0, limbs.as_ptr() as *const u8, limbs.len()),
            G6_LIT_BIG,
            "G6 lit(Big[lo,hi])"
        );
        // G7 lit(str "Tree.rec")
        let s = "Tree.rec";
        assert_eq!(
            f(9, 0, 0, 0, s.as_ptr(), s.len()),
            G7_LIT_STR_TREEREC,
            "G7 lit(str Tree.rec)"
        );
        // G8 proj(Prod, 1, lit(7))
        assert_eq!(
            f(10, GOLD_NAME_PROD, 1, 7, nul, 0),
            G8_PROJ_PROD_1_LIT7,
            "G8 proj(Prod,1,lit(7))"
        );

        // ── Mirror self-check: the native mirror reproduces the binary's
        //    words (validates the mirror INDEPENDENTLY of the JIT). ──
        assert_eq!(m::meta_sort(&m::Level::Zero), G1_SORT_ZERO, "mirror G1");
        assert_eq!(
            m::meta_const(
                &m::Name {
                    cached_hash: GOLD_NAME_NAT
                },
                &vec![]
            ),
            G3_CONST_NAT_EMPTY,
            "mirror G3"
        );
        assert_eq!(
            m::meta_lit(&m::Literal::Nat(m::BigNat::Small(42))),
            G5_LIT_42,
            "mirror G5"
        );
        assert_eq!(
            m::meta_proj(
                &m::Name {
                    cached_hash: GOLD_NAME_PROD
                },
                1,
                m::meta_lit(&m::Literal::Nat(m::BigNat::Small(7))),
            ),
            G8_PROJ_PROD_1_LIT7,
            "mirror G8"
        );

        // ── ARMED CONTROLS ──
        // (a) +1-corrupted golden must reject.
        assert_ne!(
            f(0, 0, 0, 0, nul, 0),
            G1_SORT_ZERO.wrapping_add(1),
            "ARMED CONTROL FAILED: corrupted golden (G1+1) matched"
        );
        // (b) crossed goldens must reject (G3's word for the G5 shape).
        assert_ne!(
            f(7, 42, 0, 0, nul, 0),
            G3_CONST_NAT_EMPTY,
            "ARMED CONTROL FAILED: crossed golden (G3 for lit(42)) matched"
        );
        // (c) crossed NAME must reject (name v where the golden used u).
        assert_ne!(
            f(11, GOLD_NAME_V, 0, 0, nul, 0),
            G2_SORT_SUCC_PARAM_U,
            "ARMED CONTROL FAILED: sort(succ(param v)) matched the param-u golden"
        );

        drop(buffer);
    });
    println!(
        "sip_meta_goldens: 8/8 clean-kernel meta goldens bit-identical (JIT), mirror self-check green, 3 armed controls rejected"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// EMBEDDED MODULES (verbatim MIR-driver emits; see file header for regen).
// ════════════════════════════════════════════════════════════════════════════

const SIP_BYTES_MODULE: &str = r##"; TrustIr text format v1
module "mir::closure::sip_bytes_root"
target "aarch64-apple-darwin" 8 little
file 0 "clean_siphash_slice.rs"

functy.0 = (ptr, ptr, u64) -> ()

functy.1 = (ptr, u64, ptr, u64, ptr, u64) -> (u64)

functy.2 = (ptr) -> ()

functy.3 = (ptr, ptr) -> ()

functy.4 = (ptr) -> (u64)

functy.5 = (ptr, u64, u64) -> (u64)

functy.6 = (ptr) -> ()

functy.7 = (ptr, u64) -> (u64)

functy.8 = (ptr) -> ()

functy.9 = (ptr, u64) -> (u32)

functy.10 = (ptr, u64) -> (u16)

functy.11 = (ptr) -> ()

functy.12 = (u64, u64) -> (u64)

functy.13 = (u64, u32) -> (u64)

fn @_RINvNtNtCs2EYQwhfuABO_4core5slice3raw14from_raw_partshECs6Skw9Chgdp8_19clean_siphash_slice(functy.0) {
}

fn @sip_bytes_root(functy.1) {
bb0(%0: ptr, %1: u64, %2: ptr, %3: u64, %4: ptr, %5: u64):
    %13 = alloca (i64, i64), align 8
    %14 = alloca (i64, i64), align 8
    %15 = alloca (i64, i64), align 8
    %16 = alloca (i64, i64, i64, i64, i64, i64, i64, i64, i64), align 8
    call @func.0(%13, %0, %1)
    br bb1(%2, %3, %4, %5)
bb1(%6: ptr, %7: u64, %8: ptr, %9: u64):
    call @func.0(%14, %6, %7)
    br bb2(%8, %9)
bb2(%10: ptr, %11: u64):
    call @func.0(%15, %10, %11)
    br bb3
bb3:
    call @func.2(%16)
    br bb4
bb4:
    call @func.3(%16, %13)
    br bb5
bb5:
    call @func.3(%16, %14)
    br bb6
bb6:
    call @func.3(%16, %15)
    br bb7
bb7:
    %17 = call @func.4(%16)
    br bb8(%17)
bb8(%12: u64):
    ret %12
}

fn @SipHasher13__new(functy.2) {
bb0(%0: ptr):
    %1 = alloca (i64, i64, i64, i64), align 8
    %2 = const u64 0
    %3 = const u64 0
    %4 = const u64 8317987319222330741
    %5 = xor u64 %2, %4
    %6 = const u64 7816392313619706465
    %7 = xor u64 %2, %6
    %8 = const u64 7237128888997146477
    %9 = xor u64 %3, %8
    %10 = const u64 8387220255154660723
    %11 = xor u64 %3, %10
    store u64 %5, ptr %1
    %12 = const i64 8
    %13 = gep i8, ptr %1, %12
    store u64 %7, ptr %13
    %14 = const i64 16
    %15 = gep i8, ptr %1, %14
    store u64 %9, ptr %15
    %16 = const i64 24
    %17 = gep i8, ptr %1, %16
    store u64 %11, ptr %17
    %18 = const i64 32
    %19 = gep i8, ptr %0, %18
    store u64 %2, ptr %19
    %20 = const i64 40
    %21 = gep i8, ptr %0, %20
    store u64 %3, ptr %21
    %22 = const u64 0
    %23 = const i64 48
    %24 = gep i8, ptr %0, %23
    store u64 %22, ptr %24
    %25 = load i64, ptr %1
    store i64 %25, ptr %0
    %26 = const i64 8
    %27 = gep i8, ptr %1, %26
    %28 = const i64 8
    %29 = gep i8, ptr %0, %28
    %30 = load i64, ptr %27
    store i64 %30, ptr %29
    %31 = const i64 16
    %32 = gep i8, ptr %1, %31
    %33 = const i64 16
    %34 = gep i8, ptr %0, %33
    %35 = load i64, ptr %32
    store i64 %35, ptr %34
    %36 = const i64 24
    %37 = gep i8, ptr %1, %36
    %38 = const i64 24
    %39 = gep i8, ptr %0, %38
    %40 = load i64, ptr %37
    store i64 %40, ptr %39
    %41 = const u64 0
    %42 = const i64 56
    %43 = gep i8, ptr %0, %42
    store u64 %41, ptr %43
    %44 = const u64 0
    %45 = const i64 64
    %46 = gep i8, ptr %0, %45
    store u64 %44, ptr %46
    ret
}

fn @SipHasher13__write(functy.3) {
bb0(%0: ptr, %1: ptr):
    %54 = alloca i64, align 8
    %55 = alloca (i64, i64), align 8
    %56 = alloca (i64, i64), align 8
    %57 = alloca (i64, i64), align 8
    %58 = alloca (i64, i64), align 8
    %59 = alloca (i64, i64), align 8
    %60 = alloca (i64, i64), align 8
    %61 = alloca (i64, i64), align 8
    store ptr %0, ptr %54
    %62 = const i64 8
    %63 = gep i8, ptr %1, %62
    %64 = load u64, ptr %63
    %65 = load ptr, ptr %54
    %66 = const i64 48
    %67 = gep i8, ptr %65, %66
    %68 = load u64, ptr %67
    %69, %70 = add.overflow u64 %68, %64
    store u64 %69, ptr %55
    %71 = const i64 8
    %72 = gep i8, ptr %55, %71
    store bool %70, ptr %72
    %73 = const i64 8
    %74 = gep i8, ptr %55, %73
    %75 = load bool, ptr %74
    %76 = const bool false
    %77 = icmp eq bool %75, %76
    condbr %77, bb1(%64), bb25
bb1(%2: u64):
    %78 = load u64, ptr %55
    %79 = load ptr, ptr %54
    %80 = const i64 48
    %81 = gep i8, ptr %79, %80
    store u64 %78, ptr %81
    %82 = const u64 0
    %83 = load ptr, ptr %54
    %84 = const i64 64
    %85 = gep i8, ptr %83, %84
    %86 = load u64, ptr %85
    %87 = const u64 0
    %88 = icmp ne u64 %86, %87
    condbr %88, bb2(%2), bb14(%2, %82)
bb2(%3: u64):
    %89 = load ptr, ptr %54
    %90 = const i64 64
    %91 = gep i8, ptr %89, %90
    %92 = load u64, ptr %91
    %93 = const u64 8
    %94, %95 = sub.overflow u64 %93, %92
    store u64 %94, ptr %56
    %96 = const i64 8
    %97 = gep i8, ptr %56, %96
    store bool %95, ptr %97
    %98 = const i64 8
    %99 = gep i8, ptr %56, %98
    %100 = load bool, ptr %99
    %101 = const bool false
    %102 = icmp eq bool %100, %101
    condbr %102, bb3(%3), bb25
bb3(%4: u64):
    %103 = load u64, ptr %56
    %104 = icmp ult u64 %4, %103
    condbr %104, bb4(%4, %103), bb5(%4, %103)
bb4(%5: u64, %6: u64):
    br bb6(%5, %6, %5)
bb5(%7: u64, %8: u64):
    br bb6(%7, %8, %8)
bb6(%9: u64, %10: u64, %11: u64):
    %105 = const u64 0
    %106 = call @func.5(%1, %105, %11)
    br bb7(%9, %10, %106)
bb7(%12: u64, %13: u64, %14: u64):
    %107 = load ptr, ptr %54
    %108 = const i64 64
    %109 = gep i8, ptr %107, %108
    %110 = load u64, ptr %109
    %111 = const u64 8
    %112, %113 = mul.overflow u64 %111, %110
    store u64 %112, ptr %57
    %114 = const i64 8
    %115 = gep i8, ptr %57, %114
    store bool %113, ptr %115
    %116 = const i64 8
    %117 = gep i8, ptr %57, %116
    %118 = load bool, ptr %117
    %119 = const bool false
    %120 = icmp eq bool %118, %119
    condbr %120, bb8(%12, %13, %14), bb25
bb8(%15: u64, %16: u64, %17: u64):
    %121 = load u64, ptr %57
    %122 = trunc u64 %121 to u32
    %123 = const u32 64
    %124 = icmp ult u32 %122, %123
    condbr %124, bb9(%15, %16, %17, %122), bb25
bb9(%18: u64, %19: u64, %20: u64, %21: u32):
    %125 = zext u32 %21 to u64
    %126 = shl u64 %20, %125
    %127 = load ptr, ptr %54
    %128 = const i64 56
    %129 = gep i8, ptr %127, %128
    %130 = load u64, ptr %129
    %131 = or u64 %130, %126
    %132 = load ptr, ptr %54
    %133 = const i64 56
    %134 = gep i8, ptr %132, %133
    store u64 %131, ptr %134
    %135 = icmp ult u64 %18, %19
    condbr %135, bb10(%18), bb12(%18, %19)
bb10(%22: u64):
    %136 = load ptr, ptr %54
    %137 = const i64 64
    %138 = gep i8, ptr %136, %137
    %139 = load u64, ptr %138
    %140, %141 = add.overflow u64 %139, %22
    store u64 %140, ptr %58
    %142 = const i64 8
    %143 = gep i8, ptr %58, %142
    store bool %141, ptr %143
    %144 = const i64 8
    %145 = gep i8, ptr %58, %144
    %146 = load bool, ptr %145
    %147 = const bool false
    %148 = icmp eq bool %146, %147
    condbr %148, bb11, bb25
bb11:
    %149 = load u64, ptr %58
    %150 = load ptr, ptr %54
    %151 = const i64 64
    %152 = gep i8, ptr %150, %151
    store u64 %149, ptr %152
    br bb24
bb12(%23: u64, %24: u64):
    %153 = load ptr, ptr %54
    %154 = const i64 56
    %155 = gep i8, ptr %153, %154
    %156 = load u64, ptr %155
    %157 = load ptr, ptr %54
    %158 = const i64 24
    %159 = gep i8, ptr %157, %158
    %160 = load u64, ptr %159
    %161 = xor u64 %160, %156
    %162 = load ptr, ptr %54
    %163 = const i64 24
    %164 = gep i8, ptr %162, %163
    store u64 %161, ptr %164
    %165 = load ptr, ptr %54
    call @func.6(%165)
    br bb13(%23, %24)
bb13(%25: u64, %26: u64):
    %166 = load ptr, ptr %54
    %167 = const i64 56
    %168 = gep i8, ptr %166, %167
    %169 = load u64, ptr %168
    %170 = load ptr, ptr %54
    %171 = load u64, ptr %170
    %172 = xor u64 %171, %169
    %173 = load ptr, ptr %54
    store u64 %172, ptr %173
    %174 = const u64 0
    %175 = load ptr, ptr %54
    %176 = const i64 64
    %177 = gep i8, ptr %175, %176
    store u64 %174, ptr %177
    br bb14(%25, %26)
bb14(%27: u64, %28: u64):
    %178, %179 = sub.overflow u64 %27, %28
    store u64 %178, ptr %59
    %180 = const i64 8
    %181 = gep i8, ptr %59, %180
    store bool %179, ptr %181
    %182 = const i64 8
    %183 = gep i8, ptr %59, %182
    %184 = load bool, ptr %183
    %185 = const bool false
    %186 = icmp eq bool %184, %185
    condbr %186, bb15(%28), bb25
bb15(%29: u64):
    %187 = load u64, ptr %59
    %188 = const u64 7
    %189 = and u64 %187, %188
    br bb16(%187, %189, %29)
bb16(%30: u64, %31: u64, %32: u64):
    %190, %191 = sub.overflow u64 %30, %31
    store u64 %190, ptr %60
    %192 = const i64 8
    %193 = gep i8, ptr %60, %192
    store bool %191, ptr %193
    %194 = const i64 8
    %195 = gep i8, ptr %60, %194
    %196 = load bool, ptr %195
    %197 = const bool false
    %198 = icmp eq bool %196, %197
    condbr %198, bb17(%30, %31, %32, %32), bb25
bb17(%33: u64, %34: u64, %35: u64, %36: u64):
    %199 = load u64, ptr %60
    %200 = icmp ult u64 %36, %199
    condbr %200, bb18(%33, %34, %35), bb22(%34, %35)
bb18(%37: u64, %38: u64, %39: u64):
    %201 = call @func.7(%1, %39)
    br bb19(%37, %38, %39, %201)
bb19(%40: u64, %41: u64, %42: u64, %43: u64):
    %202 = load ptr, ptr %54
    %203 = const i64 24
    %204 = gep i8, ptr %202, %203
    %205 = load u64, ptr %204
    %206 = xor u64 %205, %43
    %207 = load ptr, ptr %54
    %208 = const i64 24
    %209 = gep i8, ptr %207, %208
    store u64 %206, ptr %209
    %210 = load ptr, ptr %54
    call @func.6(%210)
    br bb20(%40, %41, %42, %43)
bb20(%44: u64, %45: u64, %46: u64, %47: u64):
    %211 = load ptr, ptr %54
    %212 = load u64, ptr %211
    %213 = xor u64 %212, %47
    %214 = load ptr, ptr %54
    store u64 %213, ptr %214
    %215 = const u64 8
    %216, %217 = add.overflow u64 %46, %215
    store u64 %216, ptr %61
    %218 = const i64 8
    %219 = gep i8, ptr %61, %218
    store bool %217, ptr %219
    %220 = const i64 8
    %221 = gep i8, ptr %61, %220
    %222 = load bool, ptr %221
    %223 = const bool false
    %224 = icmp eq bool %222, %223
    condbr %224, bb21(%44, %45), bb25
bb21(%48: u64, %49: u64):
    %225 = load u64, ptr %61
    br bb16(%48, %49, %225)
bb22(%50: u64, %51: u64):
    %226 = call @func.5(%1, %51, %50)
    br bb23(%50, %226)
bb23(%52: u64, %53: u64):
    %227 = load ptr, ptr %54
    %228 = const i64 56
    %229 = gep i8, ptr %227, %228
    store u64 %53, ptr %229
    %230 = load ptr, ptr %54
    %231 = const i64 64
    %232 = gep i8, ptr %230, %231
    store u64 %52, ptr %232
    br bb24
bb24:
    ret
bb25:
    unreachable
}

fn @SipHasher13__finish(functy.4) {
bb0(%0: ptr):
    %4 = alloca (i64, i64, i64, i64), align 8
    %5 = load i64, ptr %0
    store i64 %5, ptr %4
    %6 = const i64 8
    %7 = gep i8, ptr %0, %6
    %8 = const i64 8
    %9 = gep i8, ptr %4, %8
    %10 = load i64, ptr %7
    store i64 %10, ptr %9
    %11 = const i64 16
    %12 = gep i8, ptr %0, %11
    %13 = const i64 16
    %14 = gep i8, ptr %4, %13
    %15 = load i64, ptr %12
    store i64 %15, ptr %14
    %16 = const i64 24
    %17 = gep i8, ptr %0, %16
    %18 = const i64 24
    %19 = gep i8, ptr %4, %18
    %20 = load i64, ptr %17
    store i64 %20, ptr %19
    %21 = const i64 48
    %22 = gep i8, ptr %0, %21
    %23 = load u64, ptr %22
    %24 = const u64 255
    %25 = and u64 %23, %24
    %26 = const i32 56
    %27 = bitcast i32 %26 to u32
    %28 = const u32 64
    %29 = icmp ult u32 %27, %28
    condbr %29, bb1(%0, %25), bb4
bb1(%1: ptr, %2: u64):
    %30 = const i32 56
    %31 = zext i32 %30 to u64
    %32 = shl u64 %2, %31
    %33 = const i64 56
    %34 = gep i8, ptr %1, %33
    %35 = load u64, ptr %34
    %36 = or u64 %32, %35
    %37 = const i64 24
    %38 = gep i8, ptr %4, %37
    %39 = load u64, ptr %38
    %40 = xor u64 %39, %36
    %41 = const i64 24
    %42 = gep i8, ptr %4, %41
    store u64 %40, ptr %42
    call @func.6(%4)
    br bb2(%36)
bb2(%3: u64):
    %43 = load u64, ptr %4
    %44 = xor u64 %43, %3
    store u64 %44, ptr %4
    %45 = const i64 8
    %46 = gep i8, ptr %4, %45
    %47 = load u64, ptr %46
    %48 = const u64 255
    %49 = xor u64 %47, %48
    %50 = const i64 8
    %51 = gep i8, ptr %4, %50
    store u64 %49, ptr %51
    call @func.8(%4)
    br bb3
bb3:
    %52 = load u64, ptr %4
    %53 = const i64 16
    %54 = gep i8, ptr %4, %53
    %55 = load u64, ptr %54
    %56 = xor u64 %52, %55
    %57 = const i64 8
    %58 = gep i8, ptr %4, %57
    %59 = load u64, ptr %58
    %60 = xor u64 %56, %59
    %61 = const i64 24
    %62 = gep i8, ptr %4, %61
    %63 = load u64, ptr %62
    %64 = xor u64 %60, %63
    ret %64
bb4:
    unreachable
}

fn @u8to64_le(functy.5) {
bb0(%0: ptr, %1: u64, %2: u64):
    %76 = alloca (i64, i64), align 8
    %77 = alloca (i64, i64), align 8
    %78 = alloca (i64, i64), align 8
    %79 = alloca (i64, i64), align 8
    %80 = alloca (i64, i64), align 8
    %81 = alloca (i64, i64), align 8
    %82 = alloca (i64, i64), align 8
    %83 = alloca (i64, i64), align 8
    %84 = alloca (i64, i64), align 8
    %85 = alloca (i64, i64), align 8
    %86 = const u64 0
    %87 = const u64 0
    %88 = const u64 3
    %89, %90 = add.overflow u64 %86, %88
    store u64 %89, ptr %76
    %91 = const i64 8
    %92 = gep i8, ptr %76, %91
    store bool %90, ptr %92
    %93 = const i64 8
    %94 = gep i8, ptr %76, %93
    %95 = load bool, ptr %94
    %96 = const bool false
    %97 = icmp eq bool %95, %96
    condbr %97, bb1(%1, %2, %86, %87), bb22
bb1(%3: u64, %4: u64, %5: u64, %6: u64):
    %98 = load u64, ptr %76
    %99 = icmp ult u64 %98, %4
    condbr %99, bb2(%3, %4, %5), bb6(%3, %4, %5, %6)
bb2(%7: u64, %8: u64, %9: u64):
    %100, %101 = add.overflow u64 %7, %9
    store u64 %100, ptr %77
    %102 = const i64 8
    %103 = gep i8, ptr %77, %102
    store bool %101, ptr %103
    %104 = const i64 8
    %105 = gep i8, ptr %77, %104
    %106 = load bool, ptr %105
    %107 = const bool false
    %108 = icmp eq bool %106, %107
    condbr %108, bb3(%7, %8, %9), bb22
bb3(%10: u64, %11: u64, %12: u64):
    %109 = load u64, ptr %77
    %110 = call @func.9(%0, %109)
    br bb4(%10, %11, %12, %110)
bb4(%13: u64, %14: u64, %15: u64, %16: u32):
    %111 = zext u32 %16 to u64
    %112 = const u64 4
    %113, %114 = add.overflow u64 %15, %112
    store u64 %113, ptr %78
    %115 = const i64 8
    %116 = gep i8, ptr %78, %115
    store bool %114, ptr %116
    %117 = const i64 8
    %118 = gep i8, ptr %78, %117
    %119 = load bool, ptr %118
    %120 = const bool false
    %121 = icmp eq bool %119, %120
    condbr %121, bb5(%13, %14, %111), bb22
bb5(%17: u64, %18: u64, %19: u64):
    %122 = load u64, ptr %78
    br bb6(%17, %18, %122, %19)
bb6(%20: u64, %21: u64, %22: u64, %23: u64):
    %123 = const u64 1
    %124, %125 = add.overflow u64 %22, %123
    store u64 %124, ptr %79
    %126 = const i64 8
    %127 = gep i8, ptr %79, %126
    store bool %125, ptr %127
    %128 = const i64 8
    %129 = gep i8, ptr %79, %128
    %130 = load bool, ptr %129
    %131 = const bool false
    %132 = icmp eq bool %130, %131
    condbr %132, bb7(%20, %21, %22, %23), bb22
bb7(%24: u64, %25: u64, %26: u64, %27: u64):
    %133 = load u64, ptr %79
    %134 = icmp ult u64 %133, %25
    condbr %134, bb8(%24, %25, %26, %27), bb14(%24, %25, %26, %27)
bb8(%28: u64, %29: u64, %30: u64, %31: u64):
    %135, %136 = add.overflow u64 %28, %30
    store u64 %135, ptr %80
    %137 = const i64 8
    %138 = gep i8, ptr %80, %137
    store bool %136, ptr %138
    %139 = const i64 8
    %140 = gep i8, ptr %80, %139
    %141 = load bool, ptr %140
    %142 = const bool false
    %143 = icmp eq bool %141, %142
    condbr %143, bb9(%28, %29, %30, %31), bb22
bb9(%32: u64, %33: u64, %34: u64, %35: u64):
    %144 = load u64, ptr %80
    %145 = call @func.10(%0, %144)
    br bb10(%32, %33, %34, %35, %145)
bb10(%36: u64, %37: u64, %38: u64, %39: u64, %40: u16):
    %146 = zext u16 %40 to u64
    %147 = const u64 8
    %148, %149 = mul.overflow u64 %38, %147
    store u64 %148, ptr %81
    %150 = const i64 8
    %151 = gep i8, ptr %81, %150
    store bool %149, ptr %151
    %152 = const i64 8
    %153 = gep i8, ptr %81, %152
    %154 = load bool, ptr %153
    %155 = const bool false
    %156 = icmp eq bool %154, %155
    condbr %156, bb11(%36, %37, %38, %39, %146), bb22
bb11(%41: u64, %42: u64, %43: u64, %44: u64, %45: u64):
    %157 = load u64, ptr %81
    %158 = trunc u64 %157 to u32
    %159 = const u32 64
    %160 = icmp ult u32 %158, %159
    condbr %160, bb12(%41, %42, %43, %44, %45, %158), bb22
bb12(%46: u64, %47: u64, %48: u64, %49: u64, %50: u64, %51: u32):
    %161 = zext u32 %51 to u64
    %162 = shl u64 %50, %161
    %163 = or u64 %49, %162
    %164 = const u64 2
    %165, %166 = add.overflow u64 %48, %164
    store u64 %165, ptr %82
    %167 = const i64 8
    %168 = gep i8, ptr %82, %167
    store bool %166, ptr %168
    %169 = const i64 8
    %170 = gep i8, ptr %82, %169
    %171 = load bool, ptr %170
    %172 = const bool false
    %173 = icmp eq bool %171, %172
    condbr %173, bb13(%46, %47, %163), bb22
bb13(%52: u64, %53: u64, %54: u64):
    %174 = load u64, ptr %82
    br bb14(%52, %53, %174, %54)
bb14(%55: u64, %56: u64, %57: u64, %58: u64):
    %175 = icmp ult u64 %57, %56
    condbr %175, bb15(%55, %57, %58), bb21(%58)
bb15(%59: u64, %60: u64, %61: u64):
    %176, %177 = add.overflow u64 %59, %60
    store u64 %176, ptr %83
    %178 = const i64 8
    %179 = gep i8, ptr %83, %178
    store bool %177, ptr %179
    %180 = const i64 8
    %181 = gep i8, ptr %83, %180
    %182 = load bool, ptr %181
    %183 = const bool false
    %184 = icmp eq bool %182, %183
    condbr %184, bb16(%60, %61), bb22
bb16(%62: u64, %63: u64):
    %185 = load u64, ptr %83
    %186 = const i64 8
    %187 = gep i8, ptr %0, %186
    %188 = load u64, ptr %187
    %189 = icmp ult u64 %185, %188
    condbr %189, bb17(%62, %63, %185), bb22
bb17(%64: u64, %65: u64, %66: u64):
    %190 = load ptr, ptr %0
    %191 = gep u8, ptr %190, %66
    %192 = load u8, ptr %191
    %193 = zext u8 %192 to u64
    %194 = const u64 8
    %195, %196 = mul.overflow u64 %64, %194
    store u64 %195, ptr %84
    %197 = const i64 8
    %198 = gep i8, ptr %84, %197
    store bool %196, ptr %198
    %199 = const i64 8
    %200 = gep i8, ptr %84, %199
    %201 = load bool, ptr %200
    %202 = const bool false
    %203 = icmp eq bool %201, %202
    condbr %203, bb18(%64, %65, %193), bb22
bb18(%67: u64, %68: u64, %69: u64):
    %204 = load u64, ptr %84
    %205 = trunc u64 %204 to u32
    %206 = const u32 64
    %207 = icmp ult u32 %205, %206
    condbr %207, bb19(%67, %68, %69, %205), bb22
bb19(%70: u64, %71: u64, %72: u64, %73: u32):
    %208 = zext u32 %73 to u64
    %209 = shl u64 %72, %208
    %210 = or u64 %71, %209
    %211 = const u64 1
    %212, %213 = add.overflow u64 %70, %211
    store u64 %212, ptr %85
    %214 = const i64 8
    %215 = gep i8, ptr %85, %214
    store bool %213, ptr %215
    %216 = const i64 8
    %217 = gep i8, ptr %85, %216
    %218 = load bool, ptr %217
    %219 = const bool false
    %220 = icmp eq bool %218, %219
    condbr %220, bb20(%210), bb22
bb20(%74: u64):
    %221 = load u64, ptr %85
    br bb21(%74)
bb21(%75: u64):
    ret %75
bb22:
    unreachable
}

fn @sip13_c_rounds(functy.6) {
bb0(%0: ptr):
    call @func.11(%0)
    br bb1
bb1:
    ret
}

fn @load_u64_le(functy.7) {
bb0(%0: ptr, %1: u64):
    %56 = alloca (i64, i64), align 8
    %57 = alloca (i64, i64), align 8
    %58 = alloca (i64, i64), align 8
    %59 = alloca (i64, i64), align 8
    %60 = alloca (i64, i64), align 8
    %61 = alloca (i64, i64), align 8
    %62 = alloca (i64, i64), align 8
    %63 = const i64 8
    %64 = gep i8, ptr %0, %63
    %65 = load u64, ptr %64
    %66 = icmp ult u64 %1, %65
    condbr %66, bb1(%1), bb23
bb1(%2: u64):
    %67 = load ptr, ptr %0
    %68 = gep u8, ptr %67, %2
    %69 = load u8, ptr %68
    %70 = zext u8 %69 to u64
    %71 = const u64 1
    %72, %73 = add.overflow u64 %2, %71
    store u64 %72, ptr %56
    %74 = const i64 8
    %75 = gep i8, ptr %56, %74
    store bool %73, ptr %75
    %76 = const i64 8
    %77 = gep i8, ptr %56, %76
    %78 = load bool, ptr %77
    %79 = const bool false
    %80 = icmp eq bool %78, %79
    condbr %80, bb2(%2, %70), bb23
bb2(%3: u64, %4: u64):
    %81 = load u64, ptr %56
    %82 = const i64 8
    %83 = gep i8, ptr %0, %82
    %84 = load u64, ptr %83
    %85 = icmp ult u64 %81, %84
    condbr %85, bb3(%3, %4, %81), bb23
bb3(%5: u64, %6: u64, %7: u64):
    %86 = load ptr, ptr %0
    %87 = gep u8, ptr %86, %7
    %88 = load u8, ptr %87
    %89 = zext u8 %88 to u64
    %90 = const u32 8
    %91 = const u32 64
    %92 = icmp ult u32 %90, %91
    condbr %92, bb4(%5, %6, %89), bb23
bb4(%8: u64, %9: u64, %10: u64):
    %93 = const u32 8
    %94 = zext u32 %93 to u64
    %95 = shl u64 %10, %94
    %96 = or u64 %9, %95
    %97 = const u64 2
    %98, %99 = add.overflow u64 %8, %97
    store u64 %98, ptr %57
    %100 = const i64 8
    %101 = gep i8, ptr %57, %100
    store bool %99, ptr %101
    %102 = const i64 8
    %103 = gep i8, ptr %57, %102
    %104 = load bool, ptr %103
    %105 = const bool false
    %106 = icmp eq bool %104, %105
    condbr %106, bb5(%8, %96), bb23
bb5(%11: u64, %12: u64):
    %107 = load u64, ptr %57
    %108 = const i64 8
    %109 = gep i8, ptr %0, %108
    %110 = load u64, ptr %109
    %111 = icmp ult u64 %107, %110
    condbr %111, bb6(%11, %12, %107), bb23
bb6(%13: u64, %14: u64, %15: u64):
    %112 = load ptr, ptr %0
    %113 = gep u8, ptr %112, %15
    %114 = load u8, ptr %113
    %115 = zext u8 %114 to u64
    %116 = const u32 16
    %117 = const u32 64
    %118 = icmp ult u32 %116, %117
    condbr %118, bb7(%13, %14, %115), bb23
bb7(%16: u64, %17: u64, %18: u64):
    %119 = const u32 16
    %120 = zext u32 %119 to u64
    %121 = shl u64 %18, %120
    %122 = or u64 %17, %121
    %123 = const u64 3
    %124, %125 = add.overflow u64 %16, %123
    store u64 %124, ptr %58
    %126 = const i64 8
    %127 = gep i8, ptr %58, %126
    store bool %125, ptr %127
    %128 = const i64 8
    %129 = gep i8, ptr %58, %128
    %130 = load bool, ptr %129
    %131 = const bool false
    %132 = icmp eq bool %130, %131
    condbr %132, bb8(%16, %122), bb23
bb8(%19: u64, %20: u64):
    %133 = load u64, ptr %58
    %134 = const i64 8
    %135 = gep i8, ptr %0, %134
    %136 = load u64, ptr %135
    %137 = icmp ult u64 %133, %136
    condbr %137, bb9(%19, %20, %133), bb23
bb9(%21: u64, %22: u64, %23: u64):
    %138 = load ptr, ptr %0
    %139 = gep u8, ptr %138, %23
    %140 = load u8, ptr %139
    %141 = zext u8 %140 to u64
    %142 = const u32 24
    %143 = const u32 64
    %144 = icmp ult u32 %142, %143
    condbr %144, bb10(%21, %22, %141), bb23
bb10(%24: u64, %25: u64, %26: u64):
    %145 = const u32 24
    %146 = zext u32 %145 to u64
    %147 = shl u64 %26, %146
    %148 = or u64 %25, %147
    %149 = const u64 4
    %150, %151 = add.overflow u64 %24, %149
    store u64 %150, ptr %59
    %152 = const i64 8
    %153 = gep i8, ptr %59, %152
    store bool %151, ptr %153
    %154 = const i64 8
    %155 = gep i8, ptr %59, %154
    %156 = load bool, ptr %155
    %157 = const bool false
    %158 = icmp eq bool %156, %157
    condbr %158, bb11(%24, %148), bb23
bb11(%27: u64, %28: u64):
    %159 = load u64, ptr %59
    %160 = const i64 8
    %161 = gep i8, ptr %0, %160
    %162 = load u64, ptr %161
    %163 = icmp ult u64 %159, %162
    condbr %163, bb12(%27, %28, %159), bb23
bb12(%29: u64, %30: u64, %31: u64):
    %164 = load ptr, ptr %0
    %165 = gep u8, ptr %164, %31
    %166 = load u8, ptr %165
    %167 = zext u8 %166 to u64
    %168 = const u32 32
    %169 = const u32 64
    %170 = icmp ult u32 %168, %169
    condbr %170, bb13(%29, %30, %167), bb23
bb13(%32: u64, %33: u64, %34: u64):
    %171 = const u32 32
    %172 = zext u32 %171 to u64
    %173 = shl u64 %34, %172
    %174 = or u64 %33, %173
    %175 = const u64 5
    %176, %177 = add.overflow u64 %32, %175
    store u64 %176, ptr %60
    %178 = const i64 8
    %179 = gep i8, ptr %60, %178
    store bool %177, ptr %179
    %180 = const i64 8
    %181 = gep i8, ptr %60, %180
    %182 = load bool, ptr %181
    %183 = const bool false
    %184 = icmp eq bool %182, %183
    condbr %184, bb14(%32, %174), bb23
bb14(%35: u64, %36: u64):
    %185 = load u64, ptr %60
    %186 = const i64 8
    %187 = gep i8, ptr %0, %186
    %188 = load u64, ptr %187
    %189 = icmp ult u64 %185, %188
    condbr %189, bb15(%35, %36, %185), bb23
bb15(%37: u64, %38: u64, %39: u64):
    %190 = load ptr, ptr %0
    %191 = gep u8, ptr %190, %39
    %192 = load u8, ptr %191
    %193 = zext u8 %192 to u64
    %194 = const u32 40
    %195 = const u32 64
    %196 = icmp ult u32 %194, %195
    condbr %196, bb16(%37, %38, %193), bb23
bb16(%40: u64, %41: u64, %42: u64):
    %197 = const u32 40
    %198 = zext u32 %197 to u64
    %199 = shl u64 %42, %198
    %200 = or u64 %41, %199
    %201 = const u64 6
    %202, %203 = add.overflow u64 %40, %201
    store u64 %202, ptr %61
    %204 = const i64 8
    %205 = gep i8, ptr %61, %204
    store bool %203, ptr %205
    %206 = const i64 8
    %207 = gep i8, ptr %61, %206
    %208 = load bool, ptr %207
    %209 = const bool false
    %210 = icmp eq bool %208, %209
    condbr %210, bb17(%40, %200), bb23
bb17(%43: u64, %44: u64):
    %211 = load u64, ptr %61
    %212 = const i64 8
    %213 = gep i8, ptr %0, %212
    %214 = load u64, ptr %213
    %215 = icmp ult u64 %211, %214
    condbr %215, bb18(%43, %44, %211), bb23
bb18(%45: u64, %46: u64, %47: u64):
    %216 = load ptr, ptr %0
    %217 = gep u8, ptr %216, %47
    %218 = load u8, ptr %217
    %219 = zext u8 %218 to u64
    %220 = const u32 48
    %221 = const u32 64
    %222 = icmp ult u32 %220, %221
    condbr %222, bb19(%45, %46, %219), bb23
bb19(%48: u64, %49: u64, %50: u64):
    %223 = const u32 48
    %224 = zext u32 %223 to u64
    %225 = shl u64 %50, %224
    %226 = or u64 %49, %225
    %227 = const u64 7
    %228, %229 = add.overflow u64 %48, %227
    store u64 %228, ptr %62
    %230 = const i64 8
    %231 = gep i8, ptr %62, %230
    store bool %229, ptr %231
    %232 = const i64 8
    %233 = gep i8, ptr %62, %232
    %234 = load bool, ptr %233
    %235 = const bool false
    %236 = icmp eq bool %234, %235
    condbr %236, bb20(%226), bb23
bb20(%51: u64):
    %237 = load u64, ptr %62
    %238 = const i64 8
    %239 = gep i8, ptr %0, %238
    %240 = load u64, ptr %239
    %241 = icmp ult u64 %237, %240
    condbr %241, bb21(%51, %237), bb23
bb21(%52: u64, %53: u64):
    %242 = load ptr, ptr %0
    %243 = gep u8, ptr %242, %53
    %244 = load u8, ptr %243
    %245 = zext u8 %244 to u64
    %246 = const u32 56
    %247 = const u32 64
    %248 = icmp ult u32 %246, %247
    condbr %248, bb22(%52, %245), bb23
bb22(%54: u64, %55: u64):
    %249 = const u32 56
    %250 = zext u32 %249 to u64
    %251 = shl u64 %55, %250
    %252 = or u64 %54, %251
    ret %252
bb23:
    unreachable
}

fn @sip13_d_rounds(functy.8) {
bb0(%0: ptr):
    call @func.11(%0)
    br bb1(%0)
bb1(%1: ptr):
    call @func.11(%1)
    br bb2(%1)
bb2(%2: ptr):
    call @func.11(%2)
    br bb3
bb3:
    ret
}

fn @load_u32_le(functy.9) {
bb0(%0: ptr, %1: u64):
    %24 = alloca (i64, i64), align 8
    %25 = alloca (i64, i64), align 8
    %26 = alloca (i64, i64), align 8
    %27 = const i64 8
    %28 = gep i8, ptr %0, %27
    %29 = load u64, ptr %28
    %30 = icmp ult u64 %1, %29
    condbr %30, bb1(%1), bb11
bb1(%2: u64):
    %31 = load ptr, ptr %0
    %32 = gep u8, ptr %31, %2
    %33 = load u8, ptr %32
    %34 = zext u8 %33 to u64
    %35 = const u64 1
    %36, %37 = add.overflow u64 %2, %35
    store u64 %36, ptr %24
    %38 = const i64 8
    %39 = gep i8, ptr %24, %38
    store bool %37, ptr %39
    %40 = const i64 8
    %41 = gep i8, ptr %24, %40
    %42 = load bool, ptr %41
    %43 = const bool false
    %44 = icmp eq bool %42, %43
    condbr %44, bb2(%2, %34), bb11
bb2(%3: u64, %4: u64):
    %45 = load u64, ptr %24
    %46 = const i64 8
    %47 = gep i8, ptr %0, %46
    %48 = load u64, ptr %47
    %49 = icmp ult u64 %45, %48
    condbr %49, bb3(%3, %4, %45), bb11
bb3(%5: u64, %6: u64, %7: u64):
    %50 = load ptr, ptr %0
    %51 = gep u8, ptr %50, %7
    %52 = load u8, ptr %51
    %53 = zext u8 %52 to u64
    %54 = const u32 8
    %55 = const u32 64
    %56 = icmp ult u32 %54, %55
    condbr %56, bb4(%5, %6, %53), bb11
bb4(%8: u64, %9: u64, %10: u64):
    %57 = const u32 8
    %58 = zext u32 %57 to u64
    %59 = shl u64 %10, %58
    %60 = or u64 %9, %59
    %61 = const u64 2
    %62, %63 = add.overflow u64 %8, %61
    store u64 %62, ptr %25
    %64 = const i64 8
    %65 = gep i8, ptr %25, %64
    store bool %63, ptr %65
    %66 = const i64 8
    %67 = gep i8, ptr %25, %66
    %68 = load bool, ptr %67
    %69 = const bool false
    %70 = icmp eq bool %68, %69
    condbr %70, bb5(%8, %60), bb11
bb5(%11: u64, %12: u64):
    %71 = load u64, ptr %25
    %72 = const i64 8
    %73 = gep i8, ptr %0, %72
    %74 = load u64, ptr %73
    %75 = icmp ult u64 %71, %74
    condbr %75, bb6(%11, %12, %71), bb11
bb6(%13: u64, %14: u64, %15: u64):
    %76 = load ptr, ptr %0
    %77 = gep u8, ptr %76, %15
    %78 = load u8, ptr %77
    %79 = zext u8 %78 to u64
    %80 = const u32 16
    %81 = const u32 64
    %82 = icmp ult u32 %80, %81
    condbr %82, bb7(%13, %14, %79), bb11
bb7(%16: u64, %17: u64, %18: u64):
    %83 = const u32 16
    %84 = zext u32 %83 to u64
    %85 = shl u64 %18, %84
    %86 = or u64 %17, %85
    %87 = const u64 3
    %88, %89 = add.overflow u64 %16, %87
    store u64 %88, ptr %26
    %90 = const i64 8
    %91 = gep i8, ptr %26, %90
    store bool %89, ptr %91
    %92 = const i64 8
    %93 = gep i8, ptr %26, %92
    %94 = load bool, ptr %93
    %95 = const bool false
    %96 = icmp eq bool %94, %95
    condbr %96, bb8(%86), bb11
bb8(%19: u64):
    %97 = load u64, ptr %26
    %98 = const i64 8
    %99 = gep i8, ptr %0, %98
    %100 = load u64, ptr %99
    %101 = icmp ult u64 %97, %100
    condbr %101, bb9(%19, %97), bb11
bb9(%20: u64, %21: u64):
    %102 = load ptr, ptr %0
    %103 = gep u8, ptr %102, %21
    %104 = load u8, ptr %103
    %105 = zext u8 %104 to u64
    %106 = const u32 24
    %107 = const u32 64
    %108 = icmp ult u32 %106, %107
    condbr %108, bb10(%20, %105), bb11
bb10(%22: u64, %23: u64):
    %109 = const u32 24
    %110 = zext u32 %109 to u64
    %111 = shl u64 %23, %110
    %112 = or u64 %22, %111
    %113 = trunc u64 %112 to u32
    ret %113
bb11:
    unreachable
}

fn @load_u16_le(functy.10) {
bb0(%0: ptr, %1: u64):
    %8 = alloca (i64, i64), align 8
    %9 = const i64 8
    %10 = gep i8, ptr %0, %9
    %11 = load u64, ptr %10
    %12 = icmp ult u64 %1, %11
    condbr %12, bb1(%1), bb5
bb1(%2: u64):
    %13 = load ptr, ptr %0
    %14 = gep u8, ptr %13, %2
    %15 = load u8, ptr %14
    %16 = zext u8 %15 to u64
    %17 = const u64 1
    %18, %19 = add.overflow u64 %2, %17
    store u64 %18, ptr %8
    %20 = const i64 8
    %21 = gep i8, ptr %8, %20
    store bool %19, ptr %21
    %22 = const i64 8
    %23 = gep i8, ptr %8, %22
    %24 = load bool, ptr %23
    %25 = const bool false
    %26 = icmp eq bool %24, %25
    condbr %26, bb2(%16), bb5
bb2(%3: u64):
    %27 = load u64, ptr %8
    %28 = const i64 8
    %29 = gep i8, ptr %0, %28
    %30 = load u64, ptr %29
    %31 = icmp ult u64 %27, %30
    condbr %31, bb3(%3, %27), bb5
bb3(%4: u64, %5: u64):
    %32 = load ptr, ptr %0
    %33 = gep u8, ptr %32, %5
    %34 = load u8, ptr %33
    %35 = zext u8 %34 to u64
    %36 = const u32 8
    %37 = const u32 64
    %38 = icmp ult u32 %36, %37
    condbr %38, bb4(%4, %35), bb5
bb4(%6: u64, %7: u64):
    %39 = const u32 8
    %40 = zext u32 %39 to u64
    %41 = shl u64 %7, %40
    %42 = or u64 %6, %41
    %43 = trunc u64 %42 to u16
    ret %43
bb5:
    unreachable
}

fn @sip_compress(functy.11) {
bb0(%0: ptr):
    %21 = load u64, ptr %0
    %22 = const i64 16
    %23 = gep i8, ptr %0, %22
    %24 = load u64, ptr %23
    %25 = call @func.12(%21, %24)
    br bb1(%0, %25)
bb1(%1: ptr, %2: u64):
    store u64 %2, ptr %1
    %26 = const i64 8
    %27 = gep i8, ptr %1, %26
    %28 = load u64, ptr %27
    %29 = const i64 24
    %30 = gep i8, ptr %1, %29
    %31 = load u64, ptr %30
    %32 = call @func.12(%28, %31)
    br bb2(%1, %32)
bb2(%3: ptr, %4: u64):
    %33 = const i64 8
    %34 = gep i8, ptr %3, %33
    store u64 %4, ptr %34
    %35 = const i64 16
    %36 = gep i8, ptr %3, %35
    %37 = load u64, ptr %36
    %38 = const u32 13
    %39 = call @func.13(%37, %38)
    br bb3(%3, %39)
bb3(%5: ptr, %6: u64):
    %40 = const i64 16
    %41 = gep i8, ptr %5, %40
    store u64 %6, ptr %41
    %42 = load u64, ptr %5
    %43 = const i64 16
    %44 = gep i8, ptr %5, %43
    %45 = load u64, ptr %44
    %46 = xor u64 %45, %42
    %47 = const i64 16
    %48 = gep i8, ptr %5, %47
    store u64 %46, ptr %48
    %49 = const i64 24
    %50 = gep i8, ptr %5, %49
    %51 = load u64, ptr %50
    %52 = const u32 16
    %53 = call @func.13(%51, %52)
    br bb4(%5, %53)
bb4(%7: ptr, %8: u64):
    %54 = const i64 24
    %55 = gep i8, ptr %7, %54
    store u64 %8, ptr %55
    %56 = const i64 8
    %57 = gep i8, ptr %7, %56
    %58 = load u64, ptr %57
    %59 = const i64 24
    %60 = gep i8, ptr %7, %59
    %61 = load u64, ptr %60
    %62 = xor u64 %61, %58
    %63 = const i64 24
    %64 = gep i8, ptr %7, %63
    store u64 %62, ptr %64
    %65 = load u64, ptr %7
    %66 = const u32 32
    %67 = call @func.13(%65, %66)
    br bb5(%7, %67)
bb5(%9: ptr, %10: u64):
    store u64 %10, ptr %9
    %68 = const i64 8
    %69 = gep i8, ptr %9, %68
    %70 = load u64, ptr %69
    %71 = const i64 16
    %72 = gep i8, ptr %9, %71
    %73 = load u64, ptr %72
    %74 = call @func.12(%70, %73)
    br bb6(%9, %74)
bb6(%11: ptr, %12: u64):
    %75 = const i64 8
    %76 = gep i8, ptr %11, %75
    store u64 %12, ptr %76
    %77 = load u64, ptr %11
    %78 = const i64 24
    %79 = gep i8, ptr %11, %78
    %80 = load u64, ptr %79
    %81 = call @func.12(%77, %80)
    br bb7(%11, %81)
bb7(%13: ptr, %14: u64):
    store u64 %14, ptr %13
    %82 = const i64 16
    %83 = gep i8, ptr %13, %82
    %84 = load u64, ptr %83
    %85 = const u32 17
    %86 = call @func.13(%84, %85)
    br bb8(%13, %86)
bb8(%15: ptr, %16: u64):
    %87 = const i64 16
    %88 = gep i8, ptr %15, %87
    store u64 %16, ptr %88
    %89 = const i64 8
    %90 = gep i8, ptr %15, %89
    %91 = load u64, ptr %90
    %92 = const i64 16
    %93 = gep i8, ptr %15, %92
    %94 = load u64, ptr %93
    %95 = xor u64 %94, %91
    %96 = const i64 16
    %97 = gep i8, ptr %15, %96
    store u64 %95, ptr %97
    %98 = const i64 24
    %99 = gep i8, ptr %15, %98
    %100 = load u64, ptr %99
    %101 = const u32 21
    %102 = call @func.13(%100, %101)
    br bb9(%15, %102)
bb9(%17: ptr, %18: u64):
    %103 = const i64 24
    %104 = gep i8, ptr %17, %103
    store u64 %18, ptr %104
    %105 = load u64, ptr %17
    %106 = const i64 24
    %107 = gep i8, ptr %17, %106
    %108 = load u64, ptr %107
    %109 = xor u64 %108, %105
    %110 = const i64 24
    %111 = gep i8, ptr %17, %110
    store u64 %109, ptr %111
    %112 = const i64 8
    %113 = gep i8, ptr %17, %112
    %114 = load u64, ptr %113
    %115 = const u32 32
    %116 = call @func.13(%114, %115)
    br bb10(%17, %116)
bb10(%19: ptr, %20: u64):
    %117 = const i64 8
    %118 = gep i8, ptr %19, %117
    store u64 %20, ptr %118
    ret
}

fn @w_add(functy.12) {
bb0(%0: u64, %1: u64):
    %16 = alloca (i64, i64), align 8
    %17 = alloca (i64, i64), align 8
    %18 = alloca (i64, i64), align 8
    %19 = const u64 4294967295
    %20 = and u64 %0, %19
    %21 = const u64 4294967295
    %22 = and u64 %1, %21
    %23, %24 = add.overflow u64 %20, %22
    store u64 %23, ptr %16
    %25 = const i64 8
    %26 = gep i8, ptr %16, %25
    store bool %24, ptr %26
    %27 = const i64 8
    %28 = gep i8, ptr %16, %27
    %29 = load bool, ptr %28
    %30 = const bool false
    %31 = icmp eq bool %29, %30
    condbr %31, bb1(%0, %1), bb8
bb1(%2: u64, %3: u64):
    %32 = load u64, ptr %16
    %33 = const i32 32
    %34 = bitcast i32 %33 to u32
    %35 = const u32 64
    %36 = icmp ult u32 %34, %35
    condbr %36, bb2(%2, %3, %32), bb8
bb2(%4: u64, %5: u64, %6: u64):
    %37 = const i32 32
    %38 = zext i32 %37 to u64
    %39 = lshr u64 %4, %38
    %40 = const i32 32
    %41 = bitcast i32 %40 to u32
    %42 = const u32 64
    %43 = icmp ult u32 %41, %42
    condbr %43, bb3(%5, %6, %39), bb8
bb3(%7: u64, %8: u64, %9: u64):
    %44 = const i32 32
    %45 = zext i32 %44 to u64
    %46 = lshr u64 %7, %45
    %47, %48 = add.overflow u64 %9, %46
    store u64 %47, ptr %17
    %49 = const i64 8
    %50 = gep i8, ptr %17, %49
    store bool %48, ptr %50
    %51 = const i64 8
    %52 = gep i8, ptr %17, %51
    %53 = load bool, ptr %52
    %54 = const bool false
    %55 = icmp eq bool %53, %54
    condbr %55, bb4(%8), bb8
bb4(%10: u64):
    %56 = load u64, ptr %17
    %57 = const i32 32
    %58 = bitcast i32 %57 to u32
    %59 = const u32 64
    %60 = icmp ult u32 %58, %59
    condbr %60, bb5(%10, %56), bb8
bb5(%11: u64, %12: u64):
    %61 = const i32 32
    %62 = zext i32 %61 to u64
    %63 = lshr u64 %11, %62
    %64, %65 = add.overflow u64 %12, %63
    store u64 %64, ptr %18
    %66 = const i64 8
    %67 = gep i8, ptr %18, %66
    store bool %65, ptr %67
    %68 = const i64 8
    %69 = gep i8, ptr %18, %68
    %70 = load bool, ptr %69
    %71 = const bool false
    %72 = icmp eq bool %70, %71
    condbr %72, bb6(%11), bb8
bb6(%13: u64):
    %73 = load u64, ptr %18
    %74 = const i32 32
    %75 = bitcast i32 %74 to u32
    %76 = const u32 64
    %77 = icmp ult u32 %75, %76
    condbr %77, bb7(%13, %73), bb8
bb7(%14: u64, %15: u64):
    %78 = const i32 32
    %79 = zext i32 %78 to u64
    %80 = shl u64 %15, %79
    %81 = const u64 4294967295
    %82 = and u64 %14, %81
    %83 = or u64 %80, %82
    ret %83
bb8:
    unreachable
}

fn @rotl(functy.13) {
bb0(%0: u64, %1: u32):
    %9 = alloca (i32, i32), align 4
    %10 = const u32 64
    %11 = icmp ult u32 %1, %10
    condbr %11, bb1(%0, %1), bb4
bb1(%2: u64, %3: u32):
    %12 = zext u32 %3 to u64
    %13 = shl u64 %2, %12
    %14 = const u32 64
    %15, %16 = sub.overflow u32 %14, %3
    store u32 %15, ptr %9
    %17 = const i64 4
    %18 = gep i8, ptr %9, %17
    store bool %16, ptr %18
    %19 = const i64 4
    %20 = gep i8, ptr %9, %19
    %21 = load bool, ptr %20
    %22 = const bool false
    %23 = icmp eq bool %21, %22
    condbr %23, bb2(%2, %13), bb4
bb2(%4: u64, %5: u64):
    %24 = load u32, ptr %9
    %25 = const u32 64
    %26 = icmp ult u32 %24, %25
    condbr %26, bb3(%4, %5, %24), bb4
bb3(%6: u64, %7: u64, %8: u32):
    %27 = zext u32 %8 to u64
    %28 = lshr u64 %6, %27
    %29 = or u64 %7, %28
    ret %29
bb4:
    unreachable
}
"##;

const SIP_INTS_MODULE: &str = r##"; TrustIr text format v1
module "mir::closure::sip_ints_root"
target "aarch64-apple-darwin" 8 little
file 0 "clean_siphash_slice.rs"

functy.0 = (u8, u8) -> (u8)

functy.1 = (u64, u64, u32, u8) -> (u64)

functy.2 = (ptr) -> ()

functy.3 = (ptr, u64) -> ()

functy.4 = (ptr, u32) -> ()

functy.5 = (ptr, u8) -> ()

functy.6 = (ptr, u64) -> ()

functy.7 = (ptr, u16) -> ()

functy.8 = (ptr) -> (u64)

functy.9 = (ptr, ptr) -> ()

functy.10 = (ptr) -> ()

functy.11 = (ptr) -> ()

functy.12 = (ptr, u64, u64) -> (u64)

functy.13 = (ptr, u64) -> (u64)

functy.14 = (ptr) -> ()

functy.15 = (ptr, u64) -> (u32)

functy.16 = (ptr, u64) -> (u16)

functy.17 = (u64, u64) -> (u64)

functy.18 = (u64, u32) -> (u64)

fn @_RNvMs4_NtCs2EYQwhfuABO_4core3numh12wrapping_add(functy.0) {
}

fn @sip_ints_root(functy.1) {
bb0(%0: u64, %1: u64, %2: u32, %3: u8):
    %86 = alloca (i64, i64, i64, i64, i64, i64, i64, i64, i64), align 8
    call @func.2(%86)
    br bb1(%0, %1, %2, %3)
bb1(%4: u64, %5: u64, %6: u32, %7: u8):
    %87 = const u64 0
    %88 = icmp eq u64 %4, %87
    condbr %88, bb2(%5), bb3(%4, %5, %6, %7)
bb2(%8: u64):
    call @func.3(%86, %8)
    br bb37
bb3(%9: u64, %10: u64, %11: u32, %12: u8):
    %89 = const u64 1
    %90 = icmp eq u64 %9, %89
    condbr %90, bb4(%11), bb5(%9, %10, %11, %12)
bb4(%13: u32):
    call @func.4(%86, %13)
    br bb38
bb5(%14: u64, %15: u64, %16: u32, %17: u8):
    %91 = const u64 2
    %92 = icmp eq u64 %14, %91
    condbr %92, bb6(%17), bb7(%14, %15, %16, %17)
bb6(%18: u8):
    call @func.5(%86, %18)
    br bb39
bb7(%19: u64, %20: u64, %21: u32, %22: u8):
    %93 = const u64 3
    %94 = icmp eq u64 %19, %93
    condbr %94, bb8(%20, %22), bb10(%19, %20, %21, %22)
bb8(%23: u64, %24: u8):
    call @func.5(%86, %24)
    br bb9(%23)
bb9(%25: u64):
    call @func.3(%86, %25)
    br bb40
bb10(%26: u64, %27: u64, %28: u32, %29: u8):
    %95 = const u64 4
    %96 = icmp eq u64 %26, %95
    condbr %96, bb11(%27, %28, %29), bb14(%26, %27, %28, %29)
bb11(%30: u64, %31: u32, %32: u8):
    call @func.4(%86, %31)
    br bb12(%30, %32)
bb12(%33: u64, %34: u8):
    call @func.3(%86, %33)
    br bb13(%34)
bb13(%35: u8):
    call @func.5(%86, %35)
    br bb41
bb14(%36: u64, %37: u64, %38: u32, %39: u8):
    %97 = const u64 5
    %98 = icmp eq u64 %36, %97
    condbr %98, bb15(%37), bb16(%36, %37, %38, %39)
bb15(%40: u64):
    call @func.6(%86, %40)
    br bb42
bb16(%41: u64, %42: u64, %43: u32, %44: u8):
    %99 = const u64 6
    %100 = icmp eq u64 %41, %99
    condbr %100, bb17(%42, %43, %44), bb23(%41, %42, %43, %44)
bb17(%45: u64, %46: u32, %47: u8):
    call @func.5(%86, %47)
    br bb18(%45, %46, %47)
bb18(%48: u64, %49: u32, %50: u8):
    %101 = const u8 255
    %102 = xor u8 %50, %101
    call @func.5(%86, %102)
    br bb19(%48, %49, %50)
bb19(%51: u64, %52: u32, %53: u8):
    %103 = const u8 1
    %104 = call @func.0(%53, %103)
    br bb20(%51, %52, %86, %104)
bb20(%54: u64, %55: u32, %56: ptr, %57: u8):
    call @func.5(%56, %57)
    br bb21(%54, %55)
bb21(%58: u64, %59: u32):
    call @func.4(%86, %59)
    br bb22(%58)
bb22(%60: u64):
    call @func.3(%86, %60)
    br bb43
bb23(%61: u64, %62: u64, %63: u32, %64: u8):
    %105 = const u64 7
    %106 = icmp eq u64 %61, %105
    condbr %106, bb24(%63), bb25(%61, %62, %63, %64)
bb24(%65: u32):
    %107 = const u32 65535
    %108 = and u32 %65, %107
    %109 = trunc u32 %108 to u16
    call @func.7(%86, %109)
    br bb44
bb25(%66: u64, %67: u64, %68: u32, %69: u8):
    %110 = const u64 8
    %111 = icmp eq u64 %66, %110
    condbr %111, bb26(%67, %68, %69), bb30(%66, %67)
bb26(%70: u64, %71: u32, %72: u8):
    call @func.5(%86, %72)
    br bb27(%70, %71)
bb27(%73: u64, %74: u32):
    %112 = const u32 65535
    %113 = and u32 %74, %112
    %114 = trunc u32 %113 to u16
    call @func.7(%86, %114)
    br bb28(%73, %74)
bb28(%75: u64, %76: u32):
    call @func.4(%86, %76)
    br bb29(%75)
bb29(%77: u64):
    call @func.3(%86, %77)
    br bb45
bb30(%78: u64, %79: u64):
    %115 = const u64 9
    %116 = icmp eq u64 %78, %115
    condbr %116, bb31(%79), bb33(%78, %79)
bb31(%80: u64):
    call @func.3(%86, %80)
    br bb32
bb32:
    %117 = const u8 255
    call @func.5(%86, %117)
    br bb46
bb33(%81: u64, %82: u64):
    call @func.3(%86, %82)
    br bb34(%81, %82)
bb34(%83: u64, %84: u64):
    %118 = xor u64 %84, %83
    call @func.3(%86, %118)
    br bb47
bb35:
    %119 = call @func.8(%86)
    br bb36(%119)
bb36(%85: u64):
    ret %85
bb37:
    br bb35
bb38:
    br bb35
bb39:
    br bb35
bb40:
    br bb35
bb41:
    br bb35
bb42:
    br bb35
bb43:
    br bb35
bb44:
    br bb35
bb45:
    br bb35
bb46:
    br bb35
bb47:
    br bb35
}

fn @SipHasher13__new(functy.2) {
bb0(%0: ptr):
    %1 = alloca (i64, i64, i64, i64), align 8
    %2 = const u64 0
    %3 = const u64 0
    %4 = const u64 8317987319222330741
    %5 = xor u64 %2, %4
    %6 = const u64 7816392313619706465
    %7 = xor u64 %2, %6
    %8 = const u64 7237128888997146477
    %9 = xor u64 %3, %8
    %10 = const u64 8387220255154660723
    %11 = xor u64 %3, %10
    store u64 %5, ptr %1
    %12 = const i64 8
    %13 = gep i8, ptr %1, %12
    store u64 %7, ptr %13
    %14 = const i64 16
    %15 = gep i8, ptr %1, %14
    store u64 %9, ptr %15
    %16 = const i64 24
    %17 = gep i8, ptr %1, %16
    store u64 %11, ptr %17
    %18 = const i64 32
    %19 = gep i8, ptr %0, %18
    store u64 %2, ptr %19
    %20 = const i64 40
    %21 = gep i8, ptr %0, %20
    store u64 %3, ptr %21
    %22 = const u64 0
    %23 = const i64 48
    %24 = gep i8, ptr %0, %23
    store u64 %22, ptr %24
    %25 = load i64, ptr %1
    store i64 %25, ptr %0
    %26 = const i64 8
    %27 = gep i8, ptr %1, %26
    %28 = const i64 8
    %29 = gep i8, ptr %0, %28
    %30 = load i64, ptr %27
    store i64 %30, ptr %29
    %31 = const i64 16
    %32 = gep i8, ptr %1, %31
    %33 = const i64 16
    %34 = gep i8, ptr %0, %33
    %35 = load i64, ptr %32
    store i64 %35, ptr %34
    %36 = const i64 24
    %37 = gep i8, ptr %1, %36
    %38 = const i64 24
    %39 = gep i8, ptr %0, %38
    %40 = load i64, ptr %37
    store i64 %40, ptr %39
    %41 = const u64 0
    %42 = const i64 56
    %43 = gep i8, ptr %0, %42
    store u64 %41, ptr %43
    %44 = const u64 0
    %45 = const i64 64
    %46 = gep i8, ptr %0, %45
    store u64 %44, ptr %46
    ret
}

fn @SipHasher13__write_u64(functy.3) {
bb0(%0: ptr, %1: u64):
    %44 = alloca (i8, i8, i8, i8, i8, i8, i8, i8), align 1
    %45 = alloca (i64, i64), align 8
    %46 = trunc u64 %1 to u8
    %47 = const u32 8
    %48 = const u32 64
    %49 = icmp ult u32 %47, %48
    condbr %49, bb1(%0, %1, %46), bb9
bb1(%2: ptr, %3: u64, %4: u8):
    %50 = const u32 8
    %51 = zext u32 %50 to u64
    %52 = lshr u64 %3, %51
    %53 = trunc u64 %52 to u8
    %54 = const u32 16
    %55 = const u32 64
    %56 = icmp ult u32 %54, %55
    condbr %56, bb2(%2, %3, %4, %53), bb9
bb2(%5: ptr, %6: u64, %7: u8, %8: u8):
    %57 = const u32 16
    %58 = zext u32 %57 to u64
    %59 = lshr u64 %6, %58
    %60 = trunc u64 %59 to u8
    %61 = const u32 24
    %62 = const u32 64
    %63 = icmp ult u32 %61, %62
    condbr %63, bb3(%5, %6, %7, %8, %60), bb9
bb3(%9: ptr, %10: u64, %11: u8, %12: u8, %13: u8):
    %64 = const u32 24
    %65 = zext u32 %64 to u64
    %66 = lshr u64 %10, %65
    %67 = trunc u64 %66 to u8
    %68 = const u32 32
    %69 = const u32 64
    %70 = icmp ult u32 %68, %69
    condbr %70, bb4(%9, %10, %11, %12, %13, %67), bb9
bb4(%14: ptr, %15: u64, %16: u8, %17: u8, %18: u8, %19: u8):
    %71 = const u32 32
    %72 = zext u32 %71 to u64
    %73 = lshr u64 %15, %72
    %74 = trunc u64 %73 to u8
    %75 = const u32 40
    %76 = const u32 64
    %77 = icmp ult u32 %75, %76
    condbr %77, bb5(%14, %15, %16, %17, %18, %19, %74), bb9
bb5(%20: ptr, %21: u64, %22: u8, %23: u8, %24: u8, %25: u8, %26: u8):
    %78 = const u32 40
    %79 = zext u32 %78 to u64
    %80 = lshr u64 %21, %79
    %81 = trunc u64 %80 to u8
    %82 = const u32 48
    %83 = const u32 64
    %84 = icmp ult u32 %82, %83
    condbr %84, bb6(%20, %21, %22, %23, %24, %25, %26, %81), bb9
bb6(%27: ptr, %28: u64, %29: u8, %30: u8, %31: u8, %32: u8, %33: u8, %34: u8):
    %85 = const u32 48
    %86 = zext u32 %85 to u64
    %87 = lshr u64 %28, %86
    %88 = trunc u64 %87 to u8
    %89 = const u32 56
    %90 = const u32 64
    %91 = icmp ult u32 %89, %90
    condbr %91, bb7(%27, %28, %29, %30, %31, %32, %33, %34, %88), bb9
bb7(%35: ptr, %36: u64, %37: u8, %38: u8, %39: u8, %40: u8, %41: u8, %42: u8, %43: u8):
    %92 = const u32 56
    %93 = zext u32 %92 to u64
    %94 = lshr u64 %36, %93
    %95 = trunc u64 %94 to u8
    store u8 %37, ptr %44
    %96 = const i64 1
    %97 = gep i8, ptr %44, %96
    store u8 %38, ptr %97
    %98 = const i64 2
    %99 = gep i8, ptr %44, %98
    store u8 %39, ptr %99
    %100 = const i64 3
    %101 = gep i8, ptr %44, %100
    store u8 %40, ptr %101
    %102 = const i64 4
    %103 = gep i8, ptr %44, %102
    store u8 %41, ptr %103
    %104 = const i64 5
    %105 = gep i8, ptr %44, %104
    store u8 %42, ptr %105
    %106 = const i64 6
    %107 = gep i8, ptr %44, %106
    store u8 %43, ptr %107
    %108 = const i64 7
    %109 = gep i8, ptr %44, %108
    store u8 %95, ptr %109
    store ptr %44, ptr %45
    %110 = const i64 8
    %111 = gep i8, ptr %45, %110
    %112 = const u64 8
    store u64 %112, ptr %111
    call @func.9(%35, %45)
    br bb8
bb8:
    ret
bb9:
    unreachable
}

fn @SipHasher13__write_u32(functy.4) {
bb0(%0: ptr, %1: u32):
    %14 = alloca (i8, i8, i8, i8), align 1
    %15 = alloca (i64, i64), align 8
    %16 = zext u32 %1 to u64
    %17 = trunc u64 %16 to u8
    %18 = const u32 8
    %19 = const u32 64
    %20 = icmp ult u32 %18, %19
    condbr %20, bb1(%0, %16, %17), bb5
bb1(%2: ptr, %3: u64, %4: u8):
    %21 = const u32 8
    %22 = zext u32 %21 to u64
    %23 = lshr u64 %3, %22
    %24 = trunc u64 %23 to u8
    %25 = const u32 16
    %26 = const u32 64
    %27 = icmp ult u32 %25, %26
    condbr %27, bb2(%2, %3, %4, %24), bb5
bb2(%5: ptr, %6: u64, %7: u8, %8: u8):
    %28 = const u32 16
    %29 = zext u32 %28 to u64
    %30 = lshr u64 %6, %29
    %31 = trunc u64 %30 to u8
    %32 = const u32 24
    %33 = const u32 64
    %34 = icmp ult u32 %32, %33
    condbr %34, bb3(%5, %6, %7, %8, %31), bb5
bb3(%9: ptr, %10: u64, %11: u8, %12: u8, %13: u8):
    %35 = const u32 24
    %36 = zext u32 %35 to u64
    %37 = lshr u64 %10, %36
    %38 = trunc u64 %37 to u8
    store u8 %11, ptr %14
    %39 = const i64 1
    %40 = gep i8, ptr %14, %39
    store u8 %12, ptr %40
    %41 = const i64 2
    %42 = gep i8, ptr %14, %41
    store u8 %13, ptr %42
    %43 = const i64 3
    %44 = gep i8, ptr %14, %43
    store u8 %38, ptr %44
    store ptr %14, ptr %15
    %45 = const i64 8
    %46 = gep i8, ptr %15, %45
    %47 = const u64 4
    store u64 %47, ptr %46
    call @func.9(%9, %15)
    br bb4
bb4:
    ret
bb5:
    unreachable
}

fn @SipHasher13__write_u8(functy.5) {
bb0(%0: ptr, %1: u8):
    %2 = alloca i8, align 1
    %3 = alloca (i64, i64), align 8
    store u8 %1, ptr %2
    store ptr %2, ptr %3
    %4 = const i64 8
    %5 = gep i8, ptr %3, %4
    %6 = const u64 1
    store u64 %6, ptr %5
    call @func.9(%0, %3)
    br bb1
bb1:
    ret
}

fn @SipHasher13__write_usize(functy.6) {
bb0(%0: ptr, %1: u64):
    %44 = alloca (i8, i8, i8, i8, i8, i8, i8, i8), align 1
    %45 = alloca (i64, i64), align 8
    %46 = trunc u64 %1 to u8
    %47 = const u32 8
    %48 = const u32 64
    %49 = icmp ult u32 %47, %48
    condbr %49, bb1(%0, %1, %46), bb9
bb1(%2: ptr, %3: u64, %4: u8):
    %50 = const u32 8
    %51 = zext u32 %50 to u64
    %52 = lshr u64 %3, %51
    %53 = trunc u64 %52 to u8
    %54 = const u32 16
    %55 = const u32 64
    %56 = icmp ult u32 %54, %55
    condbr %56, bb2(%2, %3, %4, %53), bb9
bb2(%5: ptr, %6: u64, %7: u8, %8: u8):
    %57 = const u32 16
    %58 = zext u32 %57 to u64
    %59 = lshr u64 %6, %58
    %60 = trunc u64 %59 to u8
    %61 = const u32 24
    %62 = const u32 64
    %63 = icmp ult u32 %61, %62
    condbr %63, bb3(%5, %6, %7, %8, %60), bb9
bb3(%9: ptr, %10: u64, %11: u8, %12: u8, %13: u8):
    %64 = const u32 24
    %65 = zext u32 %64 to u64
    %66 = lshr u64 %10, %65
    %67 = trunc u64 %66 to u8
    %68 = const u32 32
    %69 = const u32 64
    %70 = icmp ult u32 %68, %69
    condbr %70, bb4(%9, %10, %11, %12, %13, %67), bb9
bb4(%14: ptr, %15: u64, %16: u8, %17: u8, %18: u8, %19: u8):
    %71 = const u32 32
    %72 = zext u32 %71 to u64
    %73 = lshr u64 %15, %72
    %74 = trunc u64 %73 to u8
    %75 = const u32 40
    %76 = const u32 64
    %77 = icmp ult u32 %75, %76
    condbr %77, bb5(%14, %15, %16, %17, %18, %19, %74), bb9
bb5(%20: ptr, %21: u64, %22: u8, %23: u8, %24: u8, %25: u8, %26: u8):
    %78 = const u32 40
    %79 = zext u32 %78 to u64
    %80 = lshr u64 %21, %79
    %81 = trunc u64 %80 to u8
    %82 = const u32 48
    %83 = const u32 64
    %84 = icmp ult u32 %82, %83
    condbr %84, bb6(%20, %21, %22, %23, %24, %25, %26, %81), bb9
bb6(%27: ptr, %28: u64, %29: u8, %30: u8, %31: u8, %32: u8, %33: u8, %34: u8):
    %85 = const u32 48
    %86 = zext u32 %85 to u64
    %87 = lshr u64 %28, %86
    %88 = trunc u64 %87 to u8
    %89 = const u32 56
    %90 = const u32 64
    %91 = icmp ult u32 %89, %90
    condbr %91, bb7(%27, %28, %29, %30, %31, %32, %33, %34, %88), bb9
bb7(%35: ptr, %36: u64, %37: u8, %38: u8, %39: u8, %40: u8, %41: u8, %42: u8, %43: u8):
    %92 = const u32 56
    %93 = zext u32 %92 to u64
    %94 = lshr u64 %36, %93
    %95 = trunc u64 %94 to u8
    store u8 %37, ptr %44
    %96 = const i64 1
    %97 = gep i8, ptr %44, %96
    store u8 %38, ptr %97
    %98 = const i64 2
    %99 = gep i8, ptr %44, %98
    store u8 %39, ptr %99
    %100 = const i64 3
    %101 = gep i8, ptr %44, %100
    store u8 %40, ptr %101
    %102 = const i64 4
    %103 = gep i8, ptr %44, %102
    store u8 %41, ptr %103
    %104 = const i64 5
    %105 = gep i8, ptr %44, %104
    store u8 %42, ptr %105
    %106 = const i64 6
    %107 = gep i8, ptr %44, %106
    store u8 %43, ptr %107
    %108 = const i64 7
    %109 = gep i8, ptr %44, %108
    store u8 %95, ptr %109
    store ptr %44, ptr %45
    %110 = const i64 8
    %111 = gep i8, ptr %45, %110
    %112 = const u64 8
    store u64 %112, ptr %111
    call @func.9(%35, %45)
    br bb8
bb8:
    ret
bb9:
    unreachable
}

fn @SipHasher13__write_u16(functy.7) {
bb0(%0: ptr, %1: u16):
    %5 = alloca (i8, i8), align 1
    %6 = alloca (i64, i64), align 8
    %7 = zext u16 %1 to u64
    %8 = trunc u64 %7 to u8
    %9 = const u32 8
    %10 = const u32 64
    %11 = icmp ult u32 %9, %10
    condbr %11, bb1(%0, %7, %8), bb3
bb1(%2: ptr, %3: u64, %4: u8):
    %12 = const u32 8
    %13 = zext u32 %12 to u64
    %14 = lshr u64 %3, %13
    %15 = trunc u64 %14 to u8
    store u8 %4, ptr %5
    %16 = const i64 1
    %17 = gep i8, ptr %5, %16
    store u8 %15, ptr %17
    store ptr %5, ptr %6
    %18 = const i64 8
    %19 = gep i8, ptr %6, %18
    %20 = const u64 2
    store u64 %20, ptr %19
    call @func.9(%2, %6)
    br bb2
bb2:
    ret
bb3:
    unreachable
}

fn @SipHasher13__finish(functy.8) {
bb0(%0: ptr):
    %4 = alloca (i64, i64, i64, i64), align 8
    %5 = load i64, ptr %0
    store i64 %5, ptr %4
    %6 = const i64 8
    %7 = gep i8, ptr %0, %6
    %8 = const i64 8
    %9 = gep i8, ptr %4, %8
    %10 = load i64, ptr %7
    store i64 %10, ptr %9
    %11 = const i64 16
    %12 = gep i8, ptr %0, %11
    %13 = const i64 16
    %14 = gep i8, ptr %4, %13
    %15 = load i64, ptr %12
    store i64 %15, ptr %14
    %16 = const i64 24
    %17 = gep i8, ptr %0, %16
    %18 = const i64 24
    %19 = gep i8, ptr %4, %18
    %20 = load i64, ptr %17
    store i64 %20, ptr %19
    %21 = const i64 48
    %22 = gep i8, ptr %0, %21
    %23 = load u64, ptr %22
    %24 = const u64 255
    %25 = and u64 %23, %24
    %26 = const i32 56
    %27 = bitcast i32 %26 to u32
    %28 = const u32 64
    %29 = icmp ult u32 %27, %28
    condbr %29, bb1(%0, %25), bb4
bb1(%1: ptr, %2: u64):
    %30 = const i32 56
    %31 = zext i32 %30 to u64
    %32 = shl u64 %2, %31
    %33 = const i64 56
    %34 = gep i8, ptr %1, %33
    %35 = load u64, ptr %34
    %36 = or u64 %32, %35
    %37 = const i64 24
    %38 = gep i8, ptr %4, %37
    %39 = load u64, ptr %38
    %40 = xor u64 %39, %36
    %41 = const i64 24
    %42 = gep i8, ptr %4, %41
    store u64 %40, ptr %42
    call @func.10(%4)
    br bb2(%36)
bb2(%3: u64):
    %43 = load u64, ptr %4
    %44 = xor u64 %43, %3
    store u64 %44, ptr %4
    %45 = const i64 8
    %46 = gep i8, ptr %4, %45
    %47 = load u64, ptr %46
    %48 = const u64 255
    %49 = xor u64 %47, %48
    %50 = const i64 8
    %51 = gep i8, ptr %4, %50
    store u64 %49, ptr %51
    call @func.11(%4)
    br bb3
bb3:
    %52 = load u64, ptr %4
    %53 = const i64 16
    %54 = gep i8, ptr %4, %53
    %55 = load u64, ptr %54
    %56 = xor u64 %52, %55
    %57 = const i64 8
    %58 = gep i8, ptr %4, %57
    %59 = load u64, ptr %58
    %60 = xor u64 %56, %59
    %61 = const i64 24
    %62 = gep i8, ptr %4, %61
    %63 = load u64, ptr %62
    %64 = xor u64 %60, %63
    ret %64
bb4:
    unreachable
}

fn @SipHasher13__write(functy.9) {
bb0(%0: ptr, %1: ptr):
    %54 = alloca i64, align 8
    %55 = alloca (i64, i64), align 8
    %56 = alloca (i64, i64), align 8
    %57 = alloca (i64, i64), align 8
    %58 = alloca (i64, i64), align 8
    %59 = alloca (i64, i64), align 8
    %60 = alloca (i64, i64), align 8
    %61 = alloca (i64, i64), align 8
    store ptr %0, ptr %54
    %62 = const i64 8
    %63 = gep i8, ptr %1, %62
    %64 = load u64, ptr %63
    %65 = load ptr, ptr %54
    %66 = const i64 48
    %67 = gep i8, ptr %65, %66
    %68 = load u64, ptr %67
    %69, %70 = add.overflow u64 %68, %64
    store u64 %69, ptr %55
    %71 = const i64 8
    %72 = gep i8, ptr %55, %71
    store bool %70, ptr %72
    %73 = const i64 8
    %74 = gep i8, ptr %55, %73
    %75 = load bool, ptr %74
    %76 = const bool false
    %77 = icmp eq bool %75, %76
    condbr %77, bb1(%64), bb25
bb1(%2: u64):
    %78 = load u64, ptr %55
    %79 = load ptr, ptr %54
    %80 = const i64 48
    %81 = gep i8, ptr %79, %80
    store u64 %78, ptr %81
    %82 = const u64 0
    %83 = load ptr, ptr %54
    %84 = const i64 64
    %85 = gep i8, ptr %83, %84
    %86 = load u64, ptr %85
    %87 = const u64 0
    %88 = icmp ne u64 %86, %87
    condbr %88, bb2(%2), bb14(%2, %82)
bb2(%3: u64):
    %89 = load ptr, ptr %54
    %90 = const i64 64
    %91 = gep i8, ptr %89, %90
    %92 = load u64, ptr %91
    %93 = const u64 8
    %94, %95 = sub.overflow u64 %93, %92
    store u64 %94, ptr %56
    %96 = const i64 8
    %97 = gep i8, ptr %56, %96
    store bool %95, ptr %97
    %98 = const i64 8
    %99 = gep i8, ptr %56, %98
    %100 = load bool, ptr %99
    %101 = const bool false
    %102 = icmp eq bool %100, %101
    condbr %102, bb3(%3), bb25
bb3(%4: u64):
    %103 = load u64, ptr %56
    %104 = icmp ult u64 %4, %103
    condbr %104, bb4(%4, %103), bb5(%4, %103)
bb4(%5: u64, %6: u64):
    br bb6(%5, %6, %5)
bb5(%7: u64, %8: u64):
    br bb6(%7, %8, %8)
bb6(%9: u64, %10: u64, %11: u64):
    %105 = const u64 0
    %106 = call @func.12(%1, %105, %11)
    br bb7(%9, %10, %106)
bb7(%12: u64, %13: u64, %14: u64):
    %107 = load ptr, ptr %54
    %108 = const i64 64
    %109 = gep i8, ptr %107, %108
    %110 = load u64, ptr %109
    %111 = const u64 8
    %112, %113 = mul.overflow u64 %111, %110
    store u64 %112, ptr %57
    %114 = const i64 8
    %115 = gep i8, ptr %57, %114
    store bool %113, ptr %115
    %116 = const i64 8
    %117 = gep i8, ptr %57, %116
    %118 = load bool, ptr %117
    %119 = const bool false
    %120 = icmp eq bool %118, %119
    condbr %120, bb8(%12, %13, %14), bb25
bb8(%15: u64, %16: u64, %17: u64):
    %121 = load u64, ptr %57
    %122 = trunc u64 %121 to u32
    %123 = const u32 64
    %124 = icmp ult u32 %122, %123
    condbr %124, bb9(%15, %16, %17, %122), bb25
bb9(%18: u64, %19: u64, %20: u64, %21: u32):
    %125 = zext u32 %21 to u64
    %126 = shl u64 %20, %125
    %127 = load ptr, ptr %54
    %128 = const i64 56
    %129 = gep i8, ptr %127, %128
    %130 = load u64, ptr %129
    %131 = or u64 %130, %126
    %132 = load ptr, ptr %54
    %133 = const i64 56
    %134 = gep i8, ptr %132, %133
    store u64 %131, ptr %134
    %135 = icmp ult u64 %18, %19
    condbr %135, bb10(%18), bb12(%18, %19)
bb10(%22: u64):
    %136 = load ptr, ptr %54
    %137 = const i64 64
    %138 = gep i8, ptr %136, %137
    %139 = load u64, ptr %138
    %140, %141 = add.overflow u64 %139, %22
    store u64 %140, ptr %58
    %142 = const i64 8
    %143 = gep i8, ptr %58, %142
    store bool %141, ptr %143
    %144 = const i64 8
    %145 = gep i8, ptr %58, %144
    %146 = load bool, ptr %145
    %147 = const bool false
    %148 = icmp eq bool %146, %147
    condbr %148, bb11, bb25
bb11:
    %149 = load u64, ptr %58
    %150 = load ptr, ptr %54
    %151 = const i64 64
    %152 = gep i8, ptr %150, %151
    store u64 %149, ptr %152
    br bb24
bb12(%23: u64, %24: u64):
    %153 = load ptr, ptr %54
    %154 = const i64 56
    %155 = gep i8, ptr %153, %154
    %156 = load u64, ptr %155
    %157 = load ptr, ptr %54
    %158 = const i64 24
    %159 = gep i8, ptr %157, %158
    %160 = load u64, ptr %159
    %161 = xor u64 %160, %156
    %162 = load ptr, ptr %54
    %163 = const i64 24
    %164 = gep i8, ptr %162, %163
    store u64 %161, ptr %164
    %165 = load ptr, ptr %54
    call @func.10(%165)
    br bb13(%23, %24)
bb13(%25: u64, %26: u64):
    %166 = load ptr, ptr %54
    %167 = const i64 56
    %168 = gep i8, ptr %166, %167
    %169 = load u64, ptr %168
    %170 = load ptr, ptr %54
    %171 = load u64, ptr %170
    %172 = xor u64 %171, %169
    %173 = load ptr, ptr %54
    store u64 %172, ptr %173
    %174 = const u64 0
    %175 = load ptr, ptr %54
    %176 = const i64 64
    %177 = gep i8, ptr %175, %176
    store u64 %174, ptr %177
    br bb14(%25, %26)
bb14(%27: u64, %28: u64):
    %178, %179 = sub.overflow u64 %27, %28
    store u64 %178, ptr %59
    %180 = const i64 8
    %181 = gep i8, ptr %59, %180
    store bool %179, ptr %181
    %182 = const i64 8
    %183 = gep i8, ptr %59, %182
    %184 = load bool, ptr %183
    %185 = const bool false
    %186 = icmp eq bool %184, %185
    condbr %186, bb15(%28), bb25
bb15(%29: u64):
    %187 = load u64, ptr %59
    %188 = const u64 7
    %189 = and u64 %187, %188
    br bb16(%187, %189, %29)
bb16(%30: u64, %31: u64, %32: u64):
    %190, %191 = sub.overflow u64 %30, %31
    store u64 %190, ptr %60
    %192 = const i64 8
    %193 = gep i8, ptr %60, %192
    store bool %191, ptr %193
    %194 = const i64 8
    %195 = gep i8, ptr %60, %194
    %196 = load bool, ptr %195
    %197 = const bool false
    %198 = icmp eq bool %196, %197
    condbr %198, bb17(%30, %31, %32, %32), bb25
bb17(%33: u64, %34: u64, %35: u64, %36: u64):
    %199 = load u64, ptr %60
    %200 = icmp ult u64 %36, %199
    condbr %200, bb18(%33, %34, %35), bb22(%34, %35)
bb18(%37: u64, %38: u64, %39: u64):
    %201 = call @func.13(%1, %39)
    br bb19(%37, %38, %39, %201)
bb19(%40: u64, %41: u64, %42: u64, %43: u64):
    %202 = load ptr, ptr %54
    %203 = const i64 24
    %204 = gep i8, ptr %202, %203
    %205 = load u64, ptr %204
    %206 = xor u64 %205, %43
    %207 = load ptr, ptr %54
    %208 = const i64 24
    %209 = gep i8, ptr %207, %208
    store u64 %206, ptr %209
    %210 = load ptr, ptr %54
    call @func.10(%210)
    br bb20(%40, %41, %42, %43)
bb20(%44: u64, %45: u64, %46: u64, %47: u64):
    %211 = load ptr, ptr %54
    %212 = load u64, ptr %211
    %213 = xor u64 %212, %47
    %214 = load ptr, ptr %54
    store u64 %213, ptr %214
    %215 = const u64 8
    %216, %217 = add.overflow u64 %46, %215
    store u64 %216, ptr %61
    %218 = const i64 8
    %219 = gep i8, ptr %61, %218
    store bool %217, ptr %219
    %220 = const i64 8
    %221 = gep i8, ptr %61, %220
    %222 = load bool, ptr %221
    %223 = const bool false
    %224 = icmp eq bool %222, %223
    condbr %224, bb21(%44, %45), bb25
bb21(%48: u64, %49: u64):
    %225 = load u64, ptr %61
    br bb16(%48, %49, %225)
bb22(%50: u64, %51: u64):
    %226 = call @func.12(%1, %51, %50)
    br bb23(%50, %226)
bb23(%52: u64, %53: u64):
    %227 = load ptr, ptr %54
    %228 = const i64 56
    %229 = gep i8, ptr %227, %228
    store u64 %53, ptr %229
    %230 = load ptr, ptr %54
    %231 = const i64 64
    %232 = gep i8, ptr %230, %231
    store u64 %52, ptr %232
    br bb24
bb24:
    ret
bb25:
    unreachable
}

fn @sip13_c_rounds(functy.10) {
bb0(%0: ptr):
    call @func.14(%0)
    br bb1
bb1:
    ret
}

fn @sip13_d_rounds(functy.11) {
bb0(%0: ptr):
    call @func.14(%0)
    br bb1(%0)
bb1(%1: ptr):
    call @func.14(%1)
    br bb2(%1)
bb2(%2: ptr):
    call @func.14(%2)
    br bb3
bb3:
    ret
}

fn @u8to64_le(functy.12) {
bb0(%0: ptr, %1: u64, %2: u64):
    %76 = alloca (i64, i64), align 8
    %77 = alloca (i64, i64), align 8
    %78 = alloca (i64, i64), align 8
    %79 = alloca (i64, i64), align 8
    %80 = alloca (i64, i64), align 8
    %81 = alloca (i64, i64), align 8
    %82 = alloca (i64, i64), align 8
    %83 = alloca (i64, i64), align 8
    %84 = alloca (i64, i64), align 8
    %85 = alloca (i64, i64), align 8
    %86 = const u64 0
    %87 = const u64 0
    %88 = const u64 3
    %89, %90 = add.overflow u64 %86, %88
    store u64 %89, ptr %76
    %91 = const i64 8
    %92 = gep i8, ptr %76, %91
    store bool %90, ptr %92
    %93 = const i64 8
    %94 = gep i8, ptr %76, %93
    %95 = load bool, ptr %94
    %96 = const bool false
    %97 = icmp eq bool %95, %96
    condbr %97, bb1(%1, %2, %86, %87), bb22
bb1(%3: u64, %4: u64, %5: u64, %6: u64):
    %98 = load u64, ptr %76
    %99 = icmp ult u64 %98, %4
    condbr %99, bb2(%3, %4, %5), bb6(%3, %4, %5, %6)
bb2(%7: u64, %8: u64, %9: u64):
    %100, %101 = add.overflow u64 %7, %9
    store u64 %100, ptr %77
    %102 = const i64 8
    %103 = gep i8, ptr %77, %102
    store bool %101, ptr %103
    %104 = const i64 8
    %105 = gep i8, ptr %77, %104
    %106 = load bool, ptr %105
    %107 = const bool false
    %108 = icmp eq bool %106, %107
    condbr %108, bb3(%7, %8, %9), bb22
bb3(%10: u64, %11: u64, %12: u64):
    %109 = load u64, ptr %77
    %110 = call @func.15(%0, %109)
    br bb4(%10, %11, %12, %110)
bb4(%13: u64, %14: u64, %15: u64, %16: u32):
    %111 = zext u32 %16 to u64
    %112 = const u64 4
    %113, %114 = add.overflow u64 %15, %112
    store u64 %113, ptr %78
    %115 = const i64 8
    %116 = gep i8, ptr %78, %115
    store bool %114, ptr %116
    %117 = const i64 8
    %118 = gep i8, ptr %78, %117
    %119 = load bool, ptr %118
    %120 = const bool false
    %121 = icmp eq bool %119, %120
    condbr %121, bb5(%13, %14, %111), bb22
bb5(%17: u64, %18: u64, %19: u64):
    %122 = load u64, ptr %78
    br bb6(%17, %18, %122, %19)
bb6(%20: u64, %21: u64, %22: u64, %23: u64):
    %123 = const u64 1
    %124, %125 = add.overflow u64 %22, %123
    store u64 %124, ptr %79
    %126 = const i64 8
    %127 = gep i8, ptr %79, %126
    store bool %125, ptr %127
    %128 = const i64 8
    %129 = gep i8, ptr %79, %128
    %130 = load bool, ptr %129
    %131 = const bool false
    %132 = icmp eq bool %130, %131
    condbr %132, bb7(%20, %21, %22, %23), bb22
bb7(%24: u64, %25: u64, %26: u64, %27: u64):
    %133 = load u64, ptr %79
    %134 = icmp ult u64 %133, %25
    condbr %134, bb8(%24, %25, %26, %27), bb14(%24, %25, %26, %27)
bb8(%28: u64, %29: u64, %30: u64, %31: u64):
    %135, %136 = add.overflow u64 %28, %30
    store u64 %135, ptr %80
    %137 = const i64 8
    %138 = gep i8, ptr %80, %137
    store bool %136, ptr %138
    %139 = const i64 8
    %140 = gep i8, ptr %80, %139
    %141 = load bool, ptr %140
    %142 = const bool false
    %143 = icmp eq bool %141, %142
    condbr %143, bb9(%28, %29, %30, %31), bb22
bb9(%32: u64, %33: u64, %34: u64, %35: u64):
    %144 = load u64, ptr %80
    %145 = call @func.16(%0, %144)
    br bb10(%32, %33, %34, %35, %145)
bb10(%36: u64, %37: u64, %38: u64, %39: u64, %40: u16):
    %146 = zext u16 %40 to u64
    %147 = const u64 8
    %148, %149 = mul.overflow u64 %38, %147
    store u64 %148, ptr %81
    %150 = const i64 8
    %151 = gep i8, ptr %81, %150
    store bool %149, ptr %151
    %152 = const i64 8
    %153 = gep i8, ptr %81, %152
    %154 = load bool, ptr %153
    %155 = const bool false
    %156 = icmp eq bool %154, %155
    condbr %156, bb11(%36, %37, %38, %39, %146), bb22
bb11(%41: u64, %42: u64, %43: u64, %44: u64, %45: u64):
    %157 = load u64, ptr %81
    %158 = trunc u64 %157 to u32
    %159 = const u32 64
    %160 = icmp ult u32 %158, %159
    condbr %160, bb12(%41, %42, %43, %44, %45, %158), bb22
bb12(%46: u64, %47: u64, %48: u64, %49: u64, %50: u64, %51: u32):
    %161 = zext u32 %51 to u64
    %162 = shl u64 %50, %161
    %163 = or u64 %49, %162
    %164 = const u64 2
    %165, %166 = add.overflow u64 %48, %164
    store u64 %165, ptr %82
    %167 = const i64 8
    %168 = gep i8, ptr %82, %167
    store bool %166, ptr %168
    %169 = const i64 8
    %170 = gep i8, ptr %82, %169
    %171 = load bool, ptr %170
    %172 = const bool false
    %173 = icmp eq bool %171, %172
    condbr %173, bb13(%46, %47, %163), bb22
bb13(%52: u64, %53: u64, %54: u64):
    %174 = load u64, ptr %82
    br bb14(%52, %53, %174, %54)
bb14(%55: u64, %56: u64, %57: u64, %58: u64):
    %175 = icmp ult u64 %57, %56
    condbr %175, bb15(%55, %57, %58), bb21(%58)
bb15(%59: u64, %60: u64, %61: u64):
    %176, %177 = add.overflow u64 %59, %60
    store u64 %176, ptr %83
    %178 = const i64 8
    %179 = gep i8, ptr %83, %178
    store bool %177, ptr %179
    %180 = const i64 8
    %181 = gep i8, ptr %83, %180
    %182 = load bool, ptr %181
    %183 = const bool false
    %184 = icmp eq bool %182, %183
    condbr %184, bb16(%60, %61), bb22
bb16(%62: u64, %63: u64):
    %185 = load u64, ptr %83
    %186 = const i64 8
    %187 = gep i8, ptr %0, %186
    %188 = load u64, ptr %187
    %189 = icmp ult u64 %185, %188
    condbr %189, bb17(%62, %63, %185), bb22
bb17(%64: u64, %65: u64, %66: u64):
    %190 = load ptr, ptr %0
    %191 = gep u8, ptr %190, %66
    %192 = load u8, ptr %191
    %193 = zext u8 %192 to u64
    %194 = const u64 8
    %195, %196 = mul.overflow u64 %64, %194
    store u64 %195, ptr %84
    %197 = const i64 8
    %198 = gep i8, ptr %84, %197
    store bool %196, ptr %198
    %199 = const i64 8
    %200 = gep i8, ptr %84, %199
    %201 = load bool, ptr %200
    %202 = const bool false
    %203 = icmp eq bool %201, %202
    condbr %203, bb18(%64, %65, %193), bb22
bb18(%67: u64, %68: u64, %69: u64):
    %204 = load u64, ptr %84
    %205 = trunc u64 %204 to u32
    %206 = const u32 64
    %207 = icmp ult u32 %205, %206
    condbr %207, bb19(%67, %68, %69, %205), bb22
bb19(%70: u64, %71: u64, %72: u64, %73: u32):
    %208 = zext u32 %73 to u64
    %209 = shl u64 %72, %208
    %210 = or u64 %71, %209
    %211 = const u64 1
    %212, %213 = add.overflow u64 %70, %211
    store u64 %212, ptr %85
    %214 = const i64 8
    %215 = gep i8, ptr %85, %214
    store bool %213, ptr %215
    %216 = const i64 8
    %217 = gep i8, ptr %85, %216
    %218 = load bool, ptr %217
    %219 = const bool false
    %220 = icmp eq bool %218, %219
    condbr %220, bb20(%210), bb22
bb20(%74: u64):
    %221 = load u64, ptr %85
    br bb21(%74)
bb21(%75: u64):
    ret %75
bb22:
    unreachable
}

fn @load_u64_le(functy.13) {
bb0(%0: ptr, %1: u64):
    %56 = alloca (i64, i64), align 8
    %57 = alloca (i64, i64), align 8
    %58 = alloca (i64, i64), align 8
    %59 = alloca (i64, i64), align 8
    %60 = alloca (i64, i64), align 8
    %61 = alloca (i64, i64), align 8
    %62 = alloca (i64, i64), align 8
    %63 = const i64 8
    %64 = gep i8, ptr %0, %63
    %65 = load u64, ptr %64
    %66 = icmp ult u64 %1, %65
    condbr %66, bb1(%1), bb23
bb1(%2: u64):
    %67 = load ptr, ptr %0
    %68 = gep u8, ptr %67, %2
    %69 = load u8, ptr %68
    %70 = zext u8 %69 to u64
    %71 = const u64 1
    %72, %73 = add.overflow u64 %2, %71
    store u64 %72, ptr %56
    %74 = const i64 8
    %75 = gep i8, ptr %56, %74
    store bool %73, ptr %75
    %76 = const i64 8
    %77 = gep i8, ptr %56, %76
    %78 = load bool, ptr %77
    %79 = const bool false
    %80 = icmp eq bool %78, %79
    condbr %80, bb2(%2, %70), bb23
bb2(%3: u64, %4: u64):
    %81 = load u64, ptr %56
    %82 = const i64 8
    %83 = gep i8, ptr %0, %82
    %84 = load u64, ptr %83
    %85 = icmp ult u64 %81, %84
    condbr %85, bb3(%3, %4, %81), bb23
bb3(%5: u64, %6: u64, %7: u64):
    %86 = load ptr, ptr %0
    %87 = gep u8, ptr %86, %7
    %88 = load u8, ptr %87
    %89 = zext u8 %88 to u64
    %90 = const u32 8
    %91 = const u32 64
    %92 = icmp ult u32 %90, %91
    condbr %92, bb4(%5, %6, %89), bb23
bb4(%8: u64, %9: u64, %10: u64):
    %93 = const u32 8
    %94 = zext u32 %93 to u64
    %95 = shl u64 %10, %94
    %96 = or u64 %9, %95
    %97 = const u64 2
    %98, %99 = add.overflow u64 %8, %97
    store u64 %98, ptr %57
    %100 = const i64 8
    %101 = gep i8, ptr %57, %100
    store bool %99, ptr %101
    %102 = const i64 8
    %103 = gep i8, ptr %57, %102
    %104 = load bool, ptr %103
    %105 = const bool false
    %106 = icmp eq bool %104, %105
    condbr %106, bb5(%8, %96), bb23
bb5(%11: u64, %12: u64):
    %107 = load u64, ptr %57
    %108 = const i64 8
    %109 = gep i8, ptr %0, %108
    %110 = load u64, ptr %109
    %111 = icmp ult u64 %107, %110
    condbr %111, bb6(%11, %12, %107), bb23
bb6(%13: u64, %14: u64, %15: u64):
    %112 = load ptr, ptr %0
    %113 = gep u8, ptr %112, %15
    %114 = load u8, ptr %113
    %115 = zext u8 %114 to u64
    %116 = const u32 16
    %117 = const u32 64
    %118 = icmp ult u32 %116, %117
    condbr %118, bb7(%13, %14, %115), bb23
bb7(%16: u64, %17: u64, %18: u64):
    %119 = const u32 16
    %120 = zext u32 %119 to u64
    %121 = shl u64 %18, %120
    %122 = or u64 %17, %121
    %123 = const u64 3
    %124, %125 = add.overflow u64 %16, %123
    store u64 %124, ptr %58
    %126 = const i64 8
    %127 = gep i8, ptr %58, %126
    store bool %125, ptr %127
    %128 = const i64 8
    %129 = gep i8, ptr %58, %128
    %130 = load bool, ptr %129
    %131 = const bool false
    %132 = icmp eq bool %130, %131
    condbr %132, bb8(%16, %122), bb23
bb8(%19: u64, %20: u64):
    %133 = load u64, ptr %58
    %134 = const i64 8
    %135 = gep i8, ptr %0, %134
    %136 = load u64, ptr %135
    %137 = icmp ult u64 %133, %136
    condbr %137, bb9(%19, %20, %133), bb23
bb9(%21: u64, %22: u64, %23: u64):
    %138 = load ptr, ptr %0
    %139 = gep u8, ptr %138, %23
    %140 = load u8, ptr %139
    %141 = zext u8 %140 to u64
    %142 = const u32 24
    %143 = const u32 64
    %144 = icmp ult u32 %142, %143
    condbr %144, bb10(%21, %22, %141), bb23
bb10(%24: u64, %25: u64, %26: u64):
    %145 = const u32 24
    %146 = zext u32 %145 to u64
    %147 = shl u64 %26, %146
    %148 = or u64 %25, %147
    %149 = const u64 4
    %150, %151 = add.overflow u64 %24, %149
    store u64 %150, ptr %59
    %152 = const i64 8
    %153 = gep i8, ptr %59, %152
    store bool %151, ptr %153
    %154 = const i64 8
    %155 = gep i8, ptr %59, %154
    %156 = load bool, ptr %155
    %157 = const bool false
    %158 = icmp eq bool %156, %157
    condbr %158, bb11(%24, %148), bb23
bb11(%27: u64, %28: u64):
    %159 = load u64, ptr %59
    %160 = const i64 8
    %161 = gep i8, ptr %0, %160
    %162 = load u64, ptr %161
    %163 = icmp ult u64 %159, %162
    condbr %163, bb12(%27, %28, %159), bb23
bb12(%29: u64, %30: u64, %31: u64):
    %164 = load ptr, ptr %0
    %165 = gep u8, ptr %164, %31
    %166 = load u8, ptr %165
    %167 = zext u8 %166 to u64
    %168 = const u32 32
    %169 = const u32 64
    %170 = icmp ult u32 %168, %169
    condbr %170, bb13(%29, %30, %167), bb23
bb13(%32: u64, %33: u64, %34: u64):
    %171 = const u32 32
    %172 = zext u32 %171 to u64
    %173 = shl u64 %34, %172
    %174 = or u64 %33, %173
    %175 = const u64 5
    %176, %177 = add.overflow u64 %32, %175
    store u64 %176, ptr %60
    %178 = const i64 8
    %179 = gep i8, ptr %60, %178
    store bool %177, ptr %179
    %180 = const i64 8
    %181 = gep i8, ptr %60, %180
    %182 = load bool, ptr %181
    %183 = const bool false
    %184 = icmp eq bool %182, %183
    condbr %184, bb14(%32, %174), bb23
bb14(%35: u64, %36: u64):
    %185 = load u64, ptr %60
    %186 = const i64 8
    %187 = gep i8, ptr %0, %186
    %188 = load u64, ptr %187
    %189 = icmp ult u64 %185, %188
    condbr %189, bb15(%35, %36, %185), bb23
bb15(%37: u64, %38: u64, %39: u64):
    %190 = load ptr, ptr %0
    %191 = gep u8, ptr %190, %39
    %192 = load u8, ptr %191
    %193 = zext u8 %192 to u64
    %194 = const u32 40
    %195 = const u32 64
    %196 = icmp ult u32 %194, %195
    condbr %196, bb16(%37, %38, %193), bb23
bb16(%40: u64, %41: u64, %42: u64):
    %197 = const u32 40
    %198 = zext u32 %197 to u64
    %199 = shl u64 %42, %198
    %200 = or u64 %41, %199
    %201 = const u64 6
    %202, %203 = add.overflow u64 %40, %201
    store u64 %202, ptr %61
    %204 = const i64 8
    %205 = gep i8, ptr %61, %204
    store bool %203, ptr %205
    %206 = const i64 8
    %207 = gep i8, ptr %61, %206
    %208 = load bool, ptr %207
    %209 = const bool false
    %210 = icmp eq bool %208, %209
    condbr %210, bb17(%40, %200), bb23
bb17(%43: u64, %44: u64):
    %211 = load u64, ptr %61
    %212 = const i64 8
    %213 = gep i8, ptr %0, %212
    %214 = load u64, ptr %213
    %215 = icmp ult u64 %211, %214
    condbr %215, bb18(%43, %44, %211), bb23
bb18(%45: u64, %46: u64, %47: u64):
    %216 = load ptr, ptr %0
    %217 = gep u8, ptr %216, %47
    %218 = load u8, ptr %217
    %219 = zext u8 %218 to u64
    %220 = const u32 48
    %221 = const u32 64
    %222 = icmp ult u32 %220, %221
    condbr %222, bb19(%45, %46, %219), bb23
bb19(%48: u64, %49: u64, %50: u64):
    %223 = const u32 48
    %224 = zext u32 %223 to u64
    %225 = shl u64 %50, %224
    %226 = or u64 %49, %225
    %227 = const u64 7
    %228, %229 = add.overflow u64 %48, %227
    store u64 %228, ptr %62
    %230 = const i64 8
    %231 = gep i8, ptr %62, %230
    store bool %229, ptr %231
    %232 = const i64 8
    %233 = gep i8, ptr %62, %232
    %234 = load bool, ptr %233
    %235 = const bool false
    %236 = icmp eq bool %234, %235
    condbr %236, bb20(%226), bb23
bb20(%51: u64):
    %237 = load u64, ptr %62
    %238 = const i64 8
    %239 = gep i8, ptr %0, %238
    %240 = load u64, ptr %239
    %241 = icmp ult u64 %237, %240
    condbr %241, bb21(%51, %237), bb23
bb21(%52: u64, %53: u64):
    %242 = load ptr, ptr %0
    %243 = gep u8, ptr %242, %53
    %244 = load u8, ptr %243
    %245 = zext u8 %244 to u64
    %246 = const u32 56
    %247 = const u32 64
    %248 = icmp ult u32 %246, %247
    condbr %248, bb22(%52, %245), bb23
bb22(%54: u64, %55: u64):
    %249 = const u32 56
    %250 = zext u32 %249 to u64
    %251 = shl u64 %55, %250
    %252 = or u64 %54, %251
    ret %252
bb23:
    unreachable
}

fn @sip_compress(functy.14) {
bb0(%0: ptr):
    %21 = load u64, ptr %0
    %22 = const i64 16
    %23 = gep i8, ptr %0, %22
    %24 = load u64, ptr %23
    %25 = call @func.17(%21, %24)
    br bb1(%0, %25)
bb1(%1: ptr, %2: u64):
    store u64 %2, ptr %1
    %26 = const i64 8
    %27 = gep i8, ptr %1, %26
    %28 = load u64, ptr %27
    %29 = const i64 24
    %30 = gep i8, ptr %1, %29
    %31 = load u64, ptr %30
    %32 = call @func.17(%28, %31)
    br bb2(%1, %32)
bb2(%3: ptr, %4: u64):
    %33 = const i64 8
    %34 = gep i8, ptr %3, %33
    store u64 %4, ptr %34
    %35 = const i64 16
    %36 = gep i8, ptr %3, %35
    %37 = load u64, ptr %36
    %38 = const u32 13
    %39 = call @func.18(%37, %38)
    br bb3(%3, %39)
bb3(%5: ptr, %6: u64):
    %40 = const i64 16
    %41 = gep i8, ptr %5, %40
    store u64 %6, ptr %41
    %42 = load u64, ptr %5
    %43 = const i64 16
    %44 = gep i8, ptr %5, %43
    %45 = load u64, ptr %44
    %46 = xor u64 %45, %42
    %47 = const i64 16
    %48 = gep i8, ptr %5, %47
    store u64 %46, ptr %48
    %49 = const i64 24
    %50 = gep i8, ptr %5, %49
    %51 = load u64, ptr %50
    %52 = const u32 16
    %53 = call @func.18(%51, %52)
    br bb4(%5, %53)
bb4(%7: ptr, %8: u64):
    %54 = const i64 24
    %55 = gep i8, ptr %7, %54
    store u64 %8, ptr %55
    %56 = const i64 8
    %57 = gep i8, ptr %7, %56
    %58 = load u64, ptr %57
    %59 = const i64 24
    %60 = gep i8, ptr %7, %59
    %61 = load u64, ptr %60
    %62 = xor u64 %61, %58
    %63 = const i64 24
    %64 = gep i8, ptr %7, %63
    store u64 %62, ptr %64
    %65 = load u64, ptr %7
    %66 = const u32 32
    %67 = call @func.18(%65, %66)
    br bb5(%7, %67)
bb5(%9: ptr, %10: u64):
    store u64 %10, ptr %9
    %68 = const i64 8
    %69 = gep i8, ptr %9, %68
    %70 = load u64, ptr %69
    %71 = const i64 16
    %72 = gep i8, ptr %9, %71
    %73 = load u64, ptr %72
    %74 = call @func.17(%70, %73)
    br bb6(%9, %74)
bb6(%11: ptr, %12: u64):
    %75 = const i64 8
    %76 = gep i8, ptr %11, %75
    store u64 %12, ptr %76
    %77 = load u64, ptr %11
    %78 = const i64 24
    %79 = gep i8, ptr %11, %78
    %80 = load u64, ptr %79
    %81 = call @func.17(%77, %80)
    br bb7(%11, %81)
bb7(%13: ptr, %14: u64):
    store u64 %14, ptr %13
    %82 = const i64 16
    %83 = gep i8, ptr %13, %82
    %84 = load u64, ptr %83
    %85 = const u32 17
    %86 = call @func.18(%84, %85)
    br bb8(%13, %86)
bb8(%15: ptr, %16: u64):
    %87 = const i64 16
    %88 = gep i8, ptr %15, %87
    store u64 %16, ptr %88
    %89 = const i64 8
    %90 = gep i8, ptr %15, %89
    %91 = load u64, ptr %90
    %92 = const i64 16
    %93 = gep i8, ptr %15, %92
    %94 = load u64, ptr %93
    %95 = xor u64 %94, %91
    %96 = const i64 16
    %97 = gep i8, ptr %15, %96
    store u64 %95, ptr %97
    %98 = const i64 24
    %99 = gep i8, ptr %15, %98
    %100 = load u64, ptr %99
    %101 = const u32 21
    %102 = call @func.18(%100, %101)
    br bb9(%15, %102)
bb9(%17: ptr, %18: u64):
    %103 = const i64 24
    %104 = gep i8, ptr %17, %103
    store u64 %18, ptr %104
    %105 = load u64, ptr %17
    %106 = const i64 24
    %107 = gep i8, ptr %17, %106
    %108 = load u64, ptr %107
    %109 = xor u64 %108, %105
    %110 = const i64 24
    %111 = gep i8, ptr %17, %110
    store u64 %109, ptr %111
    %112 = const i64 8
    %113 = gep i8, ptr %17, %112
    %114 = load u64, ptr %113
    %115 = const u32 32
    %116 = call @func.18(%114, %115)
    br bb10(%17, %116)
bb10(%19: ptr, %20: u64):
    %117 = const i64 8
    %118 = gep i8, ptr %19, %117
    store u64 %20, ptr %118
    ret
}

fn @load_u32_le(functy.15) {
bb0(%0: ptr, %1: u64):
    %24 = alloca (i64, i64), align 8
    %25 = alloca (i64, i64), align 8
    %26 = alloca (i64, i64), align 8
    %27 = const i64 8
    %28 = gep i8, ptr %0, %27
    %29 = load u64, ptr %28
    %30 = icmp ult u64 %1, %29
    condbr %30, bb1(%1), bb11
bb1(%2: u64):
    %31 = load ptr, ptr %0
    %32 = gep u8, ptr %31, %2
    %33 = load u8, ptr %32
    %34 = zext u8 %33 to u64
    %35 = const u64 1
    %36, %37 = add.overflow u64 %2, %35
    store u64 %36, ptr %24
    %38 = const i64 8
    %39 = gep i8, ptr %24, %38
    store bool %37, ptr %39
    %40 = const i64 8
    %41 = gep i8, ptr %24, %40
    %42 = load bool, ptr %41
    %43 = const bool false
    %44 = icmp eq bool %42, %43
    condbr %44, bb2(%2, %34), bb11
bb2(%3: u64, %4: u64):
    %45 = load u64, ptr %24
    %46 = const i64 8
    %47 = gep i8, ptr %0, %46
    %48 = load u64, ptr %47
    %49 = icmp ult u64 %45, %48
    condbr %49, bb3(%3, %4, %45), bb11
bb3(%5: u64, %6: u64, %7: u64):
    %50 = load ptr, ptr %0
    %51 = gep u8, ptr %50, %7
    %52 = load u8, ptr %51
    %53 = zext u8 %52 to u64
    %54 = const u32 8
    %55 = const u32 64
    %56 = icmp ult u32 %54, %55
    condbr %56, bb4(%5, %6, %53), bb11
bb4(%8: u64, %9: u64, %10: u64):
    %57 = const u32 8
    %58 = zext u32 %57 to u64
    %59 = shl u64 %10, %58
    %60 = or u64 %9, %59
    %61 = const u64 2
    %62, %63 = add.overflow u64 %8, %61
    store u64 %62, ptr %25
    %64 = const i64 8
    %65 = gep i8, ptr %25, %64
    store bool %63, ptr %65
    %66 = const i64 8
    %67 = gep i8, ptr %25, %66
    %68 = load bool, ptr %67
    %69 = const bool false
    %70 = icmp eq bool %68, %69
    condbr %70, bb5(%8, %60), bb11
bb5(%11: u64, %12: u64):
    %71 = load u64, ptr %25
    %72 = const i64 8
    %73 = gep i8, ptr %0, %72
    %74 = load u64, ptr %73
    %75 = icmp ult u64 %71, %74
    condbr %75, bb6(%11, %12, %71), bb11
bb6(%13: u64, %14: u64, %15: u64):
    %76 = load ptr, ptr %0
    %77 = gep u8, ptr %76, %15
    %78 = load u8, ptr %77
    %79 = zext u8 %78 to u64
    %80 = const u32 16
    %81 = const u32 64
    %82 = icmp ult u32 %80, %81
    condbr %82, bb7(%13, %14, %79), bb11
bb7(%16: u64, %17: u64, %18: u64):
    %83 = const u32 16
    %84 = zext u32 %83 to u64
    %85 = shl u64 %18, %84
    %86 = or u64 %17, %85
    %87 = const u64 3
    %88, %89 = add.overflow u64 %16, %87
    store u64 %88, ptr %26
    %90 = const i64 8
    %91 = gep i8, ptr %26, %90
    store bool %89, ptr %91
    %92 = const i64 8
    %93 = gep i8, ptr %26, %92
    %94 = load bool, ptr %93
    %95 = const bool false
    %96 = icmp eq bool %94, %95
    condbr %96, bb8(%86), bb11
bb8(%19: u64):
    %97 = load u64, ptr %26
    %98 = const i64 8
    %99 = gep i8, ptr %0, %98
    %100 = load u64, ptr %99
    %101 = icmp ult u64 %97, %100
    condbr %101, bb9(%19, %97), bb11
bb9(%20: u64, %21: u64):
    %102 = load ptr, ptr %0
    %103 = gep u8, ptr %102, %21
    %104 = load u8, ptr %103
    %105 = zext u8 %104 to u64
    %106 = const u32 24
    %107 = const u32 64
    %108 = icmp ult u32 %106, %107
    condbr %108, bb10(%20, %105), bb11
bb10(%22: u64, %23: u64):
    %109 = const u32 24
    %110 = zext u32 %109 to u64
    %111 = shl u64 %23, %110
    %112 = or u64 %22, %111
    %113 = trunc u64 %112 to u32
    ret %113
bb11:
    unreachable
}

fn @load_u16_le(functy.16) {
bb0(%0: ptr, %1: u64):
    %8 = alloca (i64, i64), align 8
    %9 = const i64 8
    %10 = gep i8, ptr %0, %9
    %11 = load u64, ptr %10
    %12 = icmp ult u64 %1, %11
    condbr %12, bb1(%1), bb5
bb1(%2: u64):
    %13 = load ptr, ptr %0
    %14 = gep u8, ptr %13, %2
    %15 = load u8, ptr %14
    %16 = zext u8 %15 to u64
    %17 = const u64 1
    %18, %19 = add.overflow u64 %2, %17
    store u64 %18, ptr %8
    %20 = const i64 8
    %21 = gep i8, ptr %8, %20
    store bool %19, ptr %21
    %22 = const i64 8
    %23 = gep i8, ptr %8, %22
    %24 = load bool, ptr %23
    %25 = const bool false
    %26 = icmp eq bool %24, %25
    condbr %26, bb2(%16), bb5
bb2(%3: u64):
    %27 = load u64, ptr %8
    %28 = const i64 8
    %29 = gep i8, ptr %0, %28
    %30 = load u64, ptr %29
    %31 = icmp ult u64 %27, %30
    condbr %31, bb3(%3, %27), bb5
bb3(%4: u64, %5: u64):
    %32 = load ptr, ptr %0
    %33 = gep u8, ptr %32, %5
    %34 = load u8, ptr %33
    %35 = zext u8 %34 to u64
    %36 = const u32 8
    %37 = const u32 64
    %38 = icmp ult u32 %36, %37
    condbr %38, bb4(%4, %35), bb5
bb4(%6: u64, %7: u64):
    %39 = const u32 8
    %40 = zext u32 %39 to u64
    %41 = shl u64 %7, %40
    %42 = or u64 %6, %41
    %43 = trunc u64 %42 to u16
    ret %43
bb5:
    unreachable
}

fn @w_add(functy.17) {
bb0(%0: u64, %1: u64):
    %16 = alloca (i64, i64), align 8
    %17 = alloca (i64, i64), align 8
    %18 = alloca (i64, i64), align 8
    %19 = const u64 4294967295
    %20 = and u64 %0, %19
    %21 = const u64 4294967295
    %22 = and u64 %1, %21
    %23, %24 = add.overflow u64 %20, %22
    store u64 %23, ptr %16
    %25 = const i64 8
    %26 = gep i8, ptr %16, %25
    store bool %24, ptr %26
    %27 = const i64 8
    %28 = gep i8, ptr %16, %27
    %29 = load bool, ptr %28
    %30 = const bool false
    %31 = icmp eq bool %29, %30
    condbr %31, bb1(%0, %1), bb8
bb1(%2: u64, %3: u64):
    %32 = load u64, ptr %16
    %33 = const i32 32
    %34 = bitcast i32 %33 to u32
    %35 = const u32 64
    %36 = icmp ult u32 %34, %35
    condbr %36, bb2(%2, %3, %32), bb8
bb2(%4: u64, %5: u64, %6: u64):
    %37 = const i32 32
    %38 = zext i32 %37 to u64
    %39 = lshr u64 %4, %38
    %40 = const i32 32
    %41 = bitcast i32 %40 to u32
    %42 = const u32 64
    %43 = icmp ult u32 %41, %42
    condbr %43, bb3(%5, %6, %39), bb8
bb3(%7: u64, %8: u64, %9: u64):
    %44 = const i32 32
    %45 = zext i32 %44 to u64
    %46 = lshr u64 %7, %45
    %47, %48 = add.overflow u64 %9, %46
    store u64 %47, ptr %17
    %49 = const i64 8
    %50 = gep i8, ptr %17, %49
    store bool %48, ptr %50
    %51 = const i64 8
    %52 = gep i8, ptr %17, %51
    %53 = load bool, ptr %52
    %54 = const bool false
    %55 = icmp eq bool %53, %54
    condbr %55, bb4(%8), bb8
bb4(%10: u64):
    %56 = load u64, ptr %17
    %57 = const i32 32
    %58 = bitcast i32 %57 to u32
    %59 = const u32 64
    %60 = icmp ult u32 %58, %59
    condbr %60, bb5(%10, %56), bb8
bb5(%11: u64, %12: u64):
    %61 = const i32 32
    %62 = zext i32 %61 to u64
    %63 = lshr u64 %11, %62
    %64, %65 = add.overflow u64 %12, %63
    store u64 %64, ptr %18
    %66 = const i64 8
    %67 = gep i8, ptr %18, %66
    store bool %65, ptr %67
    %68 = const i64 8
    %69 = gep i8, ptr %18, %68
    %70 = load bool, ptr %69
    %71 = const bool false
    %72 = icmp eq bool %70, %71
    condbr %72, bb6(%11), bb8
bb6(%13: u64):
    %73 = load u64, ptr %18
    %74 = const i32 32
    %75 = bitcast i32 %74 to u32
    %76 = const u32 64
    %77 = icmp ult u32 %75, %76
    condbr %77, bb7(%13, %73), bb8
bb7(%14: u64, %15: u64):
    %78 = const i32 32
    %79 = zext i32 %78 to u64
    %80 = shl u64 %15, %79
    %81 = const u64 4294967295
    %82 = and u64 %14, %81
    %83 = or u64 %80, %82
    ret %83
bb8:
    unreachable
}

fn @rotl(functy.18) {
bb0(%0: u64, %1: u32):
    %9 = alloca (i32, i32), align 4
    %10 = const u32 64
    %11 = icmp ult u32 %1, %10
    condbr %11, bb1(%0, %1), bb4
bb1(%2: u64, %3: u32):
    %12 = zext u32 %3 to u64
    %13 = shl u64 %2, %12
    %14 = const u32 64
    %15, %16 = sub.overflow u32 %14, %3
    store u32 %15, ptr %9
    %17 = const i64 4
    %18 = gep i8, ptr %9, %17
    store bool %16, ptr %18
    %19 = const i64 4
    %20 = gep i8, ptr %9, %19
    %21 = load bool, ptr %20
    %22 = const bool false
    %23 = icmp eq bool %21, %22
    condbr %23, bb2(%2, %13), bb4
bb2(%4: u64, %5: u64):
    %24 = load u32, ptr %9
    %25 = const u32 64
    %26 = icmp ult u32 %24, %25
    condbr %26, bb3(%4, %5, %24), bb4
bb3(%6: u64, %7: u64, %8: u32):
    %27 = zext u32 %8 to u64
    %28 = lshr u64 %6, %27
    %29 = or u64 %7, %28
    ret %29
bb4:
    unreachable
}
"##;

const META_SIP_MODULE: &str = r##"; TrustIr text format v1
module "mir::closure::meta_sip_root"
target "aarch64-apple-darwin" 8 little
file 0 "clean_siphash_slice.rs"

functy.0 = (ptr) -> ()

functy.1 = (ptr, ptr) -> ()

functy.2 = (ptr, ptr, u64) -> ()

functy.3 = (ptr) -> ()

functy.4 = (ptr, u64) -> ()

functy.5 = (ptr, ptr, u64) -> ()

functy.6 = (ptr, ptr) -> ()

functy.7 = (ptr, ptr) -> ()

functy.8 = (ptr, ptr) -> ()

functy.9 = (u64, u64, u64, u64, ptr, u64) -> (u64)

functy.10 = (ptr) -> ()

functy.11 = (ptr, ptr) -> ()

functy.12 = (ptr, ptr) -> ()

functy.13 = (u64) -> (u64)

functy.14 = (ptr, ptr) -> ()

functy.15 = (ptr, u64) -> ()

functy.16 = (ptr, ptr, ptr) -> ()

functy.17 = (ptr, ptr, ptr) -> ()

functy.18 = (ptr) -> (u64)

functy.19 = (ptr) -> (u64)

functy.20 = (ptr) -> (u64)

functy.21 = (ptr) -> (u64)

functy.22 = (ptr, u64) -> (ptr)

functy.23 = (ptr, ptr) -> ()

functy.24 = (ptr) -> (u64)

functy.25 = (ptr, ptr) -> ()

functy.26 = (ptr) -> (u64)

functy.27 = (ptr, u64) -> (ptr)

functy.28 = (u32, u32) -> (u32)

functy.29 = (ptr, ptr) -> ()

functy.30 = (ptr) -> ()

functy.31 = (ptr, ptr) -> ()

functy.32 = (ptr) -> (u64)

functy.33 = (ptr, u64) -> ()

functy.34 = (ptr, u64) -> ()

functy.35 = (ptr, ptr) -> ()

functy.36 = (u64, u64) -> (u64)

functy.37 = (u64, u64) -> (u64)

functy.38 = (ptr) -> (bool)

functy.39 = (ptr) -> (bool)

functy.40 = (u32, u32) -> (u32)

functy.41 = (ptr, u32, u32, u32, bool, bool, bool, bool) -> ()

functy.42 = (u64) -> (u8)

functy.43 = (u64) -> (u32)

functy.44 = (u64) -> (u32)

functy.45 = (u64) -> (bool)

functy.46 = (u64) -> (bool)

functy.47 = (u64) -> (bool)

functy.48 = (u64) -> (bool)

functy.49 = (ptr) -> ()

functy.50 = (ptr) -> ()

functy.51 = (ptr, ptr) -> ()

functy.52 = (ptr, u8) -> ()

functy.53 = (ptr) -> ()

functy.54 = (ptr, u64, u64) -> (u64)

functy.55 = (ptr, u64) -> (u64)

functy.56 = (u64, u64) -> (u64)

functy.57 = (u64, u32) -> (u64)

functy.58 = (ptr, u64) -> (u32)

functy.59 = (ptr, u64) -> (u16)

fn @_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNtCs6Skw9Chgdp8_19clean_siphash_slice5LevelE3newBE_(functy.0) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6Skw9Chgdp8_19clean_siphash_slice5LevelE4pushBH_(functy.1) {
}

fn @_RINvNtNtCs2EYQwhfuABO_4core5slice3raw14from_raw_partsyECs6Skw9Chgdp8_19clean_siphash_slice(functy.2) {
}

fn @_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecyE3newCs6Skw9Chgdp8_19clean_siphash_slice(functy.3) {
}

fn @_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecyE4pushCs6Skw9Chgdp8_19clean_siphash_slice(functy.4) {
}

fn @_RINvNtNtCs2EYQwhfuABO_4core5slice3raw14from_raw_partshECs6Skw9Chgdp8_19clean_siphash_slice(functy.5) {
}

fn @_RNvNtNtCs2EYQwhfuABO_4core3str8converts19from_utf8_uncheckedCs6Skw9Chgdp8_19clean_siphash_slice(functy.6) {
}

fn @_RNvXs17_NtCskTzINo8ZBH9_5alloc4syncINtB6_3ArceEINtNtCs2EYQwhfuABO_4core7convert4FromReE4fromCs6Skw9Chgdp8_19clean_siphash_slice(functy.7) {
}

fn @_RNvXs7_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6Skw9Chgdp8_19clean_siphash_slice5LevelENtNtNtCs2EYQwhfuABO_4core3ops5deref5Deref5derefBH_(functy.8) {
}

fn @meta_sip_root(functy.9) {
bb0(%0: u64, %1: u64, %2: u64, %3: u64, %4: ptr, %5: u64):
    %172 = alloca i64, align 8
    %173 = alloca (i64, i64, i64, i64, i64), align 8
    %174 = alloca (i64, i64, i64, i64), align 8
    %175 = alloca (i64, i64, i64), align 8
    %176 = alloca i64, align 8
    %177 = alloca (i64, i64, i64, i64, i64), align 8
    %178 = alloca (i64, i64, i64, i64), align 8
    %179 = alloca (i64, i64, i64), align 8
    %180 = alloca (i64, i64, i64), align 8
    %181 = alloca i64, align 8
    %182 = alloca (i64, i64, i64, i64, i64), align 8
    %183 = alloca (i64, i64, i64, i64), align 8
    %184 = alloca (i64, i64, i64), align 8
    %185 = alloca i64, align 8
    %186 = alloca i64, align 8
    %187 = alloca (i64, i64, i64, i64, i64), align 8
    %188 = alloca (i64, i64, i64, i64), align 8
    %189 = alloca (i64, i64, i64), align 8
    %190 = alloca (i64, i64, i64), align 8
    %191 = alloca (i64, i64, i64), align 8
    %192 = alloca (i64, i64, i64), align 8
    %193 = alloca i64, align 8
    %194 = alloca i64, align 8
    %195 = alloca (i64, i64, i64, i64, i64), align 8
    %196 = alloca (i64, i64, i64, i64), align 8
    %197 = alloca (i64, i64, i64), align 8
    %198 = alloca (i64, i64, i64), align 8
    %199 = alloca i64, align 8
    %200 = alloca (i64, i64, i64), align 8
    %201 = alloca i64, align 8
    %202 = alloca (i64, i64, i64), align 8
    %203 = alloca i64, align 8
    %204 = alloca (i64, i64, i64, i64, i64), align 8
    %205 = alloca (i64, i64, i64, i64), align 8
    %206 = alloca i64, align 8
    %207 = alloca (i64, i64, i64), align 8
    %208 = alloca (i64, i64, i64), align 8
    %209 = alloca (i64, i64, i64), align 8
    %210 = alloca i64, align 8
    %211 = alloca (i64, i64, i64), align 8
    %212 = alloca i64, align 8
    %213 = alloca (i64, i64, i64, i64, i64), align 8
    %214 = alloca (i64, i64, i64, i64), align 8
    %215 = alloca i64, align 8
    %216 = alloca (i64, i64, i64), align 8
    %217 = alloca i64, align 8
    %218 = alloca (i64, i64, i64, i64, i64), align 8
    %219 = alloca (i64, i64, i64, i64), align 8
    %220 = alloca (i64, i64, i64), align 8
    %221 = alloca (i64, i64, i64), align 8
    %222 = alloca (i64, i64), align 8
    %223 = alloca (i64, i64, i64), align 8
    %224 = alloca (i64, i64), align 8
    %225 = alloca i64, align 8
    %226 = alloca (i64, i64, i64, i64, i64), align 8
    %227 = alloca (i64, i64, i64, i64), align 8
    %228 = alloca (i64, i64, i64), align 8
    %229 = alloca (i64, i64, i64), align 8
    %230 = alloca (i64, i64, i64), align 8
    %231 = alloca (i64, i64), align 8
    %232 = alloca (i64, i64), align 8
    %233 = alloca (i64, i64), align 8
    %234 = alloca i64, align 8
    %235 = alloca (i64, i64, i64, i64, i64), align 8
    %236 = alloca (i64, i64, i64, i64), align 8
    %237 = alloca (i64, i64, i64), align 8
    %238 = alloca (i64, i64, i64, i64, i64), align 8
    %239 = alloca (i64, i64, i64, i64), align 8
    %240 = alloca (i64, i64, i64), align 8
    %241 = alloca (i64, i64, i64), align 8
    %242 = alloca i64, align 8
    %243 = alloca (i64, i64, i64, i64, i64), align 8
    %244 = alloca (i64, i64, i64, i64), align 8
    %245 = alloca i64, align 8
    %246 = alloca i64, align 8
    %247 = alloca i64, align 8
    %248 = alloca (i64, i64, i64, i64, i64), align 8
    %249 = alloca (i64, i64, i64, i64), align 8
    %250 = alloca (i64, i64, i64), align 8
    %251 = alloca (i64, i64, i64), align 8
    %252 = alloca i64, align 8
    %253 = alloca (i64, i64, i64), align 8
    %254 = alloca (i64, i64, i64), align 8
    %255 = alloca (i64, i64, i64), align 8
    %256 = alloca i64, align 8
    %257 = alloca i64, align 8
    %258 = alloca (i64, i64, i64), align 8
    %259 = alloca (i64, i64), align 8
    %260 = alloca (i64, i64, i64), align 8
    %261 = alloca (i64, i64, i64), align 8
    %262 = alloca (i64, i64, i64), align 8
    %263 = alloca i64, align 8
    %264 = alloca (i64, i64, i64), align 8
    %265 = alloca (i64, i64), align 8
    %266 = alloca (i64, i64, i64), align 8
    %267 = alloca (i64, i64, i64), align 8
    %268 = alloca (i64, i64), align 8
    %269 = alloca (i64, i64), align 8
    %270 = alloca (i64, i64), align 8
    %271 = alloca (i64, i64, i64), align 8
    %272 = const bool false
    %273 = const bool false
    %274 = const bool false
    %275 = const bool false
    %276 = const u64 0
    %277 = icmp eq u64 %0, %276
    condbr %277, bb1, bb6(%0, %1, %2, %3, %4, %5)
bb1:
    call @func.10(%175)
    br bb2
bb2:
    %278 = const i64 8
    %279 = gep i8, ptr %174, %278
    %280 = load i64, ptr %175
    store i64 %280, ptr %279
    %281 = const i64 8
    %282 = gep i8, ptr %175, %281
    %283 = const i64 8
    %284 = gep i8, ptr %279, %283
    %285 = load i64, ptr %282
    store i64 %285, ptr %284
    %286 = const i64 16
    %287 = gep i8, ptr %175, %286
    %288 = const i64 16
    %289 = gep i8, ptr %279, %288
    %290 = load i64, ptr %287
    store i64 %290, ptr %289
    %291 = const i64 -9223372036854775808
    store i64 %291, ptr %174
    call @func.11(%173, %174)
    br bb3
bb3:
    call @func.12(%172, %173)
    br bb4
bb4:
    %292 = load u64, ptr %172
    %293 = call @func.13(%292)
    br bb5(%293)
bb5(%6: u64):
    br bb129(%6)
bb6(%7: u64, %8: u64, %9: u64, %10: u64, %11: ptr, %12: u64):
    %294 = const u64 1
    %295 = icmp eq u64 %7, %294
    condbr %295, bb7, bb13(%7, %8, %9, %10, %11, %12)
bb7:
    call @func.10(%180)
    br bb8
bb8:
    call @func.14(%179, %180)
    br bb9
bb9:
    %296 = const i64 8
    %297 = gep i8, ptr %178, %296
    %298 = load i64, ptr %179
    store i64 %298, ptr %297
    %299 = const i64 8
    %300 = gep i8, ptr %179, %299
    %301 = const i64 8
    %302 = gep i8, ptr %297, %301
    %303 = load i64, ptr %300
    store i64 %303, ptr %302
    %304 = const i64 16
    %305 = gep i8, ptr %179, %304
    %306 = const i64 16
    %307 = gep i8, ptr %297, %306
    %308 = load i64, ptr %305
    store i64 %308, ptr %307
    %309 = const i64 -9223372036854775808
    store i64 %309, ptr %178
    call @func.11(%177, %178)
    br bb10
bb10:
    call @func.12(%176, %177)
    br bb11
bb11:
    %310 = load u64, ptr %176
    %311 = call @func.13(%310)
    br bb12(%311)
bb12(%13: u64):
    br bb129(%13)
bb13(%14: u64, %15: u64, %16: u64, %17: u64, %18: ptr, %19: u64):
    %312 = const u64 2
    %313 = icmp eq u64 %14, %312
    condbr %313, bb14(%15), bb19(%14, %15, %16, %17, %18, %19)
bb14(%20: u64):
    store u64 %20, ptr %185
    %314 = load u64, ptr %185
    call @func.15(%184, %314)
    br bb15
bb15:
    %315 = const i64 8
    %316 = gep i8, ptr %183, %315
    %317 = load i64, ptr %184
    store i64 %317, ptr %316
    %318 = const i64 8
    %319 = gep i8, ptr %184, %318
    %320 = const i64 8
    %321 = gep i8, ptr %316, %320
    %322 = load i64, ptr %319
    store i64 %322, ptr %321
    %323 = const i64 16
    %324 = gep i8, ptr %184, %323
    %325 = const i64 16
    %326 = gep i8, ptr %316, %325
    %327 = load i64, ptr %324
    store i64 %327, ptr %326
    %328 = const i64 -9223372036854775808
    store i64 %328, ptr %183
    call @func.11(%182, %183)
    br bb16
bb16:
    call @func.12(%181, %182)
    br bb17
bb17:
    %329 = load u64, ptr %181
    %330 = call @func.13(%329)
    br bb18(%330)
bb18(%21: u64):
    br bb129(%21)
bb19(%22: u64, %23: u64, %24: u64, %25: u64, %26: ptr, %27: u64):
    %331 = const u64 3
    %332 = icmp eq u64 %22, %331
    condbr %332, bb20(%23), bb28(%22, %23, %24, %25, %26, %27)
bb20(%28: u64):
    call @func.10(%191)
    br bb21(%28)
bb21(%29: u64):
    call @func.14(%190, %191)
    br bb22(%29)
bb22(%30: u64):
    %333 = const bool true
    store u64 %30, ptr %193
    %334 = load u64, ptr %193
    call @func.15(%192, %334)
    br bb23
bb23:
    %335 = const bool false
    call @func.16(%189, %190, %192)
    br bb24
bb24:
    %336 = const bool false
    %337 = const i64 8
    %338 = gep i8, ptr %188, %337
    %339 = load i64, ptr %189
    store i64 %339, ptr %338
    %340 = const i64 8
    %341 = gep i8, ptr %189, %340
    %342 = const i64 8
    %343 = gep i8, ptr %338, %342
    %344 = load i64, ptr %341
    store i64 %344, ptr %343
    %345 = const i64 16
    %346 = gep i8, ptr %189, %345
    %347 = const i64 16
    %348 = gep i8, ptr %338, %347
    %349 = load i64, ptr %346
    store i64 %349, ptr %348
    %350 = const i64 -9223372036854775808
    store i64 %350, ptr %188
    call @func.11(%187, %188)
    br bb25
bb25:
    call @func.12(%186, %187)
    br bb26
bb26:
    %351 = load u64, ptr %186
    %352 = call @func.13(%351)
    br bb27(%352)
bb27(%31: u64):
    br bb129(%31)
bb28(%32: u64, %33: u64, %34: u64, %35: u64, %36: ptr, %37: u64):
    %353 = const u64 4
    %354 = icmp eq u64 %32, %353
    condbr %354, bb29(%33, %34), bb36(%32, %33, %34, %35, %36, %37)
bb29(%38: u64, %39: u64):
    store u64 %38, ptr %199
    %355 = const bool true
    %356 = load u64, ptr %199
    call @func.15(%198, %356)
    br bb30(%39)
bb30(%40: u64):
    store u64 %40, ptr %201
    %357 = load u64, ptr %201
    call @func.15(%200, %357)
    br bb31
bb31:
    %358 = const bool false
    call @func.17(%197, %198, %200)
    br bb32
bb32:
    %359 = const bool false
    %360 = const i64 8
    %361 = gep i8, ptr %196, %360
    %362 = load i64, ptr %197
    store i64 %362, ptr %361
    %363 = const i64 8
    %364 = gep i8, ptr %197, %363
    %365 = const i64 8
    %366 = gep i8, ptr %361, %365
    %367 = load i64, ptr %364
    store i64 %367, ptr %366
    %368 = const i64 16
    %369 = gep i8, ptr %197, %368
    %370 = const i64 16
    %371 = gep i8, ptr %361, %370
    %372 = load i64, ptr %369
    store i64 %372, ptr %371
    %373 = const i64 -9223372036854775808
    store i64 %373, ptr %196
    call @func.11(%195, %196)
    br bb33
bb33:
    call @func.12(%194, %195)
    br bb34
bb34:
    %374 = load u64, ptr %194
    %375 = call @func.13(%374)
    br bb35(%375)
bb35(%41: u64):
    br bb129(%41)
bb36(%42: u64, %43: u64, %44: u64, %45: u64, %46: ptr, %47: u64):
    %376 = const u64 5
    %377 = icmp eq u64 %42, %376
    condbr %377, bb37(%43), bb42(%42, %43, %44, %45, %46, %47)
bb37(%48: u64):
    call @func.0(%202)
    br bb38(%48)
bb38(%49: u64):
    store u64 %49, ptr %206
    %378 = const i64 24
    %379 = gep i8, ptr %205, %378
    %380 = load i64, ptr %206
    store i64 %380, ptr %379
    %381 = load i64, ptr %202
    store i64 %381, ptr %205
    %382 = const i64 8
    %383 = gep i8, ptr %202, %382
    %384 = const i64 8
    %385 = gep i8, ptr %205, %384
    %386 = load i64, ptr %383
    store i64 %386, ptr %385
    %387 = const i64 16
    %388 = gep i8, ptr %202, %387
    %389 = const i64 16
    %390 = gep i8, ptr %205, %389
    %391 = load i64, ptr %388
    store i64 %391, ptr %390
    call @func.11(%204, %205)
    br bb39
bb39:
    call @func.12(%203, %204)
    br bb40
bb40:
    %392 = load u64, ptr %203
    %393 = call @func.13(%392)
    br bb41(%393)
bb41(%50: u64):
    br bb129(%50)
bb42(%51: u64, %52: u64, %53: u64, %54: u64, %55: ptr, %56: u64):
    %394 = const u64 6
    %395 = icmp eq u64 %51, %394
    condbr %395, bb43(%52, %53), bb53(%51, %52, %53, %54, %55, %56)
bb43(%57: u64, %58: u64):
    %396 = const bool true
    call @func.0(%207)
    br bb44(%57, %58)
bb44(%59: u64, %60: u64):
    store u64 %60, ptr %210
    %397 = load u64, ptr %210
    call @func.15(%209, %397)
    br bb45(%59, %207)
bb45(%61: u64, %62: ptr):
    call @func.14(%208, %209)
    br bb46(%61, %62)
bb46(%63: u64, %64: ptr):
    call @func.1(%64, %208)
    br bb47(%63)
bb47(%65: u64):
    call @func.10(%211)
    br bb48(%65, %207)
bb48(%66: u64, %67: ptr):
    call @func.1(%67, %211)
    br bb49(%66)
bb49(%68: u64):
    store u64 %68, ptr %215
    %398 = const bool false
    %399 = load i64, ptr %207
    store i64 %399, ptr %216
    %400 = const i64 8
    %401 = gep i8, ptr %207, %400
    %402 = const i64 8
    %403 = gep i8, ptr %216, %402
    %404 = load i64, ptr %401
    store i64 %404, ptr %403
    %405 = const i64 16
    %406 = gep i8, ptr %207, %405
    %407 = const i64 16
    %408 = gep i8, ptr %216, %407
    %409 = load i64, ptr %406
    store i64 %409, ptr %408
    %410 = const i64 24
    %411 = gep i8, ptr %214, %410
    %412 = load i64, ptr %215
    store i64 %412, ptr %411
    %413 = load i64, ptr %216
    store i64 %413, ptr %214
    %414 = const i64 8
    %415 = gep i8, ptr %216, %414
    %416 = const i64 8
    %417 = gep i8, ptr %214, %416
    %418 = load i64, ptr %415
    store i64 %418, ptr %417
    %419 = const i64 16
    %420 = gep i8, ptr %216, %419
    %421 = const i64 16
    %422 = gep i8, ptr %214, %421
    %423 = load i64, ptr %420
    store i64 %423, ptr %422
    call @func.11(%213, %214)
    br bb50
bb50:
    call @func.12(%212, %213)
    br bb51
bb51:
    %424 = load u64, ptr %212
    %425 = call @func.13(%424)
    br bb52(%425)
bb52(%69: u64):
    %426 = const bool false
    br bb129(%69)
bb53(%70: u64, %71: u64, %72: u64, %73: u64, %74: ptr, %75: u64):
    %427 = const u64 7
    %428 = icmp eq u64 %70, %427
    condbr %428, bb54(%71), bb58(%70, %71, %72, %73, %74, %75)
bb54(%76: u64):
    %429 = const i64 8
    %430 = gep i8, ptr %221, %429
    store u64 %76, ptr %430
    %431 = const i64 -9223372036854775808
    store i64 %431, ptr %221
    %432 = load i64, ptr %221
    store i64 %432, ptr %220
    %433 = const i64 8
    %434 = gep i8, ptr %221, %433
    %435 = const i64 8
    %436 = gep i8, ptr %220, %435
    %437 = load i64, ptr %434
    store i64 %437, ptr %436
    %438 = const i64 16
    %439 = gep i8, ptr %221, %438
    %440 = const i64 16
    %441 = gep i8, ptr %220, %440
    %442 = load i64, ptr %439
    store i64 %442, ptr %441
    %443 = const i64 8
    %444 = gep i8, ptr %219, %443
    %445 = load i64, ptr %220
    store i64 %445, ptr %444
    %446 = const i64 8
    %447 = gep i8, ptr %220, %446
    %448 = const i64 8
    %449 = gep i8, ptr %444, %448
    %450 = load i64, ptr %447
    store i64 %450, ptr %449
    %451 = const i64 16
    %452 = gep i8, ptr %220, %451
    %453 = const i64 16
    %454 = gep i8, ptr %444, %453
    %455 = load i64, ptr %452
    store i64 %455, ptr %454
    %456 = const i64 -9223372036854775806
    store i64 %456, ptr %219
    call @func.11(%218, %219)
    br bb55
bb55:
    call @func.12(%217, %218)
    br bb56
bb56:
    %457 = load u64, ptr %217
    %458 = call @func.13(%457)
    br bb57(%458)
bb57(%77: u64):
    br bb129(%77)
bb58(%78: u64, %79: u64, %80: u64, %81: u64, %82: ptr, %83: u64):
    %459 = const u64 8
    %460 = icmp eq u64 %78, %459
    condbr %460, bb59(%82, %83), bb71(%78, %79, %80, %81, %82, %83)
bb59(%84: ptr, %85: u64):
    call @func.2(%222, %84, %85)
    br bb60
bb60:
    %461 = const bool true
    call @func.3(%223)
    br bb61
bb61:
    %462 = const u64 0
    br bb62(%462)
bb62(%86: u64):
    %463 = const i64 8
    %464 = gep i8, ptr %222, %463
    %465 = load u64, ptr %464
    %466 = icmp ult u64 %86, %465
    condbr %466, bb63(%86), bb67
bb63(%87: u64):
    %467 = const i64 8
    %468 = gep i8, ptr %222, %467
    %469 = load u64, ptr %468
    %470 = icmp ult u64 %87, %469
    condbr %470, bb64(%87, %223, %87), bb131
bb64(%88: u64, %89: ptr, %90: u64):
    %471 = load ptr, ptr %222
    %472 = gep u64, ptr %471, %90
    %473 = load u64, ptr %472
    call @func.4(%89, %473)
    br bb65(%88)
bb65(%91: u64):
    %474 = const u64 1
    %475, %476 = add.overflow u64 %91, %474
    store u64 %475, ptr %224
    %477 = const i64 8
    %478 = gep i8, ptr %224, %477
    store bool %476, ptr %478
    %479 = const i64 8
    %480 = gep i8, ptr %224, %479
    %481 = load bool, ptr %480
    %482 = const bool false
    %483 = icmp eq bool %481, %482
    condbr %483, bb66, bb131
bb66:
    %484 = load u64, ptr %224
    br bb62(%484)
bb67:
    %485 = const bool false
    %486 = load i64, ptr %223
    store i64 %486, ptr %230
    %487 = const i64 8
    %488 = gep i8, ptr %223, %487
    %489 = const i64 8
    %490 = gep i8, ptr %230, %489
    %491 = load i64, ptr %488
    store i64 %491, ptr %490
    %492 = const i64 16
    %493 = gep i8, ptr %223, %492
    %494 = const i64 16
    %495 = gep i8, ptr %230, %494
    %496 = load i64, ptr %493
    store i64 %496, ptr %495
    %497 = load i64, ptr %230
    store i64 %497, ptr %229
    %498 = const i64 8
    %499 = gep i8, ptr %230, %498
    %500 = const i64 8
    %501 = gep i8, ptr %229, %500
    %502 = load i64, ptr %499
    store i64 %502, ptr %501
    %503 = const i64 16
    %504 = gep i8, ptr %230, %503
    %505 = const i64 16
    %506 = gep i8, ptr %229, %505
    %507 = load i64, ptr %504
    store i64 %507, ptr %506
    %508 = load i64, ptr %229
    store i64 %508, ptr %228
    %509 = const i64 8
    %510 = gep i8, ptr %229, %509
    %511 = const i64 8
    %512 = gep i8, ptr %228, %511
    %513 = load i64, ptr %510
    store i64 %513, ptr %512
    %514 = const i64 16
    %515 = gep i8, ptr %229, %514
    %516 = const i64 16
    %517 = gep i8, ptr %228, %516
    %518 = load i64, ptr %515
    store i64 %518, ptr %517
    %519 = const i64 8
    %520 = gep i8, ptr %227, %519
    %521 = load i64, ptr %228
    store i64 %521, ptr %520
    %522 = const i64 8
    %523 = gep i8, ptr %228, %522
    %524 = const i64 8
    %525 = gep i8, ptr %520, %524
    %526 = load i64, ptr %523
    store i64 %526, ptr %525
    %527 = const i64 16
    %528 = gep i8, ptr %228, %527
    %529 = const i64 16
    %530 = gep i8, ptr %520, %529
    %531 = load i64, ptr %528
    store i64 %531, ptr %530
    %532 = const i64 -9223372036854775806
    store i64 %532, ptr %227
    call @func.11(%226, %227)
    br bb68
bb68:
    call @func.12(%225, %226)
    br bb69
bb69:
    %533 = load u64, ptr %225
    %534 = call @func.13(%533)
    br bb70(%534)
bb70(%92: u64):
    %535 = const bool false
    br bb129(%92)
bb71(%93: u64, %94: u64, %95: u64, %96: u64, %97: ptr, %98: u64):
    %536 = const u64 9
    %537 = icmp eq u64 %93, %536
    condbr %537, bb72(%97, %98), bb79(%93, %94, %95, %96, %97, %98)
bb72(%99: ptr, %100: u64):
    call @func.5(%231, %99, %100)
    br bb73
bb73:
    call @func.6(%232, %231)
    br bb74
bb74:
    call @func.7(%233, %232)
    br bb75
bb75:
    %538 = const i64 8
    %539 = gep i8, ptr %237, %538
    %540 = load i64, ptr %233
    store i64 %540, ptr %539
    %541 = const i64 8
    %542 = gep i8, ptr %233, %541
    %543 = const i64 8
    %544 = gep i8, ptr %539, %543
    %545 = load i64, ptr %542
    store i64 %545, ptr %544
    %546 = const i64 -9223372036854775807
    store i64 %546, ptr %237
    %547 = const i64 8
    %548 = gep i8, ptr %236, %547
    %549 = load i64, ptr %237
    store i64 %549, ptr %548
    %550 = const i64 8
    %551 = gep i8, ptr %237, %550
    %552 = const i64 8
    %553 = gep i8, ptr %548, %552
    %554 = load i64, ptr %551
    store i64 %554, ptr %553
    %555 = const i64 16
    %556 = gep i8, ptr %237, %555
    %557 = const i64 16
    %558 = gep i8, ptr %548, %557
    %559 = load i64, ptr %556
    store i64 %559, ptr %558
    %560 = const i64 -9223372036854775806
    store i64 %560, ptr %236
    call @func.11(%235, %236)
    br bb76
bb76:
    call @func.12(%234, %235)
    br bb77
bb77:
    %561 = load u64, ptr %234
    %562 = call @func.13(%561)
    br bb78(%562)
bb78(%101: u64):
    br bb129(%101)
bb79(%102: u64, %103: u64, %104: u64, %105: u64, %106: ptr, %107: u64):
    %563 = const u64 10
    %564 = icmp eq u64 %102, %563
    condbr %564, bb80(%103, %104, %105), bb86(%102, %103, %104, %106, %107)
bb80(%108: u64, %109: u64, %110: u64):
    %565 = const i64 8
    %566 = gep i8, ptr %241, %565
    store u64 %110, ptr %566
    %567 = const i64 -9223372036854775808
    store i64 %567, ptr %241
    %568 = load i64, ptr %241
    store i64 %568, ptr %240
    %569 = const i64 8
    %570 = gep i8, ptr %241, %569
    %571 = const i64 8
    %572 = gep i8, ptr %240, %571
    %573 = load i64, ptr %570
    store i64 %573, ptr %572
    %574 = const i64 16
    %575 = gep i8, ptr %241, %574
    %576 = const i64 16
    %577 = gep i8, ptr %240, %576
    %578 = load i64, ptr %575
    store i64 %578, ptr %577
    %579 = const i64 8
    %580 = gep i8, ptr %239, %579
    %581 = load i64, ptr %240
    store i64 %581, ptr %580
    %582 = const i64 8
    %583 = gep i8, ptr %240, %582
    %584 = const i64 8
    %585 = gep i8, ptr %580, %584
    %586 = load i64, ptr %583
    store i64 %586, ptr %585
    %587 = const i64 16
    %588 = gep i8, ptr %240, %587
    %589 = const i64 16
    %590 = gep i8, ptr %580, %589
    %591 = load i64, ptr %588
    store i64 %591, ptr %590
    %592 = const i64 -9223372036854775806
    store i64 %592, ptr %239
    call @func.11(%238, %239)
    br bb81(%108, %109)
bb81(%111: u64, %112: u64):
    store u64 %111, ptr %245
    %593 = trunc u64 %112 to u32
    %594 = const i64 56
    %595 = heap_alloc rust_heap i8, %594, align 8
    %596 = const u64 1
    store u64 %596, ptr %595
    %597 = const i64 8
    %598 = gep i8, ptr %595, %597
    %599 = const u64 1
    store u64 %599, ptr %598
    %600 = const i64 16
    %601 = gep i8, ptr %595, %600
    %602 = load i64, ptr %238
    store i64 %602, ptr %601
    %603 = const i64 8
    %604 = gep i8, ptr %238, %603
    %605 = const i64 8
    %606 = gep i8, ptr %601, %605
    %607 = load i64, ptr %604
    store i64 %607, ptr %606
    %608 = const i64 16
    %609 = gep i8, ptr %238, %608
    %610 = const i64 16
    %611 = gep i8, ptr %601, %610
    %612 = load i64, ptr %609
    store i64 %612, ptr %611
    %613 = const i64 24
    %614 = gep i8, ptr %238, %613
    %615 = const i64 24
    %616 = gep i8, ptr %601, %615
    %617 = load i64, ptr %614
    store i64 %617, ptr %616
    %618 = const i64 32
    %619 = gep i8, ptr %238, %618
    %620 = const i64 32
    %621 = gep i8, ptr %601, %620
    %622 = load i64, ptr %619
    store i64 %622, ptr %621
    store ptr %595, ptr %246
    br bb82(%593)
bb82(%113: u32):
    %623 = const i64 16
    %624 = gep i8, ptr %244, %623
    %625 = load i64, ptr %245
    store i64 %625, ptr %624
    %626 = const i64 24
    %627 = gep i8, ptr %244, %626
    store u32 %113, ptr %627
    %628 = load ptr, ptr %246
    %629 = const i64 8
    %630 = gep i8, ptr %244, %629
    store ptr %628, ptr %630
    %631 = const i64 -9223372036854775805
    store i64 %631, ptr %244
    call @func.11(%243, %244)
    br bb83
bb83:
    call @func.12(%242, %243)
    br bb84
bb84:
    %632 = load u64, ptr %242
    %633 = call @func.13(%632)
    br bb85(%633)
bb85(%114: u64):
    br bb129(%114)
bb86(%115: u64, %116: u64, %117: u64, %118: ptr, %119: u64):
    %634 = const u64 11
    %635 = icmp eq u64 %115, %634
    condbr %635, bb87(%116), bb93(%115, %116, %117, %118, %119)
bb87(%120: u64):
    store u64 %120, ptr %252
    %636 = load u64, ptr %252
    call @func.15(%251, %636)
    br bb88
bb88:
    call @func.14(%250, %251)
    br bb89
bb89:
    %637 = const i64 8
    %638 = gep i8, ptr %249, %637
    %639 = load i64, ptr %250
    store i64 %639, ptr %638
    %640 = const i64 8
    %641 = gep i8, ptr %250, %640
    %642 = const i64 8
    %643 = gep i8, ptr %638, %642
    %644 = load i64, ptr %641
    store i64 %644, ptr %643
    %645 = const i64 16
    %646 = gep i8, ptr %250, %645
    %647 = const i64 16
    %648 = gep i8, ptr %638, %647
    %649 = load i64, ptr %646
    store i64 %649, ptr %648
    %650 = const i64 -9223372036854775808
    store i64 %650, ptr %249
    call @func.11(%248, %249)
    br bb90
bb90:
    call @func.12(%247, %248)
    br bb91
bb91:
    %651 = load u64, ptr %247
    %652 = call @func.13(%651)
    br bb92(%652)
bb92(%121: u64):
    br bb129(%121)
bb93(%122: u64, %123: u64, %124: u64, %125: ptr, %126: u64):
    %653 = const u64 20
    %654 = icmp eq u64 %122, %653
    condbr %654, bb94, bb97(%122, %123, %124, %125, %126)
bb94:
    call @func.10(%253)
    br bb95
bb95:
    %655 = call @func.18(%253)
    br bb96(%655)
bb96(%127: u64):
    br bb129(%127)
bb97(%128: u64, %129: u64, %130: u64, %131: ptr, %132: u64):
    %656 = const u64 21
    %657 = icmp eq u64 %128, %656
    condbr %657, bb98(%129), bb102(%128, %129, %130, %131, %132)
bb98(%133: u64):
    store u64 %133, ptr %256
    %658 = load u64, ptr %256
    call @func.15(%255, %658)
    br bb99
bb99:
    call @func.14(%254, %255)
    br bb100
bb100:
    %659 = call @func.18(%254)
    br bb101(%659)
bb101(%134: u64):
    br bb129(%134)
bb102(%135: u64, %136: u64, %137: u64, %138: ptr, %139: u64):
    %660 = const u64 22
    %661 = icmp eq u64 %135, %660
    condbr %661, bb103(%136), bb104(%135, %136, %137, %138, %139)
bb103(%140: u64):
    store u64 %140, ptr %257
    %662 = call @func.19(%257)
    br bb130(%662)
bb104(%141: u64, %142: u64, %143: u64, %144: ptr, %145: u64):
    %663 = const u64 23
    %664 = icmp eq u64 %141, %663
    condbr %664, bb105, bb109(%141, %142, %143, %144, %145)
bb105:
    call @func.0(%258)
    br bb106
bb106:
    call @func.8(%259, %258)
    br bb107
bb107:
    %665 = call @func.20(%259)
    br bb108(%665)
bb108(%146: u64):
    br bb129(%146)
bb109(%147: u64, %148: u64, %149: u64, %150: ptr, %151: u64):
    %666 = const u64 24
    %667 = icmp eq u64 %147, %666
    condbr %667, bb110(%149), bb119(%147, %148, %150, %151)
bb110(%152: u64):
    call @func.0(%260)
    br bb111(%152)
bb111(%153: u64):
    store u64 %153, ptr %263
    %668 = load u64, ptr %263
    call @func.15(%262, %668)
    br bb112(%260)
bb112(%154: ptr):
    call @func.14(%261, %262)
    br bb113(%154)
bb113(%155: ptr):
    call @func.1(%155, %261)
    br bb114
bb114:
    call @func.10(%264)
    br bb115(%260)
bb115(%156: ptr):
    call @func.1(%156, %264)
    br bb116
bb116:
    call @func.8(%265, %260)
    br bb117
bb117:
    %669 = call @func.20(%265)
    br bb118(%669)
bb118(%157: u64):
    br bb129(%157)
bb119(%158: u64, %159: u64, %160: ptr, %161: u64):
    %670 = const u64 25
    %671 = icmp eq u64 %158, %670
    condbr %671, bb120(%159), bb122(%158, %160, %161)
bb120(%162: u64):
    %672 = const i64 8
    %673 = gep i8, ptr %267, %672
    store u64 %162, ptr %673
    %674 = const i64 -9223372036854775808
    store i64 %674, ptr %267
    %675 = load i64, ptr %267
    store i64 %675, ptr %266
    %676 = const i64 8
    %677 = gep i8, ptr %267, %676
    %678 = const i64 8
    %679 = gep i8, ptr %266, %678
    %680 = load i64, ptr %677
    store i64 %680, ptr %679
    %681 = const i64 16
    %682 = gep i8, ptr %267, %681
    %683 = const i64 16
    %684 = gep i8, ptr %266, %683
    %685 = load i64, ptr %682
    store i64 %685, ptr %684
    %686 = call @func.24(%266)
    br bb121(%686)
bb121(%163: u64):
    br bb129(%163)
bb122(%164: u64, %165: ptr, %166: u64):
    %687 = const u64 26
    %688 = icmp eq u64 %164, %687
    condbr %688, bb123(%165, %166), bb128
bb123(%167: ptr, %168: u64):
    call @func.5(%268, %167, %168)
    br bb124
bb124:
    call @func.6(%269, %268)
    br bb125
bb125:
    call @func.7(%270, %269)
    br bb126
bb126:
    %689 = const i64 8
    %690 = gep i8, ptr %271, %689
    %691 = load i64, ptr %270
    store i64 %691, ptr %690
    %692 = const i64 8
    %693 = gep i8, ptr %270, %692
    %694 = const i64 8
    %695 = gep i8, ptr %690, %694
    %696 = load i64, ptr %693
    store i64 %696, ptr %695
    %697 = const i64 -9223372036854775807
    store i64 %697, ptr %271
    %698 = call @func.24(%271)
    br bb127(%698)
bb127(%169: u64):
    br bb129(%169)
bb128:
    %699 = const u64 16045690984833335023
    br bb129(%699)
bb129(%170: u64):
    ret %170
bb130(%171: u64):
    br bb129(%171)
bb131:
    unreachable
}

fn @Level__zero(functy.10) {
bb0(%0: ptr):
    %1 = const i64 0
    store i64 %1, ptr %0
    ret
}

fn @Expr__from_kind(functy.11) {
bb0(%0: ptr, %1: ptr):
    %2 = alloca i64, align 8
    %3 = alloca (i64, i64, i64, i64), align 8
    call @func.29(%2, %1)
    br bb1
bb1:
    %4 = load i64, ptr %1
    store i64 %4, ptr %3
    %5 = const i64 8
    %6 = gep i8, ptr %1, %5
    %7 = const i64 8
    %8 = gep i8, ptr %3, %7
    %9 = load i64, ptr %6
    store i64 %9, ptr %8
    %10 = const i64 16
    %11 = gep i8, ptr %1, %10
    %12 = const i64 16
    %13 = gep i8, ptr %3, %12
    %14 = load i64, ptr %11
    store i64 %14, ptr %13
    %15 = const i64 24
    %16 = gep i8, ptr %1, %15
    %17 = const i64 24
    %18 = gep i8, ptr %3, %17
    %19 = load i64, ptr %16
    store i64 %19, ptr %18
    %20 = load i64, ptr %3
    store i64 %20, ptr %0
    %21 = const i64 8
    %22 = gep i8, ptr %3, %21
    %23 = const i64 8
    %24 = gep i8, ptr %0, %23
    %25 = load i64, ptr %22
    store i64 %25, ptr %24
    %26 = const i64 16
    %27 = gep i8, ptr %3, %26
    %28 = const i64 16
    %29 = gep i8, ptr %0, %28
    %30 = load i64, ptr %27
    store i64 %30, ptr %29
    %31 = const i64 24
    %32 = gep i8, ptr %3, %31
    %33 = const i64 24
    %34 = gep i8, ptr %0, %33
    %35 = load i64, ptr %32
    store i64 %35, ptr %34
    %36 = const i64 32
    %37 = gep i8, ptr %0, %36
    %38 = load i64, ptr %2
    store i64 %38, ptr %37
    ret
}

fn @Expr__meta(functy.12) {
bb0(%0: ptr, %1: ptr):
    %2 = const i64 32
    %3 = gep i8, ptr %1, %2
    %4 = load i64, ptr %3
    store i64 %4, ptr %0
    ret
}

fn @ExprMeta__raw(functy.13) {
bb0(%0: u64):
    %1 = alloca i64, align 8
    store u64 %0, ptr %1
    %2 = load u64, ptr %1
    ret %2
}

fn @Level__succ(functy.14) {
bb0(%0: ptr, %1: ptr):
    %2 = alloca i64, align 8
    %3 = const i64 40
    %4 = heap_alloc rust_heap i8, %3, align 8
    %5 = const u64 1
    store u64 %5, ptr %4
    %6 = const i64 8
    %7 = gep i8, ptr %4, %6
    %8 = const u64 1
    store u64 %8, ptr %7
    %9 = const i64 16
    %10 = gep i8, ptr %4, %9
    %11 = load i64, ptr %1
    store i64 %11, ptr %10
    %12 = const i64 8
    %13 = gep i8, ptr %1, %12
    %14 = const i64 8
    %15 = gep i8, ptr %10, %14
    %16 = load i64, ptr %13
    store i64 %16, ptr %15
    %17 = const i64 16
    %18 = gep i8, ptr %1, %17
    %19 = const i64 16
    %20 = gep i8, ptr %10, %19
    %21 = load i64, ptr %18
    store i64 %21, ptr %20
    store ptr %4, ptr %2
    br bb1
bb1:
    %22 = load ptr, ptr %2
    %23 = const i64 8
    %24 = gep i8, ptr %0, %23
    store ptr %22, ptr %24
    %25 = const i64 1
    store i64 %25, ptr %0
    ret
}

fn @Level__param(functy.15) {
bb0(%0: ptr, %1: u64):
    %2 = alloca i64, align 8
    store u64 %1, ptr %2
    %3 = const i64 8
    %4 = gep i8, ptr %0, %3
    %5 = load i64, ptr %2
    store i64 %5, ptr %4
    %6 = const i64 4
    store i64 %6, ptr %0
    ret
}

fn @Level__max_raw(functy.16) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %3 = alloca i64, align 8
    %4 = alloca i64, align 8
    %5 = alloca (i64, i64, i64), align 8
    %6 = const bool false
    %7 = const bool true
    %8 = const i64 40
    %9 = heap_alloc rust_heap i8, %8, align 8
    %10 = const u64 1
    store u64 %10, ptr %9
    %11 = const i64 8
    %12 = gep i8, ptr %9, %11
    %13 = const u64 1
    store u64 %13, ptr %12
    %14 = const i64 16
    %15 = gep i8, ptr %9, %14
    %16 = load i64, ptr %1
    store i64 %16, ptr %15
    %17 = const i64 8
    %18 = gep i8, ptr %1, %17
    %19 = const i64 8
    %20 = gep i8, ptr %15, %19
    %21 = load i64, ptr %18
    store i64 %21, ptr %20
    %22 = const i64 16
    %23 = gep i8, ptr %1, %22
    %24 = const i64 16
    %25 = gep i8, ptr %15, %24
    %26 = load i64, ptr %23
    store i64 %26, ptr %25
    store ptr %9, ptr %3
    br bb1
bb1:
    %27 = const bool false
    %28 = load i64, ptr %2
    store i64 %28, ptr %5
    %29 = const i64 8
    %30 = gep i8, ptr %2, %29
    %31 = const i64 8
    %32 = gep i8, ptr %5, %31
    %33 = load i64, ptr %30
    store i64 %33, ptr %32
    %34 = const i64 16
    %35 = gep i8, ptr %2, %34
    %36 = const i64 16
    %37 = gep i8, ptr %5, %36
    %38 = load i64, ptr %35
    store i64 %38, ptr %37
    %39 = const i64 40
    %40 = heap_alloc rust_heap i8, %39, align 8
    %41 = const u64 1
    store u64 %41, ptr %40
    %42 = const i64 8
    %43 = gep i8, ptr %40, %42
    %44 = const u64 1
    store u64 %44, ptr %43
    %45 = const i64 16
    %46 = gep i8, ptr %40, %45
    %47 = load i64, ptr %5
    store i64 %47, ptr %46
    %48 = const i64 8
    %49 = gep i8, ptr %5, %48
    %50 = const i64 8
    %51 = gep i8, ptr %46, %50
    %52 = load i64, ptr %49
    store i64 %52, ptr %51
    %53 = const i64 16
    %54 = gep i8, ptr %5, %53
    %55 = const i64 16
    %56 = gep i8, ptr %46, %55
    %57 = load i64, ptr %54
    store i64 %57, ptr %56
    store ptr %40, ptr %4
    br bb2
bb2:
    %58 = load ptr, ptr %3
    %59 = const i64 8
    %60 = gep i8, ptr %0, %59
    store ptr %58, ptr %60
    %61 = load ptr, ptr %4
    %62 = const i64 16
    %63 = gep i8, ptr %0, %62
    store ptr %61, ptr %63
    %64 = const i64 2
    store i64 %64, ptr %0
    ret
}

fn @Level__imax_raw(functy.17) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %3 = alloca i64, align 8
    %4 = alloca i64, align 8
    %5 = alloca (i64, i64, i64), align 8
    %6 = const bool false
    %7 = const bool true
    %8 = const i64 40
    %9 = heap_alloc rust_heap i8, %8, align 8
    %10 = const u64 1
    store u64 %10, ptr %9
    %11 = const i64 8
    %12 = gep i8, ptr %9, %11
    %13 = const u64 1
    store u64 %13, ptr %12
    %14 = const i64 16
    %15 = gep i8, ptr %9, %14
    %16 = load i64, ptr %1
    store i64 %16, ptr %15
    %17 = const i64 8
    %18 = gep i8, ptr %1, %17
    %19 = const i64 8
    %20 = gep i8, ptr %15, %19
    %21 = load i64, ptr %18
    store i64 %21, ptr %20
    %22 = const i64 16
    %23 = gep i8, ptr %1, %22
    %24 = const i64 16
    %25 = gep i8, ptr %15, %24
    %26 = load i64, ptr %23
    store i64 %26, ptr %25
    store ptr %9, ptr %3
    br bb1
bb1:
    %27 = const bool false
    %28 = load i64, ptr %2
    store i64 %28, ptr %5
    %29 = const i64 8
    %30 = gep i8, ptr %2, %29
    %31 = const i64 8
    %32 = gep i8, ptr %5, %31
    %33 = load i64, ptr %30
    store i64 %33, ptr %32
    %34 = const i64 16
    %35 = gep i8, ptr %2, %34
    %36 = const i64 16
    %37 = gep i8, ptr %5, %36
    %38 = load i64, ptr %35
    store i64 %38, ptr %37
    %39 = const i64 40
    %40 = heap_alloc rust_heap i8, %39, align 8
    %41 = const u64 1
    store u64 %41, ptr %40
    %42 = const i64 8
    %43 = gep i8, ptr %40, %42
    %44 = const u64 1
    store u64 %44, ptr %43
    %45 = const i64 16
    %46 = gep i8, ptr %40, %45
    %47 = load i64, ptr %5
    store i64 %47, ptr %46
    %48 = const i64 8
    %49 = gep i8, ptr %5, %48
    %50 = const i64 8
    %51 = gep i8, ptr %46, %50
    %52 = load i64, ptr %49
    store i64 %52, ptr %51
    %53 = const i64 16
    %54 = gep i8, ptr %5, %53
    %55 = const i64 16
    %56 = gep i8, ptr %46, %55
    %57 = load i64, ptr %54
    store i64 %57, ptr %56
    store ptr %40, ptr %4
    br bb2
bb2:
    %58 = load ptr, ptr %3
    %59 = const i64 8
    %60 = gep i8, ptr %0, %59
    store ptr %58, ptr %60
    %61 = load ptr, ptr %4
    %62 = const i64 16
    %63 = gep i8, ptr %0, %62
    store ptr %61, ptr %63
    %64 = const i64 3
    store i64 %64, ptr %0
    ret
}

fn @sip_hash_level(functy.18) {
bb0(%0: ptr):
    %3 = alloca (i64, i64, i64, i64, i64, i64, i64, i64, i64), align 8
    call @func.30(%3)
    br bb1(%0)
bb1(%1: ptr):
    call @func.31(%3, %1)
    br bb2
bb2:
    %4 = call @func.32(%3)
    br bb3(%4)
bb3(%2: u64):
    ret %2
}

fn @sip_hash_name(functy.19) {
bb0(%0: ptr):
    %3 = alloca (i64, i64, i64, i64, i64, i64, i64, i64, i64), align 8
    call @func.30(%3)
    br bb1(%0)
bb1(%1: ptr):
    %4 = load u64, ptr %1
    call @func.33(%3, %4)
    br bb2
bb2:
    %5 = call @func.32(%3)
    br bb3(%5)
bb3(%2: u64):
    ret %2
}

fn @sip_hash_levels(functy.20) {
bb0(%0: ptr):
    %8 = alloca (i64, i64, i64, i64, i64, i64, i64, i64, i64), align 8
    %9 = alloca (i64, i64), align 8
    call @func.30(%8)
    br bb1
bb1:
    %10 = const i64 8
    %11 = gep i8, ptr %0, %10
    %12 = load u64, ptr %11
    call @func.34(%8, %12)
    br bb2
bb2:
    %13 = const u64 0
    br bb3(%13)
bb3(%1: u64):
    %14 = const i64 8
    %15 = gep i8, ptr %0, %14
    %16 = load u64, ptr %15
    %17 = icmp ult u64 %1, %16
    condbr %17, bb4(%1), bb8
bb4(%2: u64):
    %18 = const i64 8
    %19 = gep i8, ptr %0, %18
    %20 = load u64, ptr %19
    %21 = icmp ult u64 %2, %20
    condbr %21, bb5(%2, %8, %2), bb10
bb5(%3: u64, %4: ptr, %5: u64):
    %22 = load ptr, ptr %0
    %23 = const u64 24
    %24 = mul u64 %5, %23
    %25 = gep i8, ptr %22, %24
    call @func.31(%4, %25)
    br bb6(%3)
bb6(%6: u64):
    %26 = const u64 1
    %27, %28 = add.overflow u64 %6, %26
    store u64 %27, ptr %9
    %29 = const i64 8
    %30 = gep i8, ptr %9, %29
    store bool %28, ptr %30
    %31 = const i64 8
    %32 = gep i8, ptr %9, %31
    %33 = load bool, ptr %32
    %34 = const bool false
    %35 = icmp eq bool %33, %34
    condbr %35, bb7, bb10
bb7:
    %36 = load u64, ptr %9
    br bb3(%36)
bb8:
    %37 = call @func.32(%8)
    br bb9(%37)
bb9(%7: u64):
    ret %7
bb10:
    unreachable
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecyE3lenCs6Skw9Chgdp8_19clean_siphash_slice(functy.21) {
}

fn @_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecyEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexCs6Skw9Chgdp8_19clean_siphash_slice(functy.22) {
}

fn @_RNvXsw_NtCskTzINo8ZBH9_5alloc4syncINtB5_3ArceENtNtNtCs2EYQwhfuABO_4core3ops5deref5Deref5derefCs6Skw9Chgdp8_19clean_siphash_slice(functy.23) {
}

fn @sip_hash_lit(functy.24) {
bb0(%0: ptr):
    %25 = alloca i64, align 8
    %26 = alloca (i64, i64, i64, i64, i64, i64, i64, i64, i64), align 8
    %27 = alloca i64, align 8
    %28 = alloca (i64, i64), align 8
    %29 = alloca (i64, i64), align 8
    %30 = alloca (i64, i64), align 8
    store ptr %0, ptr %25
    call @func.30(%26)
    br bb1
bb1:
    %31 = load ptr, ptr %25
    %32 = load i64, ptr %31
    %33 = const i64 -9223372036854775807
    %34 = icmp eq i64 %32, %33
    %35 = const i64 1
    %36 = const i64 0
    %37 = select i64 %34, %35, %36
    switch %37 [ 0: bb4 1: bb3 default: bb2 ]
bb2:
    unreachable
bb3:
    %38 = load ptr, ptr %25
    %39 = const i64 8
    %40 = gep i8, ptr %38, %39
    %41 = const u64 1
    call @func.34(%26, %41)
    br bb18(%40)
bb4:
    %42 = load ptr, ptr %25
    store ptr %42, ptr %27
    %43 = const u64 0
    call @func.34(%26, %43)
    br bb5
bb5:
    %44 = load ptr, ptr %27
    %45 = load i64, ptr %44
    %46 = const i64 -9223372036854775808
    %47 = icmp eq i64 %45, %46
    %48 = const i64 0
    %49 = const i64 1
    %50 = select i64 %47, %48, %49
    switch %50 [ 0: bb7 1: bb6 default: bb2 ]
bb6:
    %51 = load ptr, ptr %27
    %52 = const u64 1
    call @func.34(%26, %52)
    br bb9(%51)
bb7:
    %53 = load ptr, ptr %27
    %54 = const i64 8
    %55 = gep i8, ptr %53, %54
    %56 = const u64 0
    call @func.34(%26, %56)
    br bb8(%55)
bb8(%1: ptr):
    %57 = load u64, ptr %1
    call @func.33(%26, %57)
    br bb21
bb9(%2: ptr):
    %58 = call @func.21(%2)
    br bb10(%2, %26, %58)
bb10(%3: ptr, %4: ptr, %5: u64):
    call @func.34(%4, %5)
    br bb11(%3)
bb11(%6: ptr):
    %59 = const u64 0
    br bb12(%6, %59)
bb12(%7: ptr, %8: u64):
    %60 = call @func.21(%7)
    br bb13(%7, %8, %8, %60)
bb13(%9: ptr, %10: u64, %11: u64, %12: u64):
    %61 = icmp ult u64 %11, %12
    condbr %61, bb14(%9, %10), bb21
bb14(%13: ptr, %14: u64):
    %62 = call @func.22(%13, %14)
    br bb15(%13, %14, %26, %62)
bb15(%15: ptr, %16: u64, %17: ptr, %18: ptr):
    %63 = load u64, ptr %18
    call @func.33(%17, %63)
    br bb16(%15, %16)
bb16(%19: ptr, %20: u64):
    %64 = const u64 1
    %65, %66 = add.overflow u64 %20, %64
    store u64 %65, ptr %28
    %67 = const i64 8
    %68 = gep i8, ptr %28, %67
    store bool %66, ptr %68
    %69 = const i64 8
    %70 = gep i8, ptr %28, %69
    %71 = load bool, ptr %70
    %72 = const bool false
    %73 = icmp eq bool %71, %72
    condbr %73, bb17(%19), bb23
bb17(%21: ptr):
    %74 = load u64, ptr %28
    br bb12(%21, %74)
bb18(%22: ptr):
    call @func.23(%29, %22)
    br bb19
bb19:
    %75 = load i64, ptr %29
    store i64 %75, ptr %30
    %76 = const i64 8
    %77 = gep i8, ptr %29, %76
    %78 = const i64 8
    %79 = gep i8, ptr %30, %78
    %80 = load i64, ptr %77
    store i64 %80, ptr %79
    br bb20(%26)
bb20(%23: ptr):
    call @func.35(%23, %30)
    br bb21
bb21:
    %81 = call @func.32(%26)
    br bb22(%81)
bb22(%24: u64):
    ret %24
bb23:
    unreachable
}

fn @_RNvXs7_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6Skw9Chgdp8_19clean_siphash_slice5LevelENtNtNtCs2EYQwhfuABO_4core3ops5deref5Deref5derefBH_(functy.25) {
}

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCs6Skw9Chgdp8_19clean_siphash_slice5LevelE3lenBG_(functy.26) {
}

fn @_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs6Skw9Chgdp8_19clean_siphash_slice5LevelEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_(functy.27) {
}

fn @_RNvYmNtNtCs2EYQwhfuABO_4core3cmp3Ord3minCs6Skw9Chgdp8_19clean_siphash_slice(functy.28) {
}

fn @ExprKind__compute_meta(functy.29) {
bb0(%0: ptr, %1: ptr):
    %180 = alloca i64, align 8
    %181 = alloca (i64, i64), align 8
    %182 = alloca (i64, i64), align 8
    %183 = alloca (i64, i64), align 8
    %184 = alloca i64, align 8
    %185 = alloca (i32, i32), align 4
    store ptr %1, ptr %180
    %186 = load ptr, ptr %180
    %187 = load i64, ptr %186
    %188 = const i64 1
    %189 = const i64 -9223372036854775808
    %190 = icmp eq i64 %187, %189
    %191 = const i64 0
    %192 = select i64 %190, %191, %188
    %193 = const i64 -9223372036854775806
    %194 = icmp eq i64 %187, %193
    %195 = const i64 2
    %196 = select i64 %194, %195, %192
    %197 = const i64 -9223372036854775805
    %198 = icmp eq i64 %187, %197
    %199 = const i64 3
    %200 = select i64 %198, %199, %196
    switch %200 [ 0: bb5 1: bb4 2: bb3 3: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %201 = load ptr, ptr %180
    %202 = const i64 16
    %203 = gep i8, ptr %201, %202
    %204 = load ptr, ptr %180
    %205 = const i64 24
    %206 = gep i8, ptr %204, %205
    %207 = load ptr, ptr %180
    %208 = const i64 8
    %209 = gep i8, ptr %207, %208
    %210 = load ptr, ptr %209
    %211 = const i64 16
    %212 = gep i8, ptr %210, %211
    br bb35(%203, %206, %212)
bb3:
    %213 = load ptr, ptr %180
    %214 = const i64 8
    %215 = gep i8, ptr %213, %214
    %216 = call @func.24(%215)
    br bb33(%216)
bb4:
    %217 = load ptr, ptr %180
    %218 = const i64 24
    %219 = gep i8, ptr %217, %218
    %220 = load ptr, ptr %180
    %221 = call @func.19(%219)
    br bb10(%220, %221)
bb5:
    %222 = load ptr, ptr %180
    %223 = const i64 8
    %224 = gep i8, ptr %222, %223
    %225 = call @func.18(%224)
    br bb6(%224, %225)
bb6(%2: ptr, %3: u64):
    %226 = const u64 11
    %227 = call @func.37(%226, %3)
    br bb7(%2, %227)
bb7(%4: ptr, %5: u64):
    %228 = trunc u64 %5 to u32
    %229 = call @func.38(%4)
    br bb8(%4, %228, %229)
bb8(%6: ptr, %7: u32, %8: bool):
    %230 = call @func.39(%6)
    br bb9(%7, %8, %230)
bb9(%9: u32, %10: bool, %11: bool):
    %231 = const u32 0
    %232 = const u32 0
    %233 = const bool false
    %234 = const bool false
    call @func.41(%0, %9, %231, %232, %233, %234, %10, %11)
    br bb50
bb10(%12: ptr, %13: u64):
    call @func.25(%181, %12)
    br bb11(%12, %13)
bb11(%14: ptr, %15: u64):
    %235 = call @func.20(%181)
    br bb12(%14, %15, %235)
bb12(%16: ptr, %17: u64, %18: u64):
    %236 = const bool false
    %237 = const u64 0
    br bb13(%16, %17, %18, %236, %237)
bb13(%19: ptr, %20: u64, %21: u64, %22: bool, %23: u64):
    %238 = call @func.26(%19)
    br bb14(%19, %20, %21, %22, %23, %23, %238)
bb14(%24: ptr, %25: u64, %26: u64, %27: bool, %28: u64, %29: u64, %30: u64):
    %239 = icmp ult u64 %29, %30
    condbr %239, bb15(%24, %25, %26, %27, %28), bb21(%24, %25, %26, %27)
bb15(%31: ptr, %32: u64, %33: u64, %34: bool, %35: u64):
    %240 = call @func.27(%31, %35)
    br bb16(%31, %32, %33, %34, %35, %240)
bb16(%36: ptr, %37: u64, %38: u64, %39: bool, %40: u64, %41: ptr):
    %241 = call @func.39(%41)
    br bb17(%36, %37, %38, %39, %40, %241)
bb17(%42: ptr, %43: u64, %44: u64, %45: bool, %46: u64, %47: bool):
    condbr %47, bb18(%42, %43, %44), bb19(%42, %43, %44, %45, %46)
bb18(%48: ptr, %49: u64, %50: u64):
    %242 = const bool true
    br bb21(%48, %49, %50, %242)
bb19(%51: ptr, %52: u64, %53: u64, %54: bool, %55: u64):
    %243 = const u64 1
    %244, %245 = add.overflow u64 %55, %243
    store u64 %244, ptr %182
    %246 = const i64 8
    %247 = gep i8, ptr %182, %246
    store bool %245, ptr %247
    %248 = const i64 8
    %249 = gep i8, ptr %182, %248
    %250 = load bool, ptr %249
    %251 = const bool false
    %252 = icmp eq bool %250, %251
    condbr %252, bb20(%51, %52, %53, %54), bb51
bb20(%56: ptr, %57: u64, %58: u64, %59: bool):
    %253 = load u64, ptr %182
    br bb13(%56, %57, %58, %59, %253)
bb21(%60: ptr, %61: u64, %62: u64, %63: bool):
    %254 = const bool false
    %255 = const u64 0
    br bb22(%60, %61, %62, %63, %254, %255)
bb22(%64: ptr, %65: u64, %66: u64, %67: bool, %68: bool, %69: u64):
    %256 = call @func.26(%64)
    br bb23(%64, %65, %66, %67, %68, %69, %69, %256)
bb23(%70: ptr, %71: u64, %72: u64, %73: bool, %74: bool, %75: u64, %76: u64, %77: u64):
    %257 = icmp ult u64 %76, %77
    condbr %257, bb24(%70, %71, %72, %73, %74, %75), bb30(%71, %72, %73, %74)
bb24(%78: ptr, %79: u64, %80: u64, %81: bool, %82: bool, %83: u64):
    %258 = call @func.27(%78, %83)
    br bb25(%78, %79, %80, %81, %82, %83, %258)
bb25(%84: ptr, %85: u64, %86: u64, %87: bool, %88: bool, %89: u64, %90: ptr):
    %259 = call @func.38(%90)
    br bb26(%84, %85, %86, %87, %88, %89, %259)
bb26(%91: ptr, %92: u64, %93: u64, %94: bool, %95: bool, %96: u64, %97: bool):
    condbr %97, bb27(%92, %93, %94), bb28(%91, %92, %93, %94, %95, %96)
bb27(%98: u64, %99: u64, %100: bool):
    %260 = const bool true
    br bb30(%98, %99, %100, %260)
bb28(%101: ptr, %102: u64, %103: u64, %104: bool, %105: bool, %106: u64):
    %261 = const u64 1
    %262, %263 = add.overflow u64 %106, %261
    store u64 %262, ptr %183
    %264 = const i64 8
    %265 = gep i8, ptr %183, %264
    store bool %263, ptr %265
    %266 = const i64 8
    %267 = gep i8, ptr %183, %266
    %268 = load bool, ptr %267
    %269 = const bool false
    %270 = icmp eq bool %268, %269
    condbr %270, bb29(%101, %102, %103, %104, %105), bb51
bb29(%107: ptr, %108: u64, %109: u64, %110: bool, %111: bool):
    %271 = load u64, ptr %183
    br bb22(%107, %108, %109, %110, %111, %271)
bb30(%112: u64, %113: u64, %114: bool, %115: bool):
    %272 = call @func.37(%112, %113)
    br bb31(%114, %115, %272)
bb31(%116: bool, %117: bool, %118: u64):
    %273 = const u64 5
    %274 = call @func.37(%273, %118)
    br bb32(%116, %117, %274)
bb32(%119: bool, %120: bool, %121: u64):
    %275 = trunc u64 %121 to u32
    %276 = const u32 0
    %277 = const u32 0
    %278 = const bool false
    %279 = const bool false
    call @func.41(%0, %275, %276, %277, %278, %279, %120, %119)
    br bb50
bb33(%122: u64):
    %280 = const u64 3
    %281 = call @func.37(%280, %122)
    br bb34(%281)
bb34(%123: u64):
    %282 = trunc u64 %123 to u32
    %283 = const u32 0
    %284 = const u32 0
    %285 = const bool false
    %286 = const bool false
    %287 = const bool false
    %288 = const bool false
    call @func.41(%0, %282, %283, %284, %285, %286, %287, %288)
    br bb50
bb35(%124: ptr, %125: ptr, %126: ptr):
    call @func.12(%184, %126)
    br bb36(%124, %125)
bb36(%127: ptr, %128: ptr):
    %289 = load u64, ptr %184
    %290 = call @func.42(%289)
    br bb37(%127, %128, %290)
bb37(%129: ptr, %130: ptr, %131: u8):
    %291 = zext u8 %131 to u32
    %292 = const u32 1
    %293, %294 = add.overflow u32 %291, %292
    store u32 %293, ptr %185
    %295 = const i64 4
    %296 = gep i8, ptr %185, %295
    store bool %294, ptr %296
    %297 = const i64 4
    %298 = gep i8, ptr %185, %297
    %299 = load bool, ptr %298
    %300 = const bool false
    %301 = icmp eq bool %299, %300
    condbr %301, bb38(%129, %130), bb51
bb38(%132: ptr, %133: ptr):
    %302 = load u32, ptr %185
    %303 = const u32 255
    %304 = call @func.28(%302, %303)
    br bb39(%132, %133, %304)
bb39(%134: ptr, %135: ptr, %136: u32):
    %305 = zext u32 %136 to u64
    %306 = call @func.19(%134)
    br bb40(%135, %136, %305, %306)
bb40(%137: ptr, %138: u32, %139: u64, %140: u64):
    %307 = load u32, ptr %137
    %308 = zext u32 %307 to u64
    %309 = load u64, ptr %184
    %310 = call @func.43(%309)
    br bb41(%138, %139, %140, %308, %310)
bb41(%141: u32, %142: u64, %143: u64, %144: u64, %145: u32):
    %311 = zext u32 %145 to u64
    %312 = call @func.37(%144, %311)
    br bb42(%141, %142, %143, %312)
bb42(%146: u32, %147: u64, %148: u64, %149: u64):
    %313 = call @func.37(%148, %149)
    br bb43(%146, %147, %313)
bb43(%150: u32, %151: u64, %152: u64):
    %314 = call @func.37(%151, %152)
    br bb44(%150, %314)
bb44(%153: u32, %154: u64):
    %315 = trunc u64 %154 to u32
    %316 = load u64, ptr %184
    %317 = call @func.44(%316)
    br bb45(%153, %315, %317)
bb45(%155: u32, %156: u32, %157: u32):
    %318 = load u64, ptr %184
    %319 = call @func.45(%318)
    br bb46(%155, %156, %157, %319)
bb46(%158: u32, %159: u32, %160: u32, %161: bool):
    %320 = load u64, ptr %184
    %321 = call @func.46(%320)
    br bb47(%158, %159, %160, %161, %321)
bb47(%162: u32, %163: u32, %164: u32, %165: bool, %166: bool):
    %322 = load u64, ptr %184
    %323 = call @func.47(%322)
    br bb48(%162, %163, %164, %165, %166, %323)
bb48(%167: u32, %168: u32, %169: u32, %170: bool, %171: bool, %172: bool):
    %324 = load u64, ptr %184
    %325 = call @func.48(%324)
    br bb49(%167, %168, %169, %170, %171, %172, %325)
bb49(%173: u32, %174: u32, %175: u32, %176: bool, %177: bool, %178: bool, %179: bool):
    call @func.41(%0, %174, %175, %173, %176, %177, %178, %179)
    br bb50
bb50:
    ret
bb51:
    unreachable
}

fn @SipHasher13__new(functy.30) {
bb0(%0: ptr):
    %1 = alloca (i64, i64, i64, i64), align 8
    %2 = const u64 0
    %3 = const u64 0
    %4 = const u64 8317987319222330741
    %5 = xor u64 %2, %4
    %6 = const u64 7816392313619706465
    %7 = xor u64 %2, %6
    %8 = const u64 7237128888997146477
    %9 = xor u64 %3, %8
    %10 = const u64 8387220255154660723
    %11 = xor u64 %3, %10
    store u64 %5, ptr %1
    %12 = const i64 8
    %13 = gep i8, ptr %1, %12
    store u64 %7, ptr %13
    %14 = const i64 16
    %15 = gep i8, ptr %1, %14
    store u64 %9, ptr %15
    %16 = const i64 24
    %17 = gep i8, ptr %1, %16
    store u64 %11, ptr %17
    %18 = const i64 32
    %19 = gep i8, ptr %0, %18
    store u64 %2, ptr %19
    %20 = const i64 40
    %21 = gep i8, ptr %0, %20
    store u64 %3, ptr %21
    %22 = const u64 0
    %23 = const i64 48
    %24 = gep i8, ptr %0, %23
    store u64 %22, ptr %24
    %25 = load i64, ptr %1
    store i64 %25, ptr %0
    %26 = const i64 8
    %27 = gep i8, ptr %1, %26
    %28 = const i64 8
    %29 = gep i8, ptr %0, %28
    %30 = load i64, ptr %27
    store i64 %30, ptr %29
    %31 = const i64 16
    %32 = gep i8, ptr %1, %31
    %33 = const i64 16
    %34 = gep i8, ptr %0, %33
    %35 = load i64, ptr %32
    store i64 %35, ptr %34
    %36 = const i64 24
    %37 = gep i8, ptr %1, %36
    %38 = const i64 24
    %39 = gep i8, ptr %0, %38
    %40 = load i64, ptr %37
    store i64 %40, ptr %39
    %41 = const u64 0
    %42 = const i64 56
    %43 = gep i8, ptr %0, %42
    store u64 %41, ptr %43
    %44 = const u64 0
    %45 = const i64 64
    %46 = gep i8, ptr %0, %45
    store u64 %44, ptr %46
    ret
}

fn @sip_write_level(functy.31) {
bb0(%0: ptr, %1: ptr):
    %26 = alloca i64, align 8
    store ptr %1, ptr %26
    %27 = load ptr, ptr %26
    %28 = load i64, ptr %27
    switch %28 [ 0: bb6(%0) 1: bb5(%0) 2: bb4(%0) 3: bb3(%0) 4: bb2(%0) default: bb1 ]
bb1:
    unreachable
bb2(%2: ptr):
    %29 = const u64 4
    br bb7(%2, %29)
bb3(%3: ptr):
    %30 = const u64 3
    br bb7(%3, %30)
bb4(%4: ptr):
    %31 = const u64 2
    br bb7(%4, %31)
bb5(%5: ptr):
    %32 = const u64 1
    br bb7(%5, %32)
bb6(%6: ptr):
    %33 = const u64 0
    br bb7(%6, %33)
bb7(%7: ptr, %8: u64):
    call @func.34(%7, %8)
    br bb8(%7)
bb8(%9: ptr):
    %34 = load ptr, ptr %26
    %35 = load i64, ptr %34
    switch %35 [ 0: bb18 1: bb12(%9) 2: bb11(%9) 3: bb10(%9) 4: bb9(%9) default: bb1 ]
bb9(%10: ptr):
    %36 = load ptr, ptr %26
    %37 = const i64 8
    %38 = gep i8, ptr %36, %37
    %39 = load u64, ptr %38
    call @func.33(%10, %39)
    br bb18
bb10(%11: ptr):
    %40 = load ptr, ptr %26
    %41 = const i64 8
    %42 = gep i8, ptr %40, %41
    %43 = load ptr, ptr %26
    %44 = const i64 16
    %45 = gep i8, ptr %43, %44
    br bb14(%11, %42, %45)
bb11(%12: ptr):
    %46 = load ptr, ptr %26
    %47 = const i64 8
    %48 = gep i8, ptr %46, %47
    %49 = load ptr, ptr %26
    %50 = const i64 16
    %51 = gep i8, ptr %49, %50
    br bb14(%12, %48, %51)
bb12(%13: ptr):
    %52 = load ptr, ptr %26
    %53 = const i64 8
    %54 = gep i8, ptr %52, %53
    %55 = load ptr, ptr %54
    %56 = const i64 16
    %57 = gep i8, ptr %55, %56
    br bb13(%13, %57)
bb13(%14: ptr, %15: ptr):
    call @func.31(%14, %15)
    br bb18
bb14(%16: ptr, %17: ptr, %18: ptr):
    %58 = load ptr, ptr %17
    %59 = const i64 16
    %60 = gep i8, ptr %58, %59
    br bb15(%16, %18, %60)
bb15(%19: ptr, %20: ptr, %21: ptr):
    call @func.31(%19, %21)
    br bb16(%19, %20)
bb16(%22: ptr, %23: ptr):
    %61 = load ptr, ptr %23
    %62 = const i64 16
    %63 = gep i8, ptr %61, %62
    br bb17(%22, %63)
bb17(%24: ptr, %25: ptr):
    call @func.31(%24, %25)
    br bb18
bb18:
    ret
}

fn @SipHasher13__finish(functy.32) {
bb0(%0: ptr):
    %4 = alloca (i64, i64, i64, i64), align 8
    %5 = load i64, ptr %0
    store i64 %5, ptr %4
    %6 = const i64 8
    %7 = gep i8, ptr %0, %6
    %8 = const i64 8
    %9 = gep i8, ptr %4, %8
    %10 = load i64, ptr %7
    store i64 %10, ptr %9
    %11 = const i64 16
    %12 = gep i8, ptr %0, %11
    %13 = const i64 16
    %14 = gep i8, ptr %4, %13
    %15 = load i64, ptr %12
    store i64 %15, ptr %14
    %16 = const i64 24
    %17 = gep i8, ptr %0, %16
    %18 = const i64 24
    %19 = gep i8, ptr %4, %18
    %20 = load i64, ptr %17
    store i64 %20, ptr %19
    %21 = const i64 48
    %22 = gep i8, ptr %0, %21
    %23 = load u64, ptr %22
    %24 = const u64 255
    %25 = and u64 %23, %24
    %26 = const i32 56
    %27 = bitcast i32 %26 to u32
    %28 = const u32 64
    %29 = icmp ult u32 %27, %28
    condbr %29, bb1(%0, %25), bb4
bb1(%1: ptr, %2: u64):
    %30 = const i32 56
    %31 = zext i32 %30 to u64
    %32 = shl u64 %2, %31
    %33 = const i64 56
    %34 = gep i8, ptr %1, %33
    %35 = load u64, ptr %34
    %36 = or u64 %32, %35
    %37 = const i64 24
    %38 = gep i8, ptr %4, %37
    %39 = load u64, ptr %38
    %40 = xor u64 %39, %36
    %41 = const i64 24
    %42 = gep i8, ptr %4, %41
    store u64 %40, ptr %42
    call @func.49(%4)
    br bb2(%36)
bb2(%3: u64):
    %43 = load u64, ptr %4
    %44 = xor u64 %43, %3
    store u64 %44, ptr %4
    %45 = const i64 8
    %46 = gep i8, ptr %4, %45
    %47 = load u64, ptr %46
    %48 = const u64 255
    %49 = xor u64 %47, %48
    %50 = const i64 8
    %51 = gep i8, ptr %4, %50
    store u64 %49, ptr %51
    call @func.50(%4)
    br bb3
bb3:
    %52 = load u64, ptr %4
    %53 = const i64 16
    %54 = gep i8, ptr %4, %53
    %55 = load u64, ptr %54
    %56 = xor u64 %52, %55
    %57 = const i64 8
    %58 = gep i8, ptr %4, %57
    %59 = load u64, ptr %58
    %60 = xor u64 %56, %59
    %61 = const i64 24
    %62 = gep i8, ptr %4, %61
    %63 = load u64, ptr %62
    %64 = xor u64 %60, %63
    ret %64
bb4:
    unreachable
}

fn @SipHasher13__write_u64(functy.33) {
bb0(%0: ptr, %1: u64):
    %44 = alloca (i8, i8, i8, i8, i8, i8, i8, i8), align 1
    %45 = alloca (i64, i64), align 8
    %46 = trunc u64 %1 to u8
    %47 = const u32 8
    %48 = const u32 64
    %49 = icmp ult u32 %47, %48
    condbr %49, bb1(%0, %1, %46), bb9
bb1(%2: ptr, %3: u64, %4: u8):
    %50 = const u32 8
    %51 = zext u32 %50 to u64
    %52 = lshr u64 %3, %51
    %53 = trunc u64 %52 to u8
    %54 = const u32 16
    %55 = const u32 64
    %56 = icmp ult u32 %54, %55
    condbr %56, bb2(%2, %3, %4, %53), bb9
bb2(%5: ptr, %6: u64, %7: u8, %8: u8):
    %57 = const u32 16
    %58 = zext u32 %57 to u64
    %59 = lshr u64 %6, %58
    %60 = trunc u64 %59 to u8
    %61 = const u32 24
    %62 = const u32 64
    %63 = icmp ult u32 %61, %62
    condbr %63, bb3(%5, %6, %7, %8, %60), bb9
bb3(%9: ptr, %10: u64, %11: u8, %12: u8, %13: u8):
    %64 = const u32 24
    %65 = zext u32 %64 to u64
    %66 = lshr u64 %10, %65
    %67 = trunc u64 %66 to u8
    %68 = const u32 32
    %69 = const u32 64
    %70 = icmp ult u32 %68, %69
    condbr %70, bb4(%9, %10, %11, %12, %13, %67), bb9
bb4(%14: ptr, %15: u64, %16: u8, %17: u8, %18: u8, %19: u8):
    %71 = const u32 32
    %72 = zext u32 %71 to u64
    %73 = lshr u64 %15, %72
    %74 = trunc u64 %73 to u8
    %75 = const u32 40
    %76 = const u32 64
    %77 = icmp ult u32 %75, %76
    condbr %77, bb5(%14, %15, %16, %17, %18, %19, %74), bb9
bb5(%20: ptr, %21: u64, %22: u8, %23: u8, %24: u8, %25: u8, %26: u8):
    %78 = const u32 40
    %79 = zext u32 %78 to u64
    %80 = lshr u64 %21, %79
    %81 = trunc u64 %80 to u8
    %82 = const u32 48
    %83 = const u32 64
    %84 = icmp ult u32 %82, %83
    condbr %84, bb6(%20, %21, %22, %23, %24, %25, %26, %81), bb9
bb6(%27: ptr, %28: u64, %29: u8, %30: u8, %31: u8, %32: u8, %33: u8, %34: u8):
    %85 = const u32 48
    %86 = zext u32 %85 to u64
    %87 = lshr u64 %28, %86
    %88 = trunc u64 %87 to u8
    %89 = const u32 56
    %90 = const u32 64
    %91 = icmp ult u32 %89, %90
    condbr %91, bb7(%27, %28, %29, %30, %31, %32, %33, %34, %88), bb9
bb7(%35: ptr, %36: u64, %37: u8, %38: u8, %39: u8, %40: u8, %41: u8, %42: u8, %43: u8):
    %92 = const u32 56
    %93 = zext u32 %92 to u64
    %94 = lshr u64 %36, %93
    %95 = trunc u64 %94 to u8
    store u8 %37, ptr %44
    %96 = const i64 1
    %97 = gep i8, ptr %44, %96
    store u8 %38, ptr %97
    %98 = const i64 2
    %99 = gep i8, ptr %44, %98
    store u8 %39, ptr %99
    %100 = const i64 3
    %101 = gep i8, ptr %44, %100
    store u8 %40, ptr %101
    %102 = const i64 4
    %103 = gep i8, ptr %44, %102
    store u8 %41, ptr %103
    %104 = const i64 5
    %105 = gep i8, ptr %44, %104
    store u8 %42, ptr %105
    %106 = const i64 6
    %107 = gep i8, ptr %44, %106
    store u8 %43, ptr %107
    %108 = const i64 7
    %109 = gep i8, ptr %44, %108
    store u8 %95, ptr %109
    store ptr %44, ptr %45
    %110 = const i64 8
    %111 = gep i8, ptr %45, %110
    %112 = const u64 8
    store u64 %112, ptr %111
    call @func.51(%35, %45)
    br bb8
bb8:
    ret
bb9:
    unreachable
}

fn @SipHasher13__write_usize(functy.34) {
bb0(%0: ptr, %1: u64):
    %44 = alloca (i8, i8, i8, i8, i8, i8, i8, i8), align 1
    %45 = alloca (i64, i64), align 8
    %46 = trunc u64 %1 to u8
    %47 = const u32 8
    %48 = const u32 64
    %49 = icmp ult u32 %47, %48
    condbr %49, bb1(%0, %1, %46), bb9
bb1(%2: ptr, %3: u64, %4: u8):
    %50 = const u32 8
    %51 = zext u32 %50 to u64
    %52 = lshr u64 %3, %51
    %53 = trunc u64 %52 to u8
    %54 = const u32 16
    %55 = const u32 64
    %56 = icmp ult u32 %54, %55
    condbr %56, bb2(%2, %3, %4, %53), bb9
bb2(%5: ptr, %6: u64, %7: u8, %8: u8):
    %57 = const u32 16
    %58 = zext u32 %57 to u64
    %59 = lshr u64 %6, %58
    %60 = trunc u64 %59 to u8
    %61 = const u32 24
    %62 = const u32 64
    %63 = icmp ult u32 %61, %62
    condbr %63, bb3(%5, %6, %7, %8, %60), bb9
bb3(%9: ptr, %10: u64, %11: u8, %12: u8, %13: u8):
    %64 = const u32 24
    %65 = zext u32 %64 to u64
    %66 = lshr u64 %10, %65
    %67 = trunc u64 %66 to u8
    %68 = const u32 32
    %69 = const u32 64
    %70 = icmp ult u32 %68, %69
    condbr %70, bb4(%9, %10, %11, %12, %13, %67), bb9
bb4(%14: ptr, %15: u64, %16: u8, %17: u8, %18: u8, %19: u8):
    %71 = const u32 32
    %72 = zext u32 %71 to u64
    %73 = lshr u64 %15, %72
    %74 = trunc u64 %73 to u8
    %75 = const u32 40
    %76 = const u32 64
    %77 = icmp ult u32 %75, %76
    condbr %77, bb5(%14, %15, %16, %17, %18, %19, %74), bb9
bb5(%20: ptr, %21: u64, %22: u8, %23: u8, %24: u8, %25: u8, %26: u8):
    %78 = const u32 40
    %79 = zext u32 %78 to u64
    %80 = lshr u64 %21, %79
    %81 = trunc u64 %80 to u8
    %82 = const u32 48
    %83 = const u32 64
    %84 = icmp ult u32 %82, %83
    condbr %84, bb6(%20, %21, %22, %23, %24, %25, %26, %81), bb9
bb6(%27: ptr, %28: u64, %29: u8, %30: u8, %31: u8, %32: u8, %33: u8, %34: u8):
    %85 = const u32 48
    %86 = zext u32 %85 to u64
    %87 = lshr u64 %28, %86
    %88 = trunc u64 %87 to u8
    %89 = const u32 56
    %90 = const u32 64
    %91 = icmp ult u32 %89, %90
    condbr %91, bb7(%27, %28, %29, %30, %31, %32, %33, %34, %88), bb9
bb7(%35: ptr, %36: u64, %37: u8, %38: u8, %39: u8, %40: u8, %41: u8, %42: u8, %43: u8):
    %92 = const u32 56
    %93 = zext u32 %92 to u64
    %94 = lshr u64 %36, %93
    %95 = trunc u64 %94 to u8
    store u8 %37, ptr %44
    %96 = const i64 1
    %97 = gep i8, ptr %44, %96
    store u8 %38, ptr %97
    %98 = const i64 2
    %99 = gep i8, ptr %44, %98
    store u8 %39, ptr %99
    %100 = const i64 3
    %101 = gep i8, ptr %44, %100
    store u8 %40, ptr %101
    %102 = const i64 4
    %103 = gep i8, ptr %44, %102
    store u8 %41, ptr %103
    %104 = const i64 5
    %105 = gep i8, ptr %44, %104
    store u8 %42, ptr %105
    %106 = const i64 6
    %107 = gep i8, ptr %44, %106
    store u8 %43, ptr %107
    %108 = const i64 7
    %109 = gep i8, ptr %44, %108
    store u8 %95, ptr %109
    store ptr %44, ptr %45
    %110 = const i64 8
    %111 = gep i8, ptr %45, %110
    %112 = const u64 8
    store u64 %112, ptr %111
    call @func.51(%35, %45)
    br bb8
bb8:
    ret
bb9:
    unreachable
}

fn @SipHasher13__write_str_bytes(functy.35) {
bb0(%0: ptr, %1: ptr):
    call @func.51(%0, %1)
    br bb1(%0)
bb1(%2: ptr):
    %3 = const u8 255
    call @func.52(%2, %3)
    br bb2
bb2:
    ret
}

fn @_RNvMs7_NtCs2EYQwhfuABO_4core3numy12wrapping_mul(functy.36) {
}

fn @mix_hash(functy.37) {
bb0(%0: u64, %1: u64):
    %8 = const u64 14313749767032793493
    %9 = call @func.36(%1, %8)
    br bb1(%0, %9)
bb1(%2: u64, %3: u64):
    %10 = const u32 47
    %11 = const u32 64
    %12 = icmp ult u32 %10, %11
    condbr %12, bb2(%2, %3, %3), bb4
bb2(%4: u64, %5: u64, %6: u64):
    %13 = const u32 47
    %14 = zext u32 %13 to u64
    %15 = lshr u64 %6, %14
    %16 = xor u64 %5, %15
    %17 = const u64 14313749767032793493
    %18 = xor u64 %16, %17
    %19 = xor u64 %4, %18
    %20 = const u64 14313749767032793493
    %21 = call @func.36(%19, %20)
    br bb3(%21)
bb3(%7: u64):
    ret %7
bb4:
    unreachable
}

fn @level_has_mvar(functy.38) {
bb0(%0: ptr):
    %1 = const bool false
    ret %1
}

fn @Level__has_params(functy.39) {
bb0(%0: ptr):
    %11 = alloca i64, align 8
    store ptr %0, ptr %11
    %12 = load ptr, ptr %11
    %13 = load i64, ptr %12
    switch %13 [ 0: bb6 1: bb5 2: bb4 3: bb3 4: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %14 = const bool true
    br bb14(%14)
bb3:
    %15 = load ptr, ptr %11
    %16 = const i64 8
    %17 = gep i8, ptr %15, %16
    %18 = load ptr, ptr %11
    %19 = const i64 16
    %20 = gep i8, ptr %18, %19
    br bb8(%17, %20)
bb4:
    %21 = load ptr, ptr %11
    %22 = const i64 8
    %23 = gep i8, ptr %21, %22
    %24 = load ptr, ptr %11
    %25 = const i64 16
    %26 = gep i8, ptr %24, %25
    br bb8(%23, %26)
bb5:
    %27 = load ptr, ptr %11
    %28 = const i64 8
    %29 = gep i8, ptr %27, %28
    %30 = load ptr, ptr %29
    %31 = const i64 16
    %32 = gep i8, ptr %30, %31
    br bb7(%32)
bb6:
    %33 = const bool false
    br bb14(%33)
bb7(%1: ptr):
    %34 = call @func.39(%1)
    br bb14(%34)
bb8(%2: ptr, %3: ptr):
    %35 = load ptr, ptr %2
    %36 = const i64 16
    %37 = gep i8, ptr %35, %36
    br bb9(%3, %37)
bb9(%4: ptr, %5: ptr):
    %38 = call @func.39(%5)
    br bb10(%4, %38)
bb10(%6: ptr, %7: bool):
    condbr %7, bb11, bb12(%6)
bb11:
    %39 = const bool true
    br bb14(%39)
bb12(%8: ptr):
    %40 = load ptr, ptr %8
    %41 = const i64 16
    %42 = gep i8, ptr %40, %41
    br bb13(%42)
bb13(%9: ptr):
    %43 = call @func.39(%9)
    br bb14(%43)
bb14(%10: bool):
    ret %10
}

fn @_RNvYmNtNtCs2EYQwhfuABO_4core3cmp3Ord3minCs6Skw9Chgdp8_19clean_siphash_slice(functy.40) {
}

fn @ExprMeta__pack(functy.41) {
bb0(%0: ptr, %1: u32, %2: u32, %3: u32, %4: bool, %5: bool, %6: bool, %7: bool):
    %42 = const u32 255
    %43 = call @func.40(%3, %42)
    br bb1(%1, %2, %4, %5, %6, %7, %43)
bb1(%8: u32, %9: u32, %10: bool, %11: bool, %12: bool, %13: bool, %14: u32):
    %44 = zext u32 %8 to u64
    %45 = zext u32 %14 to u64
    %46 = const u32 32
    %47 = const u32 64
    %48 = icmp ult u32 %46, %47
    condbr %48, bb2(%9, %10, %11, %12, %13, %44, %45), bb8
bb2(%15: u32, %16: bool, %17: bool, %18: bool, %19: bool, %20: u64, %21: u64):
    %49 = const u32 32
    %50 = zext u32 %49 to u64
    %51 = shl u64 %21, %50
    %52 = or u64 %20, %51
    %53 = const u64 1
    %54 = const u64 0
    %55 = select u64 %16, %53, %54
    %56 = const u32 40
    %57 = const u32 64
    %58 = icmp ult u32 %56, %57
    condbr %58, bb3(%15, %17, %18, %19, %52, %55), bb8
bb3(%22: u32, %23: bool, %24: bool, %25: bool, %26: u64, %27: u64):
    %59 = const u32 40
    %60 = zext u32 %59 to u64
    %61 = shl u64 %27, %60
    %62 = or u64 %26, %61
    %63 = const u64 1
    %64 = const u64 0
    %65 = select u64 %23, %63, %64
    %66 = const u32 41
    %67 = const u32 64
    %68 = icmp ult u32 %66, %67
    condbr %68, bb4(%22, %24, %25, %62, %65), bb8
bb4(%28: u32, %29: bool, %30: bool, %31: u64, %32: u64):
    %69 = const u32 41
    %70 = zext u32 %69 to u64
    %71 = shl u64 %32, %70
    %72 = or u64 %31, %71
    %73 = const u64 1
    %74 = const u64 0
    %75 = select u64 %29, %73, %74
    %76 = const u32 42
    %77 = const u32 64
    %78 = icmp ult u32 %76, %77
    condbr %78, bb5(%28, %30, %72, %75), bb8
bb5(%33: u32, %34: bool, %35: u64, %36: u64):
    %79 = const u32 42
    %80 = zext u32 %79 to u64
    %81 = shl u64 %36, %80
    %82 = or u64 %35, %81
    %83 = const u64 1
    %84 = const u64 0
    %85 = select u64 %34, %83, %84
    %86 = const u32 43
    %87 = const u32 64
    %88 = icmp ult u32 %86, %87
    condbr %88, bb6(%33, %82, %85), bb8
bb6(%37: u32, %38: u64, %39: u64):
    %89 = const u32 43
    %90 = zext u32 %89 to u64
    %91 = shl u64 %39, %90
    %92 = or u64 %38, %91
    %93 = zext u32 %37 to u64
    %94 = const u32 44
    %95 = const u32 64
    %96 = icmp ult u32 %94, %95
    condbr %96, bb7(%92, %93), bb8
bb7(%40: u64, %41: u64):
    %97 = const u32 44
    %98 = zext u32 %97 to u64
    %99 = shl u64 %41, %98
    %100 = or u64 %40, %99
    store u64 %100, ptr %0
    ret
bb8:
    unreachable
}

fn @ExprMeta__approx_depth(functy.42) {
bb0(%0: u64):
    %2 = alloca i64, align 8
    store u64 %0, ptr %2
    %3 = load u64, ptr %2
    %4 = const u32 32
    %5 = const u32 64
    %6 = icmp ult u32 %4, %5
    condbr %6, bb1(%3), bb2
bb1(%1: u64):
    %7 = const u32 32
    %8 = zext u32 %7 to u64
    %9 = lshr u64 %1, %8
    %10 = const u64 255
    %11 = and u64 %9, %10
    %12 = trunc u64 %11 to u8
    ret %12
bb2:
    unreachable
}

fn @ExprMeta__hash(functy.43) {
bb0(%0: u64):
    %1 = alloca i64, align 8
    store u64 %0, ptr %1
    %2 = load u64, ptr %1
    %3 = const u64 4294967295
    %4 = and u64 %2, %3
    %5 = trunc u64 %4 to u32
    ret %5
}

fn @ExprMeta__loose_bvar_range(functy.44) {
bb0(%0: u64):
    %2 = alloca i64, align 8
    store u64 %0, ptr %2
    %3 = load u64, ptr %2
    %4 = const u32 44
    %5 = const u32 64
    %6 = icmp ult u32 %4, %5
    condbr %6, bb1(%3), bb2
bb1(%1: u64):
    %7 = const u32 44
    %8 = zext u32 %7 to u64
    %9 = lshr u64 %1, %8
    %10 = trunc u64 %9 to u32
    ret %10
bb2:
    unreachable
}

fn @ExprMeta__has_fvar(functy.45) {
bb0(%0: u64):
    %2 = alloca i64, align 8
    store u64 %0, ptr %2
    %3 = load u64, ptr %2
    %4 = const u32 40
    %5 = const u32 64
    %6 = icmp ult u32 %4, %5
    condbr %6, bb1(%3), bb2
bb1(%1: u64):
    %7 = const u32 40
    %8 = zext u32 %7 to u64
    %9 = lshr u64 %1, %8
    %10 = const u64 1
    %11 = and u64 %9, %10
    %12 = const u64 1
    %13 = icmp eq u64 %11, %12
    ret %13
bb2:
    unreachable
}

fn @ExprMeta__has_expr_mvar(functy.46) {
bb0(%0: u64):
    %2 = alloca i64, align 8
    store u64 %0, ptr %2
    %3 = load u64, ptr %2
    %4 = const u32 41
    %5 = const u32 64
    %6 = icmp ult u32 %4, %5
    condbr %6, bb1(%3), bb2
bb1(%1: u64):
    %7 = const u32 41
    %8 = zext u32 %7 to u64
    %9 = lshr u64 %1, %8
    %10 = const u64 1
    %11 = and u64 %9, %10
    %12 = const u64 1
    %13 = icmp eq u64 %11, %12
    ret %13
bb2:
    unreachable
}

fn @ExprMeta__has_level_mvar(functy.47) {
bb0(%0: u64):
    %2 = alloca i64, align 8
    store u64 %0, ptr %2
    %3 = load u64, ptr %2
    %4 = const u32 42
    %5 = const u32 64
    %6 = icmp ult u32 %4, %5
    condbr %6, bb1(%3), bb2
bb1(%1: u64):
    %7 = const u32 42
    %8 = zext u32 %7 to u64
    %9 = lshr u64 %1, %8
    %10 = const u64 1
    %11 = and u64 %9, %10
    %12 = const u64 1
    %13 = icmp eq u64 %11, %12
    ret %13
bb2:
    unreachable
}

fn @ExprMeta__has_level_param(functy.48) {
bb0(%0: u64):
    %2 = alloca i64, align 8
    store u64 %0, ptr %2
    %3 = load u64, ptr %2
    %4 = const u32 43
    %5 = const u32 64
    %6 = icmp ult u32 %4, %5
    condbr %6, bb1(%3), bb2
bb1(%1: u64):
    %7 = const u32 43
    %8 = zext u32 %7 to u64
    %9 = lshr u64 %1, %8
    %10 = const u64 1
    %11 = and u64 %9, %10
    %12 = const u64 1
    %13 = icmp eq u64 %11, %12
    ret %13
bb2:
    unreachable
}

fn @sip13_c_rounds(functy.49) {
bb0(%0: ptr):
    call @func.53(%0)
    br bb1
bb1:
    ret
}

fn @sip13_d_rounds(functy.50) {
bb0(%0: ptr):
    call @func.53(%0)
    br bb1(%0)
bb1(%1: ptr):
    call @func.53(%1)
    br bb2(%1)
bb2(%2: ptr):
    call @func.53(%2)
    br bb3
bb3:
    ret
}

fn @SipHasher13__write(functy.51) {
bb0(%0: ptr, %1: ptr):
    %54 = alloca i64, align 8
    %55 = alloca (i64, i64), align 8
    %56 = alloca (i64, i64), align 8
    %57 = alloca (i64, i64), align 8
    %58 = alloca (i64, i64), align 8
    %59 = alloca (i64, i64), align 8
    %60 = alloca (i64, i64), align 8
    %61 = alloca (i64, i64), align 8
    store ptr %0, ptr %54
    %62 = const i64 8
    %63 = gep i8, ptr %1, %62
    %64 = load u64, ptr %63
    %65 = load ptr, ptr %54
    %66 = const i64 48
    %67 = gep i8, ptr %65, %66
    %68 = load u64, ptr %67
    %69, %70 = add.overflow u64 %68, %64
    store u64 %69, ptr %55
    %71 = const i64 8
    %72 = gep i8, ptr %55, %71
    store bool %70, ptr %72
    %73 = const i64 8
    %74 = gep i8, ptr %55, %73
    %75 = load bool, ptr %74
    %76 = const bool false
    %77 = icmp eq bool %75, %76
    condbr %77, bb1(%64), bb25
bb1(%2: u64):
    %78 = load u64, ptr %55
    %79 = load ptr, ptr %54
    %80 = const i64 48
    %81 = gep i8, ptr %79, %80
    store u64 %78, ptr %81
    %82 = const u64 0
    %83 = load ptr, ptr %54
    %84 = const i64 64
    %85 = gep i8, ptr %83, %84
    %86 = load u64, ptr %85
    %87 = const u64 0
    %88 = icmp ne u64 %86, %87
    condbr %88, bb2(%2), bb14(%2, %82)
bb2(%3: u64):
    %89 = load ptr, ptr %54
    %90 = const i64 64
    %91 = gep i8, ptr %89, %90
    %92 = load u64, ptr %91
    %93 = const u64 8
    %94, %95 = sub.overflow u64 %93, %92
    store u64 %94, ptr %56
    %96 = const i64 8
    %97 = gep i8, ptr %56, %96
    store bool %95, ptr %97
    %98 = const i64 8
    %99 = gep i8, ptr %56, %98
    %100 = load bool, ptr %99
    %101 = const bool false
    %102 = icmp eq bool %100, %101
    condbr %102, bb3(%3), bb25
bb3(%4: u64):
    %103 = load u64, ptr %56
    %104 = icmp ult u64 %4, %103
    condbr %104, bb4(%4, %103), bb5(%4, %103)
bb4(%5: u64, %6: u64):
    br bb6(%5, %6, %5)
bb5(%7: u64, %8: u64):
    br bb6(%7, %8, %8)
bb6(%9: u64, %10: u64, %11: u64):
    %105 = const u64 0
    %106 = call @func.54(%1, %105, %11)
    br bb7(%9, %10, %106)
bb7(%12: u64, %13: u64, %14: u64):
    %107 = load ptr, ptr %54
    %108 = const i64 64
    %109 = gep i8, ptr %107, %108
    %110 = load u64, ptr %109
    %111 = const u64 8
    %112, %113 = mul.overflow u64 %111, %110
    store u64 %112, ptr %57
    %114 = const i64 8
    %115 = gep i8, ptr %57, %114
    store bool %113, ptr %115
    %116 = const i64 8
    %117 = gep i8, ptr %57, %116
    %118 = load bool, ptr %117
    %119 = const bool false
    %120 = icmp eq bool %118, %119
    condbr %120, bb8(%12, %13, %14), bb25
bb8(%15: u64, %16: u64, %17: u64):
    %121 = load u64, ptr %57
    %122 = trunc u64 %121 to u32
    %123 = const u32 64
    %124 = icmp ult u32 %122, %123
    condbr %124, bb9(%15, %16, %17, %122), bb25
bb9(%18: u64, %19: u64, %20: u64, %21: u32):
    %125 = zext u32 %21 to u64
    %126 = shl u64 %20, %125
    %127 = load ptr, ptr %54
    %128 = const i64 56
    %129 = gep i8, ptr %127, %128
    %130 = load u64, ptr %129
    %131 = or u64 %130, %126
    %132 = load ptr, ptr %54
    %133 = const i64 56
    %134 = gep i8, ptr %132, %133
    store u64 %131, ptr %134
    %135 = icmp ult u64 %18, %19
    condbr %135, bb10(%18), bb12(%18, %19)
bb10(%22: u64):
    %136 = load ptr, ptr %54
    %137 = const i64 64
    %138 = gep i8, ptr %136, %137
    %139 = load u64, ptr %138
    %140, %141 = add.overflow u64 %139, %22
    store u64 %140, ptr %58
    %142 = const i64 8
    %143 = gep i8, ptr %58, %142
    store bool %141, ptr %143
    %144 = const i64 8
    %145 = gep i8, ptr %58, %144
    %146 = load bool, ptr %145
    %147 = const bool false
    %148 = icmp eq bool %146, %147
    condbr %148, bb11, bb25
bb11:
    %149 = load u64, ptr %58
    %150 = load ptr, ptr %54
    %151 = const i64 64
    %152 = gep i8, ptr %150, %151
    store u64 %149, ptr %152
    br bb24
bb12(%23: u64, %24: u64):
    %153 = load ptr, ptr %54
    %154 = const i64 56
    %155 = gep i8, ptr %153, %154
    %156 = load u64, ptr %155
    %157 = load ptr, ptr %54
    %158 = const i64 24
    %159 = gep i8, ptr %157, %158
    %160 = load u64, ptr %159
    %161 = xor u64 %160, %156
    %162 = load ptr, ptr %54
    %163 = const i64 24
    %164 = gep i8, ptr %162, %163
    store u64 %161, ptr %164
    %165 = load ptr, ptr %54
    call @func.49(%165)
    br bb13(%23, %24)
bb13(%25: u64, %26: u64):
    %166 = load ptr, ptr %54
    %167 = const i64 56
    %168 = gep i8, ptr %166, %167
    %169 = load u64, ptr %168
    %170 = load ptr, ptr %54
    %171 = load u64, ptr %170
    %172 = xor u64 %171, %169
    %173 = load ptr, ptr %54
    store u64 %172, ptr %173
    %174 = const u64 0
    %175 = load ptr, ptr %54
    %176 = const i64 64
    %177 = gep i8, ptr %175, %176
    store u64 %174, ptr %177
    br bb14(%25, %26)
bb14(%27: u64, %28: u64):
    %178, %179 = sub.overflow u64 %27, %28
    store u64 %178, ptr %59
    %180 = const i64 8
    %181 = gep i8, ptr %59, %180
    store bool %179, ptr %181
    %182 = const i64 8
    %183 = gep i8, ptr %59, %182
    %184 = load bool, ptr %183
    %185 = const bool false
    %186 = icmp eq bool %184, %185
    condbr %186, bb15(%28), bb25
bb15(%29: u64):
    %187 = load u64, ptr %59
    %188 = const u64 7
    %189 = and u64 %187, %188
    br bb16(%187, %189, %29)
bb16(%30: u64, %31: u64, %32: u64):
    %190, %191 = sub.overflow u64 %30, %31
    store u64 %190, ptr %60
    %192 = const i64 8
    %193 = gep i8, ptr %60, %192
    store bool %191, ptr %193
    %194 = const i64 8
    %195 = gep i8, ptr %60, %194
    %196 = load bool, ptr %195
    %197 = const bool false
    %198 = icmp eq bool %196, %197
    condbr %198, bb17(%30, %31, %32, %32), bb25
bb17(%33: u64, %34: u64, %35: u64, %36: u64):
    %199 = load u64, ptr %60
    %200 = icmp ult u64 %36, %199
    condbr %200, bb18(%33, %34, %35), bb22(%34, %35)
bb18(%37: u64, %38: u64, %39: u64):
    %201 = call @func.55(%1, %39)
    br bb19(%37, %38, %39, %201)
bb19(%40: u64, %41: u64, %42: u64, %43: u64):
    %202 = load ptr, ptr %54
    %203 = const i64 24
    %204 = gep i8, ptr %202, %203
    %205 = load u64, ptr %204
    %206 = xor u64 %205, %43
    %207 = load ptr, ptr %54
    %208 = const i64 24
    %209 = gep i8, ptr %207, %208
    store u64 %206, ptr %209
    %210 = load ptr, ptr %54
    call @func.49(%210)
    br bb20(%40, %41, %42, %43)
bb20(%44: u64, %45: u64, %46: u64, %47: u64):
    %211 = load ptr, ptr %54
    %212 = load u64, ptr %211
    %213 = xor u64 %212, %47
    %214 = load ptr, ptr %54
    store u64 %213, ptr %214
    %215 = const u64 8
    %216, %217 = add.overflow u64 %46, %215
    store u64 %216, ptr %61
    %218 = const i64 8
    %219 = gep i8, ptr %61, %218
    store bool %217, ptr %219
    %220 = const i64 8
    %221 = gep i8, ptr %61, %220
    %222 = load bool, ptr %221
    %223 = const bool false
    %224 = icmp eq bool %222, %223
    condbr %224, bb21(%44, %45), bb25
bb21(%48: u64, %49: u64):
    %225 = load u64, ptr %61
    br bb16(%48, %49, %225)
bb22(%50: u64, %51: u64):
    %226 = call @func.54(%1, %51, %50)
    br bb23(%50, %226)
bb23(%52: u64, %53: u64):
    %227 = load ptr, ptr %54
    %228 = const i64 56
    %229 = gep i8, ptr %227, %228
    store u64 %53, ptr %229
    %230 = load ptr, ptr %54
    %231 = const i64 64
    %232 = gep i8, ptr %230, %231
    store u64 %52, ptr %232
    br bb24
bb24:
    ret
bb25:
    unreachable
}

fn @SipHasher13__write_u8(functy.52) {
bb0(%0: ptr, %1: u8):
    %2 = alloca i8, align 1
    %3 = alloca (i64, i64), align 8
    store u8 %1, ptr %2
    store ptr %2, ptr %3
    %4 = const i64 8
    %5 = gep i8, ptr %3, %4
    %6 = const u64 1
    store u64 %6, ptr %5
    call @func.51(%0, %3)
    br bb1
bb1:
    ret
}

fn @sip_compress(functy.53) {
bb0(%0: ptr):
    %21 = load u64, ptr %0
    %22 = const i64 16
    %23 = gep i8, ptr %0, %22
    %24 = load u64, ptr %23
    %25 = call @func.56(%21, %24)
    br bb1(%0, %25)
bb1(%1: ptr, %2: u64):
    store u64 %2, ptr %1
    %26 = const i64 8
    %27 = gep i8, ptr %1, %26
    %28 = load u64, ptr %27
    %29 = const i64 24
    %30 = gep i8, ptr %1, %29
    %31 = load u64, ptr %30
    %32 = call @func.56(%28, %31)
    br bb2(%1, %32)
bb2(%3: ptr, %4: u64):
    %33 = const i64 8
    %34 = gep i8, ptr %3, %33
    store u64 %4, ptr %34
    %35 = const i64 16
    %36 = gep i8, ptr %3, %35
    %37 = load u64, ptr %36
    %38 = const u32 13
    %39 = call @func.57(%37, %38)
    br bb3(%3, %39)
bb3(%5: ptr, %6: u64):
    %40 = const i64 16
    %41 = gep i8, ptr %5, %40
    store u64 %6, ptr %41
    %42 = load u64, ptr %5
    %43 = const i64 16
    %44 = gep i8, ptr %5, %43
    %45 = load u64, ptr %44
    %46 = xor u64 %45, %42
    %47 = const i64 16
    %48 = gep i8, ptr %5, %47
    store u64 %46, ptr %48
    %49 = const i64 24
    %50 = gep i8, ptr %5, %49
    %51 = load u64, ptr %50
    %52 = const u32 16
    %53 = call @func.57(%51, %52)
    br bb4(%5, %53)
bb4(%7: ptr, %8: u64):
    %54 = const i64 24
    %55 = gep i8, ptr %7, %54
    store u64 %8, ptr %55
    %56 = const i64 8
    %57 = gep i8, ptr %7, %56
    %58 = load u64, ptr %57
    %59 = const i64 24
    %60 = gep i8, ptr %7, %59
    %61 = load u64, ptr %60
    %62 = xor u64 %61, %58
    %63 = const i64 24
    %64 = gep i8, ptr %7, %63
    store u64 %62, ptr %64
    %65 = load u64, ptr %7
    %66 = const u32 32
    %67 = call @func.57(%65, %66)
    br bb5(%7, %67)
bb5(%9: ptr, %10: u64):
    store u64 %10, ptr %9
    %68 = const i64 8
    %69 = gep i8, ptr %9, %68
    %70 = load u64, ptr %69
    %71 = const i64 16
    %72 = gep i8, ptr %9, %71
    %73 = load u64, ptr %72
    %74 = call @func.56(%70, %73)
    br bb6(%9, %74)
bb6(%11: ptr, %12: u64):
    %75 = const i64 8
    %76 = gep i8, ptr %11, %75
    store u64 %12, ptr %76
    %77 = load u64, ptr %11
    %78 = const i64 24
    %79 = gep i8, ptr %11, %78
    %80 = load u64, ptr %79
    %81 = call @func.56(%77, %80)
    br bb7(%11, %81)
bb7(%13: ptr, %14: u64):
    store u64 %14, ptr %13
    %82 = const i64 16
    %83 = gep i8, ptr %13, %82
    %84 = load u64, ptr %83
    %85 = const u32 17
    %86 = call @func.57(%84, %85)
    br bb8(%13, %86)
bb8(%15: ptr, %16: u64):
    %87 = const i64 16
    %88 = gep i8, ptr %15, %87
    store u64 %16, ptr %88
    %89 = const i64 8
    %90 = gep i8, ptr %15, %89
    %91 = load u64, ptr %90
    %92 = const i64 16
    %93 = gep i8, ptr %15, %92
    %94 = load u64, ptr %93
    %95 = xor u64 %94, %91
    %96 = const i64 16
    %97 = gep i8, ptr %15, %96
    store u64 %95, ptr %97
    %98 = const i64 24
    %99 = gep i8, ptr %15, %98
    %100 = load u64, ptr %99
    %101 = const u32 21
    %102 = call @func.57(%100, %101)
    br bb9(%15, %102)
bb9(%17: ptr, %18: u64):
    %103 = const i64 24
    %104 = gep i8, ptr %17, %103
    store u64 %18, ptr %104
    %105 = load u64, ptr %17
    %106 = const i64 24
    %107 = gep i8, ptr %17, %106
    %108 = load u64, ptr %107
    %109 = xor u64 %108, %105
    %110 = const i64 24
    %111 = gep i8, ptr %17, %110
    store u64 %109, ptr %111
    %112 = const i64 8
    %113 = gep i8, ptr %17, %112
    %114 = load u64, ptr %113
    %115 = const u32 32
    %116 = call @func.57(%114, %115)
    br bb10(%17, %116)
bb10(%19: ptr, %20: u64):
    %117 = const i64 8
    %118 = gep i8, ptr %19, %117
    store u64 %20, ptr %118
    ret
}

fn @u8to64_le(functy.54) {
bb0(%0: ptr, %1: u64, %2: u64):
    %76 = alloca (i64, i64), align 8
    %77 = alloca (i64, i64), align 8
    %78 = alloca (i64, i64), align 8
    %79 = alloca (i64, i64), align 8
    %80 = alloca (i64, i64), align 8
    %81 = alloca (i64, i64), align 8
    %82 = alloca (i64, i64), align 8
    %83 = alloca (i64, i64), align 8
    %84 = alloca (i64, i64), align 8
    %85 = alloca (i64, i64), align 8
    %86 = const u64 0
    %87 = const u64 0
    %88 = const u64 3
    %89, %90 = add.overflow u64 %86, %88
    store u64 %89, ptr %76
    %91 = const i64 8
    %92 = gep i8, ptr %76, %91
    store bool %90, ptr %92
    %93 = const i64 8
    %94 = gep i8, ptr %76, %93
    %95 = load bool, ptr %94
    %96 = const bool false
    %97 = icmp eq bool %95, %96
    condbr %97, bb1(%1, %2, %86, %87), bb22
bb1(%3: u64, %4: u64, %5: u64, %6: u64):
    %98 = load u64, ptr %76
    %99 = icmp ult u64 %98, %4
    condbr %99, bb2(%3, %4, %5), bb6(%3, %4, %5, %6)
bb2(%7: u64, %8: u64, %9: u64):
    %100, %101 = add.overflow u64 %7, %9
    store u64 %100, ptr %77
    %102 = const i64 8
    %103 = gep i8, ptr %77, %102
    store bool %101, ptr %103
    %104 = const i64 8
    %105 = gep i8, ptr %77, %104
    %106 = load bool, ptr %105
    %107 = const bool false
    %108 = icmp eq bool %106, %107
    condbr %108, bb3(%7, %8, %9), bb22
bb3(%10: u64, %11: u64, %12: u64):
    %109 = load u64, ptr %77
    %110 = call @func.58(%0, %109)
    br bb4(%10, %11, %12, %110)
bb4(%13: u64, %14: u64, %15: u64, %16: u32):
    %111 = zext u32 %16 to u64
    %112 = const u64 4
    %113, %114 = add.overflow u64 %15, %112
    store u64 %113, ptr %78
    %115 = const i64 8
    %116 = gep i8, ptr %78, %115
    store bool %114, ptr %116
    %117 = const i64 8
    %118 = gep i8, ptr %78, %117
    %119 = load bool, ptr %118
    %120 = const bool false
    %121 = icmp eq bool %119, %120
    condbr %121, bb5(%13, %14, %111), bb22
bb5(%17: u64, %18: u64, %19: u64):
    %122 = load u64, ptr %78
    br bb6(%17, %18, %122, %19)
bb6(%20: u64, %21: u64, %22: u64, %23: u64):
    %123 = const u64 1
    %124, %125 = add.overflow u64 %22, %123
    store u64 %124, ptr %79
    %126 = const i64 8
    %127 = gep i8, ptr %79, %126
    store bool %125, ptr %127
    %128 = const i64 8
    %129 = gep i8, ptr %79, %128
    %130 = load bool, ptr %129
    %131 = const bool false
    %132 = icmp eq bool %130, %131
    condbr %132, bb7(%20, %21, %22, %23), bb22
bb7(%24: u64, %25: u64, %26: u64, %27: u64):
    %133 = load u64, ptr %79
    %134 = icmp ult u64 %133, %25
    condbr %134, bb8(%24, %25, %26, %27), bb14(%24, %25, %26, %27)
bb8(%28: u64, %29: u64, %30: u64, %31: u64):
    %135, %136 = add.overflow u64 %28, %30
    store u64 %135, ptr %80
    %137 = const i64 8
    %138 = gep i8, ptr %80, %137
    store bool %136, ptr %138
    %139 = const i64 8
    %140 = gep i8, ptr %80, %139
    %141 = load bool, ptr %140
    %142 = const bool false
    %143 = icmp eq bool %141, %142
    condbr %143, bb9(%28, %29, %30, %31), bb22
bb9(%32: u64, %33: u64, %34: u64, %35: u64):
    %144 = load u64, ptr %80
    %145 = call @func.59(%0, %144)
    br bb10(%32, %33, %34, %35, %145)
bb10(%36: u64, %37: u64, %38: u64, %39: u64, %40: u16):
    %146 = zext u16 %40 to u64
    %147 = const u64 8
    %148, %149 = mul.overflow u64 %38, %147
    store u64 %148, ptr %81
    %150 = const i64 8
    %151 = gep i8, ptr %81, %150
    store bool %149, ptr %151
    %152 = const i64 8
    %153 = gep i8, ptr %81, %152
    %154 = load bool, ptr %153
    %155 = const bool false
    %156 = icmp eq bool %154, %155
    condbr %156, bb11(%36, %37, %38, %39, %146), bb22
bb11(%41: u64, %42: u64, %43: u64, %44: u64, %45: u64):
    %157 = load u64, ptr %81
    %158 = trunc u64 %157 to u32
    %159 = const u32 64
    %160 = icmp ult u32 %158, %159
    condbr %160, bb12(%41, %42, %43, %44, %45, %158), bb22
bb12(%46: u64, %47: u64, %48: u64, %49: u64, %50: u64, %51: u32):
    %161 = zext u32 %51 to u64
    %162 = shl u64 %50, %161
    %163 = or u64 %49, %162
    %164 = const u64 2
    %165, %166 = add.overflow u64 %48, %164
    store u64 %165, ptr %82
    %167 = const i64 8
    %168 = gep i8, ptr %82, %167
    store bool %166, ptr %168
    %169 = const i64 8
    %170 = gep i8, ptr %82, %169
    %171 = load bool, ptr %170
    %172 = const bool false
    %173 = icmp eq bool %171, %172
    condbr %173, bb13(%46, %47, %163), bb22
bb13(%52: u64, %53: u64, %54: u64):
    %174 = load u64, ptr %82
    br bb14(%52, %53, %174, %54)
bb14(%55: u64, %56: u64, %57: u64, %58: u64):
    %175 = icmp ult u64 %57, %56
    condbr %175, bb15(%55, %57, %58), bb21(%58)
bb15(%59: u64, %60: u64, %61: u64):
    %176, %177 = add.overflow u64 %59, %60
    store u64 %176, ptr %83
    %178 = const i64 8
    %179 = gep i8, ptr %83, %178
    store bool %177, ptr %179
    %180 = const i64 8
    %181 = gep i8, ptr %83, %180
    %182 = load bool, ptr %181
    %183 = const bool false
    %184 = icmp eq bool %182, %183
    condbr %184, bb16(%60, %61), bb22
bb16(%62: u64, %63: u64):
    %185 = load u64, ptr %83
    %186 = const i64 8
    %187 = gep i8, ptr %0, %186
    %188 = load u64, ptr %187
    %189 = icmp ult u64 %185, %188
    condbr %189, bb17(%62, %63, %185), bb22
bb17(%64: u64, %65: u64, %66: u64):
    %190 = load ptr, ptr %0
    %191 = gep u8, ptr %190, %66
    %192 = load u8, ptr %191
    %193 = zext u8 %192 to u64
    %194 = const u64 8
    %195, %196 = mul.overflow u64 %64, %194
    store u64 %195, ptr %84
    %197 = const i64 8
    %198 = gep i8, ptr %84, %197
    store bool %196, ptr %198
    %199 = const i64 8
    %200 = gep i8, ptr %84, %199
    %201 = load bool, ptr %200
    %202 = const bool false
    %203 = icmp eq bool %201, %202
    condbr %203, bb18(%64, %65, %193), bb22
bb18(%67: u64, %68: u64, %69: u64):
    %204 = load u64, ptr %84
    %205 = trunc u64 %204 to u32
    %206 = const u32 64
    %207 = icmp ult u32 %205, %206
    condbr %207, bb19(%67, %68, %69, %205), bb22
bb19(%70: u64, %71: u64, %72: u64, %73: u32):
    %208 = zext u32 %73 to u64
    %209 = shl u64 %72, %208
    %210 = or u64 %71, %209
    %211 = const u64 1
    %212, %213 = add.overflow u64 %70, %211
    store u64 %212, ptr %85
    %214 = const i64 8
    %215 = gep i8, ptr %85, %214
    store bool %213, ptr %215
    %216 = const i64 8
    %217 = gep i8, ptr %85, %216
    %218 = load bool, ptr %217
    %219 = const bool false
    %220 = icmp eq bool %218, %219
    condbr %220, bb20(%210), bb22
bb20(%74: u64):
    %221 = load u64, ptr %85
    br bb21(%74)
bb21(%75: u64):
    ret %75
bb22:
    unreachable
}

fn @load_u64_le(functy.55) {
bb0(%0: ptr, %1: u64):
    %56 = alloca (i64, i64), align 8
    %57 = alloca (i64, i64), align 8
    %58 = alloca (i64, i64), align 8
    %59 = alloca (i64, i64), align 8
    %60 = alloca (i64, i64), align 8
    %61 = alloca (i64, i64), align 8
    %62 = alloca (i64, i64), align 8
    %63 = const i64 8
    %64 = gep i8, ptr %0, %63
    %65 = load u64, ptr %64
    %66 = icmp ult u64 %1, %65
    condbr %66, bb1(%1), bb23
bb1(%2: u64):
    %67 = load ptr, ptr %0
    %68 = gep u8, ptr %67, %2
    %69 = load u8, ptr %68
    %70 = zext u8 %69 to u64
    %71 = const u64 1
    %72, %73 = add.overflow u64 %2, %71
    store u64 %72, ptr %56
    %74 = const i64 8
    %75 = gep i8, ptr %56, %74
    store bool %73, ptr %75
    %76 = const i64 8
    %77 = gep i8, ptr %56, %76
    %78 = load bool, ptr %77
    %79 = const bool false
    %80 = icmp eq bool %78, %79
    condbr %80, bb2(%2, %70), bb23
bb2(%3: u64, %4: u64):
    %81 = load u64, ptr %56
    %82 = const i64 8
    %83 = gep i8, ptr %0, %82
    %84 = load u64, ptr %83
    %85 = icmp ult u64 %81, %84
    condbr %85, bb3(%3, %4, %81), bb23
bb3(%5: u64, %6: u64, %7: u64):
    %86 = load ptr, ptr %0
    %87 = gep u8, ptr %86, %7
    %88 = load u8, ptr %87
    %89 = zext u8 %88 to u64
    %90 = const u32 8
    %91 = const u32 64
    %92 = icmp ult u32 %90, %91
    condbr %92, bb4(%5, %6, %89), bb23
bb4(%8: u64, %9: u64, %10: u64):
    %93 = const u32 8
    %94 = zext u32 %93 to u64
    %95 = shl u64 %10, %94
    %96 = or u64 %9, %95
    %97 = const u64 2
    %98, %99 = add.overflow u64 %8, %97
    store u64 %98, ptr %57
    %100 = const i64 8
    %101 = gep i8, ptr %57, %100
    store bool %99, ptr %101
    %102 = const i64 8
    %103 = gep i8, ptr %57, %102
    %104 = load bool, ptr %103
    %105 = const bool false
    %106 = icmp eq bool %104, %105
    condbr %106, bb5(%8, %96), bb23
bb5(%11: u64, %12: u64):
    %107 = load u64, ptr %57
    %108 = const i64 8
    %109 = gep i8, ptr %0, %108
    %110 = load u64, ptr %109
    %111 = icmp ult u64 %107, %110
    condbr %111, bb6(%11, %12, %107), bb23
bb6(%13: u64, %14: u64, %15: u64):
    %112 = load ptr, ptr %0
    %113 = gep u8, ptr %112, %15
    %114 = load u8, ptr %113
    %115 = zext u8 %114 to u64
    %116 = const u32 16
    %117 = const u32 64
    %118 = icmp ult u32 %116, %117
    condbr %118, bb7(%13, %14, %115), bb23
bb7(%16: u64, %17: u64, %18: u64):
    %119 = const u32 16
    %120 = zext u32 %119 to u64
    %121 = shl u64 %18, %120
    %122 = or u64 %17, %121
    %123 = const u64 3
    %124, %125 = add.overflow u64 %16, %123
    store u64 %124, ptr %58
    %126 = const i64 8
    %127 = gep i8, ptr %58, %126
    store bool %125, ptr %127
    %128 = const i64 8
    %129 = gep i8, ptr %58, %128
    %130 = load bool, ptr %129
    %131 = const bool false
    %132 = icmp eq bool %130, %131
    condbr %132, bb8(%16, %122), bb23
bb8(%19: u64, %20: u64):
    %133 = load u64, ptr %58
    %134 = const i64 8
    %135 = gep i8, ptr %0, %134
    %136 = load u64, ptr %135
    %137 = icmp ult u64 %133, %136
    condbr %137, bb9(%19, %20, %133), bb23
bb9(%21: u64, %22: u64, %23: u64):
    %138 = load ptr, ptr %0
    %139 = gep u8, ptr %138, %23
    %140 = load u8, ptr %139
    %141 = zext u8 %140 to u64
    %142 = const u32 24
    %143 = const u32 64
    %144 = icmp ult u32 %142, %143
    condbr %144, bb10(%21, %22, %141), bb23
bb10(%24: u64, %25: u64, %26: u64):
    %145 = const u32 24
    %146 = zext u32 %145 to u64
    %147 = shl u64 %26, %146
    %148 = or u64 %25, %147
    %149 = const u64 4
    %150, %151 = add.overflow u64 %24, %149
    store u64 %150, ptr %59
    %152 = const i64 8
    %153 = gep i8, ptr %59, %152
    store bool %151, ptr %153
    %154 = const i64 8
    %155 = gep i8, ptr %59, %154
    %156 = load bool, ptr %155
    %157 = const bool false
    %158 = icmp eq bool %156, %157
    condbr %158, bb11(%24, %148), bb23
bb11(%27: u64, %28: u64):
    %159 = load u64, ptr %59
    %160 = const i64 8
    %161 = gep i8, ptr %0, %160
    %162 = load u64, ptr %161
    %163 = icmp ult u64 %159, %162
    condbr %163, bb12(%27, %28, %159), bb23
bb12(%29: u64, %30: u64, %31: u64):
    %164 = load ptr, ptr %0
    %165 = gep u8, ptr %164, %31
    %166 = load u8, ptr %165
    %167 = zext u8 %166 to u64
    %168 = const u32 32
    %169 = const u32 64
    %170 = icmp ult u32 %168, %169
    condbr %170, bb13(%29, %30, %167), bb23
bb13(%32: u64, %33: u64, %34: u64):
    %171 = const u32 32
    %172 = zext u32 %171 to u64
    %173 = shl u64 %34, %172
    %174 = or u64 %33, %173
    %175 = const u64 5
    %176, %177 = add.overflow u64 %32, %175
    store u64 %176, ptr %60
    %178 = const i64 8
    %179 = gep i8, ptr %60, %178
    store bool %177, ptr %179
    %180 = const i64 8
    %181 = gep i8, ptr %60, %180
    %182 = load bool, ptr %181
    %183 = const bool false
    %184 = icmp eq bool %182, %183
    condbr %184, bb14(%32, %174), bb23
bb14(%35: u64, %36: u64):
    %185 = load u64, ptr %60
    %186 = const i64 8
    %187 = gep i8, ptr %0, %186
    %188 = load u64, ptr %187
    %189 = icmp ult u64 %185, %188
    condbr %189, bb15(%35, %36, %185), bb23
bb15(%37: u64, %38: u64, %39: u64):
    %190 = load ptr, ptr %0
    %191 = gep u8, ptr %190, %39
    %192 = load u8, ptr %191
    %193 = zext u8 %192 to u64
    %194 = const u32 40
    %195 = const u32 64
    %196 = icmp ult u32 %194, %195
    condbr %196, bb16(%37, %38, %193), bb23
bb16(%40: u64, %41: u64, %42: u64):
    %197 = const u32 40
    %198 = zext u32 %197 to u64
    %199 = shl u64 %42, %198
    %200 = or u64 %41, %199
    %201 = const u64 6
    %202, %203 = add.overflow u64 %40, %201
    store u64 %202, ptr %61
    %204 = const i64 8
    %205 = gep i8, ptr %61, %204
    store bool %203, ptr %205
    %206 = const i64 8
    %207 = gep i8, ptr %61, %206
    %208 = load bool, ptr %207
    %209 = const bool false
    %210 = icmp eq bool %208, %209
    condbr %210, bb17(%40, %200), bb23
bb17(%43: u64, %44: u64):
    %211 = load u64, ptr %61
    %212 = const i64 8
    %213 = gep i8, ptr %0, %212
    %214 = load u64, ptr %213
    %215 = icmp ult u64 %211, %214
    condbr %215, bb18(%43, %44, %211), bb23
bb18(%45: u64, %46: u64, %47: u64):
    %216 = load ptr, ptr %0
    %217 = gep u8, ptr %216, %47
    %218 = load u8, ptr %217
    %219 = zext u8 %218 to u64
    %220 = const u32 48
    %221 = const u32 64
    %222 = icmp ult u32 %220, %221
    condbr %222, bb19(%45, %46, %219), bb23
bb19(%48: u64, %49: u64, %50: u64):
    %223 = const u32 48
    %224 = zext u32 %223 to u64
    %225 = shl u64 %50, %224
    %226 = or u64 %49, %225
    %227 = const u64 7
    %228, %229 = add.overflow u64 %48, %227
    store u64 %228, ptr %62
    %230 = const i64 8
    %231 = gep i8, ptr %62, %230
    store bool %229, ptr %231
    %232 = const i64 8
    %233 = gep i8, ptr %62, %232
    %234 = load bool, ptr %233
    %235 = const bool false
    %236 = icmp eq bool %234, %235
    condbr %236, bb20(%226), bb23
bb20(%51: u64):
    %237 = load u64, ptr %62
    %238 = const i64 8
    %239 = gep i8, ptr %0, %238
    %240 = load u64, ptr %239
    %241 = icmp ult u64 %237, %240
    condbr %241, bb21(%51, %237), bb23
bb21(%52: u64, %53: u64):
    %242 = load ptr, ptr %0
    %243 = gep u8, ptr %242, %53
    %244 = load u8, ptr %243
    %245 = zext u8 %244 to u64
    %246 = const u32 56
    %247 = const u32 64
    %248 = icmp ult u32 %246, %247
    condbr %248, bb22(%52, %245), bb23
bb22(%54: u64, %55: u64):
    %249 = const u32 56
    %250 = zext u32 %249 to u64
    %251 = shl u64 %55, %250
    %252 = or u64 %54, %251
    ret %252
bb23:
    unreachable
}

fn @w_add(functy.56) {
bb0(%0: u64, %1: u64):
    %16 = alloca (i64, i64), align 8
    %17 = alloca (i64, i64), align 8
    %18 = alloca (i64, i64), align 8
    %19 = const u64 4294967295
    %20 = and u64 %0, %19
    %21 = const u64 4294967295
    %22 = and u64 %1, %21
    %23, %24 = add.overflow u64 %20, %22
    store u64 %23, ptr %16
    %25 = const i64 8
    %26 = gep i8, ptr %16, %25
    store bool %24, ptr %26
    %27 = const i64 8
    %28 = gep i8, ptr %16, %27
    %29 = load bool, ptr %28
    %30 = const bool false
    %31 = icmp eq bool %29, %30
    condbr %31, bb1(%0, %1), bb8
bb1(%2: u64, %3: u64):
    %32 = load u64, ptr %16
    %33 = const i32 32
    %34 = bitcast i32 %33 to u32
    %35 = const u32 64
    %36 = icmp ult u32 %34, %35
    condbr %36, bb2(%2, %3, %32), bb8
bb2(%4: u64, %5: u64, %6: u64):
    %37 = const i32 32
    %38 = zext i32 %37 to u64
    %39 = lshr u64 %4, %38
    %40 = const i32 32
    %41 = bitcast i32 %40 to u32
    %42 = const u32 64
    %43 = icmp ult u32 %41, %42
    condbr %43, bb3(%5, %6, %39), bb8
bb3(%7: u64, %8: u64, %9: u64):
    %44 = const i32 32
    %45 = zext i32 %44 to u64
    %46 = lshr u64 %7, %45
    %47, %48 = add.overflow u64 %9, %46
    store u64 %47, ptr %17
    %49 = const i64 8
    %50 = gep i8, ptr %17, %49
    store bool %48, ptr %50
    %51 = const i64 8
    %52 = gep i8, ptr %17, %51
    %53 = load bool, ptr %52
    %54 = const bool false
    %55 = icmp eq bool %53, %54
    condbr %55, bb4(%8), bb8
bb4(%10: u64):
    %56 = load u64, ptr %17
    %57 = const i32 32
    %58 = bitcast i32 %57 to u32
    %59 = const u32 64
    %60 = icmp ult u32 %58, %59
    condbr %60, bb5(%10, %56), bb8
bb5(%11: u64, %12: u64):
    %61 = const i32 32
    %62 = zext i32 %61 to u64
    %63 = lshr u64 %11, %62
    %64, %65 = add.overflow u64 %12, %63
    store u64 %64, ptr %18
    %66 = const i64 8
    %67 = gep i8, ptr %18, %66
    store bool %65, ptr %67
    %68 = const i64 8
    %69 = gep i8, ptr %18, %68
    %70 = load bool, ptr %69
    %71 = const bool false
    %72 = icmp eq bool %70, %71
    condbr %72, bb6(%11), bb8
bb6(%13: u64):
    %73 = load u64, ptr %18
    %74 = const i32 32
    %75 = bitcast i32 %74 to u32
    %76 = const u32 64
    %77 = icmp ult u32 %75, %76
    condbr %77, bb7(%13, %73), bb8
bb7(%14: u64, %15: u64):
    %78 = const i32 32
    %79 = zext i32 %78 to u64
    %80 = shl u64 %15, %79
    %81 = const u64 4294967295
    %82 = and u64 %14, %81
    %83 = or u64 %80, %82
    ret %83
bb8:
    unreachable
}

fn @rotl(functy.57) {
bb0(%0: u64, %1: u32):
    %9 = alloca (i32, i32), align 4
    %10 = const u32 64
    %11 = icmp ult u32 %1, %10
    condbr %11, bb1(%0, %1), bb4
bb1(%2: u64, %3: u32):
    %12 = zext u32 %3 to u64
    %13 = shl u64 %2, %12
    %14 = const u32 64
    %15, %16 = sub.overflow u32 %14, %3
    store u32 %15, ptr %9
    %17 = const i64 4
    %18 = gep i8, ptr %9, %17
    store bool %16, ptr %18
    %19 = const i64 4
    %20 = gep i8, ptr %9, %19
    %21 = load bool, ptr %20
    %22 = const bool false
    %23 = icmp eq bool %21, %22
    condbr %23, bb2(%2, %13), bb4
bb2(%4: u64, %5: u64):
    %24 = load u32, ptr %9
    %25 = const u32 64
    %26 = icmp ult u32 %24, %25
    condbr %26, bb3(%4, %5, %24), bb4
bb3(%6: u64, %7: u64, %8: u32):
    %27 = zext u32 %8 to u64
    %28 = lshr u64 %6, %27
    %29 = or u64 %7, %28
    ret %29
bb4:
    unreachable
}

fn @load_u32_le(functy.58) {
bb0(%0: ptr, %1: u64):
    %24 = alloca (i64, i64), align 8
    %25 = alloca (i64, i64), align 8
    %26 = alloca (i64, i64), align 8
    %27 = const i64 8
    %28 = gep i8, ptr %0, %27
    %29 = load u64, ptr %28
    %30 = icmp ult u64 %1, %29
    condbr %30, bb1(%1), bb11
bb1(%2: u64):
    %31 = load ptr, ptr %0
    %32 = gep u8, ptr %31, %2
    %33 = load u8, ptr %32
    %34 = zext u8 %33 to u64
    %35 = const u64 1
    %36, %37 = add.overflow u64 %2, %35
    store u64 %36, ptr %24
    %38 = const i64 8
    %39 = gep i8, ptr %24, %38
    store bool %37, ptr %39
    %40 = const i64 8
    %41 = gep i8, ptr %24, %40
    %42 = load bool, ptr %41
    %43 = const bool false
    %44 = icmp eq bool %42, %43
    condbr %44, bb2(%2, %34), bb11
bb2(%3: u64, %4: u64):
    %45 = load u64, ptr %24
    %46 = const i64 8
    %47 = gep i8, ptr %0, %46
    %48 = load u64, ptr %47
    %49 = icmp ult u64 %45, %48
    condbr %49, bb3(%3, %4, %45), bb11
bb3(%5: u64, %6: u64, %7: u64):
    %50 = load ptr, ptr %0
    %51 = gep u8, ptr %50, %7
    %52 = load u8, ptr %51
    %53 = zext u8 %52 to u64
    %54 = const u32 8
    %55 = const u32 64
    %56 = icmp ult u32 %54, %55
    condbr %56, bb4(%5, %6, %53), bb11
bb4(%8: u64, %9: u64, %10: u64):
    %57 = const u32 8
    %58 = zext u32 %57 to u64
    %59 = shl u64 %10, %58
    %60 = or u64 %9, %59
    %61 = const u64 2
    %62, %63 = add.overflow u64 %8, %61
    store u64 %62, ptr %25
    %64 = const i64 8
    %65 = gep i8, ptr %25, %64
    store bool %63, ptr %65
    %66 = const i64 8
    %67 = gep i8, ptr %25, %66
    %68 = load bool, ptr %67
    %69 = const bool false
    %70 = icmp eq bool %68, %69
    condbr %70, bb5(%8, %60), bb11
bb5(%11: u64, %12: u64):
    %71 = load u64, ptr %25
    %72 = const i64 8
    %73 = gep i8, ptr %0, %72
    %74 = load u64, ptr %73
    %75 = icmp ult u64 %71, %74
    condbr %75, bb6(%11, %12, %71), bb11
bb6(%13: u64, %14: u64, %15: u64):
    %76 = load ptr, ptr %0
    %77 = gep u8, ptr %76, %15
    %78 = load u8, ptr %77
    %79 = zext u8 %78 to u64
    %80 = const u32 16
    %81 = const u32 64
    %82 = icmp ult u32 %80, %81
    condbr %82, bb7(%13, %14, %79), bb11
bb7(%16: u64, %17: u64, %18: u64):
    %83 = const u32 16
    %84 = zext u32 %83 to u64
    %85 = shl u64 %18, %84
    %86 = or u64 %17, %85
    %87 = const u64 3
    %88, %89 = add.overflow u64 %16, %87
    store u64 %88, ptr %26
    %90 = const i64 8
    %91 = gep i8, ptr %26, %90
    store bool %89, ptr %91
    %92 = const i64 8
    %93 = gep i8, ptr %26, %92
    %94 = load bool, ptr %93
    %95 = const bool false
    %96 = icmp eq bool %94, %95
    condbr %96, bb8(%86), bb11
bb8(%19: u64):
    %97 = load u64, ptr %26
    %98 = const i64 8
    %99 = gep i8, ptr %0, %98
    %100 = load u64, ptr %99
    %101 = icmp ult u64 %97, %100
    condbr %101, bb9(%19, %97), bb11
bb9(%20: u64, %21: u64):
    %102 = load ptr, ptr %0
    %103 = gep u8, ptr %102, %21
    %104 = load u8, ptr %103
    %105 = zext u8 %104 to u64
    %106 = const u32 24
    %107 = const u32 64
    %108 = icmp ult u32 %106, %107
    condbr %108, bb10(%20, %105), bb11
bb10(%22: u64, %23: u64):
    %109 = const u32 24
    %110 = zext u32 %109 to u64
    %111 = shl u64 %23, %110
    %112 = or u64 %22, %111
    %113 = trunc u64 %112 to u32
    ret %113
bb11:
    unreachable
}

fn @load_u16_le(functy.59) {
bb0(%0: ptr, %1: u64):
    %8 = alloca (i64, i64), align 8
    %9 = const i64 8
    %10 = gep i8, ptr %0, %9
    %11 = load u64, ptr %10
    %12 = icmp ult u64 %1, %11
    condbr %12, bb1(%1), bb5
bb1(%2: u64):
    %13 = load ptr, ptr %0
    %14 = gep u8, ptr %13, %2
    %15 = load u8, ptr %14
    %16 = zext u8 %15 to u64
    %17 = const u64 1
    %18, %19 = add.overflow u64 %2, %17
    store u64 %18, ptr %8
    %20 = const i64 8
    %21 = gep i8, ptr %8, %20
    store bool %19, ptr %21
    %22 = const i64 8
    %23 = gep i8, ptr %8, %22
    %24 = load bool, ptr %23
    %25 = const bool false
    %26 = icmp eq bool %24, %25
    condbr %26, bb2(%16), bb5
bb2(%3: u64):
    %27 = load u64, ptr %8
    %28 = const i64 8
    %29 = gep i8, ptr %0, %28
    %30 = load u64, ptr %29
    %31 = icmp ult u64 %27, %30
    condbr %31, bb3(%3, %27), bb5
bb3(%4: u64, %5: u64):
    %32 = load ptr, ptr %0
    %33 = gep u8, ptr %32, %5
    %34 = load u8, ptr %33
    %35 = zext u8 %34 to u64
    %36 = const u32 8
    %37 = const u32 64
    %38 = icmp ult u32 %36, %37
    condbr %38, bb4(%4, %35), bb5
bb4(%6: u64, %7: u64):
    %39 = const u32 8
    %40 = zext u32 %39 to u64
    %41 = shl u64 %7, %40
    %42 = or u64 %6, %41
    %43 = trunc u64 %42 to u16
    ret %43
bb5:
    unreachable
}
"##;
