//! R4 STAGE 2 — str BYTE ACCESS + str-ITERATOR ELEMENTS + the `.rec`-INTERNING
//! DE-MODELING (thread R4). Round 3 landed stage 1 (&'static str literals as
//! immortal (ptr,len) heap-image pairs); this file proves stage 2: the JIT
//! machine code now READS those bytes IN-MODULE — `str::as_bytes` / `str::len`
//! / `str::bytes` / `<[u8]>::iter` / the blanket-identity `into_iter` and the
//! `str::Bytes` `next` all lower to fat-pair lane reads + cursor arithmetic
//! (no call, no extern) — and, on top of that, clean-kernel's
//! `Name::from_string_uncached` runs UNROLLED over literal parts with the REAL
//! recursive `Name` (Arc parent chain, `Arc<str>` payload), its `cached_hash`
//! BIT-IDENTICAL to the real clean-kernel at every node, and the
//! mutual-recursor `.rec` boundary de-modeled: `rec_name_of` now CONSTRUCTS
//! ind/rec names in-module and selects by REAL `Name` equality — no
//! pre-interned RecPair table.
//!
//! FRONTEND (r4-str-stage2 worktree, branch off trust-ir 6787ae6,
//! frontend/src/mir_lower.rs only, ADDITIVE):
//!   * `StrInlineOp` — `str::as_bytes` (fat-pair 2-lane copy), `str::len`
//!     (metadata-lane load), `str::bytes` + `<[u8]>::iter` (cursor init
//!     cur=ptr,end=ptr+len at +0/+8), blanket `impl<I: Iterator> IntoIterator
//!     for I` identity (aggregate copy; gated to the modeled u8-iterator
//!     states via the impl's UNINSTANTIATED Self being a bare type param —
//!     concrete `&[T]`/`&Vec<T>`/`Vec<T>` impls untouched).
//!   * `IterKind::StrBytes` — `<str::Bytes as Iterator>::next` inlined
//!     (`Some(u8)` by value; `Bytes<'a>` has no type arg — the round-1 T3
//!     "iterator has no element type arg" gap, closed).
//!     NO-DRIFT: re-emits of the whnf gold (`_baseline_whnf.tir`, 115661 bytes)
//!     and of `str_const_ident_root` (vs the const in e2e_str_const_lowering.rs)
//!     are BYTE-IDENTICAL under this frontend. `<[u8]>::iter` is u8-gated and
//!     `Arc<str>` deref is NOT inlined precisely to preserve the landed extern
//!     surfaces (`<[Constant]>::iter`, `<Arc<str> as Deref>::deref` in the
//!     round-1 fixtures).
//!
//! MODELED BOUNDARIES (documented in the slice header too):
//!   * stage-1 address identity / allocation count (unchanged);
//!   * `Arc<str>` crossings: `Arc::<str>::from` (the allocation) and
//!     `<Arc<str> as Deref>::deref` (identity-shaped) are extern + FAITHFUL
//!     host shims calling the real alloc machinery — deref-as-extern is the
//!     LANDED convention (round-1 fixtures), kept for no-drift;
//!   * `wrapping_mul`/`wrapping_add` extern leaf shims (the whnf-gold
//!     convention — inlining them would drift the gate);
//!   * drops not emitted (leak model). `Arc::new(Name)` and `Arc<Name>` deref
//!     are INLINED in-module (landed RUNG 5/6) — the parent chain never
//!     leaves the module.
//!
//! ORACLES (three, independent):
//!   1. Native PRODUCTION-FORM transcriptions in this file: `mix_hash`
//!      verbatim; `murmur_hash_64a` in the as-chunks/block form
//!      (`chunks_exact(8)` + `from_le_bytes` + tail-enumerate — the module
//!      carries the INDEX-LOOP transcription, so agreement here proves
//!      [T-murmur-idx] on every tested input); `from_string_uncached` with the
//!      REAL `split('.')` + REAL `str::parse::<u64>()` (the module carries the
//!      UNROLLED fold + parse transcription, so agreement proves [T-unroll] +
//!      [T-parse]).
//!   2. GOLDEN CONSTANTS pinned from the REAL clean-kernel binary
//!      ($HOME/clean/crates/clean-kernel, `Name::from_string(s).lean4_hash()`,
//!      2026-07-03): Tree.rec=0x293412c406e2a88e, Forest.rec=
//!      0x6d912edca1677fc9, Nat.42.rec=0xa5a77a7093d17e6f,
//!      VeryLongPartName.rec=0xdb80a1b49b5a786f, 0.rec=0x8e52403ea5048303,
//!      Tree=0x799c131f2f585927, Forest=0x67467aab1408ef94,
//!      Nat.42=0x8b3462f30ba63902, Nat.43=0xa28f7c8b558963cd,
//!      Dead.rec=0x6948d04776fff93c, anon=1723.
//!   3. Per-node RAW-MEMORY decode of the JIT-built Name (tag@0: 0=Anon 1=Str
//!      2=Num; payload@8; cached_hash@32; ArcInner header 16 bytes, repr(C) —
//!      offsets read off the emitted IR itself) with the hash chain RECOMPUTED
//!      host-side from the STORED Arc<str> bytes — bit-identical at EVERY node.
//!
//! Slice (verbatim transcription + regen instructions):
//!   tests/slices/str_stage2_slice.rs
//! All four embedded modules emitted with the r4-str-stage2 frontend;
//! validate_module = 0 error(s), re-parse OK for all four; re-asserted at test
//! time.
//!
//! REGEN (per module):
//!   S=$HOME/trust/build/aarch64-apple-darwin/stage1
//!   cd <r4-str-stage2 worktree>/frontend && env -u RUSTUP_TOOLCHAIN \
//!     RUSTC=$S/bin/rustc \
//!     DYLD_LIBRARY_PATH=$S/lib/rustlib/aarch64-apple-darwin/lib \
//!     $S/bin/cargo run --bin trust_ir_mir -- \
//!     ../../trust-cg/crates/trust-cg-codegen/tests/slices/str_stage2_slice.rs \
//!     --crate-type=lib --mir-emit-closure <root> <out.tir>
//!
//! HANG SAFETY: every JIT compile+execute runs on a WATCHDOG worker thread
//! (180s bound; a hung worker leaks the buffer, never frees machine code
//! under execution). COVERAGE: aarch64-gated. Run ONE TEST PER PROCESS:
//!   perl -e 'alarm 300; exec @ARGV' -- cargo test -p trust-cg-codegen \
//!     --test e2e_str_stage2 -- --exact <name> --test-threads=1

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::sync::Arc;
use std::sync::mpsc;
use std::time::Duration;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

// ── shared harness (the e2e_str_const_lowering.rs discipline) ───────────────

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

/// The module-side fat pair layout: [data ptr at +0, byte length at +8].
#[repr(C)]
#[derive(Clone, Copy)]
struct FatPair {
    ptr: *const u8,
    len: u64,
}

extern "C" fn shim_rust_alloc(size: usize, align: usize) -> *mut u8 {
    unsafe {
        let layout = std::alloc::Layout::from_size_align(size, align).expect("valid layout");
        std::alloc::alloc(layout)
    }
}

extern "C" fn shim_wrapping_mul_u64(a: u64, b: u64) -> u64 {
    a.wrapping_mul(b)
}

extern "C" fn shim_wrapping_add_u64(a: u64, b: u64) -> u64 {
    a.wrapping_add(b)
}

extern "C" fn shim_wrapping_mul_usize(a: usize, b: usize) -> usize {
    a.wrapping_mul(b)
}

/// FAITHFUL `Arc::<str>::from(&str)` shim (sret 16-byte Arc<str> value +
/// (ptr,len) pair by ref): builds a REAL `Arc<str>` (real ArcInner allocation,
/// real refcounts, bytes copied verbatim) and moves the 16-byte Arc VALUE into
/// the module's slot. The Arc intentionally leaks (the landed leak model).
extern "C" fn shim_arc_str_from(sret: *mut u8, pair: *const FatPair) {
    unsafe {
        let p = *pair;
        let s = std::str::from_utf8(std::slice::from_raw_parts(p.ptr, p.len as usize))
            .expect("Arc::<str>::from shim received non-UTF8 bytes — a corrupted literal image");
        let a: Arc<str> = Arc::from(s);
        std::ptr::write(sret as *mut Arc<str>, a);
    }
}

/// FAITHFUL `<Arc<str> as Deref>::deref` shim (sret (ptr,len) pair + thin
/// `&Arc<str>`): calls the REAL deref. Identity-shaped (ArcInner data ptr +
/// len) — the byte COMPARISON over the returned pair runs back in-module.
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

// Extern symbol names read VERBATIM from the emitted modules (v0 mangling;
// instantiating crate = the slice crate).
const SYM_WRAPPING_MUL_U64: &str = "_RNvMs7_NtCs2EYQwhfuABO_4core3numy12wrapping_mul";
const SYM_WRAPPING_ADD_U64: &str = "_RNvMs7_NtCs2EYQwhfuABO_4core3numy12wrapping_add";
const SYM_WRAPPING_MUL_USIZE: &str = "_RNvMs9_NtCs2EYQwhfuABO_4core3numj12wrapping_mul";
const SYM_ARC_STR_FROM: &str = "_RNvXs17_NtCskTzINo8ZBH9_5alloc4syncINtB6_3ArceEINtNtCs2EYQwhfuABO_4core7convert4FromReE4fromCs77po20IQdNn_16str_stage2_slice";
const SYM_ARC_STR_DEREF: &str = "_RNvXsw_NtCskTzINo8ZBH9_5alloc4syncINtB5_3ArceENtNtNtCs2EYQwhfuABO_4core3ops5deref5Deref5derefCs77po20IQdNn_16str_stage2_slice";

fn stage2_externs() -> HashMap<String, *const u8> {
    let mut e: HashMap<String, *const u8> = HashMap::new();
    e.insert("__rust_alloc".to_string(), shim_rust_alloc as *const u8);
    e.insert(
        SYM_WRAPPING_MUL_U64.to_string(),
        shim_wrapping_mul_u64 as *const u8,
    );
    e.insert(
        SYM_WRAPPING_ADD_U64.to_string(),
        shim_wrapping_add_u64 as *const u8,
    );
    e.insert(
        SYM_WRAPPING_MUL_USIZE.to_string(),
        shim_wrapping_mul_usize as *const u8,
    );
    e.insert(SYM_ARC_STR_FROM.to_string(), shim_arc_str_from as *const u8);
    e.insert(
        SYM_ARC_STR_DEREF.to_string(),
        shim_arc_str_deref as *const u8,
    );
    e
}

fn run_with_watchdog<T: Send + 'static>(what: &str, f: impl FnOnce() -> T + Send + 'static) -> T {
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let _ = tx.send(f());
    });
    match rx.recv_timeout(Duration::from_secs(180)) {
        Ok(v) => v,
        Err(_) => panic!("WATCHDOG: `{what}` did not complete within 180s (JIT hang?)"),
    }
}

// ── native oracle 1: PRODUCTION-FORM transcriptions ─────────────────────────

/// clean-kernel expr/meta.rs mix_hash — VERBATIM.
fn native_mix_hash(h: u64, k: u64) -> u64 {
    const M: u64 = 0xc6a4_a793_5bd1_e995;
    const R: u32 = 47;
    let mut k = k.wrapping_mul(M);
    k ^= k >> R;
    k ^= M;
    let mut h = h ^ k;
    h = h.wrapping_mul(M);
    h
}

/// clean-kernel murmur_hash_64a in the PRODUCTION block form: 8-byte chunks +
/// `u64::from_le_bytes` + enumerate-tail (`as_chunks` ≡ `chunks_exact(8)` +
/// remainder). The MODULE carries the index-loop transcription — agreement
/// here proves [T-murmur-idx] on every tested input.
fn native_murmur_hash_64a(data: &[u8], seed: u64) -> u64 {
    const M: u64 = 0xc6a4_a793_5bd1_e995;
    const R: u32 = 47;
    let len = data.len();
    let mut h: u64 = seed ^ (len as u64).wrapping_mul(M);
    let mut chunks = data.chunks_exact(8);
    for block in &mut chunks {
        let mut k = u64::from_le_bytes(block.try_into().expect("8-byte chunk"));
        k = k.wrapping_mul(M);
        k ^= k >> (R & 63);
        k = k.wrapping_mul(M);
        h ^= k;
        h = h.wrapping_mul(M);
    }
    let tail = chunks.remainder();
    for (i, &b) in tail.iter().enumerate() {
        h ^= (b as u64) << (i.wrapping_mul(8) & 63);
    }
    if !tail.is_empty() {
        h = h.wrapping_mul(M);
    }
    h ^= h >> (R & 63);
    h = h.wrapping_mul(M);
    h ^= h >> (R & 63);
    h
}

/// A decoded Name component, leaf-to-root.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Comp {
    Str(Vec<u8>),
    Num(u64),
}

/// Native `from_string_uncached` with the REAL `split('.')` + REAL
/// `str::parse::<u64>()` (production name.rs:557-565 verbatim over the comp
/// list): returns (leaf-to-root comps, cached_hash chain value). The module
/// carries the UNROLLED fold + the parse transcription — agreement proves
/// [T-unroll] + [T-parse].
fn native_from_string_uncached(s: &str) -> (Vec<Comp>, u64) {
    let mut comps_root_to_leaf: Vec<Comp> = Vec::new();
    let mut h: u64 = 1723; // anon
    for part in s.split('.') {
        if let Ok(n) = part.parse::<u64>() {
            h = native_mix_hash(h, n);
            comps_root_to_leaf.push(Comp::Num(n));
        } else {
            h = native_mix_hash(h, native_murmur_hash_64a(part.as_bytes(), 11));
            comps_root_to_leaf.push(Comp::Str(part.as_bytes().to_vec()));
        }
    }
    let mut leaf_to_root = comps_root_to_leaf;
    leaf_to_root.reverse();
    (leaf_to_root, h)
}

// ── native oracle 2: GOLDEN constants from the REAL clean-kernel binary ─────
// ($HOME/clean clean-kernel, `Name::from_string(s).lean4_hash()`, 2026-07-03.)

const GOLDEN_TREE_REC: u64 = 0x293412c406e2a88e;
const GOLDEN_FOREST_REC: u64 = 0x6d912edca1677fc9;
const GOLDEN_NAT_42_REC: u64 = 0xa5a77a7093d17e6f;
const GOLDEN_LONG_REC: u64 = 0xdb80a1b49b5a786f; // VeryLongPartName.rec
const GOLDEN_ZERO_REC: u64 = 0x8e52403ea5048303; // 0.rec

// ── the JIT-side raw Name decode ─────────────────────────────────────────────
// Offsets read off the emitted IR itself (see name_anon / name_num_part in the
// embedded modules): Name = 40 bytes { NameInner @0..32, cached_hash @32 };
// NameInner tag = i64 @0 (source order: 0=Anon, 1=Str, 2=Num); Str payload =
// { Arc<Name> (ArcInner base ptr) @8, Arc<str> (ArcInner base ptr @16, len
// @24) }; Num payload is FIELD-REORDERED by layout: { u64 @8, Arc<Name> @16 }
// (both read verbatim off name_str_part/name_num_part). ArcInner is repr(C):
// { strong @0, weak @8, data @16 } — both the module's inlined Arc::new(Name)
// blocks and the shim-built real Arc<str> blocks carry data at +16.

/// Walk a JIT-built Name at `ptr`: returns (leaf-to-root comps, root hash,
/// per-node hashes leaf-to-root). Panics on an unknown tag (fail-loud decode).
unsafe fn decode_jit_name(ptr: *const u8) -> (Vec<Comp>, u64, Vec<u64>) {
    unsafe {
        let mut comps = Vec::new();
        let mut node_hashes = Vec::new();
        let read_u64 = |p: *const u8| -> u64 { (p as *const u64).read_unaligned() };
        let read_ptr = |p: *const u8| -> *const u8 { (p as *const *const u8).read_unaligned() };
        let root_hash = read_u64(ptr.add(32));
        let mut cur = ptr;
        loop {
            let tag = read_u64(cur);
            node_hashes.push(read_u64(cur.add(32)));
            match tag {
                0 => break,
                1 => {
                    let parent_inner = read_ptr(cur.add(8));
                    let s_inner = read_ptr(cur.add(16));
                    let s_len = read_u64(cur.add(24)) as usize;
                    let bytes = std::slice::from_raw_parts(s_inner.add(16), s_len).to_vec();
                    comps.push(Comp::Str(bytes));
                    cur = parent_inner.add(16);
                }
                2 => {
                    // NOTE the Num payload is FIELD-REORDERED by layout
                    // (verbatim from the emitted name_num_part stores):
                    // n (u64) @ +8, Arc<Name> parent @ +16.
                    let n = read_u64(cur.add(8));
                    let parent_inner = read_ptr(cur.add(16));
                    comps.push(Comp::Num(n));
                    cur = parent_inner.add(16);
                }
                t => panic!("decode_jit_name: unknown NameInner tag {t} (layout drift?)"),
            }
        }
        (comps, root_hash, node_hashes)
    }
}

/// Recompute the production hash chain from decoded comps (leaf-to-root):
/// returns per-node hashes leaf-to-root INCLUDING the final Anon node (1723).
fn recompute_hash_chain(comps: &[Comp]) -> Vec<u64> {
    // Build root-to-leaf running hashes, then reverse.
    let mut fwd = vec![1723u64];
    for c in comps.iter().rev() {
        let prev = *fwd.last().unwrap();
        let h = match c {
            Comp::Str(b) => native_mix_hash(prev, native_murmur_hash_64a(b, 11)),
            Comp::Num(n) => native_mix_hash(prev, *n),
        };
        fwd.push(h);
    }
    fwd.reverse();
    fwd
}

// ── the literals swept by the byte roots (mirror of the slice's pick_lit) ───

const LITS: [&str; 5] = [
    "rec",
    "Tree.rec",
    "VeryLongPartName",
    "VeryLongPartName.rec",
    "",
];

// ═══════════════════════════════════════════════════════════════════════════
// Embedded MIR-closure emits (verbatim r4-str-stage2 frontend output)
// ═══════════════════════════════════════════════════════════════════════════

/// VERBATIM `--mir-emit-closure str_stage2_bytes_root` emit of tests/slices/str_stage2_slice.rs (r4-str-stage2 frontend). 28994 bytes; 4 closure members; validate_module = 0; re-parse OK.
const BYTES_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::str_stage2_bytes_root"
target "aarch64-apple-darwin" 8 little
file 0 "str_stage2_slice.rs"

functy.0 = (u64, u64) -> (u64)

functy.1 = (u64, u64) -> (u64)

functy.2 = (u64, u64) -> (u64)

functy.3 = (ptr, u64) -> ()

functy.4 = (u64, u64) -> (u64)

functy.5 = (u64, u64) -> (u64)

functy.6 = (ptr, u64) -> (u64)

functy.7 = (ptr, ptr) -> (bool)

fn @_RNvMs7_NtCs2EYQwhfuABO_4core3numy12wrapping_mul(functy.0) {
}

fn @_RNvMs7_NtCs2EYQwhfuABO_4core3numy12wrapping_add(functy.1) {
}

fn @str_stage2_bytes_root(functy.2) {
bb0(%0: u64, %1: u64):
    %37 = alloca (i64, i64), align 8
    %38 = alloca (i64, i64), align 8
    %39 = alloca (i64, i64), align 8
    %40 = alloca (i64, i64), align 8
    %41 = alloca (i64, i64), align 8
    %42 = alloca (i64, i64), align 8
    %43 = alloca (i64, i64), align 8
    %44 = alloca (i8, i8), align 1
    %45 = alloca (i64, i64), align 8
    %46 = alloca (i64, i64), align 8
    %47 = alloca (i64, i64), align 8
    %48 = alloca (i64, i64), align 8
    %49 = alloca (i64, i64), align 8
    %50 = alloca i64, align 8
    %51 = alloca (i64, i64), align 8
    %52 = alloca (i64, i64), align 8
    %53 = alloca (i64, i64), align 8
    %54 = alloca (i64, i64), align 8
    %55 = alloca (i64, i64), align 8
    %56 = alloca (i64, i64), align 8
    %57 = alloca (i64, i64), align 8
    %58 = alloca (i64, i64), align 8
    %59 = const i64 4
    %60 = heap_alloc rust_heap i8, %59, align 1
    %61 = const u8 84
    store u8 %61, ptr %60
    %62 = const i64 1
    %63 = gep i8, ptr %60, %62
    %64 = const u8 114
    store u8 %64, ptr %63
    %65 = const i64 2
    %66 = gep i8, ptr %60, %65
    %67 = const u8 101
    store u8 %67, ptr %66
    %68 = const i64 3
    %69 = gep i8, ptr %60, %68
    %70 = const u8 101
    store u8 %70, ptr %69
    %71 = alloca (i64, i64), align 8
    store ptr %60, ptr %71
    %72 = const i64 8
    %73 = gep i8, ptr %71, %72
    %74 = const u64 4
    store u64 %74, ptr %73
    %75 = const i64 4
    %76 = heap_alloc rust_heap i8, %75, align 1
    %77 = const u8 84
    store u8 %77, ptr %76
    %78 = const i64 1
    %79 = gep i8, ptr %76, %78
    %80 = const u8 114
    store u8 %80, ptr %79
    %81 = const i64 2
    %82 = gep i8, ptr %76, %81
    %83 = const u8 101
    store u8 %83, ptr %82
    %84 = const i64 3
    %85 = gep i8, ptr %76, %84
    %86 = const u8 88
    store u8 %86, ptr %85
    %87 = alloca (i64, i64), align 8
    store ptr %76, ptr %87
    %88 = const i64 8
    %89 = gep i8, ptr %87, %88
    %90 = const u64 4
    store u64 %90, ptr %89
    %91 = const i64 3
    %92 = heap_alloc rust_heap i8, %91, align 1
    %93 = const u8 84
    store u8 %93, ptr %92
    %94 = const i64 1
    %95 = gep i8, ptr %92, %94
    %96 = const u8 114
    store u8 %96, ptr %95
    %97 = const i64 2
    %98 = gep i8, ptr %92, %97
    %99 = const u8 101
    store u8 %99, ptr %98
    %100 = alloca (i64, i64), align 8
    store ptr %92, ptr %100
    %101 = const i64 8
    %102 = gep i8, ptr %100, %101
    %103 = const u64 3
    store u64 %103, ptr %102
    %104 = const i64 1
    %105 = heap_alloc rust_heap i8, %104, align 1
    %106 = alloca (i64, i64), align 8
    store ptr %105, ptr %106
    %107 = const i64 8
    %108 = gep i8, ptr %106, %107
    %109 = const u64 0
    store u64 %109, ptr %108
    %110 = const u64 0
    %111 = icmp eq u64 %0, %110
    condbr %111, bb1(%1), bb4(%0, %1)
bb1(%2: u64):
    call @func.3(%37, %2)
    br bb2
bb2:
    %112 = load i64, ptr %37
    store i64 %112, ptr %38
    %113 = const i64 8
    %114 = gep i8, ptr %37, %113
    %115 = const i64 8
    %116 = gep i8, ptr %38, %115
    %117 = load i64, ptr %114
    store i64 %117, ptr %116
    br bb3
bb3:
    %118 = const u64 11
    %119 = call @func.6(%38, %118)
    br bb42(%119)
bb4(%3: u64, %4: u64):
    %120 = const u64 1
    %121 = icmp eq u64 %3, %120
    condbr %121, bb5(%4), bb8(%3, %4)
bb5(%5: u64):
    call @func.3(%39, %5)
    br bb6
bb6:
    %122 = const i64 8
    %123 = gep i8, ptr %39, %122
    %124 = load u64, ptr %123
    br bb7(%124)
bb7(%6: u64):
    br bb42(%6)
bb8(%7: u64, %8: u64):
    %125 = const u64 2
    %126 = icmp eq u64 %7, %125
    condbr %126, bb9(%8), bb20(%7, %8)
bb9(%9: u64):
    call @func.3(%40, %9)
    br bb10
bb10:
    %127 = const u64 0
    %128 = load ptr, ptr %40
    %129 = const i64 8
    %130 = gep i8, ptr %40, %129
    %131 = load i64, ptr %130
    %132 = gep i8, ptr %128, %131
    store ptr %128, ptr %42
    %133 = const i64 8
    %134 = gep i8, ptr %42, %133
    store ptr %132, ptr %134
    br bb11(%127)
bb11(%10: u64):
    %135 = load i64, ptr %42
    store i64 %135, ptr %41
    %136 = const i64 8
    %137 = gep i8, ptr %42, %136
    %138 = const i64 8
    %139 = gep i8, ptr %41, %138
    %140 = load i64, ptr %137
    store i64 %140, ptr %139
    br bb12(%10)
bb12(%11: u64):
    %141 = load i64, ptr %41
    store i64 %141, ptr %43
    %142 = const i64 8
    %143 = gep i8, ptr %41, %142
    %144 = const i64 8
    %145 = gep i8, ptr %43, %144
    %146 = load i64, ptr %143
    store i64 %146, ptr %145
    br bb13(%11)
bb13(%12: u64):
    %147 = load ptr, ptr %43
    %148 = const i64 8
    %149 = gep i8, ptr %43, %148
    %150 = load ptr, ptr %149
    %151 = ptrtoint ptr %147 to u64
    %152 = ptrtoint ptr %150 to u64
    %153 = icmp ult u64 %151, %152
    condbr %153, bb43, bb44
bb14(%13: u64):
    %161 = load i8, ptr %44
    %162 = sext i8 %161 to i64
    switch %162 [ 0: bb17(%13) 1: bb16(%13) default: bb15 ]
bb15:
    unreachable
bb16(%14: u64):
    %163 = const i64 1
    %164 = gep i8, ptr %44, %163
    %165 = load u8, ptr %164
    %166 = const u64 31
    %167 = call @func.0(%14, %166)
    br bb18(%165, %167)
bb17(%15: u64):
    br bb42(%15)
bb18(%16: u8, %17: u64):
    %168 = zext u8 %16 to u64
    %169 = call @func.1(%17, %168)
    br bb19(%169)
bb19(%18: u64):
    br bb13(%18)
bb20(%19: u64, %20: u64):
    %170 = const u64 3
    %171 = icmp eq u64 %19, %170
    condbr %171, bb21(%20), bb32(%20)
bb21(%21: u64):
    call @func.3(%45, %21)
    br bb22
bb22:
    %172 = const u64 0
    %173 = load i64, ptr %45
    store i64 %173, ptr %48
    %174 = const i64 8
    %175 = gep i8, ptr %45, %174
    %176 = const i64 8
    %177 = gep i8, ptr %48, %176
    %178 = load i64, ptr %175
    store i64 %178, ptr %177
    br bb23(%172)
bb23(%22: u64):
    %179 = load ptr, ptr %48
    %180 = const i64 8
    %181 = gep i8, ptr %48, %180
    %182 = load i64, ptr %181
    %183 = gep i8, ptr %179, %182
    store ptr %179, ptr %47
    %184 = const i64 8
    %185 = gep i8, ptr %47, %184
    store ptr %183, ptr %185
    br bb24(%22)
bb24(%23: u64):
    %186 = load i64, ptr %47
    store i64 %186, ptr %46
    %187 = const i64 8
    %188 = gep i8, ptr %47, %187
    %189 = const i64 8
    %190 = gep i8, ptr %46, %189
    %191 = load i64, ptr %188
    store i64 %191, ptr %190
    br bb25(%23)
bb25(%24: u64):
    %192 = load i64, ptr %46
    store i64 %192, ptr %49
    %193 = const i64 8
    %194 = gep i8, ptr %46, %193
    %195 = const i64 8
    %196 = gep i8, ptr %49, %195
    %197 = load i64, ptr %194
    store i64 %197, ptr %196
    br bb26(%24)
bb26(%25: u64):
    %198 = load ptr, ptr %49
    %199 = const i64 8
    %200 = gep i8, ptr %49, %199
    %201 = load ptr, ptr %200
    %202 = ptrtoint ptr %198 to u64
    %203 = ptrtoint ptr %201 to u64
    %204 = icmp ult u64 %202, %203
    condbr %204, bb45, bb46
bb27(%26: u64):
    %208 = load i64, ptr %50
    %209 = const i64 0
    %210 = icmp eq i64 %208, %209
    %211 = const i64 0
    %212 = const i64 1
    %213 = select i64 %210, %211, %212
    switch %213 [ 0: bb29(%26) 1: bb28(%26) default: bb15 ]
bb28(%27: u64):
    %214 = load ptr, ptr %50
    %215 = load u8, ptr %214
    %216 = const u64 31
    %217 = call @func.0(%27, %216)
    br bb30(%215, %217)
bb29(%28: u64):
    br bb42(%28)
bb30(%29: u8, %30: u64):
    %218 = zext u8 %29 to u64
    %219 = call @func.1(%30, %218)
    br bb31(%219)
bb31(%31: u64):
    br bb26(%31)
bb32(%32: u64):
    %220 = const u64 0
    %221 = icmp eq u64 %32, %220
    condbr %221, bb33, bb34(%32)
bb33:
    store ptr %60, ptr %51
    %222 = const i64 8
    %223 = gep i8, ptr %51, %222
    %224 = const u64 4
    store u64 %224, ptr %223
    store ptr %60, ptr %52
    %225 = const i64 8
    %226 = gep i8, ptr %52, %225
    %227 = const u64 4
    store u64 %227, ptr %226
    %228 = call @func.7(%51, %52)
    br bb39(%228)
bb34(%33: u64):
    %229 = const u64 1
    %230 = icmp eq u64 %33, %229
    condbr %230, bb35, bb36(%33)
bb35:
    store ptr %60, ptr %53
    %231 = const i64 8
    %232 = gep i8, ptr %53, %231
    %233 = const u64 4
    store u64 %233, ptr %232
    store ptr %76, ptr %54
    %234 = const i64 8
    %235 = gep i8, ptr %54, %234
    %236 = const u64 4
    store u64 %236, ptr %235
    %237 = call @func.7(%53, %54)
    br bb39(%237)
bb36(%34: u64):
    %238 = const u64 2
    %239 = icmp eq u64 %34, %238
    condbr %239, bb37, bb38
bb37:
    store ptr %60, ptr %55
    %240 = const i64 8
    %241 = gep i8, ptr %55, %240
    %242 = const u64 4
    store u64 %242, ptr %241
    store ptr %92, ptr %56
    %243 = const i64 8
    %244 = gep i8, ptr %56, %243
    %245 = const u64 3
    store u64 %245, ptr %244
    %246 = call @func.7(%55, %56)
    br bb39(%246)
bb38:
    store ptr %105, ptr %57
    %247 = const i64 8
    %248 = gep i8, ptr %57, %247
    %249 = const u64 0
    store u64 %249, ptr %248
    store ptr %105, ptr %58
    %250 = const i64 8
    %251 = gep i8, ptr %58, %250
    %252 = const u64 0
    store u64 %252, ptr %251
    %253 = call @func.7(%57, %58)
    br bb39(%253)
bb39(%35: bool):
    condbr %35, bb40, bb41
bb40:
    %254 = const u64 1
    br bb42(%254)
bb41:
    %255 = const u64 0
    br bb42(%255)
bb42(%36: u64):
    ret %36
bb43:
    %154 = const i64 1
    %155 = gep i8, ptr %147, %154
    store ptr %155, ptr %43
    %156 = const i64 1
    %157 = gep i8, ptr %44, %156
    %158 = load u8, ptr %147
    store u8 %158, ptr %157
    %159 = const i8 1
    store i8 %159, ptr %44
    br bb14(%12)
bb44:
    %160 = const i8 0
    store i8 %160, ptr %44
    br bb14(%12)
bb45:
    %205 = const i64 1
    %206 = gep i8, ptr %198, %205
    store ptr %206, ptr %49
    store ptr %198, ptr %50
    br bb27(%25)
bb46:
    %207 = const i64 0
    store i64 %207, ptr %50
    br bb27(%25)
}

fn @pick_lit(functy.3) {
bb0(%0: ptr, %1: u64):
    %5 = const i64 3
    %6 = heap_alloc rust_heap i8, %5, align 1
    %7 = const u8 114
    store u8 %7, ptr %6
    %8 = const i64 1
    %9 = gep i8, ptr %6, %8
    %10 = const u8 101
    store u8 %10, ptr %9
    %11 = const i64 2
    %12 = gep i8, ptr %6, %11
    %13 = const u8 99
    store u8 %13, ptr %12
    %14 = alloca (i64, i64), align 8
    store ptr %6, ptr %14
    %15 = const i64 8
    %16 = gep i8, ptr %14, %15
    %17 = const u64 3
    store u64 %17, ptr %16
    %18 = const i64 8
    %19 = heap_alloc rust_heap i8, %18, align 1
    %20 = const u8 84
    store u8 %20, ptr %19
    %21 = const i64 1
    %22 = gep i8, ptr %19, %21
    %23 = const u8 114
    store u8 %23, ptr %22
    %24 = const i64 2
    %25 = gep i8, ptr %19, %24
    %26 = const u8 101
    store u8 %26, ptr %25
    %27 = const i64 3
    %28 = gep i8, ptr %19, %27
    %29 = const u8 101
    store u8 %29, ptr %28
    %30 = const i64 4
    %31 = gep i8, ptr %19, %30
    %32 = const u8 46
    store u8 %32, ptr %31
    %33 = const i64 5
    %34 = gep i8, ptr %19, %33
    %35 = const u8 114
    store u8 %35, ptr %34
    %36 = const i64 6
    %37 = gep i8, ptr %19, %36
    %38 = const u8 101
    store u8 %38, ptr %37
    %39 = const i64 7
    %40 = gep i8, ptr %19, %39
    %41 = const u8 99
    store u8 %41, ptr %40
    %42 = alloca (i64, i64), align 8
    store ptr %19, ptr %42
    %43 = const i64 8
    %44 = gep i8, ptr %42, %43
    %45 = const u64 8
    store u64 %45, ptr %44
    %46 = const i64 16
    %47 = heap_alloc rust_heap i8, %46, align 1
    %48 = const u8 86
    store u8 %48, ptr %47
    %49 = const i64 1
    %50 = gep i8, ptr %47, %49
    %51 = const u8 101
    store u8 %51, ptr %50
    %52 = const i64 2
    %53 = gep i8, ptr %47, %52
    %54 = const u8 114
    store u8 %54, ptr %53
    %55 = const i64 3
    %56 = gep i8, ptr %47, %55
    %57 = const u8 121
    store u8 %57, ptr %56
    %58 = const i64 4
    %59 = gep i8, ptr %47, %58
    %60 = const u8 76
    store u8 %60, ptr %59
    %61 = const i64 5
    %62 = gep i8, ptr %47, %61
    %63 = const u8 111
    store u8 %63, ptr %62
    %64 = const i64 6
    %65 = gep i8, ptr %47, %64
    %66 = const u8 110
    store u8 %66, ptr %65
    %67 = const i64 7
    %68 = gep i8, ptr %47, %67
    %69 = const u8 103
    store u8 %69, ptr %68
    %70 = const i64 8
    %71 = gep i8, ptr %47, %70
    %72 = const u8 80
    store u8 %72, ptr %71
    %73 = const i64 9
    %74 = gep i8, ptr %47, %73
    %75 = const u8 97
    store u8 %75, ptr %74
    %76 = const i64 10
    %77 = gep i8, ptr %47, %76
    %78 = const u8 114
    store u8 %78, ptr %77
    %79 = const i64 11
    %80 = gep i8, ptr %47, %79
    %81 = const u8 116
    store u8 %81, ptr %80
    %82 = const i64 12
    %83 = gep i8, ptr %47, %82
    %84 = const u8 78
    store u8 %84, ptr %83
    %85 = const i64 13
    %86 = gep i8, ptr %47, %85
    %87 = const u8 97
    store u8 %87, ptr %86
    %88 = const i64 14
    %89 = gep i8, ptr %47, %88
    %90 = const u8 109
    store u8 %90, ptr %89
    %91 = const i64 15
    %92 = gep i8, ptr %47, %91
    %93 = const u8 101
    store u8 %93, ptr %92
    %94 = alloca (i64, i64), align 8
    store ptr %47, ptr %94
    %95 = const i64 8
    %96 = gep i8, ptr %94, %95
    %97 = const u64 16
    store u64 %97, ptr %96
    %98 = const i64 20
    %99 = heap_alloc rust_heap i8, %98, align 1
    %100 = const u8 86
    store u8 %100, ptr %99
    %101 = const i64 1
    %102 = gep i8, ptr %99, %101
    %103 = const u8 101
    store u8 %103, ptr %102
    %104 = const i64 2
    %105 = gep i8, ptr %99, %104
    %106 = const u8 114
    store u8 %106, ptr %105
    %107 = const i64 3
    %108 = gep i8, ptr %99, %107
    %109 = const u8 121
    store u8 %109, ptr %108
    %110 = const i64 4
    %111 = gep i8, ptr %99, %110
    %112 = const u8 76
    store u8 %112, ptr %111
    %113 = const i64 5
    %114 = gep i8, ptr %99, %113
    %115 = const u8 111
    store u8 %115, ptr %114
    %116 = const i64 6
    %117 = gep i8, ptr %99, %116
    %118 = const u8 110
    store u8 %118, ptr %117
    %119 = const i64 7
    %120 = gep i8, ptr %99, %119
    %121 = const u8 103
    store u8 %121, ptr %120
    %122 = const i64 8
    %123 = gep i8, ptr %99, %122
    %124 = const u8 80
    store u8 %124, ptr %123
    %125 = const i64 9
    %126 = gep i8, ptr %99, %125
    %127 = const u8 97
    store u8 %127, ptr %126
    %128 = const i64 10
    %129 = gep i8, ptr %99, %128
    %130 = const u8 114
    store u8 %130, ptr %129
    %131 = const i64 11
    %132 = gep i8, ptr %99, %131
    %133 = const u8 116
    store u8 %133, ptr %132
    %134 = const i64 12
    %135 = gep i8, ptr %99, %134
    %136 = const u8 78
    store u8 %136, ptr %135
    %137 = const i64 13
    %138 = gep i8, ptr %99, %137
    %139 = const u8 97
    store u8 %139, ptr %138
    %140 = const i64 14
    %141 = gep i8, ptr %99, %140
    %142 = const u8 109
    store u8 %142, ptr %141
    %143 = const i64 15
    %144 = gep i8, ptr %99, %143
    %145 = const u8 101
    store u8 %145, ptr %144
    %146 = const i64 16
    %147 = gep i8, ptr %99, %146
    %148 = const u8 46
    store u8 %148, ptr %147
    %149 = const i64 17
    %150 = gep i8, ptr %99, %149
    %151 = const u8 114
    store u8 %151, ptr %150
    %152 = const i64 18
    %153 = gep i8, ptr %99, %152
    %154 = const u8 101
    store u8 %154, ptr %153
    %155 = const i64 19
    %156 = gep i8, ptr %99, %155
    %157 = const u8 99
    store u8 %157, ptr %156
    %158 = alloca (i64, i64), align 8
    store ptr %99, ptr %158
    %159 = const i64 8
    %160 = gep i8, ptr %158, %159
    %161 = const u64 20
    store u64 %161, ptr %160
    %162 = const i64 1
    %163 = heap_alloc rust_heap i8, %162, align 1
    %164 = alloca (i64, i64), align 8
    store ptr %163, ptr %164
    %165 = const i64 8
    %166 = gep i8, ptr %164, %165
    %167 = const u64 0
    store u64 %167, ptr %166
    %168 = const u64 0
    %169 = icmp eq u64 %1, %168
    condbr %169, bb1, bb2(%1)
bb1:
    store ptr %6, ptr %0
    %170 = const i64 8
    %171 = gep i8, ptr %0, %170
    %172 = const u64 3
    store u64 %172, ptr %171
    br bb9
bb2(%2: u64):
    %173 = const u64 1
    %174 = icmp eq u64 %2, %173
    condbr %174, bb3, bb4(%2)
bb3:
    store ptr %19, ptr %0
    %175 = const i64 8
    %176 = gep i8, ptr %0, %175
    %177 = const u64 8
    store u64 %177, ptr %176
    br bb9
bb4(%3: u64):
    %178 = const u64 2
    %179 = icmp eq u64 %3, %178
    condbr %179, bb5, bb6(%3)
bb5:
    store ptr %47, ptr %0
    %180 = const i64 8
    %181 = gep i8, ptr %0, %180
    %182 = const u64 16
    store u64 %182, ptr %181
    br bb9
bb6(%4: u64):
    %183 = const u64 3
    %184 = icmp eq u64 %4, %183
    condbr %184, bb7, bb8
bb7:
    store ptr %99, ptr %0
    %185 = const i64 8
    %186 = gep i8, ptr %0, %185
    %187 = const u64 20
    store u64 %187, ptr %186
    br bb9
bb8:
    store ptr %163, ptr %0
    %188 = const i64 8
    %189 = gep i8, ptr %0, %188
    %190 = const u64 0
    store u64 %190, ptr %189
    br bb9
bb9:
    ret
}

fn @_RNvMs7_NtCs2EYQwhfuABO_4core3numy12wrapping_mul(functy.4) {
}

fn @_RNvMs9_NtCs2EYQwhfuABO_4core3numj12wrapping_mul(functy.5) {
}

fn @murmur_hash_64a_idx(functy.6) {
bb0(%0: ptr, %1: u64):
    %151 = alloca (i64, i64), align 8
    %152 = alloca (i64, i64), align 8
    %153 = alloca (i32, i32), align 4
    %154 = alloca (i64, i64), align 8
    %155 = alloca (i64, i64), align 8
    %156 = alloca (i64, i64), align 8
    %157 = alloca (i64, i64), align 8
    %158 = alloca (i64, i64), align 8
    %159 = const i64 8
    %160 = gep i8, ptr %0, %159
    %161 = load u64, ptr %160
    %162 = const u64 14313749767032793493
    %163 = call @func.4(%161, %162)
    br bb1(%1, %161, %163)
bb1(%2: u64, %3: u64, %4: u64):
    %164 = xor u64 %2, %4
    %165 = const u64 8
    %166 = const u64 0
    %167 = icmp eq u64 %165, %166
    %168 = const bool false
    %169 = icmp eq bool %167, %168
    condbr %169, bb2(%3, %164), bb35
bb2(%5: u64, %6: u64):
    %170 = const u64 8
    %171 = udiv u64 %5, %170
    %172 = const u64 0
    br bb3(%5, %6, %171, %172)
bb3(%7: u64, %8: u64, %9: u64, %10: u64):
    %173 = icmp ult u64 %10, %9
    condbr %173, bb4(%7, %8, %9, %10), bb19(%7, %8, %9)
bb4(%11: u64, %12: u64, %13: u64, %14: u64):
    %174 = const u64 8
    %175, %176 = mul.overflow u64 %14, %174
    store u64 %175, ptr %151
    %177 = const i64 8
    %178 = gep i8, ptr %151, %177
    store bool %176, ptr %178
    %179 = const i64 8
    %180 = gep i8, ptr %151, %179
    %181 = load bool, ptr %180
    %182 = const bool false
    %183 = icmp eq bool %181, %182
    condbr %183, bb5(%11, %12, %13, %14), bb35
bb5(%15: u64, %16: u64, %17: u64, %18: u64):
    %184 = load u64, ptr %151
    %185 = const u64 0
    %186 = const u64 0
    br bb6(%15, %16, %17, %18, %184, %185, %186)
bb6(%19: u64, %20: u64, %21: u64, %22: u64, %23: u64, %24: u64, %25: u64):
    %187 = const u64 8
    %188 = icmp ult u64 %25, %187
    condbr %188, bb7(%19, %20, %21, %22, %23, %24, %25), bb13(%19, %20, %21, %22, %24)
bb7(%26: u64, %27: u64, %28: u64, %29: u64, %30: u64, %31: u64, %32: u64):
    %189, %190 = add.overflow u64 %30, %32
    store u64 %189, ptr %152
    %191 = const i64 8
    %192 = gep i8, ptr %152, %191
    store bool %190, ptr %192
    %193 = const i64 8
    %194 = gep i8, ptr %152, %193
    %195 = load bool, ptr %194
    %196 = const bool false
    %197 = icmp eq bool %195, %196
    condbr %197, bb8(%26, %27, %28, %29, %30, %31, %32), bb35
bb8(%33: u64, %34: u64, %35: u64, %36: u64, %37: u64, %38: u64, %39: u64):
    %198 = load u64, ptr %152
    %199 = const i64 8
    %200 = gep i8, ptr %0, %199
    %201 = load u64, ptr %200
    %202 = icmp ult u64 %198, %201
    condbr %202, bb9(%33, %34, %35, %36, %37, %38, %39, %198), bb35
bb9(%40: u64, %41: u64, %42: u64, %43: u64, %44: u64, %45: u64, %46: u64, %47: u64):
    %203 = load ptr, ptr %0
    %204 = gep u8, ptr %203, %47
    %205 = load u8, ptr %204
    %206 = zext u8 %205 to u64
    %207 = trunc u64 %46 to u32
    %208 = const u32 8
    %209, %210 = mul.overflow u32 %208, %207
    store u32 %209, ptr %153
    %211 = const i64 4
    %212 = gep i8, ptr %153, %211
    store bool %210, ptr %212
    %213 = const i64 4
    %214 = gep i8, ptr %153, %213
    %215 = load bool, ptr %214
    %216 = const bool false
    %217 = icmp eq bool %215, %216
    condbr %217, bb10(%40, %41, %42, %43, %44, %45, %46, %206), bb35
bb10(%48: u64, %49: u64, %50: u64, %51: u64, %52: u64, %53: u64, %54: u64, %55: u64):
    %218 = load u32, ptr %153
    %219 = const u32 64
    %220 = icmp ult u32 %218, %219
    condbr %220, bb11(%48, %49, %50, %51, %52, %53, %54, %55, %218), bb35
bb11(%56: u64, %57: u64, %58: u64, %59: u64, %60: u64, %61: u64, %62: u64, %63: u64, %64: u32):
    %221 = zext u32 %64 to u64
    %222 = shl u64 %63, %221
    %223 = or u64 %61, %222
    %224 = const u64 1
    %225, %226 = add.overflow u64 %62, %224
    store u64 %225, ptr %154
    %227 = const i64 8
    %228 = gep i8, ptr %154, %227
    store bool %226, ptr %228
    %229 = const i64 8
    %230 = gep i8, ptr %154, %229
    %231 = load bool, ptr %230
    %232 = const bool false
    %233 = icmp eq bool %231, %232
    condbr %233, bb12(%56, %57, %58, %59, %60, %223), bb35
bb12(%65: u64, %66: u64, %67: u64, %68: u64, %69: u64, %70: u64):
    %234 = load u64, ptr %154
    br bb6(%65, %66, %67, %68, %69, %70, %234)
bb13(%71: u64, %72: u64, %73: u64, %74: u64, %75: u64):
    %235 = const u64 14313749767032793493
    %236 = call @func.4(%75, %235)
    br bb14(%71, %72, %73, %74, %236)
bb14(%76: u64, %77: u64, %78: u64, %79: u64, %80: u64):
    %237 = const u32 47
    %238 = const u32 63
    %239 = and u32 %237, %238
    %240 = const u32 64
    %241 = icmp ult u32 %239, %240
    condbr %241, bb15(%76, %77, %78, %79, %80, %80, %239), bb35
bb15(%81: u64, %82: u64, %83: u64, %84: u64, %85: u64, %86: u64, %87: u32):
    %242 = zext u32 %87 to u64
    %243 = lshr u64 %86, %242
    %244 = xor u64 %85, %243
    %245 = const u64 14313749767032793493
    %246 = call @func.4(%244, %245)
    br bb16(%81, %82, %83, %84, %246)
bb16(%88: u64, %89: u64, %90: u64, %91: u64, %92: u64):
    %247 = xor u64 %89, %92
    %248 = const u64 14313749767032793493
    %249 = call @func.4(%247, %248)
    br bb17(%88, %90, %91, %249)
bb17(%93: u64, %94: u64, %95: u64, %96: u64):
    %250 = const u64 1
    %251, %252 = add.overflow u64 %95, %250
    store u64 %251, ptr %155
    %253 = const i64 8
    %254 = gep i8, ptr %155, %253
    store bool %252, ptr %254
    %255 = const i64 8
    %256 = gep i8, ptr %155, %255
    %257 = load bool, ptr %256
    %258 = const bool false
    %259 = icmp eq bool %257, %258
    condbr %259, bb18(%93, %96, %94), bb35
bb18(%97: u64, %98: u64, %99: u64):
    %260 = load u64, ptr %155
    br bb3(%97, %98, %99, %260)
bb19(%100: u64, %101: u64, %102: u64):
    %261 = const u64 8
    %262, %263 = mul.overflow u64 %102, %261
    store u64 %262, ptr %156
    %264 = const i64 8
    %265 = gep i8, ptr %156, %264
    store bool %263, ptr %265
    %266 = const i64 8
    %267 = gep i8, ptr %156, %266
    %268 = load bool, ptr %267
    %269 = const bool false
    %270 = icmp eq bool %268, %269
    condbr %270, bb20(%100, %101), bb35
bb20(%103: u64, %104: u64):
    %271 = load u64, ptr %156
    br bb21(%103, %104, %271, %271)
bb21(%105: u64, %106: u64, %107: u64, %108: u64):
    %272 = icmp ult u64 %108, %105
    condbr %272, bb22(%105, %106, %107, %108), bb28(%105, %106, %107)
bb22(%109: u64, %110: u64, %111: u64, %112: u64):
    %273 = const i64 8
    %274 = gep i8, ptr %0, %273
    %275 = load u64, ptr %274
    %276 = icmp ult u64 %112, %275
    condbr %276, bb23(%109, %110, %111, %112, %112), bb35
bb23(%113: u64, %114: u64, %115: u64, %116: u64, %117: u64):
    %277 = load ptr, ptr %0
    %278 = gep u8, ptr %277, %117
    %279 = load u8, ptr %278
    %280 = zext u8 %279 to u64
    %281, %282 = sub.overflow u64 %116, %115
    store u64 %281, ptr %157
    %283 = const i64 8
    %284 = gep i8, ptr %157, %283
    store bool %282, ptr %284
    %285 = const i64 8
    %286 = gep i8, ptr %157, %285
    %287 = load bool, ptr %286
    %288 = const bool false
    %289 = icmp eq bool %287, %288
    condbr %289, bb24(%113, %114, %115, %116, %280), bb35
bb24(%118: u64, %119: u64, %120: u64, %121: u64, %122: u64):
    %290 = load u64, ptr %157
    %291 = const u64 8
    %292 = call @func.5(%290, %291)
    br bb25(%118, %119, %120, %121, %122, %292)
bb25(%123: u64, %124: u64, %125: u64, %126: u64, %127: u64, %128: u64):
    %293 = const u64 63
    %294 = and u64 %128, %293
    %295 = const u64 64
    %296 = icmp ult u64 %294, %295
    condbr %296, bb26(%123, %124, %125, %126, %127, %294), bb35
bb26(%129: u64, %130: u64, %131: u64, %132: u64, %133: u64, %134: u64):
    %297 = shl u64 %133, %134
    %298 = xor u64 %130, %297
    %299 = const u64 1
    %300, %301 = add.overflow u64 %132, %299
    store u64 %300, ptr %158
    %302 = const i64 8
    %303 = gep i8, ptr %158, %302
    store bool %301, ptr %303
    %304 = const i64 8
    %305 = gep i8, ptr %158, %304
    %306 = load bool, ptr %305
    %307 = const bool false
    %308 = icmp eq bool %306, %307
    condbr %308, bb27(%129, %298, %131), bb35
bb27(%135: u64, %136: u64, %137: u64):
    %309 = load u64, ptr %158
    br bb21(%135, %136, %137, %309)
bb28(%138: u64, %139: u64, %140: u64):
    %310 = icmp ult u64 %140, %138
    condbr %310, bb29(%139), bb31(%139)
bb29(%141: u64):
    %311 = const u64 14313749767032793493
    %312 = call @func.4(%141, %311)
    br bb30(%312)
bb30(%142: u64):
    br bb31(%142)
bb31(%143: u64):
    %313 = const u32 47
    %314 = const u32 63
    %315 = and u32 %313, %314
    %316 = const u32 64
    %317 = icmp ult u32 %315, %316
    condbr %317, bb32(%143, %143, %315), bb35
bb32(%144: u64, %145: u64, %146: u32):
    %318 = zext u32 %146 to u64
    %319 = lshr u64 %145, %318
    %320 = xor u64 %144, %319
    %321 = const u64 14313749767032793493
    %322 = call @func.4(%320, %321)
    br bb33(%322)
bb33(%147: u64):
    %323 = const u32 47
    %324 = const u32 63
    %325 = and u32 %323, %324
    %326 = const u32 64
    %327 = icmp ult u32 %325, %326
    condbr %327, bb34(%147, %147, %325), bb35
bb34(%148: u64, %149: u64, %150: u32):
    %328 = zext u32 %150 to u64
    %329 = lshr u64 %149, %328
    %330 = xor u64 %148, %329
    ret %330
bb35:
    unreachable
}

fn @str_bytes_eq(functy.7) {
bb0(%0: ptr, %1: ptr):
    %11 = alloca (i64, i64), align 8
    %12 = alloca (i64, i64), align 8
    %13 = alloca (i64, i64), align 8
    %14 = load i64, ptr %0
    store i64 %14, ptr %11
    %15 = const i64 8
    %16 = gep i8, ptr %0, %15
    %17 = const i64 8
    %18 = gep i8, ptr %11, %17
    %19 = load i64, ptr %16
    store i64 %19, ptr %18
    br bb1
bb1:
    %20 = load i64, ptr %1
    store i64 %20, ptr %12
    %21 = const i64 8
    %22 = gep i8, ptr %1, %21
    %23 = const i64 8
    %24 = gep i8, ptr %12, %23
    %25 = load i64, ptr %22
    store i64 %25, ptr %24
    br bb2
bb2:
    %26 = const i64 8
    %27 = gep i8, ptr %11, %26
    %28 = load u64, ptr %27
    %29 = const i64 8
    %30 = gep i8, ptr %12, %29
    %31 = load u64, ptr %30
    %32 = icmp ne u64 %28, %31
    condbr %32, bb3, bb4
bb3:
    %33 = const bool false
    br bb13(%33)
bb4:
    %34 = const u64 0
    br bb5(%34)
bb5(%2: u64):
    %35 = const i64 8
    %36 = gep i8, ptr %11, %35
    %37 = load u64, ptr %36
    %38 = icmp ult u64 %2, %37
    condbr %38, bb6(%2), bb12
bb6(%3: u64):
    %39 = const i64 8
    %40 = gep i8, ptr %11, %39
    %41 = load u64, ptr %40
    %42 = icmp ult u64 %3, %41
    condbr %42, bb7(%3, %3), bb14
bb7(%4: u64, %5: u64):
    %43 = load ptr, ptr %11
    %44 = gep u8, ptr %43, %5
    %45 = load u8, ptr %44
    %46 = const i64 8
    %47 = gep i8, ptr %12, %46
    %48 = load u64, ptr %47
    %49 = icmp ult u64 %4, %48
    condbr %49, bb8(%4, %45, %4), bb14
bb8(%6: u64, %7: u8, %8: u64):
    %50 = load ptr, ptr %12
    %51 = gep u8, ptr %50, %8
    %52 = load u8, ptr %51
    %53 = icmp ne u8 %7, %52
    condbr %53, bb9, bb10(%6)
bb9:
    %54 = const bool false
    br bb13(%54)
bb10(%9: u64):
    %55 = const u64 1
    %56, %57 = add.overflow u64 %9, %55
    store u64 %56, ptr %13
    %58 = const i64 8
    %59 = gep i8, ptr %13, %58
    store bool %57, ptr %59
    %60 = const i64 8
    %61 = gep i8, ptr %13, %60
    %62 = load bool, ptr %61
    %63 = const bool false
    %64 = icmp eq bool %62, %63
    condbr %64, bb11, bb14
bb11:
    %65 = load u64, ptr %13
    br bb5(%65)
bb12:
    %66 = const bool true
    br bb13(%66)
bb13(%10: bool):
    ret %10
bb14:
    unreachable
}"#;

/// VERBATIM `--mir-emit-closure str_stage2_name_root` emit (same slice/frontend). 34171 bytes; 8 closure members; validate_module = 0; re-parse OK.
const NAME_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::str_stage2_name_root"
target "aarch64-apple-darwin" 8 little
file 0 "str_stage2_slice.rs"

functy.0 = (ptr, u64) -> ()

functy.1 = (ptr) -> ()

functy.2 = (ptr, ptr, ptr) -> ()

functy.3 = (ptr, ptr) -> ()

functy.4 = (ptr, ptr, u64) -> ()

functy.5 = (ptr, ptr) -> ()

functy.6 = (ptr, ptr, ptr) -> ()

functy.7 = (u64, u64) -> (u64)

functy.8 = (u64, u64) -> (u64)

functy.9 = (u64, u64) -> (u64)

functy.10 = (u64, u64) -> (u64)

functy.11 = (ptr, u64) -> (u64)

fn @str_stage2_name_root(functy.0) {
bb0(%0: ptr, %1: u64):
    %5 = alloca (i64, i64, i64, i64, i64), align 8
    %6 = alloca (i64, i64, i64, i64, i64), align 8
    %7 = alloca (i64, i64), align 8
    %8 = alloca (i64, i64), align 8
    %9 = alloca (i64, i64, i64, i64, i64), align 8
    %10 = alloca (i64, i64, i64, i64, i64), align 8
    %11 = alloca (i64, i64), align 8
    %12 = alloca (i64, i64), align 8
    %13 = alloca (i64, i64, i64, i64, i64), align 8
    %14 = alloca (i64, i64, i64, i64, i64), align 8
    %15 = alloca (i64, i64, i64, i64, i64), align 8
    %16 = alloca (i64, i64), align 8
    %17 = alloca (i64, i64), align 8
    %18 = alloca (i64, i64), align 8
    %19 = alloca (i64, i64, i64, i64, i64), align 8
    %20 = alloca (i64, i64, i64, i64, i64), align 8
    %21 = alloca (i64, i64), align 8
    %22 = alloca (i64, i64), align 8
    %23 = alloca (i64, i64, i64, i64, i64), align 8
    %24 = alloca (i64, i64, i64, i64, i64), align 8
    %25 = alloca (i64, i64), align 8
    %26 = alloca (i64, i64), align 8
    %27 = const i64 4
    %28 = heap_alloc rust_heap i8, %27, align 1
    %29 = const u8 84
    store u8 %29, ptr %28
    %30 = const i64 1
    %31 = gep i8, ptr %28, %30
    %32 = const u8 114
    store u8 %32, ptr %31
    %33 = const i64 2
    %34 = gep i8, ptr %28, %33
    %35 = const u8 101
    store u8 %35, ptr %34
    %36 = const i64 3
    %37 = gep i8, ptr %28, %36
    %38 = const u8 101
    store u8 %38, ptr %37
    %39 = alloca (i64, i64), align 8
    store ptr %28, ptr %39
    %40 = const i64 8
    %41 = gep i8, ptr %39, %40
    %42 = const u64 4
    store u64 %42, ptr %41
    %43 = const i64 3
    %44 = heap_alloc rust_heap i8, %43, align 1
    %45 = const u8 114
    store u8 %45, ptr %44
    %46 = const i64 1
    %47 = gep i8, ptr %44, %46
    %48 = const u8 101
    store u8 %48, ptr %47
    %49 = const i64 2
    %50 = gep i8, ptr %44, %49
    %51 = const u8 99
    store u8 %51, ptr %50
    %52 = alloca (i64, i64), align 8
    store ptr %44, ptr %52
    %53 = const i64 8
    %54 = gep i8, ptr %52, %53
    %55 = const u64 3
    store u64 %55, ptr %54
    %56 = const i64 6
    %57 = heap_alloc rust_heap i8, %56, align 1
    %58 = const u8 70
    store u8 %58, ptr %57
    %59 = const i64 1
    %60 = gep i8, ptr %57, %59
    %61 = const u8 111
    store u8 %61, ptr %60
    %62 = const i64 2
    %63 = gep i8, ptr %57, %62
    %64 = const u8 114
    store u8 %64, ptr %63
    %65 = const i64 3
    %66 = gep i8, ptr %57, %65
    %67 = const u8 101
    store u8 %67, ptr %66
    %68 = const i64 4
    %69 = gep i8, ptr %57, %68
    %70 = const u8 115
    store u8 %70, ptr %69
    %71 = const i64 5
    %72 = gep i8, ptr %57, %71
    %73 = const u8 116
    store u8 %73, ptr %72
    %74 = alloca (i64, i64), align 8
    store ptr %57, ptr %74
    %75 = const i64 8
    %76 = gep i8, ptr %74, %75
    %77 = const u64 6
    store u64 %77, ptr %76
    %78 = const i64 3
    %79 = heap_alloc rust_heap i8, %78, align 1
    %80 = const u8 78
    store u8 %80, ptr %79
    %81 = const i64 1
    %82 = gep i8, ptr %79, %81
    %83 = const u8 97
    store u8 %83, ptr %82
    %84 = const i64 2
    %85 = gep i8, ptr %79, %84
    %86 = const u8 116
    store u8 %86, ptr %85
    %87 = alloca (i64, i64), align 8
    store ptr %79, ptr %87
    %88 = const i64 8
    %89 = gep i8, ptr %87, %88
    %90 = const u64 3
    store u64 %90, ptr %89
    %91 = const i64 2
    %92 = heap_alloc rust_heap i8, %91, align 1
    %93 = const u8 52
    store u8 %93, ptr %92
    %94 = const i64 1
    %95 = gep i8, ptr %92, %94
    %96 = const u8 50
    store u8 %96, ptr %95
    %97 = alloca (i64, i64), align 8
    store ptr %92, ptr %97
    %98 = const i64 8
    %99 = gep i8, ptr %97, %98
    %100 = const u64 2
    store u64 %100, ptr %99
    %101 = const i64 16
    %102 = heap_alloc rust_heap i8, %101, align 1
    %103 = const u8 86
    store u8 %103, ptr %102
    %104 = const i64 1
    %105 = gep i8, ptr %102, %104
    %106 = const u8 101
    store u8 %106, ptr %105
    %107 = const i64 2
    %108 = gep i8, ptr %102, %107
    %109 = const u8 114
    store u8 %109, ptr %108
    %110 = const i64 3
    %111 = gep i8, ptr %102, %110
    %112 = const u8 121
    store u8 %112, ptr %111
    %113 = const i64 4
    %114 = gep i8, ptr %102, %113
    %115 = const u8 76
    store u8 %115, ptr %114
    %116 = const i64 5
    %117 = gep i8, ptr %102, %116
    %118 = const u8 111
    store u8 %118, ptr %117
    %119 = const i64 6
    %120 = gep i8, ptr %102, %119
    %121 = const u8 110
    store u8 %121, ptr %120
    %122 = const i64 7
    %123 = gep i8, ptr %102, %122
    %124 = const u8 103
    store u8 %124, ptr %123
    %125 = const i64 8
    %126 = gep i8, ptr %102, %125
    %127 = const u8 80
    store u8 %127, ptr %126
    %128 = const i64 9
    %129 = gep i8, ptr %102, %128
    %130 = const u8 97
    store u8 %130, ptr %129
    %131 = const i64 10
    %132 = gep i8, ptr %102, %131
    %133 = const u8 114
    store u8 %133, ptr %132
    %134 = const i64 11
    %135 = gep i8, ptr %102, %134
    %136 = const u8 116
    store u8 %136, ptr %135
    %137 = const i64 12
    %138 = gep i8, ptr %102, %137
    %139 = const u8 78
    store u8 %139, ptr %138
    %140 = const i64 13
    %141 = gep i8, ptr %102, %140
    %142 = const u8 97
    store u8 %142, ptr %141
    %143 = const i64 14
    %144 = gep i8, ptr %102, %143
    %145 = const u8 109
    store u8 %145, ptr %144
    %146 = const i64 15
    %147 = gep i8, ptr %102, %146
    %148 = const u8 101
    store u8 %148, ptr %147
    %149 = alloca (i64, i64), align 8
    store ptr %102, ptr %149
    %150 = const i64 8
    %151 = gep i8, ptr %149, %150
    %152 = const u64 16
    store u64 %152, ptr %151
    %153 = const i64 1
    %154 = heap_alloc rust_heap i8, %153, align 1
    %155 = const u8 48
    store u8 %155, ptr %154
    %156 = alloca (i64, i64), align 8
    store ptr %154, ptr %156
    %157 = const i64 8
    %158 = gep i8, ptr %156, %157
    %159 = const u64 1
    store u64 %159, ptr %158
    %160 = const u64 0
    %161 = icmp eq u64 %1, %160
    condbr %161, bb1, bb4(%1)
bb1:
    call @func.1(%6)
    br bb2
bb2:
    store ptr %28, ptr %7
    %162 = const i64 8
    %163 = gep i8, ptr %7, %162
    %164 = const u64 4
    store u64 %164, ptr %163
    call @func.2(%5, %6, %7)
    br bb3
bb3:
    store ptr %44, ptr %8
    %165 = const i64 8
    %166 = gep i8, ptr %8, %165
    %167 = const u64 3
    store u64 %167, ptr %166
    call @func.2(%0, %5, %8)
    br bb20
bb4(%2: u64):
    %168 = const u64 1
    %169 = icmp eq u64 %2, %168
    condbr %169, bb5, bb8(%2)
bb5:
    call @func.1(%10)
    br bb6
bb6:
    store ptr %57, ptr %11
    %170 = const i64 8
    %171 = gep i8, ptr %11, %170
    %172 = const u64 6
    store u64 %172, ptr %171
    call @func.2(%9, %10, %11)
    br bb7
bb7:
    store ptr %44, ptr %12
    %173 = const i64 8
    %174 = gep i8, ptr %12, %173
    %175 = const u64 3
    store u64 %175, ptr %174
    call @func.2(%0, %9, %12)
    br bb20
bb8(%3: u64):
    %176 = const u64 2
    %177 = icmp eq u64 %3, %176
    condbr %177, bb9, bb13(%3)
bb9:
    call @func.1(%15)
    br bb10
bb10:
    store ptr %79, ptr %16
    %178 = const i64 8
    %179 = gep i8, ptr %16, %178
    %180 = const u64 3
    store u64 %180, ptr %179
    call @func.2(%14, %15, %16)
    br bb11
bb11:
    store ptr %92, ptr %17
    %181 = const i64 8
    %182 = gep i8, ptr %17, %181
    %183 = const u64 2
    store u64 %183, ptr %182
    call @func.2(%13, %14, %17)
    br bb12
bb12:
    store ptr %44, ptr %18
    %184 = const i64 8
    %185 = gep i8, ptr %18, %184
    %186 = const u64 3
    store u64 %186, ptr %185
    call @func.2(%0, %13, %18)
    br bb20
bb13(%4: u64):
    %187 = const u64 3
    %188 = icmp eq u64 %4, %187
    condbr %188, bb14, bb17
bb14:
    call @func.1(%20)
    br bb15
bb15:
    store ptr %102, ptr %21
    %189 = const i64 8
    %190 = gep i8, ptr %21, %189
    %191 = const u64 16
    store u64 %191, ptr %190
    call @func.2(%19, %20, %21)
    br bb16
bb16:
    store ptr %44, ptr %22
    %192 = const i64 8
    %193 = gep i8, ptr %22, %192
    %194 = const u64 3
    store u64 %194, ptr %193
    call @func.2(%0, %19, %22)
    br bb20
bb17:
    call @func.1(%24)
    br bb18
bb18:
    store ptr %154, ptr %25
    %195 = const i64 8
    %196 = gep i8, ptr %25, %195
    %197 = const u64 1
    store u64 %197, ptr %196
    call @func.2(%23, %24, %25)
    br bb19
bb19:
    store ptr %44, ptr %26
    %198 = const i64 8
    %199 = gep i8, ptr %26, %198
    %200 = const u64 3
    store u64 %200, ptr %199
    call @func.2(%0, %23, %26)
    br bb20
bb20:
    ret
}

fn @name_anon(functy.1) {
bb0(%0: ptr):
    %1 = alloca (i64, i64, i64, i64), align 8
    %2 = const i64 0
    store i64 %2, ptr %1
    %3 = load i64, ptr %1
    store i64 %3, ptr %0
    %4 = const i64 8
    %5 = gep i8, ptr %1, %4
    %6 = const i64 8
    %7 = gep i8, ptr %0, %6
    %8 = load i64, ptr %5
    store i64 %8, ptr %7
    %9 = const i64 16
    %10 = gep i8, ptr %1, %9
    %11 = const i64 16
    %12 = gep i8, ptr %0, %11
    %13 = load i64, ptr %10
    store i64 %13, ptr %12
    %14 = const i64 24
    %15 = gep i8, ptr %1, %14
    %16 = const i64 24
    %17 = gep i8, ptr %0, %16
    %18 = load i64, ptr %15
    store i64 %18, ptr %17
    %19 = const u64 1723
    %20 = const i64 32
    %21 = gep i8, ptr %0, %20
    store u64 %19, ptr %21
    ret
}

fn @fold_step(functy.2) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %4 = alloca (i64, i64), align 8
    %5 = alloca (i64, i64, i64, i64, i64), align 8
    %6 = alloca (i64, i64, i64, i64, i64), align 8
    %7 = const bool false
    %8 = const bool true
    call @func.3(%4, %2)
    br bb1
bb1:
    %9 = load bool, ptr %4
    %10 = const i64 8
    %11 = gep i8, ptr %4, %10
    %12 = load u64, ptr %11
    condbr %9, bb2(%12), bb3
bb2(%3: u64):
    %13 = const bool false
    %14 = load i64, ptr %1
    store i64 %14, ptr %5
    %15 = const i64 8
    %16 = gep i8, ptr %1, %15
    %17 = const i64 8
    %18 = gep i8, ptr %5, %17
    %19 = load i64, ptr %16
    store i64 %19, ptr %18
    %20 = const i64 16
    %21 = gep i8, ptr %1, %20
    %22 = const i64 16
    %23 = gep i8, ptr %5, %22
    %24 = load i64, ptr %21
    store i64 %24, ptr %23
    %25 = const i64 24
    %26 = gep i8, ptr %1, %25
    %27 = const i64 24
    %28 = gep i8, ptr %5, %27
    %29 = load i64, ptr %26
    store i64 %29, ptr %28
    %30 = const i64 32
    %31 = gep i8, ptr %1, %30
    %32 = const i64 32
    %33 = gep i8, ptr %5, %32
    %34 = load i64, ptr %31
    store i64 %34, ptr %33
    call @func.4(%0, %5, %3)
    br bb5
bb3:
    %35 = const bool false
    %36 = load i64, ptr %1
    store i64 %36, ptr %6
    %37 = const i64 8
    %38 = gep i8, ptr %1, %37
    %39 = const i64 8
    %40 = gep i8, ptr %6, %39
    %41 = load i64, ptr %38
    store i64 %41, ptr %40
    %42 = const i64 16
    %43 = gep i8, ptr %1, %42
    %44 = const i64 16
    %45 = gep i8, ptr %6, %44
    %46 = load i64, ptr %43
    store i64 %46, ptr %45
    %47 = const i64 24
    %48 = gep i8, ptr %1, %47
    %49 = const i64 24
    %50 = gep i8, ptr %6, %49
    %51 = load i64, ptr %48
    store i64 %51, ptr %50
    %52 = const i64 32
    %53 = gep i8, ptr %1, %52
    %54 = const i64 32
    %55 = gep i8, ptr %6, %54
    %56 = load i64, ptr %53
    store i64 %56, ptr %55
    call @func.6(%0, %6, %2)
    br bb6
bb4:
    ret
bb5:
    br bb4
bb6:
    br bb4
}

fn @parse_u64_ascii(functy.3) {
bb0(%0: ptr, %1: ptr):
    %39 = alloca (i64, i64), align 8
    %40 = alloca (i8, i8), align 1
    %41 = alloca (i64, i64), align 8
    %42 = alloca (i64, i64), align 8
    %43 = alloca (i64, i64), align 8
    %44 = alloca (i64, i64), align 8
    %45 = load i64, ptr %1
    store i64 %45, ptr %39
    %46 = const i64 8
    %47 = gep i8, ptr %1, %46
    %48 = const i64 8
    %49 = gep i8, ptr %39, %48
    %50 = load i64, ptr %47
    store i64 %50, ptr %49
    br bb1
bb1:
    %51 = const u64 0
    %52 = const i64 8
    %53 = gep i8, ptr %39, %52
    %54 = load u64, ptr %53
    %55 = const u64 0
    %56 = icmp ugt u64 %54, %55
    condbr %56, bb2(%51), bb5(%51)
bb2(%2: u64):
    %57 = const u64 0
    %58 = const i64 8
    %59 = gep i8, ptr %39, %58
    %60 = load u64, ptr %59
    %61 = icmp ult u64 %57, %60
    condbr %61, bb3(%2, %57), bb24
bb3(%3: u64, %4: u64):
    %62 = load ptr, ptr %39
    %63 = gep u8, ptr %62, %4
    %64 = load u8, ptr %63
    %65 = const u8 43
    %66 = icmp eq u8 %64, %65
    condbr %66, bb4, bb5(%3)
bb4:
    %67 = const u64 1
    br bb5(%67)
bb5(%5: u64):
    %68 = const i64 8
    %69 = gep i8, ptr %39, %68
    %70 = load u64, ptr %69
    %71 = icmp uge u64 %5, %70
    condbr %71, bb6, bb7(%5)
bb6:
    %72 = const bool false
    store bool %72, ptr %0
    %73 = const u64 0
    %74 = const i64 8
    %75 = gep i8, ptr %0, %74
    store u64 %73, ptr %75
    br bb23
bb7(%6: u64):
    %76 = const u64 0
    br bb8(%6, %76)
bb8(%7: u64, %8: u64):
    %77 = const i64 8
    %78 = gep i8, ptr %39, %77
    %79 = load u64, ptr %78
    %80 = icmp ult u64 %7, %79
    condbr %80, bb9(%7, %8), bb22(%8)
bb9(%9: u64, %10: u64):
    %81 = const i64 8
    %82 = gep i8, ptr %39, %81
    %83 = load u64, ptr %82
    %84 = icmp ult u64 %9, %83
    condbr %84, bb10(%9, %10, %9), bb24
bb10(%11: u64, %12: u64, %13: u64):
    %85 = load ptr, ptr %39
    %86 = gep u8, ptr %85, %13
    %87 = load u8, ptr %86
    %88 = const u8 48
    %89 = icmp ult u8 %87, %88
    condbr %89, bb12, bb11(%11, %12, %87)
bb11(%14: u64, %15: u64, %16: u8):
    %90 = const u8 57
    %91 = icmp ugt u8 %16, %90
    condbr %91, bb12, bb13(%14, %15, %16)
bb12:
    %92 = const bool false
    store bool %92, ptr %0
    %93 = const u64 0
    %94 = const i64 8
    %95 = gep i8, ptr %0, %94
    store u64 %93, ptr %95
    br bb23
bb13(%17: u64, %18: u64, %19: u8):
    %96 = const u8 48
    %97, %98 = sub.overflow u8 %19, %96
    store u8 %97, ptr %40
    %99 = const i64 1
    %100 = gep i8, ptr %40, %99
    store bool %98, ptr %100
    %101 = const i64 1
    %102 = gep i8, ptr %40, %101
    %103 = load bool, ptr %102
    %104 = const bool false
    %105 = icmp eq bool %103, %104
    condbr %105, bb14(%17, %18), bb24
bb14(%20: u64, %21: u64):
    %106 = load u8, ptr %40
    %107 = zext u8 %106 to u64
    %108 = const u64 18446744073709551615
    %109, %110 = sub.overflow u64 %108, %107
    store u64 %109, ptr %41
    %111 = const i64 8
    %112 = gep i8, ptr %41, %111
    store bool %110, ptr %112
    %113 = const i64 8
    %114 = gep i8, ptr %41, %113
    %115 = load bool, ptr %114
    %116 = const bool false
    %117 = icmp eq bool %115, %116
    condbr %117, bb15(%20, %21, %107, %21), bb24
bb15(%22: u64, %23: u64, %24: u64, %25: u64):
    %118 = load u64, ptr %41
    %119 = const u64 10
    %120 = const u64 0
    %121 = icmp eq u64 %119, %120
    %122 = const bool false
    %123 = icmp eq bool %121, %122
    condbr %123, bb16(%22, %23, %24, %25, %118), bb24
bb16(%26: u64, %27: u64, %28: u64, %29: u64, %30: u64):
    %124 = const u64 10
    %125 = udiv u64 %30, %124
    %126 = icmp ugt u64 %29, %125
    condbr %126, bb17, bb18(%26, %27, %28)
bb17:
    %127 = const bool false
    store bool %127, ptr %0
    %128 = const u64 0
    %129 = const i64 8
    %130 = gep i8, ptr %0, %129
    store u64 %128, ptr %130
    br bb23
bb18(%31: u64, %32: u64, %33: u64):
    %131 = const u64 10
    %132, %133 = mul.overflow u64 %32, %131
    store u64 %132, ptr %42
    %134 = const i64 8
    %135 = gep i8, ptr %42, %134
    store bool %133, ptr %135
    %136 = const i64 8
    %137 = gep i8, ptr %42, %136
    %138 = load bool, ptr %137
    %139 = const bool false
    %140 = icmp eq bool %138, %139
    condbr %140, bb19(%31, %33), bb24
bb19(%34: u64, %35: u64):
    %141 = load u64, ptr %42
    %142, %143 = add.overflow u64 %141, %35
    store u64 %142, ptr %43
    %144 = const i64 8
    %145 = gep i8, ptr %43, %144
    store bool %143, ptr %145
    %146 = const i64 8
    %147 = gep i8, ptr %43, %146
    %148 = load bool, ptr %147
    %149 = const bool false
    %150 = icmp eq bool %148, %149
    condbr %150, bb20(%34), bb24
bb20(%36: u64):
    %151 = load u64, ptr %43
    %152 = const u64 1
    %153, %154 = add.overflow u64 %36, %152
    store u64 %153, ptr %44
    %155 = const i64 8
    %156 = gep i8, ptr %44, %155
    store bool %154, ptr %156
    %157 = const i64 8
    %158 = gep i8, ptr %44, %157
    %159 = load bool, ptr %158
    %160 = const bool false
    %161 = icmp eq bool %159, %160
    condbr %161, bb21(%151), bb24
bb21(%37: u64):
    %162 = load u64, ptr %44
    br bb8(%162, %37)
bb22(%38: u64):
    %163 = const bool true
    store bool %163, ptr %0
    %164 = const i64 8
    %165 = gep i8, ptr %0, %164
    store u64 %38, ptr %165
    br bb23
bb23:
    ret
bb24:
    unreachable
}

fn @name_num_part(functy.4) {
bb0(%0: ptr, %1: ptr, %2: u64):
    %7 = alloca (i64, i64, i64, i64), align 8
    %8 = alloca i64, align 8
    %9 = alloca (i64, i64, i64, i64, i64), align 8
    %10 = const bool false
    %11 = const bool true
    %12 = const i64 32
    %13 = gep i8, ptr %1, %12
    %14 = load u64, ptr %13
    %15 = call @func.8(%14, %2)
    br bb1(%2, %15)
bb1(%3: u64, %4: u64):
    %16 = const bool false
    %17 = load i64, ptr %1
    store i64 %17, ptr %9
    %18 = const i64 8
    %19 = gep i8, ptr %1, %18
    %20 = const i64 8
    %21 = gep i8, ptr %9, %20
    %22 = load i64, ptr %19
    store i64 %22, ptr %21
    %23 = const i64 16
    %24 = gep i8, ptr %1, %23
    %25 = const i64 16
    %26 = gep i8, ptr %9, %25
    %27 = load i64, ptr %24
    store i64 %27, ptr %26
    %28 = const i64 24
    %29 = gep i8, ptr %1, %28
    %30 = const i64 24
    %31 = gep i8, ptr %9, %30
    %32 = load i64, ptr %29
    store i64 %32, ptr %31
    %33 = const i64 32
    %34 = gep i8, ptr %1, %33
    %35 = const i64 32
    %36 = gep i8, ptr %9, %35
    %37 = load i64, ptr %34
    store i64 %37, ptr %36
    %38 = const i64 56
    %39 = heap_alloc rust_heap i8, %38, align 8
    %40 = const u64 1
    store u64 %40, ptr %39
    %41 = const i64 8
    %42 = gep i8, ptr %39, %41
    %43 = const u64 1
    store u64 %43, ptr %42
    %44 = const i64 16
    %45 = gep i8, ptr %39, %44
    %46 = load i64, ptr %9
    store i64 %46, ptr %45
    %47 = const i64 8
    %48 = gep i8, ptr %9, %47
    %49 = const i64 8
    %50 = gep i8, ptr %45, %49
    %51 = load i64, ptr %48
    store i64 %51, ptr %50
    %52 = const i64 16
    %53 = gep i8, ptr %9, %52
    %54 = const i64 16
    %55 = gep i8, ptr %45, %54
    %56 = load i64, ptr %53
    store i64 %56, ptr %55
    %57 = const i64 24
    %58 = gep i8, ptr %9, %57
    %59 = const i64 24
    %60 = gep i8, ptr %45, %59
    %61 = load i64, ptr %58
    store i64 %61, ptr %60
    %62 = const i64 32
    %63 = gep i8, ptr %9, %62
    %64 = const i64 32
    %65 = gep i8, ptr %45, %64
    %66 = load i64, ptr %63
    store i64 %66, ptr %65
    store ptr %39, ptr %8
    br bb2(%3, %4)
bb2(%5: u64, %6: u64):
    %67 = load ptr, ptr %8
    %68 = const i64 16
    %69 = gep i8, ptr %7, %68
    store ptr %67, ptr %69
    %70 = const i64 8
    %71 = gep i8, ptr %7, %70
    store u64 %5, ptr %71
    %72 = const i64 2
    store i64 %72, ptr %7
    %73 = load i64, ptr %7
    store i64 %73, ptr %0
    %74 = const i64 8
    %75 = gep i8, ptr %7, %74
    %76 = const i64 8
    %77 = gep i8, ptr %0, %76
    %78 = load i64, ptr %75
    store i64 %78, ptr %77
    %79 = const i64 16
    %80 = gep i8, ptr %7, %79
    %81 = const i64 16
    %82 = gep i8, ptr %0, %81
    %83 = load i64, ptr %80
    store i64 %83, ptr %82
    %84 = const i64 24
    %85 = gep i8, ptr %7, %84
    %86 = const i64 24
    %87 = gep i8, ptr %0, %86
    %88 = load i64, ptr %85
    store i64 %88, ptr %87
    %89 = const i64 32
    %90 = gep i8, ptr %0, %89
    store u64 %6, ptr %90
    ret
}

fn @_RNvXs17_NtCskTzINo8ZBH9_5alloc4syncINtB6_3ArceEINtNtCs2EYQwhfuABO_4core7convert4FromReE4fromCs77po20IQdNn_16str_stage2_slice(functy.5) {
}

fn @name_str_part(functy.6) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %7 = alloca (i64, i64), align 8
    %8 = alloca (i64, i64, i64, i64), align 8
    %9 = alloca i64, align 8
    %10 = alloca (i64, i64, i64, i64, i64), align 8
    %11 = alloca (i64, i64), align 8
    %12 = const bool false
    %13 = const bool true
    %14 = load i64, ptr %2
    store i64 %14, ptr %7
    %15 = const i64 8
    %16 = gep i8, ptr %2, %15
    %17 = const i64 8
    %18 = gep i8, ptr %7, %17
    %19 = load i64, ptr %16
    store i64 %19, ptr %18
    br bb1
bb1:
    %20 = const u64 11
    %21 = call @func.11(%7, %20)
    br bb2(%21)
bb2(%3: u64):
    %22 = const i64 32
    %23 = gep i8, ptr %1, %22
    %24 = load u64, ptr %23
    %25 = call @func.8(%24, %3)
    br bb3(%25)
bb3(%4: u64):
    %26 = const bool false
    %27 = load i64, ptr %1
    store i64 %27, ptr %10
    %28 = const i64 8
    %29 = gep i8, ptr %1, %28
    %30 = const i64 8
    %31 = gep i8, ptr %10, %30
    %32 = load i64, ptr %29
    store i64 %32, ptr %31
    %33 = const i64 16
    %34 = gep i8, ptr %1, %33
    %35 = const i64 16
    %36 = gep i8, ptr %10, %35
    %37 = load i64, ptr %34
    store i64 %37, ptr %36
    %38 = const i64 24
    %39 = gep i8, ptr %1, %38
    %40 = const i64 24
    %41 = gep i8, ptr %10, %40
    %42 = load i64, ptr %39
    store i64 %42, ptr %41
    %43 = const i64 32
    %44 = gep i8, ptr %1, %43
    %45 = const i64 32
    %46 = gep i8, ptr %10, %45
    %47 = load i64, ptr %44
    store i64 %47, ptr %46
    %48 = const i64 56
    %49 = heap_alloc rust_heap i8, %48, align 8
    %50 = const u64 1
    store u64 %50, ptr %49
    %51 = const i64 8
    %52 = gep i8, ptr %49, %51
    %53 = const u64 1
    store u64 %53, ptr %52
    %54 = const i64 16
    %55 = gep i8, ptr %49, %54
    %56 = load i64, ptr %10
    store i64 %56, ptr %55
    %57 = const i64 8
    %58 = gep i8, ptr %10, %57
    %59 = const i64 8
    %60 = gep i8, ptr %55, %59
    %61 = load i64, ptr %58
    store i64 %61, ptr %60
    %62 = const i64 16
    %63 = gep i8, ptr %10, %62
    %64 = const i64 16
    %65 = gep i8, ptr %55, %64
    %66 = load i64, ptr %63
    store i64 %66, ptr %65
    %67 = const i64 24
    %68 = gep i8, ptr %10, %67
    %69 = const i64 24
    %70 = gep i8, ptr %55, %69
    %71 = load i64, ptr %68
    store i64 %71, ptr %70
    %72 = const i64 32
    %73 = gep i8, ptr %10, %72
    %74 = const i64 32
    %75 = gep i8, ptr %55, %74
    %76 = load i64, ptr %73
    store i64 %76, ptr %75
    store ptr %49, ptr %9
    br bb4(%4)
bb4(%5: u64):
    call @func.5(%11, %2)
    br bb5(%5)
bb5(%6: u64):
    %77 = load ptr, ptr %9
    %78 = const i64 8
    %79 = gep i8, ptr %8, %78
    store ptr %77, ptr %79
    %80 = const i64 16
    %81 = gep i8, ptr %8, %80
    %82 = load i64, ptr %11
    store i64 %82, ptr %81
    %83 = const i64 8
    %84 = gep i8, ptr %11, %83
    %85 = const i64 8
    %86 = gep i8, ptr %81, %85
    %87 = load i64, ptr %84
    store i64 %87, ptr %86
    %88 = const i64 1
    store i64 %88, ptr %8
    %89 = load i64, ptr %8
    store i64 %89, ptr %0
    %90 = const i64 8
    %91 = gep i8, ptr %8, %90
    %92 = const i64 8
    %93 = gep i8, ptr %0, %92
    %94 = load i64, ptr %91
    store i64 %94, ptr %93
    %95 = const i64 16
    %96 = gep i8, ptr %8, %95
    %97 = const i64 16
    %98 = gep i8, ptr %0, %97
    %99 = load i64, ptr %96
    store i64 %99, ptr %98
    %100 = const i64 24
    %101 = gep i8, ptr %8, %100
    %102 = const i64 24
    %103 = gep i8, ptr %0, %102
    %104 = load i64, ptr %101
    store i64 %104, ptr %103
    %105 = const i64 32
    %106 = gep i8, ptr %0, %105
    store u64 %6, ptr %106
    ret
}

fn @_RNvMs7_NtCs2EYQwhfuABO_4core3numy12wrapping_mul(functy.7) {
}

fn @mix_hash(functy.8) {
bb0(%0: u64, %1: u64):
    %8 = const u64 14313749767032793493
    %9 = call @func.7(%1, %8)
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
    %21 = call @func.7(%19, %20)
    br bb3(%21)
bb3(%7: u64):
    ret %7
bb4:
    unreachable
}

fn @_RNvMs7_NtCs2EYQwhfuABO_4core3numy12wrapping_mul(functy.9) {
}

fn @_RNvMs9_NtCs2EYQwhfuABO_4core3numj12wrapping_mul(functy.10) {
}

fn @murmur_hash_64a_idx(functy.11) {
bb0(%0: ptr, %1: u64):
    %151 = alloca (i64, i64), align 8
    %152 = alloca (i64, i64), align 8
    %153 = alloca (i32, i32), align 4
    %154 = alloca (i64, i64), align 8
    %155 = alloca (i64, i64), align 8
    %156 = alloca (i64, i64), align 8
    %157 = alloca (i64, i64), align 8
    %158 = alloca (i64, i64), align 8
    %159 = const i64 8
    %160 = gep i8, ptr %0, %159
    %161 = load u64, ptr %160
    %162 = const u64 14313749767032793493
    %163 = call @func.9(%161, %162)
    br bb1(%1, %161, %163)
bb1(%2: u64, %3: u64, %4: u64):
    %164 = xor u64 %2, %4
    %165 = const u64 8
    %166 = const u64 0
    %167 = icmp eq u64 %165, %166
    %168 = const bool false
    %169 = icmp eq bool %167, %168
    condbr %169, bb2(%3, %164), bb35
bb2(%5: u64, %6: u64):
    %170 = const u64 8
    %171 = udiv u64 %5, %170
    %172 = const u64 0
    br bb3(%5, %6, %171, %172)
bb3(%7: u64, %8: u64, %9: u64, %10: u64):
    %173 = icmp ult u64 %10, %9
    condbr %173, bb4(%7, %8, %9, %10), bb19(%7, %8, %9)
bb4(%11: u64, %12: u64, %13: u64, %14: u64):
    %174 = const u64 8
    %175, %176 = mul.overflow u64 %14, %174
    store u64 %175, ptr %151
    %177 = const i64 8
    %178 = gep i8, ptr %151, %177
    store bool %176, ptr %178
    %179 = const i64 8
    %180 = gep i8, ptr %151, %179
    %181 = load bool, ptr %180
    %182 = const bool false
    %183 = icmp eq bool %181, %182
    condbr %183, bb5(%11, %12, %13, %14), bb35
bb5(%15: u64, %16: u64, %17: u64, %18: u64):
    %184 = load u64, ptr %151
    %185 = const u64 0
    %186 = const u64 0
    br bb6(%15, %16, %17, %18, %184, %185, %186)
bb6(%19: u64, %20: u64, %21: u64, %22: u64, %23: u64, %24: u64, %25: u64):
    %187 = const u64 8
    %188 = icmp ult u64 %25, %187
    condbr %188, bb7(%19, %20, %21, %22, %23, %24, %25), bb13(%19, %20, %21, %22, %24)
bb7(%26: u64, %27: u64, %28: u64, %29: u64, %30: u64, %31: u64, %32: u64):
    %189, %190 = add.overflow u64 %30, %32
    store u64 %189, ptr %152
    %191 = const i64 8
    %192 = gep i8, ptr %152, %191
    store bool %190, ptr %192
    %193 = const i64 8
    %194 = gep i8, ptr %152, %193
    %195 = load bool, ptr %194
    %196 = const bool false
    %197 = icmp eq bool %195, %196
    condbr %197, bb8(%26, %27, %28, %29, %30, %31, %32), bb35
bb8(%33: u64, %34: u64, %35: u64, %36: u64, %37: u64, %38: u64, %39: u64):
    %198 = load u64, ptr %152
    %199 = const i64 8
    %200 = gep i8, ptr %0, %199
    %201 = load u64, ptr %200
    %202 = icmp ult u64 %198, %201
    condbr %202, bb9(%33, %34, %35, %36, %37, %38, %39, %198), bb35
bb9(%40: u64, %41: u64, %42: u64, %43: u64, %44: u64, %45: u64, %46: u64, %47: u64):
    %203 = load ptr, ptr %0
    %204 = gep u8, ptr %203, %47
    %205 = load u8, ptr %204
    %206 = zext u8 %205 to u64
    %207 = trunc u64 %46 to u32
    %208 = const u32 8
    %209, %210 = mul.overflow u32 %208, %207
    store u32 %209, ptr %153
    %211 = const i64 4
    %212 = gep i8, ptr %153, %211
    store bool %210, ptr %212
    %213 = const i64 4
    %214 = gep i8, ptr %153, %213
    %215 = load bool, ptr %214
    %216 = const bool false
    %217 = icmp eq bool %215, %216
    condbr %217, bb10(%40, %41, %42, %43, %44, %45, %46, %206), bb35
bb10(%48: u64, %49: u64, %50: u64, %51: u64, %52: u64, %53: u64, %54: u64, %55: u64):
    %218 = load u32, ptr %153
    %219 = const u32 64
    %220 = icmp ult u32 %218, %219
    condbr %220, bb11(%48, %49, %50, %51, %52, %53, %54, %55, %218), bb35
bb11(%56: u64, %57: u64, %58: u64, %59: u64, %60: u64, %61: u64, %62: u64, %63: u64, %64: u32):
    %221 = zext u32 %64 to u64
    %222 = shl u64 %63, %221
    %223 = or u64 %61, %222
    %224 = const u64 1
    %225, %226 = add.overflow u64 %62, %224
    store u64 %225, ptr %154
    %227 = const i64 8
    %228 = gep i8, ptr %154, %227
    store bool %226, ptr %228
    %229 = const i64 8
    %230 = gep i8, ptr %154, %229
    %231 = load bool, ptr %230
    %232 = const bool false
    %233 = icmp eq bool %231, %232
    condbr %233, bb12(%56, %57, %58, %59, %60, %223), bb35
bb12(%65: u64, %66: u64, %67: u64, %68: u64, %69: u64, %70: u64):
    %234 = load u64, ptr %154
    br bb6(%65, %66, %67, %68, %69, %70, %234)
bb13(%71: u64, %72: u64, %73: u64, %74: u64, %75: u64):
    %235 = const u64 14313749767032793493
    %236 = call @func.9(%75, %235)
    br bb14(%71, %72, %73, %74, %236)
bb14(%76: u64, %77: u64, %78: u64, %79: u64, %80: u64):
    %237 = const u32 47
    %238 = const u32 63
    %239 = and u32 %237, %238
    %240 = const u32 64
    %241 = icmp ult u32 %239, %240
    condbr %241, bb15(%76, %77, %78, %79, %80, %80, %239), bb35
bb15(%81: u64, %82: u64, %83: u64, %84: u64, %85: u64, %86: u64, %87: u32):
    %242 = zext u32 %87 to u64
    %243 = lshr u64 %86, %242
    %244 = xor u64 %85, %243
    %245 = const u64 14313749767032793493
    %246 = call @func.9(%244, %245)
    br bb16(%81, %82, %83, %84, %246)
bb16(%88: u64, %89: u64, %90: u64, %91: u64, %92: u64):
    %247 = xor u64 %89, %92
    %248 = const u64 14313749767032793493
    %249 = call @func.9(%247, %248)
    br bb17(%88, %90, %91, %249)
bb17(%93: u64, %94: u64, %95: u64, %96: u64):
    %250 = const u64 1
    %251, %252 = add.overflow u64 %95, %250
    store u64 %251, ptr %155
    %253 = const i64 8
    %254 = gep i8, ptr %155, %253
    store bool %252, ptr %254
    %255 = const i64 8
    %256 = gep i8, ptr %155, %255
    %257 = load bool, ptr %256
    %258 = const bool false
    %259 = icmp eq bool %257, %258
    condbr %259, bb18(%93, %96, %94), bb35
bb18(%97: u64, %98: u64, %99: u64):
    %260 = load u64, ptr %155
    br bb3(%97, %98, %99, %260)
bb19(%100: u64, %101: u64, %102: u64):
    %261 = const u64 8
    %262, %263 = mul.overflow u64 %102, %261
    store u64 %262, ptr %156
    %264 = const i64 8
    %265 = gep i8, ptr %156, %264
    store bool %263, ptr %265
    %266 = const i64 8
    %267 = gep i8, ptr %156, %266
    %268 = load bool, ptr %267
    %269 = const bool false
    %270 = icmp eq bool %268, %269
    condbr %270, bb20(%100, %101), bb35
bb20(%103: u64, %104: u64):
    %271 = load u64, ptr %156
    br bb21(%103, %104, %271, %271)
bb21(%105: u64, %106: u64, %107: u64, %108: u64):
    %272 = icmp ult u64 %108, %105
    condbr %272, bb22(%105, %106, %107, %108), bb28(%105, %106, %107)
bb22(%109: u64, %110: u64, %111: u64, %112: u64):
    %273 = const i64 8
    %274 = gep i8, ptr %0, %273
    %275 = load u64, ptr %274
    %276 = icmp ult u64 %112, %275
    condbr %276, bb23(%109, %110, %111, %112, %112), bb35
bb23(%113: u64, %114: u64, %115: u64, %116: u64, %117: u64):
    %277 = load ptr, ptr %0
    %278 = gep u8, ptr %277, %117
    %279 = load u8, ptr %278
    %280 = zext u8 %279 to u64
    %281, %282 = sub.overflow u64 %116, %115
    store u64 %281, ptr %157
    %283 = const i64 8
    %284 = gep i8, ptr %157, %283
    store bool %282, ptr %284
    %285 = const i64 8
    %286 = gep i8, ptr %157, %285
    %287 = load bool, ptr %286
    %288 = const bool false
    %289 = icmp eq bool %287, %288
    condbr %289, bb24(%113, %114, %115, %116, %280), bb35
bb24(%118: u64, %119: u64, %120: u64, %121: u64, %122: u64):
    %290 = load u64, ptr %157
    %291 = const u64 8
    %292 = call @func.10(%290, %291)
    br bb25(%118, %119, %120, %121, %122, %292)
bb25(%123: u64, %124: u64, %125: u64, %126: u64, %127: u64, %128: u64):
    %293 = const u64 63
    %294 = and u64 %128, %293
    %295 = const u64 64
    %296 = icmp ult u64 %294, %295
    condbr %296, bb26(%123, %124, %125, %126, %127, %294), bb35
bb26(%129: u64, %130: u64, %131: u64, %132: u64, %133: u64, %134: u64):
    %297 = shl u64 %133, %134
    %298 = xor u64 %130, %297
    %299 = const u64 1
    %300, %301 = add.overflow u64 %132, %299
    store u64 %300, ptr %158
    %302 = const i64 8
    %303 = gep i8, ptr %158, %302
    store bool %301, ptr %303
    %304 = const i64 8
    %305 = gep i8, ptr %158, %304
    %306 = load bool, ptr %305
    %307 = const bool false
    %308 = icmp eq bool %306, %307
    condbr %308, bb27(%129, %298, %131), bb35
bb27(%135: u64, %136: u64, %137: u64):
    %309 = load u64, ptr %158
    br bb21(%135, %136, %137, %309)
bb28(%138: u64, %139: u64, %140: u64):
    %310 = icmp ult u64 %140, %138
    condbr %310, bb29(%139), bb31(%139)
bb29(%141: u64):
    %311 = const u64 14313749767032793493
    %312 = call @func.9(%141, %311)
    br bb30(%312)
bb30(%142: u64):
    br bb31(%142)
bb31(%143: u64):
    %313 = const u32 47
    %314 = const u32 63
    %315 = and u32 %313, %314
    %316 = const u32 64
    %317 = icmp ult u32 %315, %316
    condbr %317, bb32(%143, %143, %315), bb35
bb32(%144: u64, %145: u64, %146: u32):
    %318 = zext u32 %146 to u64
    %319 = lshr u64 %145, %318
    %320 = xor u64 %144, %319
    %321 = const u64 14313749767032793493
    %322 = call @func.9(%320, %321)
    br bb33(%322)
bb33(%147: u64):
    %323 = const u32 47
    %324 = const u32 63
    %325 = and u32 %323, %324
    %326 = const u32 64
    %327 = icmp ult u32 %325, %326
    condbr %327, bb34(%147, %147, %325), bb35
bb34(%148: u64, %149: u64, %150: u32):
    %328 = zext u32 %150 to u64
    %329 = lshr u64 %149, %328
    %330 = xor u64 %148, %329
    ret %330
bb35:
    unreachable
}"#;

/// VERBATIM `--mir-emit-closure str_stage2_name_eq_root` emit (same slice/frontend). 41614 bytes; 10 closure members; validate_module = 0; re-parse OK.
const NAME_EQ_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::str_stage2_name_eq_root"
target "aarch64-apple-darwin" 8 little
file 0 "str_stage2_slice.rs"

functy.0 = (u64) -> (u64)

functy.1 = (ptr) -> ()

functy.2 = (ptr, ptr, ptr) -> ()

functy.3 = (ptr, ptr) -> ()

functy.4 = (ptr, ptr) -> (bool)

functy.5 = (ptr, ptr) -> ()

functy.6 = (ptr, ptr, u64) -> ()

functy.7 = (ptr, ptr) -> ()

functy.8 = (ptr, ptr, ptr) -> ()

functy.9 = (ptr, ptr) -> (bool)

functy.10 = (u64, u64) -> (u64)

functy.11 = (u64, u64) -> (u64)

functy.12 = (u64, u64) -> (u64)

functy.13 = (u64, u64) -> (u64)

functy.14 = (ptr, u64) -> (u64)

fn @str_stage2_name_eq_root(functy.0) {
bb0(%0: u64):
    %13 = alloca (i64, i64, i64, i64, i64), align 8
    %14 = alloca (i64, i64, i64, i64, i64), align 8
    %15 = alloca (i64, i64, i64, i64, i64), align 8
    %16 = alloca (i64, i64), align 8
    %17 = alloca (i64, i64), align 8
    %18 = alloca (i64, i64, i64, i64, i64), align 8
    %19 = alloca (i64, i64, i64, i64, i64), align 8
    %20 = alloca (i64, i64, i64, i64, i64), align 8
    %21 = alloca (i64, i64), align 8
    %22 = alloca (i64, i64), align 8
    %23 = alloca (i64, i64, i64, i64, i64), align 8
    %24 = alloca (i64, i64, i64, i64, i64), align 8
    %25 = alloca (i64, i64, i64, i64, i64), align 8
    %26 = alloca (i64, i64), align 8
    %27 = alloca (i64, i64), align 8
    %28 = alloca (i64, i64, i64, i64, i64), align 8
    %29 = alloca (i64, i64, i64, i64, i64), align 8
    %30 = alloca (i64, i64, i64, i64, i64), align 8
    %31 = alloca (i64, i64), align 8
    %32 = alloca (i64, i64), align 8
    %33 = alloca (i64, i64, i64, i64, i64), align 8
    %34 = alloca (i64, i64, i64, i64, i64), align 8
    %35 = alloca (i64, i64, i64, i64, i64), align 8
    %36 = alloca (i64, i64), align 8
    %37 = alloca (i64, i64), align 8
    %38 = alloca (i64, i64, i64, i64, i64), align 8
    %39 = alloca (i64, i64, i64, i64, i64), align 8
    %40 = alloca (i64, i64, i64, i64, i64), align 8
    %41 = alloca (i64, i64), align 8
    %42 = alloca (i64, i64), align 8
    %43 = alloca (i64, i64, i64, i64, i64), align 8
    %44 = alloca (i64, i64, i64, i64, i64), align 8
    %45 = alloca (i64, i64, i64, i64, i64), align 8
    %46 = alloca (i64, i64), align 8
    %47 = alloca (i64, i64), align 8
    %48 = alloca (i64, i64, i64, i64, i64), align 8
    %49 = alloca (i64, i64, i64, i64, i64), align 8
    %50 = alloca (i64, i64, i64, i64, i64), align 8
    %51 = alloca (i64, i64), align 8
    %52 = alloca (i64, i64), align 8
    %53 = const i64 4
    %54 = heap_alloc rust_heap i8, %53, align 1
    %55 = const u8 84
    store u8 %55, ptr %54
    %56 = const i64 1
    %57 = gep i8, ptr %54, %56
    %58 = const u8 114
    store u8 %58, ptr %57
    %59 = const i64 2
    %60 = gep i8, ptr %54, %59
    %61 = const u8 101
    store u8 %61, ptr %60
    %62 = const i64 3
    %63 = gep i8, ptr %54, %62
    %64 = const u8 101
    store u8 %64, ptr %63
    %65 = alloca (i64, i64), align 8
    store ptr %54, ptr %65
    %66 = const i64 8
    %67 = gep i8, ptr %65, %66
    %68 = const u64 4
    store u64 %68, ptr %67
    %69 = const i64 3
    %70 = heap_alloc rust_heap i8, %69, align 1
    %71 = const u8 114
    store u8 %71, ptr %70
    %72 = const i64 1
    %73 = gep i8, ptr %70, %72
    %74 = const u8 101
    store u8 %74, ptr %73
    %75 = const i64 2
    %76 = gep i8, ptr %70, %75
    %77 = const u8 99
    store u8 %77, ptr %76
    %78 = alloca (i64, i64), align 8
    store ptr %70, ptr %78
    %79 = const i64 8
    %80 = gep i8, ptr %78, %79
    %81 = const u64 3
    store u64 %81, ptr %80
    %82 = const i64 6
    %83 = heap_alloc rust_heap i8, %82, align 1
    %84 = const u8 70
    store u8 %84, ptr %83
    %85 = const i64 1
    %86 = gep i8, ptr %83, %85
    %87 = const u8 111
    store u8 %87, ptr %86
    %88 = const i64 2
    %89 = gep i8, ptr %83, %88
    %90 = const u8 114
    store u8 %90, ptr %89
    %91 = const i64 3
    %92 = gep i8, ptr %83, %91
    %93 = const u8 101
    store u8 %93, ptr %92
    %94 = const i64 4
    %95 = gep i8, ptr %83, %94
    %96 = const u8 115
    store u8 %96, ptr %95
    %97 = const i64 5
    %98 = gep i8, ptr %83, %97
    %99 = const u8 116
    store u8 %99, ptr %98
    %100 = alloca (i64, i64), align 8
    store ptr %83, ptr %100
    %101 = const i64 8
    %102 = gep i8, ptr %100, %101
    %103 = const u64 6
    store u64 %103, ptr %102
    %104 = const i64 3
    %105 = heap_alloc rust_heap i8, %104, align 1
    %106 = const u8 78
    store u8 %106, ptr %105
    %107 = const i64 1
    %108 = gep i8, ptr %105, %107
    %109 = const u8 97
    store u8 %109, ptr %108
    %110 = const i64 2
    %111 = gep i8, ptr %105, %110
    %112 = const u8 116
    store u8 %112, ptr %111
    %113 = alloca (i64, i64), align 8
    store ptr %105, ptr %113
    %114 = const i64 8
    %115 = gep i8, ptr %113, %114
    %116 = const u64 3
    store u64 %116, ptr %115
    %117 = const i64 2
    %118 = heap_alloc rust_heap i8, %117, align 1
    %119 = const u8 52
    store u8 %119, ptr %118
    %120 = const i64 1
    %121 = gep i8, ptr %118, %120
    %122 = const u8 50
    store u8 %122, ptr %121
    %123 = alloca (i64, i64), align 8
    store ptr %118, ptr %123
    %124 = const i64 8
    %125 = gep i8, ptr %123, %124
    %126 = const u64 2
    store u64 %126, ptr %125
    %127 = const i64 2
    %128 = heap_alloc rust_heap i8, %127, align 1
    %129 = const u8 52
    store u8 %129, ptr %128
    %130 = const i64 1
    %131 = gep i8, ptr %128, %130
    %132 = const u8 51
    store u8 %132, ptr %131
    %133 = alloca (i64, i64), align 8
    store ptr %128, ptr %133
    %134 = const i64 8
    %135 = gep i8, ptr %133, %134
    %136 = const u64 2
    store u64 %136, ptr %135
    %137 = const u64 0
    %138 = icmp eq u64 %0, %137
    condbr %138, bb1, bb10(%0)
bb1:
    call @func.1(%15)
    br bb2
bb2:
    store ptr %54, ptr %16
    %139 = const i64 8
    %140 = gep i8, ptr %16, %139
    %141 = const u64 4
    store u64 %141, ptr %140
    call @func.2(%14, %15, %16)
    br bb3
bb3:
    store ptr %70, ptr %17
    %142 = const i64 8
    %143 = gep i8, ptr %17, %142
    %144 = const u64 3
    store u64 %144, ptr %143
    call @func.2(%13, %14, %17)
    br bb4
bb4:
    call @func.1(%20)
    br bb5
bb5:
    store ptr %54, ptr %21
    %145 = const i64 8
    %146 = gep i8, ptr %21, %145
    %147 = const u64 4
    store u64 %147, ptr %146
    call @func.2(%19, %20, %21)
    br bb6
bb6:
    store ptr %70, ptr %22
    %148 = const i64 8
    %149 = gep i8, ptr %22, %148
    %150 = const u64 3
    store u64 %150, ptr %149
    call @func.2(%18, %19, %22)
    br bb7
bb7:
    %151 = call @func.4(%13, %18)
    br bb8(%151)
bb8(%1: bool):
    br bb9(%1)
bb9(%2: bool):
    br bb39(%2)
bb10(%3: u64):
    %152 = const u64 1
    %153 = icmp eq u64 %3, %152
    condbr %153, bb11, bb20(%3)
bb11:
    call @func.1(%25)
    br bb12
bb12:
    store ptr %54, ptr %26
    %154 = const i64 8
    %155 = gep i8, ptr %26, %154
    %156 = const u64 4
    store u64 %156, ptr %155
    call @func.2(%24, %25, %26)
    br bb13
bb13:
    store ptr %70, ptr %27
    %157 = const i64 8
    %158 = gep i8, ptr %27, %157
    %159 = const u64 3
    store u64 %159, ptr %158
    call @func.2(%23, %24, %27)
    br bb14
bb14:
    call @func.1(%30)
    br bb15
bb15:
    store ptr %83, ptr %31
    %160 = const i64 8
    %161 = gep i8, ptr %31, %160
    %162 = const u64 6
    store u64 %162, ptr %161
    call @func.2(%29, %30, %31)
    br bb16
bb16:
    store ptr %70, ptr %32
    %163 = const i64 8
    %164 = gep i8, ptr %32, %163
    %165 = const u64 3
    store u64 %165, ptr %164
    call @func.2(%28, %29, %32)
    br bb17
bb17:
    %166 = call @func.4(%23, %28)
    br bb18(%166)
bb18(%4: bool):
    br bb19(%4)
bb19(%5: bool):
    br bb39(%5)
bb20(%6: u64):
    %167 = const u64 2
    %168 = icmp eq u64 %6, %167
    condbr %168, bb21, bb30
bb21:
    call @func.1(%35)
    br bb22
bb22:
    store ptr %105, ptr %36
    %169 = const i64 8
    %170 = gep i8, ptr %36, %169
    %171 = const u64 3
    store u64 %171, ptr %170
    call @func.2(%34, %35, %36)
    br bb23
bb23:
    store ptr %118, ptr %37
    %172 = const i64 8
    %173 = gep i8, ptr %37, %172
    %174 = const u64 2
    store u64 %174, ptr %173
    call @func.2(%33, %34, %37)
    br bb24
bb24:
    call @func.1(%40)
    br bb25
bb25:
    store ptr %105, ptr %41
    %175 = const i64 8
    %176 = gep i8, ptr %41, %175
    %177 = const u64 3
    store u64 %177, ptr %176
    call @func.2(%39, %40, %41)
    br bb26
bb26:
    store ptr %118, ptr %42
    %178 = const i64 8
    %179 = gep i8, ptr %42, %178
    %180 = const u64 2
    store u64 %180, ptr %179
    call @func.2(%38, %39, %42)
    br bb27
bb27:
    %181 = call @func.4(%33, %38)
    br bb28(%181)
bb28(%7: bool):
    br bb29(%7)
bb29(%8: bool):
    br bb39(%8)
bb30:
    call @func.1(%45)
    br bb31
bb31:
    store ptr %105, ptr %46
    %182 = const i64 8
    %183 = gep i8, ptr %46, %182
    %184 = const u64 3
    store u64 %184, ptr %183
    call @func.2(%44, %45, %46)
    br bb32
bb32:
    store ptr %118, ptr %47
    %185 = const i64 8
    %186 = gep i8, ptr %47, %185
    %187 = const u64 2
    store u64 %187, ptr %186
    call @func.2(%43, %44, %47)
    br bb33
bb33:
    call @func.1(%50)
    br bb34
bb34:
    store ptr %105, ptr %51
    %188 = const i64 8
    %189 = gep i8, ptr %51, %188
    %190 = const u64 3
    store u64 %190, ptr %189
    call @func.2(%49, %50, %51)
    br bb35
bb35:
    store ptr %128, ptr %52
    %191 = const i64 8
    %192 = gep i8, ptr %52, %191
    %193 = const u64 2
    store u64 %193, ptr %192
    call @func.2(%48, %49, %52)
    br bb36
bb36:
    %194 = call @func.4(%43, %48)
    br bb37(%194)
bb37(%9: bool):
    br bb38(%9)
bb38(%10: bool):
    br bb39(%10)
bb39(%11: bool):
    condbr %11, bb40, bb41
bb40:
    %195 = const u64 1
    br bb42(%195)
bb41:
    %196 = const u64 0
    br bb42(%196)
bb42(%12: u64):
    ret %12
}

fn @name_anon(functy.1) {
bb0(%0: ptr):
    %1 = alloca (i64, i64, i64, i64), align 8
    %2 = const i64 0
    store i64 %2, ptr %1
    %3 = load i64, ptr %1
    store i64 %3, ptr %0
    %4 = const i64 8
    %5 = gep i8, ptr %1, %4
    %6 = const i64 8
    %7 = gep i8, ptr %0, %6
    %8 = load i64, ptr %5
    store i64 %8, ptr %7
    %9 = const i64 16
    %10 = gep i8, ptr %1, %9
    %11 = const i64 16
    %12 = gep i8, ptr %0, %11
    %13 = load i64, ptr %10
    store i64 %13, ptr %12
    %14 = const i64 24
    %15 = gep i8, ptr %1, %14
    %16 = const i64 24
    %17 = gep i8, ptr %0, %16
    %18 = load i64, ptr %15
    store i64 %18, ptr %17
    %19 = const u64 1723
    %20 = const i64 32
    %21 = gep i8, ptr %0, %20
    store u64 %19, ptr %21
    ret
}

fn @fold_step(functy.2) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %4 = alloca (i64, i64), align 8
    %5 = alloca (i64, i64, i64, i64, i64), align 8
    %6 = alloca (i64, i64, i64, i64, i64), align 8
    %7 = const bool false
    %8 = const bool true
    call @func.5(%4, %2)
    br bb1
bb1:
    %9 = load bool, ptr %4
    %10 = const i64 8
    %11 = gep i8, ptr %4, %10
    %12 = load u64, ptr %11
    condbr %9, bb2(%12), bb3
bb2(%3: u64):
    %13 = const bool false
    %14 = load i64, ptr %1
    store i64 %14, ptr %5
    %15 = const i64 8
    %16 = gep i8, ptr %1, %15
    %17 = const i64 8
    %18 = gep i8, ptr %5, %17
    %19 = load i64, ptr %16
    store i64 %19, ptr %18
    %20 = const i64 16
    %21 = gep i8, ptr %1, %20
    %22 = const i64 16
    %23 = gep i8, ptr %5, %22
    %24 = load i64, ptr %21
    store i64 %24, ptr %23
    %25 = const i64 24
    %26 = gep i8, ptr %1, %25
    %27 = const i64 24
    %28 = gep i8, ptr %5, %27
    %29 = load i64, ptr %26
    store i64 %29, ptr %28
    %30 = const i64 32
    %31 = gep i8, ptr %1, %30
    %32 = const i64 32
    %33 = gep i8, ptr %5, %32
    %34 = load i64, ptr %31
    store i64 %34, ptr %33
    call @func.6(%0, %5, %3)
    br bb5
bb3:
    %35 = const bool false
    %36 = load i64, ptr %1
    store i64 %36, ptr %6
    %37 = const i64 8
    %38 = gep i8, ptr %1, %37
    %39 = const i64 8
    %40 = gep i8, ptr %6, %39
    %41 = load i64, ptr %38
    store i64 %41, ptr %40
    %42 = const i64 16
    %43 = gep i8, ptr %1, %42
    %44 = const i64 16
    %45 = gep i8, ptr %6, %44
    %46 = load i64, ptr %43
    store i64 %46, ptr %45
    %47 = const i64 24
    %48 = gep i8, ptr %1, %47
    %49 = const i64 24
    %50 = gep i8, ptr %6, %49
    %51 = load i64, ptr %48
    store i64 %51, ptr %50
    %52 = const i64 32
    %53 = gep i8, ptr %1, %52
    %54 = const i64 32
    %55 = gep i8, ptr %6, %54
    %56 = load i64, ptr %53
    store i64 %56, ptr %55
    call @func.8(%0, %6, %2)
    br bb6
bb4:
    ret
bb5:
    br bb4
bb6:
    br bb4
}

fn @_RNvXsw_NtCskTzINo8ZBH9_5alloc4syncINtB5_3ArceENtNtNtCs2EYQwhfuABO_4core3ops5deref5Deref5derefCs77po20IQdNn_16str_stage2_slice(functy.3) {
}

fn @name_eq(functy.4) {
bb0(%0: ptr, %1: ptr):
    %23 = alloca i64, align 8
    %24 = alloca i64, align 8
    %25 = alloca (i64, i64), align 8
    %26 = alloca (i64, i64), align 8
    %27 = alloca (i64, i64), align 8
    %28 = alloca i64, align 8
    %29 = alloca i64, align 8
    %30 = alloca i64, align 8
    %31 = alloca i64, align 8
    %32 = alloca i64, align 8
    %33 = alloca i64, align 8
    %34 = alloca i64, align 8
    %35 = alloca i64, align 8
    %36 = const i64 32
    %37 = gep i8, ptr %0, %36
    %38 = load u64, ptr %37
    %39 = const i64 32
    %40 = gep i8, ptr %1, %39
    %41 = load u64, ptr %40
    %42 = icmp ne u64 %38, %41
    condbr %42, bb1, bb2(%0, %1)
bb1:
    %43 = const bool false
    br bb22(%43)
bb2(%2: ptr, %3: ptr):
    store ptr %2, ptr %23
    store ptr %3, ptr %24
    br bb3
bb3:
    %44 = load ptr, ptr %23
    %45 = load ptr, ptr %24
    store ptr %44, ptr %25
    %46 = const i64 8
    %47 = gep i8, ptr %25, %46
    store ptr %45, ptr %47
    %48 = load ptr, ptr %25
    %49 = load i64, ptr %48
    switch %49 [ 0: bb5 1: bb6 2: bb7 default: bb23 ]
bb4:
    %50 = const bool false
    br bb22(%50)
bb5:
    %51 = const i64 8
    %52 = gep i8, ptr %25, %51
    %53 = load ptr, ptr %52
    %54 = load i64, ptr %53
    switch %54 [ 0: bb10 default: bb4 ]
bb6:
    %55 = const i64 8
    %56 = gep i8, ptr %25, %55
    %57 = load ptr, ptr %56
    %58 = load i64, ptr %57
    switch %58 [ 1: bb9 default: bb4 ]
bb7:
    %59 = const i64 8
    %60 = gep i8, ptr %25, %59
    %61 = load ptr, ptr %60
    %62 = load i64, ptr %61
    switch %62 [ 2: bb8 default: bb4 ]
bb8:
    %63 = load ptr, ptr %25
    store ptr %63, ptr %28
    %64 = load ptr, ptr %28
    %65 = const i64 16
    %66 = gep i8, ptr %64, %65
    %67 = load ptr, ptr %25
    store ptr %67, ptr %29
    %68 = load ptr, ptr %29
    %69 = const i64 8
    %70 = gep i8, ptr %68, %69
    %71 = const i64 8
    %72 = gep i8, ptr %25, %71
    %73 = load ptr, ptr %72
    store ptr %73, ptr %30
    %74 = load ptr, ptr %30
    %75 = const i64 16
    %76 = gep i8, ptr %74, %75
    %77 = const i64 8
    %78 = gep i8, ptr %25, %77
    %79 = load ptr, ptr %78
    store ptr %79, ptr %31
    %80 = load ptr, ptr %31
    %81 = const i64 8
    %82 = gep i8, ptr %80, %81
    %83 = load u64, ptr %70
    %84 = load u64, ptr %82
    %85 = icmp ne u64 %83, %84
    condbr %85, bb18, bb19(%66, %76)
bb9:
    %86 = load ptr, ptr %25
    store ptr %86, ptr %32
    %87 = load ptr, ptr %32
    %88 = const i64 8
    %89 = gep i8, ptr %87, %88
    %90 = load ptr, ptr %25
    store ptr %90, ptr %33
    %91 = load ptr, ptr %33
    %92 = const i64 16
    %93 = gep i8, ptr %91, %92
    %94 = const i64 8
    %95 = gep i8, ptr %25, %94
    %96 = load ptr, ptr %95
    store ptr %96, ptr %34
    %97 = load ptr, ptr %34
    %98 = const i64 8
    %99 = gep i8, ptr %97, %98
    %100 = const i64 8
    %101 = gep i8, ptr %25, %100
    %102 = load ptr, ptr %101
    store ptr %102, ptr %35
    %103 = load ptr, ptr %35
    %104 = const i64 16
    %105 = gep i8, ptr %103, %104
    call @func.3(%26, %93)
    br bb11(%89, %99, %105)
bb10:
    %106 = const bool true
    br bb22(%106)
bb11(%4: ptr, %5: ptr, %6: ptr):
    call @func.3(%27, %6)
    br bb12(%4, %5)
bb12(%7: ptr, %8: ptr):
    %107 = call @func.9(%26, %27)
    br bb13(%7, %8, %107)
bb13(%9: ptr, %10: ptr, %11: bool):
    condbr %11, bb14(%9, %10), bb15
bb14(%12: ptr, %13: ptr):
    %108 = load ptr, ptr %12
    %109 = const i64 16
    %110 = gep i8, ptr %108, %109
    br bb16(%13, %110)
bb15:
    %111 = const bool false
    br bb22(%111)
bb16(%14: ptr, %15: ptr):
    store ptr %15, ptr %23
    %112 = load ptr, ptr %14
    %113 = const i64 16
    %114 = gep i8, ptr %112, %113
    br bb17(%114)
bb17(%16: ptr):
    store ptr %16, ptr %24
    br bb3
bb18:
    %115 = const bool false
    br bb22(%115)
bb19(%17: ptr, %18: ptr):
    %116 = load ptr, ptr %17
    %117 = const i64 16
    %118 = gep i8, ptr %116, %117
    br bb20(%18, %118)
bb20(%19: ptr, %20: ptr):
    store ptr %20, ptr %23
    %119 = load ptr, ptr %19
    %120 = const i64 16
    %121 = gep i8, ptr %119, %120
    br bb21(%121)
bb21(%21: ptr):
    store ptr %21, ptr %24
    br bb3
bb22(%22: bool):
    ret %22
bb23:
    unreachable
}

fn @parse_u64_ascii(functy.5) {
bb0(%0: ptr, %1: ptr):
    %39 = alloca (i64, i64), align 8
    %40 = alloca (i8, i8), align 1
    %41 = alloca (i64, i64), align 8
    %42 = alloca (i64, i64), align 8
    %43 = alloca (i64, i64), align 8
    %44 = alloca (i64, i64), align 8
    %45 = load i64, ptr %1
    store i64 %45, ptr %39
    %46 = const i64 8
    %47 = gep i8, ptr %1, %46
    %48 = const i64 8
    %49 = gep i8, ptr %39, %48
    %50 = load i64, ptr %47
    store i64 %50, ptr %49
    br bb1
bb1:
    %51 = const u64 0
    %52 = const i64 8
    %53 = gep i8, ptr %39, %52
    %54 = load u64, ptr %53
    %55 = const u64 0
    %56 = icmp ugt u64 %54, %55
    condbr %56, bb2(%51), bb5(%51)
bb2(%2: u64):
    %57 = const u64 0
    %58 = const i64 8
    %59 = gep i8, ptr %39, %58
    %60 = load u64, ptr %59
    %61 = icmp ult u64 %57, %60
    condbr %61, bb3(%2, %57), bb24
bb3(%3: u64, %4: u64):
    %62 = load ptr, ptr %39
    %63 = gep u8, ptr %62, %4
    %64 = load u8, ptr %63
    %65 = const u8 43
    %66 = icmp eq u8 %64, %65
    condbr %66, bb4, bb5(%3)
bb4:
    %67 = const u64 1
    br bb5(%67)
bb5(%5: u64):
    %68 = const i64 8
    %69 = gep i8, ptr %39, %68
    %70 = load u64, ptr %69
    %71 = icmp uge u64 %5, %70
    condbr %71, bb6, bb7(%5)
bb6:
    %72 = const bool false
    store bool %72, ptr %0
    %73 = const u64 0
    %74 = const i64 8
    %75 = gep i8, ptr %0, %74
    store u64 %73, ptr %75
    br bb23
bb7(%6: u64):
    %76 = const u64 0
    br bb8(%6, %76)
bb8(%7: u64, %8: u64):
    %77 = const i64 8
    %78 = gep i8, ptr %39, %77
    %79 = load u64, ptr %78
    %80 = icmp ult u64 %7, %79
    condbr %80, bb9(%7, %8), bb22(%8)
bb9(%9: u64, %10: u64):
    %81 = const i64 8
    %82 = gep i8, ptr %39, %81
    %83 = load u64, ptr %82
    %84 = icmp ult u64 %9, %83
    condbr %84, bb10(%9, %10, %9), bb24
bb10(%11: u64, %12: u64, %13: u64):
    %85 = load ptr, ptr %39
    %86 = gep u8, ptr %85, %13
    %87 = load u8, ptr %86
    %88 = const u8 48
    %89 = icmp ult u8 %87, %88
    condbr %89, bb12, bb11(%11, %12, %87)
bb11(%14: u64, %15: u64, %16: u8):
    %90 = const u8 57
    %91 = icmp ugt u8 %16, %90
    condbr %91, bb12, bb13(%14, %15, %16)
bb12:
    %92 = const bool false
    store bool %92, ptr %0
    %93 = const u64 0
    %94 = const i64 8
    %95 = gep i8, ptr %0, %94
    store u64 %93, ptr %95
    br bb23
bb13(%17: u64, %18: u64, %19: u8):
    %96 = const u8 48
    %97, %98 = sub.overflow u8 %19, %96
    store u8 %97, ptr %40
    %99 = const i64 1
    %100 = gep i8, ptr %40, %99
    store bool %98, ptr %100
    %101 = const i64 1
    %102 = gep i8, ptr %40, %101
    %103 = load bool, ptr %102
    %104 = const bool false
    %105 = icmp eq bool %103, %104
    condbr %105, bb14(%17, %18), bb24
bb14(%20: u64, %21: u64):
    %106 = load u8, ptr %40
    %107 = zext u8 %106 to u64
    %108 = const u64 18446744073709551615
    %109, %110 = sub.overflow u64 %108, %107
    store u64 %109, ptr %41
    %111 = const i64 8
    %112 = gep i8, ptr %41, %111
    store bool %110, ptr %112
    %113 = const i64 8
    %114 = gep i8, ptr %41, %113
    %115 = load bool, ptr %114
    %116 = const bool false
    %117 = icmp eq bool %115, %116
    condbr %117, bb15(%20, %21, %107, %21), bb24
bb15(%22: u64, %23: u64, %24: u64, %25: u64):
    %118 = load u64, ptr %41
    %119 = const u64 10
    %120 = const u64 0
    %121 = icmp eq u64 %119, %120
    %122 = const bool false
    %123 = icmp eq bool %121, %122
    condbr %123, bb16(%22, %23, %24, %25, %118), bb24
bb16(%26: u64, %27: u64, %28: u64, %29: u64, %30: u64):
    %124 = const u64 10
    %125 = udiv u64 %30, %124
    %126 = icmp ugt u64 %29, %125
    condbr %126, bb17, bb18(%26, %27, %28)
bb17:
    %127 = const bool false
    store bool %127, ptr %0
    %128 = const u64 0
    %129 = const i64 8
    %130 = gep i8, ptr %0, %129
    store u64 %128, ptr %130
    br bb23
bb18(%31: u64, %32: u64, %33: u64):
    %131 = const u64 10
    %132, %133 = mul.overflow u64 %32, %131
    store u64 %132, ptr %42
    %134 = const i64 8
    %135 = gep i8, ptr %42, %134
    store bool %133, ptr %135
    %136 = const i64 8
    %137 = gep i8, ptr %42, %136
    %138 = load bool, ptr %137
    %139 = const bool false
    %140 = icmp eq bool %138, %139
    condbr %140, bb19(%31, %33), bb24
bb19(%34: u64, %35: u64):
    %141 = load u64, ptr %42
    %142, %143 = add.overflow u64 %141, %35
    store u64 %142, ptr %43
    %144 = const i64 8
    %145 = gep i8, ptr %43, %144
    store bool %143, ptr %145
    %146 = const i64 8
    %147 = gep i8, ptr %43, %146
    %148 = load bool, ptr %147
    %149 = const bool false
    %150 = icmp eq bool %148, %149
    condbr %150, bb20(%34), bb24
bb20(%36: u64):
    %151 = load u64, ptr %43
    %152 = const u64 1
    %153, %154 = add.overflow u64 %36, %152
    store u64 %153, ptr %44
    %155 = const i64 8
    %156 = gep i8, ptr %44, %155
    store bool %154, ptr %156
    %157 = const i64 8
    %158 = gep i8, ptr %44, %157
    %159 = load bool, ptr %158
    %160 = const bool false
    %161 = icmp eq bool %159, %160
    condbr %161, bb21(%151), bb24
bb21(%37: u64):
    %162 = load u64, ptr %44
    br bb8(%162, %37)
bb22(%38: u64):
    %163 = const bool true
    store bool %163, ptr %0
    %164 = const i64 8
    %165 = gep i8, ptr %0, %164
    store u64 %38, ptr %165
    br bb23
bb23:
    ret
bb24:
    unreachable
}

fn @name_num_part(functy.6) {
bb0(%0: ptr, %1: ptr, %2: u64):
    %7 = alloca (i64, i64, i64, i64), align 8
    %8 = alloca i64, align 8
    %9 = alloca (i64, i64, i64, i64, i64), align 8
    %10 = const bool false
    %11 = const bool true
    %12 = const i64 32
    %13 = gep i8, ptr %1, %12
    %14 = load u64, ptr %13
    %15 = call @func.11(%14, %2)
    br bb1(%2, %15)
bb1(%3: u64, %4: u64):
    %16 = const bool false
    %17 = load i64, ptr %1
    store i64 %17, ptr %9
    %18 = const i64 8
    %19 = gep i8, ptr %1, %18
    %20 = const i64 8
    %21 = gep i8, ptr %9, %20
    %22 = load i64, ptr %19
    store i64 %22, ptr %21
    %23 = const i64 16
    %24 = gep i8, ptr %1, %23
    %25 = const i64 16
    %26 = gep i8, ptr %9, %25
    %27 = load i64, ptr %24
    store i64 %27, ptr %26
    %28 = const i64 24
    %29 = gep i8, ptr %1, %28
    %30 = const i64 24
    %31 = gep i8, ptr %9, %30
    %32 = load i64, ptr %29
    store i64 %32, ptr %31
    %33 = const i64 32
    %34 = gep i8, ptr %1, %33
    %35 = const i64 32
    %36 = gep i8, ptr %9, %35
    %37 = load i64, ptr %34
    store i64 %37, ptr %36
    %38 = const i64 56
    %39 = heap_alloc rust_heap i8, %38, align 8
    %40 = const u64 1
    store u64 %40, ptr %39
    %41 = const i64 8
    %42 = gep i8, ptr %39, %41
    %43 = const u64 1
    store u64 %43, ptr %42
    %44 = const i64 16
    %45 = gep i8, ptr %39, %44
    %46 = load i64, ptr %9
    store i64 %46, ptr %45
    %47 = const i64 8
    %48 = gep i8, ptr %9, %47
    %49 = const i64 8
    %50 = gep i8, ptr %45, %49
    %51 = load i64, ptr %48
    store i64 %51, ptr %50
    %52 = const i64 16
    %53 = gep i8, ptr %9, %52
    %54 = const i64 16
    %55 = gep i8, ptr %45, %54
    %56 = load i64, ptr %53
    store i64 %56, ptr %55
    %57 = const i64 24
    %58 = gep i8, ptr %9, %57
    %59 = const i64 24
    %60 = gep i8, ptr %45, %59
    %61 = load i64, ptr %58
    store i64 %61, ptr %60
    %62 = const i64 32
    %63 = gep i8, ptr %9, %62
    %64 = const i64 32
    %65 = gep i8, ptr %45, %64
    %66 = load i64, ptr %63
    store i64 %66, ptr %65
    store ptr %39, ptr %8
    br bb2(%3, %4)
bb2(%5: u64, %6: u64):
    %67 = load ptr, ptr %8
    %68 = const i64 16
    %69 = gep i8, ptr %7, %68
    store ptr %67, ptr %69
    %70 = const i64 8
    %71 = gep i8, ptr %7, %70
    store u64 %5, ptr %71
    %72 = const i64 2
    store i64 %72, ptr %7
    %73 = load i64, ptr %7
    store i64 %73, ptr %0
    %74 = const i64 8
    %75 = gep i8, ptr %7, %74
    %76 = const i64 8
    %77 = gep i8, ptr %0, %76
    %78 = load i64, ptr %75
    store i64 %78, ptr %77
    %79 = const i64 16
    %80 = gep i8, ptr %7, %79
    %81 = const i64 16
    %82 = gep i8, ptr %0, %81
    %83 = load i64, ptr %80
    store i64 %83, ptr %82
    %84 = const i64 24
    %85 = gep i8, ptr %7, %84
    %86 = const i64 24
    %87 = gep i8, ptr %0, %86
    %88 = load i64, ptr %85
    store i64 %88, ptr %87
    %89 = const i64 32
    %90 = gep i8, ptr %0, %89
    store u64 %6, ptr %90
    ret
}

fn @_RNvXs17_NtCskTzINo8ZBH9_5alloc4syncINtB6_3ArceEINtNtCs2EYQwhfuABO_4core7convert4FromReE4fromCs77po20IQdNn_16str_stage2_slice(functy.7) {
}

fn @name_str_part(functy.8) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %7 = alloca (i64, i64), align 8
    %8 = alloca (i64, i64, i64, i64), align 8
    %9 = alloca i64, align 8
    %10 = alloca (i64, i64, i64, i64, i64), align 8
    %11 = alloca (i64, i64), align 8
    %12 = const bool false
    %13 = const bool true
    %14 = load i64, ptr %2
    store i64 %14, ptr %7
    %15 = const i64 8
    %16 = gep i8, ptr %2, %15
    %17 = const i64 8
    %18 = gep i8, ptr %7, %17
    %19 = load i64, ptr %16
    store i64 %19, ptr %18
    br bb1
bb1:
    %20 = const u64 11
    %21 = call @func.14(%7, %20)
    br bb2(%21)
bb2(%3: u64):
    %22 = const i64 32
    %23 = gep i8, ptr %1, %22
    %24 = load u64, ptr %23
    %25 = call @func.11(%24, %3)
    br bb3(%25)
bb3(%4: u64):
    %26 = const bool false
    %27 = load i64, ptr %1
    store i64 %27, ptr %10
    %28 = const i64 8
    %29 = gep i8, ptr %1, %28
    %30 = const i64 8
    %31 = gep i8, ptr %10, %30
    %32 = load i64, ptr %29
    store i64 %32, ptr %31
    %33 = const i64 16
    %34 = gep i8, ptr %1, %33
    %35 = const i64 16
    %36 = gep i8, ptr %10, %35
    %37 = load i64, ptr %34
    store i64 %37, ptr %36
    %38 = const i64 24
    %39 = gep i8, ptr %1, %38
    %40 = const i64 24
    %41 = gep i8, ptr %10, %40
    %42 = load i64, ptr %39
    store i64 %42, ptr %41
    %43 = const i64 32
    %44 = gep i8, ptr %1, %43
    %45 = const i64 32
    %46 = gep i8, ptr %10, %45
    %47 = load i64, ptr %44
    store i64 %47, ptr %46
    %48 = const i64 56
    %49 = heap_alloc rust_heap i8, %48, align 8
    %50 = const u64 1
    store u64 %50, ptr %49
    %51 = const i64 8
    %52 = gep i8, ptr %49, %51
    %53 = const u64 1
    store u64 %53, ptr %52
    %54 = const i64 16
    %55 = gep i8, ptr %49, %54
    %56 = load i64, ptr %10
    store i64 %56, ptr %55
    %57 = const i64 8
    %58 = gep i8, ptr %10, %57
    %59 = const i64 8
    %60 = gep i8, ptr %55, %59
    %61 = load i64, ptr %58
    store i64 %61, ptr %60
    %62 = const i64 16
    %63 = gep i8, ptr %10, %62
    %64 = const i64 16
    %65 = gep i8, ptr %55, %64
    %66 = load i64, ptr %63
    store i64 %66, ptr %65
    %67 = const i64 24
    %68 = gep i8, ptr %10, %67
    %69 = const i64 24
    %70 = gep i8, ptr %55, %69
    %71 = load i64, ptr %68
    store i64 %71, ptr %70
    %72 = const i64 32
    %73 = gep i8, ptr %10, %72
    %74 = const i64 32
    %75 = gep i8, ptr %55, %74
    %76 = load i64, ptr %73
    store i64 %76, ptr %75
    store ptr %49, ptr %9
    br bb4(%4)
bb4(%5: u64):
    call @func.7(%11, %2)
    br bb5(%5)
bb5(%6: u64):
    %77 = load ptr, ptr %9
    %78 = const i64 8
    %79 = gep i8, ptr %8, %78
    store ptr %77, ptr %79
    %80 = const i64 16
    %81 = gep i8, ptr %8, %80
    %82 = load i64, ptr %11
    store i64 %82, ptr %81
    %83 = const i64 8
    %84 = gep i8, ptr %11, %83
    %85 = const i64 8
    %86 = gep i8, ptr %81, %85
    %87 = load i64, ptr %84
    store i64 %87, ptr %86
    %88 = const i64 1
    store i64 %88, ptr %8
    %89 = load i64, ptr %8
    store i64 %89, ptr %0
    %90 = const i64 8
    %91 = gep i8, ptr %8, %90
    %92 = const i64 8
    %93 = gep i8, ptr %0, %92
    %94 = load i64, ptr %91
    store i64 %94, ptr %93
    %95 = const i64 16
    %96 = gep i8, ptr %8, %95
    %97 = const i64 16
    %98 = gep i8, ptr %0, %97
    %99 = load i64, ptr %96
    store i64 %99, ptr %98
    %100 = const i64 24
    %101 = gep i8, ptr %8, %100
    %102 = const i64 24
    %103 = gep i8, ptr %0, %102
    %104 = load i64, ptr %101
    store i64 %104, ptr %103
    %105 = const i64 32
    %106 = gep i8, ptr %0, %105
    store u64 %6, ptr %106
    ret
}

fn @str_bytes_eq(functy.9) {
bb0(%0: ptr, %1: ptr):
    %11 = alloca (i64, i64), align 8
    %12 = alloca (i64, i64), align 8
    %13 = alloca (i64, i64), align 8
    %14 = load i64, ptr %0
    store i64 %14, ptr %11
    %15 = const i64 8
    %16 = gep i8, ptr %0, %15
    %17 = const i64 8
    %18 = gep i8, ptr %11, %17
    %19 = load i64, ptr %16
    store i64 %19, ptr %18
    br bb1
bb1:
    %20 = load i64, ptr %1
    store i64 %20, ptr %12
    %21 = const i64 8
    %22 = gep i8, ptr %1, %21
    %23 = const i64 8
    %24 = gep i8, ptr %12, %23
    %25 = load i64, ptr %22
    store i64 %25, ptr %24
    br bb2
bb2:
    %26 = const i64 8
    %27 = gep i8, ptr %11, %26
    %28 = load u64, ptr %27
    %29 = const i64 8
    %30 = gep i8, ptr %12, %29
    %31 = load u64, ptr %30
    %32 = icmp ne u64 %28, %31
    condbr %32, bb3, bb4
bb3:
    %33 = const bool false
    br bb13(%33)
bb4:
    %34 = const u64 0
    br bb5(%34)
bb5(%2: u64):
    %35 = const i64 8
    %36 = gep i8, ptr %11, %35
    %37 = load u64, ptr %36
    %38 = icmp ult u64 %2, %37
    condbr %38, bb6(%2), bb12
bb6(%3: u64):
    %39 = const i64 8
    %40 = gep i8, ptr %11, %39
    %41 = load u64, ptr %40
    %42 = icmp ult u64 %3, %41
    condbr %42, bb7(%3, %3), bb14
bb7(%4: u64, %5: u64):
    %43 = load ptr, ptr %11
    %44 = gep u8, ptr %43, %5
    %45 = load u8, ptr %44
    %46 = const i64 8
    %47 = gep i8, ptr %12, %46
    %48 = load u64, ptr %47
    %49 = icmp ult u64 %4, %48
    condbr %49, bb8(%4, %45, %4), bb14
bb8(%6: u64, %7: u8, %8: u64):
    %50 = load ptr, ptr %12
    %51 = gep u8, ptr %50, %8
    %52 = load u8, ptr %51
    %53 = icmp ne u8 %7, %52
    condbr %53, bb9, bb10(%6)
bb9:
    %54 = const bool false
    br bb13(%54)
bb10(%9: u64):
    %55 = const u64 1
    %56, %57 = add.overflow u64 %9, %55
    store u64 %56, ptr %13
    %58 = const i64 8
    %59 = gep i8, ptr %13, %58
    store bool %57, ptr %59
    %60 = const i64 8
    %61 = gep i8, ptr %13, %60
    %62 = load bool, ptr %61
    %63 = const bool false
    %64 = icmp eq bool %62, %63
    condbr %64, bb11, bb14
bb11:
    %65 = load u64, ptr %13
    br bb5(%65)
bb12:
    %66 = const bool true
    br bb13(%66)
bb13(%10: bool):
    ret %10
bb14:
    unreachable
}

fn @_RNvMs7_NtCs2EYQwhfuABO_4core3numy12wrapping_mul(functy.10) {
}

fn @mix_hash(functy.11) {
bb0(%0: u64, %1: u64):
    %8 = const u64 14313749767032793493
    %9 = call @func.10(%1, %8)
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
    %21 = call @func.10(%19, %20)
    br bb3(%21)
bb3(%7: u64):
    ret %7
bb4:
    unreachable
}

fn @_RNvMs7_NtCs2EYQwhfuABO_4core3numy12wrapping_mul(functy.12) {
}

fn @_RNvMs9_NtCs2EYQwhfuABO_4core3numj12wrapping_mul(functy.13) {
}

fn @murmur_hash_64a_idx(functy.14) {
bb0(%0: ptr, %1: u64):
    %151 = alloca (i64, i64), align 8
    %152 = alloca (i64, i64), align 8
    %153 = alloca (i32, i32), align 4
    %154 = alloca (i64, i64), align 8
    %155 = alloca (i64, i64), align 8
    %156 = alloca (i64, i64), align 8
    %157 = alloca (i64, i64), align 8
    %158 = alloca (i64, i64), align 8
    %159 = const i64 8
    %160 = gep i8, ptr %0, %159
    %161 = load u64, ptr %160
    %162 = const u64 14313749767032793493
    %163 = call @func.12(%161, %162)
    br bb1(%1, %161, %163)
bb1(%2: u64, %3: u64, %4: u64):
    %164 = xor u64 %2, %4
    %165 = const u64 8
    %166 = const u64 0
    %167 = icmp eq u64 %165, %166
    %168 = const bool false
    %169 = icmp eq bool %167, %168
    condbr %169, bb2(%3, %164), bb35
bb2(%5: u64, %6: u64):
    %170 = const u64 8
    %171 = udiv u64 %5, %170
    %172 = const u64 0
    br bb3(%5, %6, %171, %172)
bb3(%7: u64, %8: u64, %9: u64, %10: u64):
    %173 = icmp ult u64 %10, %9
    condbr %173, bb4(%7, %8, %9, %10), bb19(%7, %8, %9)
bb4(%11: u64, %12: u64, %13: u64, %14: u64):
    %174 = const u64 8
    %175, %176 = mul.overflow u64 %14, %174
    store u64 %175, ptr %151
    %177 = const i64 8
    %178 = gep i8, ptr %151, %177
    store bool %176, ptr %178
    %179 = const i64 8
    %180 = gep i8, ptr %151, %179
    %181 = load bool, ptr %180
    %182 = const bool false
    %183 = icmp eq bool %181, %182
    condbr %183, bb5(%11, %12, %13, %14), bb35
bb5(%15: u64, %16: u64, %17: u64, %18: u64):
    %184 = load u64, ptr %151
    %185 = const u64 0
    %186 = const u64 0
    br bb6(%15, %16, %17, %18, %184, %185, %186)
bb6(%19: u64, %20: u64, %21: u64, %22: u64, %23: u64, %24: u64, %25: u64):
    %187 = const u64 8
    %188 = icmp ult u64 %25, %187
    condbr %188, bb7(%19, %20, %21, %22, %23, %24, %25), bb13(%19, %20, %21, %22, %24)
bb7(%26: u64, %27: u64, %28: u64, %29: u64, %30: u64, %31: u64, %32: u64):
    %189, %190 = add.overflow u64 %30, %32
    store u64 %189, ptr %152
    %191 = const i64 8
    %192 = gep i8, ptr %152, %191
    store bool %190, ptr %192
    %193 = const i64 8
    %194 = gep i8, ptr %152, %193
    %195 = load bool, ptr %194
    %196 = const bool false
    %197 = icmp eq bool %195, %196
    condbr %197, bb8(%26, %27, %28, %29, %30, %31, %32), bb35
bb8(%33: u64, %34: u64, %35: u64, %36: u64, %37: u64, %38: u64, %39: u64):
    %198 = load u64, ptr %152
    %199 = const i64 8
    %200 = gep i8, ptr %0, %199
    %201 = load u64, ptr %200
    %202 = icmp ult u64 %198, %201
    condbr %202, bb9(%33, %34, %35, %36, %37, %38, %39, %198), bb35
bb9(%40: u64, %41: u64, %42: u64, %43: u64, %44: u64, %45: u64, %46: u64, %47: u64):
    %203 = load ptr, ptr %0
    %204 = gep u8, ptr %203, %47
    %205 = load u8, ptr %204
    %206 = zext u8 %205 to u64
    %207 = trunc u64 %46 to u32
    %208 = const u32 8
    %209, %210 = mul.overflow u32 %208, %207
    store u32 %209, ptr %153
    %211 = const i64 4
    %212 = gep i8, ptr %153, %211
    store bool %210, ptr %212
    %213 = const i64 4
    %214 = gep i8, ptr %153, %213
    %215 = load bool, ptr %214
    %216 = const bool false
    %217 = icmp eq bool %215, %216
    condbr %217, bb10(%40, %41, %42, %43, %44, %45, %46, %206), bb35
bb10(%48: u64, %49: u64, %50: u64, %51: u64, %52: u64, %53: u64, %54: u64, %55: u64):
    %218 = load u32, ptr %153
    %219 = const u32 64
    %220 = icmp ult u32 %218, %219
    condbr %220, bb11(%48, %49, %50, %51, %52, %53, %54, %55, %218), bb35
bb11(%56: u64, %57: u64, %58: u64, %59: u64, %60: u64, %61: u64, %62: u64, %63: u64, %64: u32):
    %221 = zext u32 %64 to u64
    %222 = shl u64 %63, %221
    %223 = or u64 %61, %222
    %224 = const u64 1
    %225, %226 = add.overflow u64 %62, %224
    store u64 %225, ptr %154
    %227 = const i64 8
    %228 = gep i8, ptr %154, %227
    store bool %226, ptr %228
    %229 = const i64 8
    %230 = gep i8, ptr %154, %229
    %231 = load bool, ptr %230
    %232 = const bool false
    %233 = icmp eq bool %231, %232
    condbr %233, bb12(%56, %57, %58, %59, %60, %223), bb35
bb12(%65: u64, %66: u64, %67: u64, %68: u64, %69: u64, %70: u64):
    %234 = load u64, ptr %154
    br bb6(%65, %66, %67, %68, %69, %70, %234)
bb13(%71: u64, %72: u64, %73: u64, %74: u64, %75: u64):
    %235 = const u64 14313749767032793493
    %236 = call @func.12(%75, %235)
    br bb14(%71, %72, %73, %74, %236)
bb14(%76: u64, %77: u64, %78: u64, %79: u64, %80: u64):
    %237 = const u32 47
    %238 = const u32 63
    %239 = and u32 %237, %238
    %240 = const u32 64
    %241 = icmp ult u32 %239, %240
    condbr %241, bb15(%76, %77, %78, %79, %80, %80, %239), bb35
bb15(%81: u64, %82: u64, %83: u64, %84: u64, %85: u64, %86: u64, %87: u32):
    %242 = zext u32 %87 to u64
    %243 = lshr u64 %86, %242
    %244 = xor u64 %85, %243
    %245 = const u64 14313749767032793493
    %246 = call @func.12(%244, %245)
    br bb16(%81, %82, %83, %84, %246)
bb16(%88: u64, %89: u64, %90: u64, %91: u64, %92: u64):
    %247 = xor u64 %89, %92
    %248 = const u64 14313749767032793493
    %249 = call @func.12(%247, %248)
    br bb17(%88, %90, %91, %249)
bb17(%93: u64, %94: u64, %95: u64, %96: u64):
    %250 = const u64 1
    %251, %252 = add.overflow u64 %95, %250
    store u64 %251, ptr %155
    %253 = const i64 8
    %254 = gep i8, ptr %155, %253
    store bool %252, ptr %254
    %255 = const i64 8
    %256 = gep i8, ptr %155, %255
    %257 = load bool, ptr %256
    %258 = const bool false
    %259 = icmp eq bool %257, %258
    condbr %259, bb18(%93, %96, %94), bb35
bb18(%97: u64, %98: u64, %99: u64):
    %260 = load u64, ptr %155
    br bb3(%97, %98, %99, %260)
bb19(%100: u64, %101: u64, %102: u64):
    %261 = const u64 8
    %262, %263 = mul.overflow u64 %102, %261
    store u64 %262, ptr %156
    %264 = const i64 8
    %265 = gep i8, ptr %156, %264
    store bool %263, ptr %265
    %266 = const i64 8
    %267 = gep i8, ptr %156, %266
    %268 = load bool, ptr %267
    %269 = const bool false
    %270 = icmp eq bool %268, %269
    condbr %270, bb20(%100, %101), bb35
bb20(%103: u64, %104: u64):
    %271 = load u64, ptr %156
    br bb21(%103, %104, %271, %271)
bb21(%105: u64, %106: u64, %107: u64, %108: u64):
    %272 = icmp ult u64 %108, %105
    condbr %272, bb22(%105, %106, %107, %108), bb28(%105, %106, %107)
bb22(%109: u64, %110: u64, %111: u64, %112: u64):
    %273 = const i64 8
    %274 = gep i8, ptr %0, %273
    %275 = load u64, ptr %274
    %276 = icmp ult u64 %112, %275
    condbr %276, bb23(%109, %110, %111, %112, %112), bb35
bb23(%113: u64, %114: u64, %115: u64, %116: u64, %117: u64):
    %277 = load ptr, ptr %0
    %278 = gep u8, ptr %277, %117
    %279 = load u8, ptr %278
    %280 = zext u8 %279 to u64
    %281, %282 = sub.overflow u64 %116, %115
    store u64 %281, ptr %157
    %283 = const i64 8
    %284 = gep i8, ptr %157, %283
    store bool %282, ptr %284
    %285 = const i64 8
    %286 = gep i8, ptr %157, %285
    %287 = load bool, ptr %286
    %288 = const bool false
    %289 = icmp eq bool %287, %288
    condbr %289, bb24(%113, %114, %115, %116, %280), bb35
bb24(%118: u64, %119: u64, %120: u64, %121: u64, %122: u64):
    %290 = load u64, ptr %157
    %291 = const u64 8
    %292 = call @func.13(%290, %291)
    br bb25(%118, %119, %120, %121, %122, %292)
bb25(%123: u64, %124: u64, %125: u64, %126: u64, %127: u64, %128: u64):
    %293 = const u64 63
    %294 = and u64 %128, %293
    %295 = const u64 64
    %296 = icmp ult u64 %294, %295
    condbr %296, bb26(%123, %124, %125, %126, %127, %294), bb35
bb26(%129: u64, %130: u64, %131: u64, %132: u64, %133: u64, %134: u64):
    %297 = shl u64 %133, %134
    %298 = xor u64 %130, %297
    %299 = const u64 1
    %300, %301 = add.overflow u64 %132, %299
    store u64 %300, ptr %158
    %302 = const i64 8
    %303 = gep i8, ptr %158, %302
    store bool %301, ptr %303
    %304 = const i64 8
    %305 = gep i8, ptr %158, %304
    %306 = load bool, ptr %305
    %307 = const bool false
    %308 = icmp eq bool %306, %307
    condbr %308, bb27(%129, %298, %131), bb35
bb27(%135: u64, %136: u64, %137: u64):
    %309 = load u64, ptr %158
    br bb21(%135, %136, %137, %309)
bb28(%138: u64, %139: u64, %140: u64):
    %310 = icmp ult u64 %140, %138
    condbr %310, bb29(%139), bb31(%139)
bb29(%141: u64):
    %311 = const u64 14313749767032793493
    %312 = call @func.12(%141, %311)
    br bb30(%312)
bb30(%142: u64):
    br bb31(%142)
bb31(%143: u64):
    %313 = const u32 47
    %314 = const u32 63
    %315 = and u32 %313, %314
    %316 = const u32 64
    %317 = icmp ult u32 %315, %316
    condbr %317, bb32(%143, %143, %315), bb35
bb32(%144: u64, %145: u64, %146: u32):
    %318 = zext u32 %146 to u64
    %319 = lshr u64 %145, %318
    %320 = xor u64 %144, %319
    %321 = const u64 14313749767032793493
    %322 = call @func.12(%320, %321)
    br bb33(%322)
bb33(%147: u64):
    %323 = const u32 47
    %324 = const u32 63
    %325 = and u32 %323, %324
    %326 = const u32 64
    %327 = icmp ult u32 %325, %326
    condbr %327, bb34(%147, %147, %325), bb35
bb34(%148: u64, %149: u64, %150: u32):
    %328 = zext u32 %150 to u64
    %329 = lshr u64 %149, %328
    %330 = xor u64 %148, %329
    ret %330
bb35:
    unreachable
}"#;

/// VERBATIM `--mir-emit-closure str_stage2_rec_scenario_root` emit (same slice/frontend). 41578 bytes; 11 closure members; validate_module = 0; re-parse OK.
const SCENARIO_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::str_stage2_rec_scenario_root"
target "aarch64-apple-darwin" 8 little
file 0 "str_stage2_slice.rs"

functy.0 = (ptr, u64) -> ()

functy.1 = (ptr) -> ()

functy.2 = (ptr, ptr, ptr) -> ()

functy.3 = (ptr, ptr) -> ()

functy.4 = (ptr, ptr) -> ()

functy.5 = (ptr, ptr, u64) -> ()

functy.6 = (ptr, ptr) -> ()

functy.7 = (ptr, ptr, ptr) -> ()

functy.8 = (ptr, ptr) -> ()

functy.9 = (ptr, ptr) -> (bool)

functy.10 = (u64, u64) -> (u64)

functy.11 = (u64, u64) -> (u64)

functy.12 = (u64, u64) -> (u64)

functy.13 = (u64, u64) -> (u64)

functy.14 = (ptr, u64) -> (u64)

functy.15 = (ptr, ptr) -> (bool)

fn @str_stage2_rec_scenario_root(functy.0) {
bb0(%0: ptr, %1: u64):
    %2 = alloca (i64, i64, i64, i64, i64), align 8
    %3 = alloca (i64, i64, i64, i64, i64), align 8
    %4 = alloca (i64, i64), align 8
    %5 = alloca (i64, i64, i64, i64, i64), align 8
    %6 = alloca (i64, i64), align 8
    %7 = const i64 4
    %8 = heap_alloc rust_heap i8, %7, align 1
    %9 = const u8 84
    store u8 %9, ptr %8
    %10 = const i64 1
    %11 = gep i8, ptr %8, %10
    %12 = const u8 114
    store u8 %12, ptr %11
    %13 = const i64 2
    %14 = gep i8, ptr %8, %13
    %15 = const u8 101
    store u8 %15, ptr %14
    %16 = const i64 3
    %17 = gep i8, ptr %8, %16
    %18 = const u8 101
    store u8 %18, ptr %17
    %19 = alloca (i64, i64), align 8
    store ptr %8, ptr %19
    %20 = const i64 8
    %21 = gep i8, ptr %19, %20
    %22 = const u64 4
    store u64 %22, ptr %21
    %23 = const i64 6
    %24 = heap_alloc rust_heap i8, %23, align 1
    %25 = const u8 70
    store u8 %25, ptr %24
    %26 = const i64 1
    %27 = gep i8, ptr %24, %26
    %28 = const u8 111
    store u8 %28, ptr %27
    %29 = const i64 2
    %30 = gep i8, ptr %24, %29
    %31 = const u8 114
    store u8 %31, ptr %30
    %32 = const i64 3
    %33 = gep i8, ptr %24, %32
    %34 = const u8 101
    store u8 %34, ptr %33
    %35 = const i64 4
    %36 = gep i8, ptr %24, %35
    %37 = const u8 115
    store u8 %37, ptr %36
    %38 = const i64 5
    %39 = gep i8, ptr %24, %38
    %40 = const u8 116
    store u8 %40, ptr %39
    %41 = alloca (i64, i64), align 8
    store ptr %24, ptr %41
    %42 = const i64 8
    %43 = gep i8, ptr %41, %42
    %44 = const u64 6
    store u64 %44, ptr %43
    %45 = const u64 0
    %46 = icmp eq u64 %1, %45
    condbr %46, bb1, bb3
bb1:
    call @func.1(%3)
    br bb2
bb2:
    store ptr %8, ptr %4
    %47 = const i64 8
    %48 = gep i8, ptr %4, %47
    %49 = const u64 4
    store u64 %49, ptr %48
    call @func.2(%2, %3, %4)
    br bb5
bb3:
    call @func.1(%5)
    br bb4
bb4:
    store ptr %24, ptr %6
    %50 = const i64 8
    %51 = gep i8, ptr %6, %50
    %52 = const u64 6
    store u64 %52, ptr %51
    call @func.2(%2, %5, %6)
    br bb5
bb5:
    call @func.3(%0, %2)
    br bb6
bb6:
    br bb7
bb7:
    ret
}

fn @name_anon(functy.1) {
bb0(%0: ptr):
    %1 = alloca (i64, i64, i64, i64), align 8
    %2 = const i64 0
    store i64 %2, ptr %1
    %3 = load i64, ptr %1
    store i64 %3, ptr %0
    %4 = const i64 8
    %5 = gep i8, ptr %1, %4
    %6 = const i64 8
    %7 = gep i8, ptr %0, %6
    %8 = load i64, ptr %5
    store i64 %8, ptr %7
    %9 = const i64 16
    %10 = gep i8, ptr %1, %9
    %11 = const i64 16
    %12 = gep i8, ptr %0, %11
    %13 = load i64, ptr %10
    store i64 %13, ptr %12
    %14 = const i64 24
    %15 = gep i8, ptr %1, %14
    %16 = const i64 24
    %17 = gep i8, ptr %0, %16
    %18 = load i64, ptr %15
    store i64 %18, ptr %17
    %19 = const u64 1723
    %20 = const i64 32
    %21 = gep i8, ptr %0, %20
    store u64 %19, ptr %21
    ret
}

fn @fold_step(functy.2) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %4 = alloca (i64, i64), align 8
    %5 = alloca (i64, i64, i64, i64, i64), align 8
    %6 = alloca (i64, i64, i64, i64, i64), align 8
    %7 = const bool false
    %8 = const bool true
    call @func.4(%4, %2)
    br bb1
bb1:
    %9 = load bool, ptr %4
    %10 = const i64 8
    %11 = gep i8, ptr %4, %10
    %12 = load u64, ptr %11
    condbr %9, bb2(%12), bb3
bb2(%3: u64):
    %13 = const bool false
    %14 = load i64, ptr %1
    store i64 %14, ptr %5
    %15 = const i64 8
    %16 = gep i8, ptr %1, %15
    %17 = const i64 8
    %18 = gep i8, ptr %5, %17
    %19 = load i64, ptr %16
    store i64 %19, ptr %18
    %20 = const i64 16
    %21 = gep i8, ptr %1, %20
    %22 = const i64 16
    %23 = gep i8, ptr %5, %22
    %24 = load i64, ptr %21
    store i64 %24, ptr %23
    %25 = const i64 24
    %26 = gep i8, ptr %1, %25
    %27 = const i64 24
    %28 = gep i8, ptr %5, %27
    %29 = load i64, ptr %26
    store i64 %29, ptr %28
    %30 = const i64 32
    %31 = gep i8, ptr %1, %30
    %32 = const i64 32
    %33 = gep i8, ptr %5, %32
    %34 = load i64, ptr %31
    store i64 %34, ptr %33
    call @func.5(%0, %5, %3)
    br bb5
bb3:
    %35 = const bool false
    %36 = load i64, ptr %1
    store i64 %36, ptr %6
    %37 = const i64 8
    %38 = gep i8, ptr %1, %37
    %39 = const i64 8
    %40 = gep i8, ptr %6, %39
    %41 = load i64, ptr %38
    store i64 %41, ptr %40
    %42 = const i64 16
    %43 = gep i8, ptr %1, %42
    %44 = const i64 16
    %45 = gep i8, ptr %6, %44
    %46 = load i64, ptr %43
    store i64 %46, ptr %45
    %47 = const i64 24
    %48 = gep i8, ptr %1, %47
    %49 = const i64 24
    %50 = gep i8, ptr %6, %49
    %51 = load i64, ptr %48
    store i64 %51, ptr %50
    %52 = const i64 32
    %53 = gep i8, ptr %1, %52
    %54 = const i64 32
    %55 = gep i8, ptr %6, %54
    %56 = load i64, ptr %53
    store i64 %56, ptr %55
    call @func.7(%0, %6, %2)
    br bb6
bb4:
    ret
bb5:
    br bb4
bb6:
    br bb4
}

fn @rec_name_of_constructed(functy.3) {
bb0(%0: ptr, %1: ptr):
    %36 = alloca (i64, i64, i64, i64, i64), align 8
    %37 = alloca (i64, i64, i64, i64, i64), align 8
    %38 = alloca (i64, i64), align 8
    %39 = alloca (i64, i64, i64, i64, i64), align 8
    %40 = alloca (i64, i64, i64, i64, i64), align 8
    %41 = alloca (i64, i64), align 8
    %42 = alloca (i64, i64, i64, i64, i64), align 8
    %43 = alloca (i64, i64), align 8
    %44 = alloca (i64, i64, i64, i64, i64), align 8
    %45 = alloca (i64, i64), align 8
    %46 = alloca (i64, i64, i64, i64, i64), align 8
    %47 = alloca (i64, i64, i64, i64, i64), align 8
    %48 = alloca (i64, i64), align 8
    %49 = alloca (i64, i64), align 8
    %50 = const i64 4
    %51 = heap_alloc rust_heap i8, %50, align 1
    %52 = const u8 84
    store u8 %52, ptr %51
    %53 = const i64 1
    %54 = gep i8, ptr %51, %53
    %55 = const u8 114
    store u8 %55, ptr %54
    %56 = const i64 2
    %57 = gep i8, ptr %51, %56
    %58 = const u8 101
    store u8 %58, ptr %57
    %59 = const i64 3
    %60 = gep i8, ptr %51, %59
    %61 = const u8 101
    store u8 %61, ptr %60
    %62 = alloca (i64, i64), align 8
    store ptr %51, ptr %62
    %63 = const i64 8
    %64 = gep i8, ptr %62, %63
    %65 = const u64 4
    store u64 %65, ptr %64
    %66 = const i64 6
    %67 = heap_alloc rust_heap i8, %66, align 1
    %68 = const u8 70
    store u8 %68, ptr %67
    %69 = const i64 1
    %70 = gep i8, ptr %67, %69
    %71 = const u8 111
    store u8 %71, ptr %70
    %72 = const i64 2
    %73 = gep i8, ptr %67, %72
    %74 = const u8 114
    store u8 %74, ptr %73
    %75 = const i64 3
    %76 = gep i8, ptr %67, %75
    %77 = const u8 101
    store u8 %77, ptr %76
    %78 = const i64 4
    %79 = gep i8, ptr %67, %78
    %80 = const u8 115
    store u8 %80, ptr %79
    %81 = const i64 5
    %82 = gep i8, ptr %67, %81
    %83 = const u8 116
    store u8 %83, ptr %82
    %84 = alloca (i64, i64), align 8
    store ptr %67, ptr %84
    %85 = const i64 8
    %86 = gep i8, ptr %84, %85
    %87 = const u64 6
    store u64 %87, ptr %86
    %88 = const i64 3
    %89 = heap_alloc rust_heap i8, %88, align 1
    %90 = const u8 114
    store u8 %90, ptr %89
    %91 = const i64 1
    %92 = gep i8, ptr %89, %91
    %93 = const u8 101
    store u8 %93, ptr %92
    %94 = const i64 2
    %95 = gep i8, ptr %89, %94
    %96 = const u8 99
    store u8 %96, ptr %95
    %97 = alloca (i64, i64), align 8
    store ptr %89, ptr %97
    %98 = const i64 8
    %99 = gep i8, ptr %97, %98
    %100 = const u64 3
    store u64 %100, ptr %99
    %101 = const i64 4
    %102 = heap_alloc rust_heap i8, %101, align 1
    %103 = const u8 68
    store u8 %103, ptr %102
    %104 = const i64 1
    %105 = gep i8, ptr %102, %104
    %106 = const u8 101
    store u8 %106, ptr %105
    %107 = const i64 2
    %108 = gep i8, ptr %102, %107
    %109 = const u8 97
    store u8 %109, ptr %108
    %110 = const i64 3
    %111 = gep i8, ptr %102, %110
    %112 = const u8 100
    store u8 %112, ptr %111
    %113 = alloca (i64, i64), align 8
    store ptr %102, ptr %113
    %114 = const i64 8
    %115 = gep i8, ptr %113, %114
    %116 = const u64 4
    store u64 %116, ptr %115
    %117 = const bool false
    %118 = const bool false
    call @func.1(%37)
    br bb1(%1)
bb1(%2: ptr):
    store ptr %51, ptr %38
    %119 = const i64 8
    %120 = gep i8, ptr %38, %119
    %121 = const u64 4
    store u64 %121, ptr %120
    call @func.2(%36, %37, %38)
    br bb2(%2)
bb2(%3: ptr):
    %122 = const bool true
    call @func.1(%40)
    br bb3(%3, %122)
bb3(%4: ptr, %5: bool):
    store ptr %67, ptr %41
    %123 = const i64 8
    %124 = gep i8, ptr %41, %123
    %125 = const u64 6
    store u64 %125, ptr %124
    call @func.2(%39, %40, %41)
    br bb4(%4, %5)
bb4(%6: ptr, %7: bool):
    %126 = const bool true
    %127 = call @func.9(%6, %36)
    br bb5(%6, %127, %126, %7)
bb5(%8: ptr, %9: bool, %10: bool, %11: bool):
    condbr %9, bb6(%10), bb7(%8, %10, %11)
bb6(%12: bool):
    %128 = const bool false
    %129 = load i64, ptr %36
    store i64 %129, ptr %42
    %130 = const i64 8
    %131 = gep i8, ptr %36, %130
    %132 = const i64 8
    %133 = gep i8, ptr %42, %132
    %134 = load i64, ptr %131
    store i64 %134, ptr %133
    %135 = const i64 16
    %136 = gep i8, ptr %36, %135
    %137 = const i64 16
    %138 = gep i8, ptr %42, %137
    %139 = load i64, ptr %136
    store i64 %139, ptr %138
    %140 = const i64 24
    %141 = gep i8, ptr %36, %140
    %142 = const i64 24
    %143 = gep i8, ptr %42, %142
    %144 = load i64, ptr %141
    store i64 %144, ptr %143
    %145 = const i64 32
    %146 = gep i8, ptr %36, %145
    %147 = const i64 32
    %148 = gep i8, ptr %42, %147
    %149 = load i64, ptr %146
    store i64 %149, ptr %148
    store ptr %89, ptr %43
    %150 = const i64 8
    %151 = gep i8, ptr %43, %150
    %152 = const u64 3
    store u64 %152, ptr %151
    call @func.2(%0, %42, %43)
    br bb18(%12, %128)
bb7(%13: ptr, %14: bool, %15: bool):
    %153 = call @func.9(%13, %39)
    br bb8(%153, %14, %15)
bb8(%16: bool, %17: bool, %18: bool):
    condbr %16, bb9(%18), bb10(%17, %18)
bb9(%19: bool):
    %154 = const bool false
    %155 = load i64, ptr %39
    store i64 %155, ptr %44
    %156 = const i64 8
    %157 = gep i8, ptr %39, %156
    %158 = const i64 8
    %159 = gep i8, ptr %44, %158
    %160 = load i64, ptr %157
    store i64 %160, ptr %159
    %161 = const i64 16
    %162 = gep i8, ptr %39, %161
    %163 = const i64 16
    %164 = gep i8, ptr %44, %163
    %165 = load i64, ptr %162
    store i64 %165, ptr %164
    %166 = const i64 24
    %167 = gep i8, ptr %39, %166
    %168 = const i64 24
    %169 = gep i8, ptr %44, %168
    %170 = load i64, ptr %167
    store i64 %170, ptr %169
    %171 = const i64 32
    %172 = gep i8, ptr %39, %171
    %173 = const i64 32
    %174 = gep i8, ptr %44, %173
    %175 = load i64, ptr %172
    store i64 %175, ptr %174
    store ptr %89, ptr %45
    %176 = const i64 8
    %177 = gep i8, ptr %45, %176
    %178 = const u64 3
    store u64 %178, ptr %177
    call @func.2(%0, %44, %45)
    br bb19(%154, %19)
bb10(%20: bool, %21: bool):
    call @func.1(%47)
    br bb11(%20, %21)
bb11(%22: bool, %23: bool):
    store ptr %102, ptr %48
    %179 = const i64 8
    %180 = gep i8, ptr %48, %179
    %181 = const u64 4
    store u64 %181, ptr %180
    call @func.2(%46, %47, %48)
    br bb12(%22, %23)
bb12(%24: bool, %25: bool):
    store ptr %89, ptr %49
    %182 = const i64 8
    %183 = gep i8, ptr %49, %182
    %184 = const u64 3
    store u64 %184, ptr %183
    call @func.2(%0, %46, %49)
    br bb20(%24, %25)
bb13(%26: bool, %27: bool):
    condbr %26, bb16(%27), bb14(%27)
bb14(%28: bool):
    %185 = const bool false
    condbr %28, bb17, bb15
bb15:
    %186 = const bool false
    ret
bb16(%29: bool):
    br bb14(%29)
bb17:
    br bb15
bb18(%30: bool, %31: bool):
    br bb13(%30, %31)
bb19(%32: bool, %33: bool):
    br bb13(%32, %33)
bb20(%34: bool, %35: bool):
    br bb13(%34, %35)
}

fn @parse_u64_ascii(functy.4) {
bb0(%0: ptr, %1: ptr):
    %39 = alloca (i64, i64), align 8
    %40 = alloca (i8, i8), align 1
    %41 = alloca (i64, i64), align 8
    %42 = alloca (i64, i64), align 8
    %43 = alloca (i64, i64), align 8
    %44 = alloca (i64, i64), align 8
    %45 = load i64, ptr %1
    store i64 %45, ptr %39
    %46 = const i64 8
    %47 = gep i8, ptr %1, %46
    %48 = const i64 8
    %49 = gep i8, ptr %39, %48
    %50 = load i64, ptr %47
    store i64 %50, ptr %49
    br bb1
bb1:
    %51 = const u64 0
    %52 = const i64 8
    %53 = gep i8, ptr %39, %52
    %54 = load u64, ptr %53
    %55 = const u64 0
    %56 = icmp ugt u64 %54, %55
    condbr %56, bb2(%51), bb5(%51)
bb2(%2: u64):
    %57 = const u64 0
    %58 = const i64 8
    %59 = gep i8, ptr %39, %58
    %60 = load u64, ptr %59
    %61 = icmp ult u64 %57, %60
    condbr %61, bb3(%2, %57), bb24
bb3(%3: u64, %4: u64):
    %62 = load ptr, ptr %39
    %63 = gep u8, ptr %62, %4
    %64 = load u8, ptr %63
    %65 = const u8 43
    %66 = icmp eq u8 %64, %65
    condbr %66, bb4, bb5(%3)
bb4:
    %67 = const u64 1
    br bb5(%67)
bb5(%5: u64):
    %68 = const i64 8
    %69 = gep i8, ptr %39, %68
    %70 = load u64, ptr %69
    %71 = icmp uge u64 %5, %70
    condbr %71, bb6, bb7(%5)
bb6:
    %72 = const bool false
    store bool %72, ptr %0
    %73 = const u64 0
    %74 = const i64 8
    %75 = gep i8, ptr %0, %74
    store u64 %73, ptr %75
    br bb23
bb7(%6: u64):
    %76 = const u64 0
    br bb8(%6, %76)
bb8(%7: u64, %8: u64):
    %77 = const i64 8
    %78 = gep i8, ptr %39, %77
    %79 = load u64, ptr %78
    %80 = icmp ult u64 %7, %79
    condbr %80, bb9(%7, %8), bb22(%8)
bb9(%9: u64, %10: u64):
    %81 = const i64 8
    %82 = gep i8, ptr %39, %81
    %83 = load u64, ptr %82
    %84 = icmp ult u64 %9, %83
    condbr %84, bb10(%9, %10, %9), bb24
bb10(%11: u64, %12: u64, %13: u64):
    %85 = load ptr, ptr %39
    %86 = gep u8, ptr %85, %13
    %87 = load u8, ptr %86
    %88 = const u8 48
    %89 = icmp ult u8 %87, %88
    condbr %89, bb12, bb11(%11, %12, %87)
bb11(%14: u64, %15: u64, %16: u8):
    %90 = const u8 57
    %91 = icmp ugt u8 %16, %90
    condbr %91, bb12, bb13(%14, %15, %16)
bb12:
    %92 = const bool false
    store bool %92, ptr %0
    %93 = const u64 0
    %94 = const i64 8
    %95 = gep i8, ptr %0, %94
    store u64 %93, ptr %95
    br bb23
bb13(%17: u64, %18: u64, %19: u8):
    %96 = const u8 48
    %97, %98 = sub.overflow u8 %19, %96
    store u8 %97, ptr %40
    %99 = const i64 1
    %100 = gep i8, ptr %40, %99
    store bool %98, ptr %100
    %101 = const i64 1
    %102 = gep i8, ptr %40, %101
    %103 = load bool, ptr %102
    %104 = const bool false
    %105 = icmp eq bool %103, %104
    condbr %105, bb14(%17, %18), bb24
bb14(%20: u64, %21: u64):
    %106 = load u8, ptr %40
    %107 = zext u8 %106 to u64
    %108 = const u64 18446744073709551615
    %109, %110 = sub.overflow u64 %108, %107
    store u64 %109, ptr %41
    %111 = const i64 8
    %112 = gep i8, ptr %41, %111
    store bool %110, ptr %112
    %113 = const i64 8
    %114 = gep i8, ptr %41, %113
    %115 = load bool, ptr %114
    %116 = const bool false
    %117 = icmp eq bool %115, %116
    condbr %117, bb15(%20, %21, %107, %21), bb24
bb15(%22: u64, %23: u64, %24: u64, %25: u64):
    %118 = load u64, ptr %41
    %119 = const u64 10
    %120 = const u64 0
    %121 = icmp eq u64 %119, %120
    %122 = const bool false
    %123 = icmp eq bool %121, %122
    condbr %123, bb16(%22, %23, %24, %25, %118), bb24
bb16(%26: u64, %27: u64, %28: u64, %29: u64, %30: u64):
    %124 = const u64 10
    %125 = udiv u64 %30, %124
    %126 = icmp ugt u64 %29, %125
    condbr %126, bb17, bb18(%26, %27, %28)
bb17:
    %127 = const bool false
    store bool %127, ptr %0
    %128 = const u64 0
    %129 = const i64 8
    %130 = gep i8, ptr %0, %129
    store u64 %128, ptr %130
    br bb23
bb18(%31: u64, %32: u64, %33: u64):
    %131 = const u64 10
    %132, %133 = mul.overflow u64 %32, %131
    store u64 %132, ptr %42
    %134 = const i64 8
    %135 = gep i8, ptr %42, %134
    store bool %133, ptr %135
    %136 = const i64 8
    %137 = gep i8, ptr %42, %136
    %138 = load bool, ptr %137
    %139 = const bool false
    %140 = icmp eq bool %138, %139
    condbr %140, bb19(%31, %33), bb24
bb19(%34: u64, %35: u64):
    %141 = load u64, ptr %42
    %142, %143 = add.overflow u64 %141, %35
    store u64 %142, ptr %43
    %144 = const i64 8
    %145 = gep i8, ptr %43, %144
    store bool %143, ptr %145
    %146 = const i64 8
    %147 = gep i8, ptr %43, %146
    %148 = load bool, ptr %147
    %149 = const bool false
    %150 = icmp eq bool %148, %149
    condbr %150, bb20(%34), bb24
bb20(%36: u64):
    %151 = load u64, ptr %43
    %152 = const u64 1
    %153, %154 = add.overflow u64 %36, %152
    store u64 %153, ptr %44
    %155 = const i64 8
    %156 = gep i8, ptr %44, %155
    store bool %154, ptr %156
    %157 = const i64 8
    %158 = gep i8, ptr %44, %157
    %159 = load bool, ptr %158
    %160 = const bool false
    %161 = icmp eq bool %159, %160
    condbr %161, bb21(%151), bb24
bb21(%37: u64):
    %162 = load u64, ptr %44
    br bb8(%162, %37)
bb22(%38: u64):
    %163 = const bool true
    store bool %163, ptr %0
    %164 = const i64 8
    %165 = gep i8, ptr %0, %164
    store u64 %38, ptr %165
    br bb23
bb23:
    ret
bb24:
    unreachable
}

fn @name_num_part(functy.5) {
bb0(%0: ptr, %1: ptr, %2: u64):
    %7 = alloca (i64, i64, i64, i64), align 8
    %8 = alloca i64, align 8
    %9 = alloca (i64, i64, i64, i64, i64), align 8
    %10 = const bool false
    %11 = const bool true
    %12 = const i64 32
    %13 = gep i8, ptr %1, %12
    %14 = load u64, ptr %13
    %15 = call @func.11(%14, %2)
    br bb1(%2, %15)
bb1(%3: u64, %4: u64):
    %16 = const bool false
    %17 = load i64, ptr %1
    store i64 %17, ptr %9
    %18 = const i64 8
    %19 = gep i8, ptr %1, %18
    %20 = const i64 8
    %21 = gep i8, ptr %9, %20
    %22 = load i64, ptr %19
    store i64 %22, ptr %21
    %23 = const i64 16
    %24 = gep i8, ptr %1, %23
    %25 = const i64 16
    %26 = gep i8, ptr %9, %25
    %27 = load i64, ptr %24
    store i64 %27, ptr %26
    %28 = const i64 24
    %29 = gep i8, ptr %1, %28
    %30 = const i64 24
    %31 = gep i8, ptr %9, %30
    %32 = load i64, ptr %29
    store i64 %32, ptr %31
    %33 = const i64 32
    %34 = gep i8, ptr %1, %33
    %35 = const i64 32
    %36 = gep i8, ptr %9, %35
    %37 = load i64, ptr %34
    store i64 %37, ptr %36
    %38 = const i64 56
    %39 = heap_alloc rust_heap i8, %38, align 8
    %40 = const u64 1
    store u64 %40, ptr %39
    %41 = const i64 8
    %42 = gep i8, ptr %39, %41
    %43 = const u64 1
    store u64 %43, ptr %42
    %44 = const i64 16
    %45 = gep i8, ptr %39, %44
    %46 = load i64, ptr %9
    store i64 %46, ptr %45
    %47 = const i64 8
    %48 = gep i8, ptr %9, %47
    %49 = const i64 8
    %50 = gep i8, ptr %45, %49
    %51 = load i64, ptr %48
    store i64 %51, ptr %50
    %52 = const i64 16
    %53 = gep i8, ptr %9, %52
    %54 = const i64 16
    %55 = gep i8, ptr %45, %54
    %56 = load i64, ptr %53
    store i64 %56, ptr %55
    %57 = const i64 24
    %58 = gep i8, ptr %9, %57
    %59 = const i64 24
    %60 = gep i8, ptr %45, %59
    %61 = load i64, ptr %58
    store i64 %61, ptr %60
    %62 = const i64 32
    %63 = gep i8, ptr %9, %62
    %64 = const i64 32
    %65 = gep i8, ptr %45, %64
    %66 = load i64, ptr %63
    store i64 %66, ptr %65
    store ptr %39, ptr %8
    br bb2(%3, %4)
bb2(%5: u64, %6: u64):
    %67 = load ptr, ptr %8
    %68 = const i64 16
    %69 = gep i8, ptr %7, %68
    store ptr %67, ptr %69
    %70 = const i64 8
    %71 = gep i8, ptr %7, %70
    store u64 %5, ptr %71
    %72 = const i64 2
    store i64 %72, ptr %7
    %73 = load i64, ptr %7
    store i64 %73, ptr %0
    %74 = const i64 8
    %75 = gep i8, ptr %7, %74
    %76 = const i64 8
    %77 = gep i8, ptr %0, %76
    %78 = load i64, ptr %75
    store i64 %78, ptr %77
    %79 = const i64 16
    %80 = gep i8, ptr %7, %79
    %81 = const i64 16
    %82 = gep i8, ptr %0, %81
    %83 = load i64, ptr %80
    store i64 %83, ptr %82
    %84 = const i64 24
    %85 = gep i8, ptr %7, %84
    %86 = const i64 24
    %87 = gep i8, ptr %0, %86
    %88 = load i64, ptr %85
    store i64 %88, ptr %87
    %89 = const i64 32
    %90 = gep i8, ptr %0, %89
    store u64 %6, ptr %90
    ret
}

fn @_RNvXs17_NtCskTzINo8ZBH9_5alloc4syncINtB6_3ArceEINtNtCs2EYQwhfuABO_4core7convert4FromReE4fromCs77po20IQdNn_16str_stage2_slice(functy.6) {
}

fn @name_str_part(functy.7) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %7 = alloca (i64, i64), align 8
    %8 = alloca (i64, i64, i64, i64), align 8
    %9 = alloca i64, align 8
    %10 = alloca (i64, i64, i64, i64, i64), align 8
    %11 = alloca (i64, i64), align 8
    %12 = const bool false
    %13 = const bool true
    %14 = load i64, ptr %2
    store i64 %14, ptr %7
    %15 = const i64 8
    %16 = gep i8, ptr %2, %15
    %17 = const i64 8
    %18 = gep i8, ptr %7, %17
    %19 = load i64, ptr %16
    store i64 %19, ptr %18
    br bb1
bb1:
    %20 = const u64 11
    %21 = call @func.14(%7, %20)
    br bb2(%21)
bb2(%3: u64):
    %22 = const i64 32
    %23 = gep i8, ptr %1, %22
    %24 = load u64, ptr %23
    %25 = call @func.11(%24, %3)
    br bb3(%25)
bb3(%4: u64):
    %26 = const bool false
    %27 = load i64, ptr %1
    store i64 %27, ptr %10
    %28 = const i64 8
    %29 = gep i8, ptr %1, %28
    %30 = const i64 8
    %31 = gep i8, ptr %10, %30
    %32 = load i64, ptr %29
    store i64 %32, ptr %31
    %33 = const i64 16
    %34 = gep i8, ptr %1, %33
    %35 = const i64 16
    %36 = gep i8, ptr %10, %35
    %37 = load i64, ptr %34
    store i64 %37, ptr %36
    %38 = const i64 24
    %39 = gep i8, ptr %1, %38
    %40 = const i64 24
    %41 = gep i8, ptr %10, %40
    %42 = load i64, ptr %39
    store i64 %42, ptr %41
    %43 = const i64 32
    %44 = gep i8, ptr %1, %43
    %45 = const i64 32
    %46 = gep i8, ptr %10, %45
    %47 = load i64, ptr %44
    store i64 %47, ptr %46
    %48 = const i64 56
    %49 = heap_alloc rust_heap i8, %48, align 8
    %50 = const u64 1
    store u64 %50, ptr %49
    %51 = const i64 8
    %52 = gep i8, ptr %49, %51
    %53 = const u64 1
    store u64 %53, ptr %52
    %54 = const i64 16
    %55 = gep i8, ptr %49, %54
    %56 = load i64, ptr %10
    store i64 %56, ptr %55
    %57 = const i64 8
    %58 = gep i8, ptr %10, %57
    %59 = const i64 8
    %60 = gep i8, ptr %55, %59
    %61 = load i64, ptr %58
    store i64 %61, ptr %60
    %62 = const i64 16
    %63 = gep i8, ptr %10, %62
    %64 = const i64 16
    %65 = gep i8, ptr %55, %64
    %66 = load i64, ptr %63
    store i64 %66, ptr %65
    %67 = const i64 24
    %68 = gep i8, ptr %10, %67
    %69 = const i64 24
    %70 = gep i8, ptr %55, %69
    %71 = load i64, ptr %68
    store i64 %71, ptr %70
    %72 = const i64 32
    %73 = gep i8, ptr %10, %72
    %74 = const i64 32
    %75 = gep i8, ptr %55, %74
    %76 = load i64, ptr %73
    store i64 %76, ptr %75
    store ptr %49, ptr %9
    br bb4(%4)
bb4(%5: u64):
    call @func.6(%11, %2)
    br bb5(%5)
bb5(%6: u64):
    %77 = load ptr, ptr %9
    %78 = const i64 8
    %79 = gep i8, ptr %8, %78
    store ptr %77, ptr %79
    %80 = const i64 16
    %81 = gep i8, ptr %8, %80
    %82 = load i64, ptr %11
    store i64 %82, ptr %81
    %83 = const i64 8
    %84 = gep i8, ptr %11, %83
    %85 = const i64 8
    %86 = gep i8, ptr %81, %85
    %87 = load i64, ptr %84
    store i64 %87, ptr %86
    %88 = const i64 1
    store i64 %88, ptr %8
    %89 = load i64, ptr %8
    store i64 %89, ptr %0
    %90 = const i64 8
    %91 = gep i8, ptr %8, %90
    %92 = const i64 8
    %93 = gep i8, ptr %0, %92
    %94 = load i64, ptr %91
    store i64 %94, ptr %93
    %95 = const i64 16
    %96 = gep i8, ptr %8, %95
    %97 = const i64 16
    %98 = gep i8, ptr %0, %97
    %99 = load i64, ptr %96
    store i64 %99, ptr %98
    %100 = const i64 24
    %101 = gep i8, ptr %8, %100
    %102 = const i64 24
    %103 = gep i8, ptr %0, %102
    %104 = load i64, ptr %101
    store i64 %104, ptr %103
    %105 = const i64 32
    %106 = gep i8, ptr %0, %105
    store u64 %6, ptr %106
    ret
}

fn @_RNvXsw_NtCskTzINo8ZBH9_5alloc4syncINtB5_3ArceENtNtNtCs2EYQwhfuABO_4core3ops5deref5Deref5derefCs77po20IQdNn_16str_stage2_slice(functy.8) {
}

fn @name_eq(functy.9) {
bb0(%0: ptr, %1: ptr):
    %23 = alloca i64, align 8
    %24 = alloca i64, align 8
    %25 = alloca (i64, i64), align 8
    %26 = alloca (i64, i64), align 8
    %27 = alloca (i64, i64), align 8
    %28 = alloca i64, align 8
    %29 = alloca i64, align 8
    %30 = alloca i64, align 8
    %31 = alloca i64, align 8
    %32 = alloca i64, align 8
    %33 = alloca i64, align 8
    %34 = alloca i64, align 8
    %35 = alloca i64, align 8
    %36 = const i64 32
    %37 = gep i8, ptr %0, %36
    %38 = load u64, ptr %37
    %39 = const i64 32
    %40 = gep i8, ptr %1, %39
    %41 = load u64, ptr %40
    %42 = icmp ne u64 %38, %41
    condbr %42, bb1, bb2(%0, %1)
bb1:
    %43 = const bool false
    br bb22(%43)
bb2(%2: ptr, %3: ptr):
    store ptr %2, ptr %23
    store ptr %3, ptr %24
    br bb3
bb3:
    %44 = load ptr, ptr %23
    %45 = load ptr, ptr %24
    store ptr %44, ptr %25
    %46 = const i64 8
    %47 = gep i8, ptr %25, %46
    store ptr %45, ptr %47
    %48 = load ptr, ptr %25
    %49 = load i64, ptr %48
    switch %49 [ 0: bb5 1: bb6 2: bb7 default: bb23 ]
bb4:
    %50 = const bool false
    br bb22(%50)
bb5:
    %51 = const i64 8
    %52 = gep i8, ptr %25, %51
    %53 = load ptr, ptr %52
    %54 = load i64, ptr %53
    switch %54 [ 0: bb10 default: bb4 ]
bb6:
    %55 = const i64 8
    %56 = gep i8, ptr %25, %55
    %57 = load ptr, ptr %56
    %58 = load i64, ptr %57
    switch %58 [ 1: bb9 default: bb4 ]
bb7:
    %59 = const i64 8
    %60 = gep i8, ptr %25, %59
    %61 = load ptr, ptr %60
    %62 = load i64, ptr %61
    switch %62 [ 2: bb8 default: bb4 ]
bb8:
    %63 = load ptr, ptr %25
    store ptr %63, ptr %28
    %64 = load ptr, ptr %28
    %65 = const i64 16
    %66 = gep i8, ptr %64, %65
    %67 = load ptr, ptr %25
    store ptr %67, ptr %29
    %68 = load ptr, ptr %29
    %69 = const i64 8
    %70 = gep i8, ptr %68, %69
    %71 = const i64 8
    %72 = gep i8, ptr %25, %71
    %73 = load ptr, ptr %72
    store ptr %73, ptr %30
    %74 = load ptr, ptr %30
    %75 = const i64 16
    %76 = gep i8, ptr %74, %75
    %77 = const i64 8
    %78 = gep i8, ptr %25, %77
    %79 = load ptr, ptr %78
    store ptr %79, ptr %31
    %80 = load ptr, ptr %31
    %81 = const i64 8
    %82 = gep i8, ptr %80, %81
    %83 = load u64, ptr %70
    %84 = load u64, ptr %82
    %85 = icmp ne u64 %83, %84
    condbr %85, bb18, bb19(%66, %76)
bb9:
    %86 = load ptr, ptr %25
    store ptr %86, ptr %32
    %87 = load ptr, ptr %32
    %88 = const i64 8
    %89 = gep i8, ptr %87, %88
    %90 = load ptr, ptr %25
    store ptr %90, ptr %33
    %91 = load ptr, ptr %33
    %92 = const i64 16
    %93 = gep i8, ptr %91, %92
    %94 = const i64 8
    %95 = gep i8, ptr %25, %94
    %96 = load ptr, ptr %95
    store ptr %96, ptr %34
    %97 = load ptr, ptr %34
    %98 = const i64 8
    %99 = gep i8, ptr %97, %98
    %100 = const i64 8
    %101 = gep i8, ptr %25, %100
    %102 = load ptr, ptr %101
    store ptr %102, ptr %35
    %103 = load ptr, ptr %35
    %104 = const i64 16
    %105 = gep i8, ptr %103, %104
    call @func.8(%26, %93)
    br bb11(%89, %99, %105)
bb10:
    %106 = const bool true
    br bb22(%106)
bb11(%4: ptr, %5: ptr, %6: ptr):
    call @func.8(%27, %6)
    br bb12(%4, %5)
bb12(%7: ptr, %8: ptr):
    %107 = call @func.15(%26, %27)
    br bb13(%7, %8, %107)
bb13(%9: ptr, %10: ptr, %11: bool):
    condbr %11, bb14(%9, %10), bb15
bb14(%12: ptr, %13: ptr):
    %108 = load ptr, ptr %12
    %109 = const i64 16
    %110 = gep i8, ptr %108, %109
    br bb16(%13, %110)
bb15:
    %111 = const bool false
    br bb22(%111)
bb16(%14: ptr, %15: ptr):
    store ptr %15, ptr %23
    %112 = load ptr, ptr %14
    %113 = const i64 16
    %114 = gep i8, ptr %112, %113
    br bb17(%114)
bb17(%16: ptr):
    store ptr %16, ptr %24
    br bb3
bb18:
    %115 = const bool false
    br bb22(%115)
bb19(%17: ptr, %18: ptr):
    %116 = load ptr, ptr %17
    %117 = const i64 16
    %118 = gep i8, ptr %116, %117
    br bb20(%18, %118)
bb20(%19: ptr, %20: ptr):
    store ptr %20, ptr %23
    %119 = load ptr, ptr %19
    %120 = const i64 16
    %121 = gep i8, ptr %119, %120
    br bb21(%121)
bb21(%21: ptr):
    store ptr %21, ptr %24
    br bb3
bb22(%22: bool):
    ret %22
bb23:
    unreachable
}

fn @_RNvMs7_NtCs2EYQwhfuABO_4core3numy12wrapping_mul(functy.10) {
}

fn @mix_hash(functy.11) {
bb0(%0: u64, %1: u64):
    %8 = const u64 14313749767032793493
    %9 = call @func.10(%1, %8)
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
    %21 = call @func.10(%19, %20)
    br bb3(%21)
bb3(%7: u64):
    ret %7
bb4:
    unreachable
}

fn @_RNvMs7_NtCs2EYQwhfuABO_4core3numy12wrapping_mul(functy.12) {
}

fn @_RNvMs9_NtCs2EYQwhfuABO_4core3numj12wrapping_mul(functy.13) {
}

fn @murmur_hash_64a_idx(functy.14) {
bb0(%0: ptr, %1: u64):
    %151 = alloca (i64, i64), align 8
    %152 = alloca (i64, i64), align 8
    %153 = alloca (i32, i32), align 4
    %154 = alloca (i64, i64), align 8
    %155 = alloca (i64, i64), align 8
    %156 = alloca (i64, i64), align 8
    %157 = alloca (i64, i64), align 8
    %158 = alloca (i64, i64), align 8
    %159 = const i64 8
    %160 = gep i8, ptr %0, %159
    %161 = load u64, ptr %160
    %162 = const u64 14313749767032793493
    %163 = call @func.12(%161, %162)
    br bb1(%1, %161, %163)
bb1(%2: u64, %3: u64, %4: u64):
    %164 = xor u64 %2, %4
    %165 = const u64 8
    %166 = const u64 0
    %167 = icmp eq u64 %165, %166
    %168 = const bool false
    %169 = icmp eq bool %167, %168
    condbr %169, bb2(%3, %164), bb35
bb2(%5: u64, %6: u64):
    %170 = const u64 8
    %171 = udiv u64 %5, %170
    %172 = const u64 0
    br bb3(%5, %6, %171, %172)
bb3(%7: u64, %8: u64, %9: u64, %10: u64):
    %173 = icmp ult u64 %10, %9
    condbr %173, bb4(%7, %8, %9, %10), bb19(%7, %8, %9)
bb4(%11: u64, %12: u64, %13: u64, %14: u64):
    %174 = const u64 8
    %175, %176 = mul.overflow u64 %14, %174
    store u64 %175, ptr %151
    %177 = const i64 8
    %178 = gep i8, ptr %151, %177
    store bool %176, ptr %178
    %179 = const i64 8
    %180 = gep i8, ptr %151, %179
    %181 = load bool, ptr %180
    %182 = const bool false
    %183 = icmp eq bool %181, %182
    condbr %183, bb5(%11, %12, %13, %14), bb35
bb5(%15: u64, %16: u64, %17: u64, %18: u64):
    %184 = load u64, ptr %151
    %185 = const u64 0
    %186 = const u64 0
    br bb6(%15, %16, %17, %18, %184, %185, %186)
bb6(%19: u64, %20: u64, %21: u64, %22: u64, %23: u64, %24: u64, %25: u64):
    %187 = const u64 8
    %188 = icmp ult u64 %25, %187
    condbr %188, bb7(%19, %20, %21, %22, %23, %24, %25), bb13(%19, %20, %21, %22, %24)
bb7(%26: u64, %27: u64, %28: u64, %29: u64, %30: u64, %31: u64, %32: u64):
    %189, %190 = add.overflow u64 %30, %32
    store u64 %189, ptr %152
    %191 = const i64 8
    %192 = gep i8, ptr %152, %191
    store bool %190, ptr %192
    %193 = const i64 8
    %194 = gep i8, ptr %152, %193
    %195 = load bool, ptr %194
    %196 = const bool false
    %197 = icmp eq bool %195, %196
    condbr %197, bb8(%26, %27, %28, %29, %30, %31, %32), bb35
bb8(%33: u64, %34: u64, %35: u64, %36: u64, %37: u64, %38: u64, %39: u64):
    %198 = load u64, ptr %152
    %199 = const i64 8
    %200 = gep i8, ptr %0, %199
    %201 = load u64, ptr %200
    %202 = icmp ult u64 %198, %201
    condbr %202, bb9(%33, %34, %35, %36, %37, %38, %39, %198), bb35
bb9(%40: u64, %41: u64, %42: u64, %43: u64, %44: u64, %45: u64, %46: u64, %47: u64):
    %203 = load ptr, ptr %0
    %204 = gep u8, ptr %203, %47
    %205 = load u8, ptr %204
    %206 = zext u8 %205 to u64
    %207 = trunc u64 %46 to u32
    %208 = const u32 8
    %209, %210 = mul.overflow u32 %208, %207
    store u32 %209, ptr %153
    %211 = const i64 4
    %212 = gep i8, ptr %153, %211
    store bool %210, ptr %212
    %213 = const i64 4
    %214 = gep i8, ptr %153, %213
    %215 = load bool, ptr %214
    %216 = const bool false
    %217 = icmp eq bool %215, %216
    condbr %217, bb10(%40, %41, %42, %43, %44, %45, %46, %206), bb35
bb10(%48: u64, %49: u64, %50: u64, %51: u64, %52: u64, %53: u64, %54: u64, %55: u64):
    %218 = load u32, ptr %153
    %219 = const u32 64
    %220 = icmp ult u32 %218, %219
    condbr %220, bb11(%48, %49, %50, %51, %52, %53, %54, %55, %218), bb35
bb11(%56: u64, %57: u64, %58: u64, %59: u64, %60: u64, %61: u64, %62: u64, %63: u64, %64: u32):
    %221 = zext u32 %64 to u64
    %222 = shl u64 %63, %221
    %223 = or u64 %61, %222
    %224 = const u64 1
    %225, %226 = add.overflow u64 %62, %224
    store u64 %225, ptr %154
    %227 = const i64 8
    %228 = gep i8, ptr %154, %227
    store bool %226, ptr %228
    %229 = const i64 8
    %230 = gep i8, ptr %154, %229
    %231 = load bool, ptr %230
    %232 = const bool false
    %233 = icmp eq bool %231, %232
    condbr %233, bb12(%56, %57, %58, %59, %60, %223), bb35
bb12(%65: u64, %66: u64, %67: u64, %68: u64, %69: u64, %70: u64):
    %234 = load u64, ptr %154
    br bb6(%65, %66, %67, %68, %69, %70, %234)
bb13(%71: u64, %72: u64, %73: u64, %74: u64, %75: u64):
    %235 = const u64 14313749767032793493
    %236 = call @func.12(%75, %235)
    br bb14(%71, %72, %73, %74, %236)
bb14(%76: u64, %77: u64, %78: u64, %79: u64, %80: u64):
    %237 = const u32 47
    %238 = const u32 63
    %239 = and u32 %237, %238
    %240 = const u32 64
    %241 = icmp ult u32 %239, %240
    condbr %241, bb15(%76, %77, %78, %79, %80, %80, %239), bb35
bb15(%81: u64, %82: u64, %83: u64, %84: u64, %85: u64, %86: u64, %87: u32):
    %242 = zext u32 %87 to u64
    %243 = lshr u64 %86, %242
    %244 = xor u64 %85, %243
    %245 = const u64 14313749767032793493
    %246 = call @func.12(%244, %245)
    br bb16(%81, %82, %83, %84, %246)
bb16(%88: u64, %89: u64, %90: u64, %91: u64, %92: u64):
    %247 = xor u64 %89, %92
    %248 = const u64 14313749767032793493
    %249 = call @func.12(%247, %248)
    br bb17(%88, %90, %91, %249)
bb17(%93: u64, %94: u64, %95: u64, %96: u64):
    %250 = const u64 1
    %251, %252 = add.overflow u64 %95, %250
    store u64 %251, ptr %155
    %253 = const i64 8
    %254 = gep i8, ptr %155, %253
    store bool %252, ptr %254
    %255 = const i64 8
    %256 = gep i8, ptr %155, %255
    %257 = load bool, ptr %256
    %258 = const bool false
    %259 = icmp eq bool %257, %258
    condbr %259, bb18(%93, %96, %94), bb35
bb18(%97: u64, %98: u64, %99: u64):
    %260 = load u64, ptr %155
    br bb3(%97, %98, %99, %260)
bb19(%100: u64, %101: u64, %102: u64):
    %261 = const u64 8
    %262, %263 = mul.overflow u64 %102, %261
    store u64 %262, ptr %156
    %264 = const i64 8
    %265 = gep i8, ptr %156, %264
    store bool %263, ptr %265
    %266 = const i64 8
    %267 = gep i8, ptr %156, %266
    %268 = load bool, ptr %267
    %269 = const bool false
    %270 = icmp eq bool %268, %269
    condbr %270, bb20(%100, %101), bb35
bb20(%103: u64, %104: u64):
    %271 = load u64, ptr %156
    br bb21(%103, %104, %271, %271)
bb21(%105: u64, %106: u64, %107: u64, %108: u64):
    %272 = icmp ult u64 %108, %105
    condbr %272, bb22(%105, %106, %107, %108), bb28(%105, %106, %107)
bb22(%109: u64, %110: u64, %111: u64, %112: u64):
    %273 = const i64 8
    %274 = gep i8, ptr %0, %273
    %275 = load u64, ptr %274
    %276 = icmp ult u64 %112, %275
    condbr %276, bb23(%109, %110, %111, %112, %112), bb35
bb23(%113: u64, %114: u64, %115: u64, %116: u64, %117: u64):
    %277 = load ptr, ptr %0
    %278 = gep u8, ptr %277, %117
    %279 = load u8, ptr %278
    %280 = zext u8 %279 to u64
    %281, %282 = sub.overflow u64 %116, %115
    store u64 %281, ptr %157
    %283 = const i64 8
    %284 = gep i8, ptr %157, %283
    store bool %282, ptr %284
    %285 = const i64 8
    %286 = gep i8, ptr %157, %285
    %287 = load bool, ptr %286
    %288 = const bool false
    %289 = icmp eq bool %287, %288
    condbr %289, bb24(%113, %114, %115, %116, %280), bb35
bb24(%118: u64, %119: u64, %120: u64, %121: u64, %122: u64):
    %290 = load u64, ptr %157
    %291 = const u64 8
    %292 = call @func.13(%290, %291)
    br bb25(%118, %119, %120, %121, %122, %292)
bb25(%123: u64, %124: u64, %125: u64, %126: u64, %127: u64, %128: u64):
    %293 = const u64 63
    %294 = and u64 %128, %293
    %295 = const u64 64
    %296 = icmp ult u64 %294, %295
    condbr %296, bb26(%123, %124, %125, %126, %127, %294), bb35
bb26(%129: u64, %130: u64, %131: u64, %132: u64, %133: u64, %134: u64):
    %297 = shl u64 %133, %134
    %298 = xor u64 %130, %297
    %299 = const u64 1
    %300, %301 = add.overflow u64 %132, %299
    store u64 %300, ptr %158
    %302 = const i64 8
    %303 = gep i8, ptr %158, %302
    store bool %301, ptr %303
    %304 = const i64 8
    %305 = gep i8, ptr %158, %304
    %306 = load bool, ptr %305
    %307 = const bool false
    %308 = icmp eq bool %306, %307
    condbr %308, bb27(%129, %298, %131), bb35
bb27(%135: u64, %136: u64, %137: u64):
    %309 = load u64, ptr %158
    br bb21(%135, %136, %137, %309)
bb28(%138: u64, %139: u64, %140: u64):
    %310 = icmp ult u64 %140, %138
    condbr %310, bb29(%139), bb31(%139)
bb29(%141: u64):
    %311 = const u64 14313749767032793493
    %312 = call @func.12(%141, %311)
    br bb30(%312)
bb30(%142: u64):
    br bb31(%142)
bb31(%143: u64):
    %313 = const u32 47
    %314 = const u32 63
    %315 = and u32 %313, %314
    %316 = const u32 64
    %317 = icmp ult u32 %315, %316
    condbr %317, bb32(%143, %143, %315), bb35
bb32(%144: u64, %145: u64, %146: u32):
    %318 = zext u32 %146 to u64
    %319 = lshr u64 %145, %318
    %320 = xor u64 %144, %319
    %321 = const u64 14313749767032793493
    %322 = call @func.12(%320, %321)
    br bb33(%322)
bb33(%147: u64):
    %323 = const u32 47
    %324 = const u32 63
    %325 = and u32 %323, %324
    %326 = const u32 64
    %327 = icmp ult u32 %325, %326
    condbr %327, bb34(%147, %147, %325), bb35
bb34(%148: u64, %149: u64, %150: u32):
    %328 = zext u32 %150 to u64
    %329 = lshr u64 %149, %328
    %330 = xor u64 %148, %329
    ret %330
bb35:
    unreachable
}

fn @str_bytes_eq(functy.15) {
bb0(%0: ptr, %1: ptr):
    %11 = alloca (i64, i64), align 8
    %12 = alloca (i64, i64), align 8
    %13 = alloca (i64, i64), align 8
    %14 = load i64, ptr %0
    store i64 %14, ptr %11
    %15 = const i64 8
    %16 = gep i8, ptr %0, %15
    %17 = const i64 8
    %18 = gep i8, ptr %11, %17
    %19 = load i64, ptr %16
    store i64 %19, ptr %18
    br bb1
bb1:
    %20 = load i64, ptr %1
    store i64 %20, ptr %12
    %21 = const i64 8
    %22 = gep i8, ptr %1, %21
    %23 = const i64 8
    %24 = gep i8, ptr %12, %23
    %25 = load i64, ptr %22
    store i64 %25, ptr %24
    br bb2
bb2:
    %26 = const i64 8
    %27 = gep i8, ptr %11, %26
    %28 = load u64, ptr %27
    %29 = const i64 8
    %30 = gep i8, ptr %12, %29
    %31 = load u64, ptr %30
    %32 = icmp ne u64 %28, %31
    condbr %32, bb3, bb4
bb3:
    %33 = const bool false
    br bb13(%33)
bb4:
    %34 = const u64 0
    br bb5(%34)
bb5(%2: u64):
    %35 = const i64 8
    %36 = gep i8, ptr %11, %35
    %37 = load u64, ptr %36
    %38 = icmp ult u64 %2, %37
    condbr %38, bb6(%2), bb12
bb6(%3: u64):
    %39 = const i64 8
    %40 = gep i8, ptr %11, %39
    %41 = load u64, ptr %40
    %42 = icmp ult u64 %3, %41
    condbr %42, bb7(%3, %3), bb14
bb7(%4: u64, %5: u64):
    %43 = load ptr, ptr %11
    %44 = gep u8, ptr %43, %5
    %45 = load u8, ptr %44
    %46 = const i64 8
    %47 = gep i8, ptr %12, %46
    %48 = load u64, ptr %47
    %49 = icmp ult u64 %4, %48
    condbr %49, bb8(%4, %45, %4), bb14
bb8(%6: u64, %7: u8, %8: u64):
    %50 = load ptr, ptr %12
    %51 = gep u8, ptr %50, %8
    %52 = load u8, ptr %51
    %53 = icmp ne u8 %7, %52
    condbr %53, bb9, bb10(%6)
bb9:
    %54 = const bool false
    br bb13(%54)
bb10(%9: u64):
    %55 = const u64 1
    %56, %57 = add.overflow u64 %9, %55
    store u64 %56, ptr %13
    %58 = const i64 8
    %59 = gep i8, ptr %13, %58
    store bool %57, ptr %59
    %60 = const i64 8
    %61 = gep i8, ptr %13, %60
    %62 = load bool, ptr %61
    %63 = const bool false
    %64 = icmp eq bool %62, %63
    condbr %64, bb11, bb14
bb11:
    %65 = load u64, ptr %13
    br bb5(%65)
bb12:
    %66 = const bool true
    br bb13(%66)
bb13(%10: bool):
    ret %10
bb14:
    unreachable
}"#;

// ═══════════════════════════════════════════════════════════════════════════
// Tests — byte access (priority 1) + iterator walks (priority 2)
// ═══════════════════════════════════════════════════════════════════════════

fn run_bytes_root_sweep(mode: u64, idxs: &[u64]) -> Vec<u64> {
    let idxs: Vec<u64> = idxs.to_vec();
    run_with_watchdog("bytes_root JIT sweep", move || {
        let buffer = jit_module(BYTES_TRUST_IR, "str_stage2_bytes_root", &stage2_externs());
        let f: extern "C" fn(u64, u64) -> u64 =
            unsafe { std::mem::transmute(bind(&buffer, "str_stage2_bytes_root")) };
        idxs.iter().map(|&i| f(mode, i)).collect()
    })
}

/// Mode 0: the REAL kernel string hash (`murmur_hash_64a(s.as_bytes(), 11)`)
/// over five literals covering every murmur path (tail-only / exactly one
/// block / two blocks / blocks+tail / empty) — computed ENTIRELY in JIT
/// machine code (as_bytes inline, index loads, bounds checks; only the
/// wrapping leaves cross). Native oracle: the PRODUCTION block-form murmur.
#[test]
fn str2_murmur_native_eq_jit() {
    let jit = run_bytes_root_sweep(0, &[0, 1, 2, 3, 4]);
    for (i, lit) in LITS.iter().enumerate() {
        let native = native_murmur_hash_64a(lit.as_bytes(), 11);
        assert_eq!(
            jit[i], native,
            "murmur(lit[{i}]={lit:?}): native (block-form) != JIT (index-form) — [T-murmur-idx] broken"
        );
    }
    // NEGATIVE CONTROLS (armed): a single corrupted byte and a wrong seed must
    // both disagree — the equality is sensitive to every byte and the seed.
    assert_ne!(
        jit[0],
        native_murmur_hash_64a(b"reX", 11),
        "negative control must FAIL: corrupted byte should disagree"
    );
    assert_ne!(
        jit[1],
        native_murmur_hash_64a("Tree.rec".as_bytes(), 12),
        "negative control must FAIL: wrong seed should disagree"
    );
}

/// Mode 1: `str::len` INLINE (metadata-lane load) over the five literals.
#[test]
fn str2_len_native_eq_jit() {
    let jit = run_bytes_root_sweep(1, &[0, 1, 2, 3, 4]);
    for (i, lit) in LITS.iter().enumerate() {
        assert_eq!(
            jit[i],
            lit.len() as u64,
            "len(lit[{i}]={lit:?}): native != JIT"
        );
    }
    assert_ne!(
        jit[0], 4,
        "negative control must FAIL: off-by-one length should disagree"
    );
}

/// Mode 2: `for b in s.bytes()` — the str BYTES iterator walk (cursor init +
/// blanket-identity into_iter + StrBytes next, all in JIT machine code).
#[test]
fn str2_bytes_iter_native_eq_jit() {
    let jit = run_bytes_root_sweep(2, &[0, 1, 2, 3, 4]);
    for (i, lit) in LITS.iter().enumerate() {
        let native = lit
            .bytes()
            .fold(0u64, |h, b| h.wrapping_mul(31).wrapping_add(b as u64));
        assert_eq!(
            jit[i], native,
            "bytes()-fold(lit[{i}]={lit:?}): native != JIT"
        );
    }
    // NEGATIVE CONTROL (armed): a REVERSED byte order must disagree (the fold
    // is order-sensitive — proves the cursor walks forward).
    let reversed = "cer"
        .bytes()
        .fold(0u64, |h, b| h.wrapping_mul(31).wrapping_add(b as u64));
    assert_ne!(
        jit[0], reversed,
        "negative control must FAIL: reversed order should disagree"
    );
}

/// Mode 3: `for &b in s.as_bytes().iter()` — the u8 SLICE-iterator walk
/// (`<[u8]>::iter` cursor init + SliceIter next).
#[test]
fn str2_sliceiter_native_eq_jit() {
    let jit = run_bytes_root_sweep(3, &[0, 1, 2, 3, 4]);
    for (i, lit) in LITS.iter().enumerate() {
        let native = lit
            .as_bytes()
            .iter()
            .fold(0u64, |h, &b| h.wrapping_mul(31).wrapping_add(b as u64));
        assert_eq!(
            jit[i], native,
            "as_bytes().iter()-fold(lit[{i}]={lit:?}): native != JIT"
        );
    }
    assert_ne!(
        jit[1], jit[2],
        "negative control must FAIL: different literals should hash differently"
    );
}

/// Mode 4: `str_bytes_eq` polarity — the byte-compare machinery `name_eq`'s
/// structural walk uses, over literal pairs. Rows 1 and 2 are the ARMED
/// sensitivity controls: a same-length single-byte corruption and a length
/// mismatch must both be caught by the JIT machine code.
#[test]
fn str2_bytes_eq_native_eq_jit() {
    let jit = run_bytes_root_sweep(4, &[0, 1, 2, 3]);
    let pairs: [(&str, &str); 4] = [
        ("Tree", "Tree"),
        ("Tree", "TreX"),
        ("Tree", "Tre"),
        ("", ""),
    ];
    for (i, (a, b)) in pairs.iter().enumerate() {
        let native = (a == b) as u64;
        assert_eq!(jit[i], native, "str_bytes_eq{:?}: native != JIT", (a, b));
    }
    assert_eq!(
        jit[1], 0,
        "ARMED: same-length byte corruption must be caught in-module"
    );
    assert_eq!(jit[2], 0, "ARMED: length mismatch must be caught in-module");
}

// ═══════════════════════════════════════════════════════════════════════════
// Tests — the prize: from_string_uncached UNROLLED, bit-identical Names
// ═══════════════════════════════════════════════════════════════════════════

/// JIT one Name-returning root and decode the sret Name for each selector.
fn run_name_root(
    module: &'static str,
    what: &'static str,
    root: &'static str,
    sels: &'static [u64],
) -> Vec<(Vec<Comp>, u64, Vec<u64>)> {
    run_with_watchdog(what, move || {
        let buffer = jit_module(module, what, &stage2_externs());
        let f: extern "C" fn(*mut [u64; 5], u64) =
            unsafe { std::mem::transmute(bind(&buffer, root)) };
        sels.iter()
            .map(|&sel| {
                let mut out = std::mem::MaybeUninit::<[u64; 5]>::zeroed();
                f(out.as_mut_ptr(), sel);
                // The returned Name references JIT/shim heap (all immortal by
                // the leak model); decode by raw layout — never dropped.
                unsafe { decode_jit_name(out.as_ptr() as *const u8) }
            })
            .collect()
    })
}

/// THE PRIZE, part 1: `from_string_uncached` UNROLLED over literal parts runs
/// in JIT machine code building the REAL recursive Name — and the result is
/// BIT-IDENTICAL to the real clean-kernel: root hash == the golden
/// `lean4_hash()` constants, every node's cached_hash matches the production
/// chain recomputed from the STORED Arc<str> bytes, components (kind + bytes
/// + numeric values, incl. the parse->Num branch for "42"/"0") match the
///   native split+parse fold.
#[test]
fn str2_name_unrolled_bitidentical_native_eq_jit() {
    let results = run_name_root(
        NAME_TRUST_IR,
        "name_root JIT sweep",
        "str_stage2_name_root",
        &[0, 1, 2, 3, 4],
    );
    let dotted = [
        "Tree.rec",
        "Forest.rec",
        "Nat.42.rec",
        "VeryLongPartName.rec",
        "0.rec",
    ];
    let golden = [
        GOLDEN_TREE_REC,
        GOLDEN_FOREST_REC,
        GOLDEN_NAT_42_REC,
        GOLDEN_LONG_REC,
        GOLDEN_ZERO_REC,
    ];
    for (i, (comps, hash, node_hashes)) in results.iter().enumerate() {
        let (native_comps, native_hash) = native_from_string_uncached(dotted[i]);
        assert_eq!(
            *hash, native_hash,
            "{}: JIT cached_hash != native production fold",
            dotted[i]
        );
        assert_eq!(
            *hash, golden[i],
            "{}: JIT cached_hash != REAL clean-kernel golden constant",
            dotted[i]
        );
        assert_eq!(
            comps, &native_comps,
            "{}: decoded components != native split+parse fold",
            dotted[i]
        );
        // Per-node bit-identity: the chain recomputed from the DECODED comps
        // (str bytes read out of the shim-built Arc<str> blocks) must equal
        // the per-node cached_hash values the JIT stored, at every node down
        // to the Anon root (1723).
        let expect_chain = recompute_hash_chain(comps);
        assert_eq!(
            node_hashes, &expect_chain,
            "{}: per-node cached_hash chain != production recompute",
            dotted[i]
        );
    }
    // The parse->Num branch REALLY ran: "42" and "0" must decode as Num.
    assert_eq!(
        results[2].0[1],
        Comp::Num(42),
        "Nat.42.rec: middle component must be NameInner::Num(42) — the [T-parse] num branch"
    );
    assert_eq!(
        results[4].0[1],
        Comp::Num(0),
        "0.rec: root-adjacent component must be NameInner::Num(0)"
    );
    // NEGATIVE CONTROLS (armed): a corrupted golden and crossed results must
    // disagree — the equalities above are sensitive to every bit.
    assert_ne!(
        results[0].1,
        GOLDEN_TREE_REC.wrapping_add(1),
        "negative control must FAIL: golden+1 should disagree"
    );
    assert_ne!(
        results[0].1, results[1].1,
        "negative control must FAIL: Tree.rec and Forest.rec must hash differently"
    );
    let (corrupt_comps, _) = native_from_string_uncached("TreX.rec");
    assert_ne!(
        &results[0].0, &corrupt_comps,
        "negative control must FAIL: corrupted component should disagree"
    );
}

/// Production `Name::eq` (hash fast-path + full structural walk with
/// in-module byte compares over the deref'd Arc<str> pairs) over names
/// constructed in-module: [eq, hash-fastpath-ne, num-walk-eq, num-ne].
#[test]
fn str2_name_eq_native_eq_jit() {
    let jit = run_with_watchdog("name_eq_root JIT sweep", move || {
        let buffer = jit_module(
            NAME_EQ_TRUST_IR,
            "str_stage2_name_eq_root",
            &stage2_externs(),
        );
        let f: extern "C" fn(u64) -> u64 =
            unsafe { std::mem::transmute(bind(&buffer, "str_stage2_name_eq_root")) };
        [f(0), f(1), f(2), f(3)]
    });
    // Native oracle: the same four comparisons under the production semantics
    // (value equality of the built names).
    let pairs = [
        ("Tree.rec", "Tree.rec"),
        ("Tree.rec", "Forest.rec"),
        ("Nat.42", "Nat.42"),
        ("Nat.42", "Nat.43"),
    ];
    for (i, (a, b)) in pairs.iter().enumerate() {
        let na = native_from_string_uncached(a);
        let nb = native_from_string_uncached(b);
        let native = (na == nb) as u64;
        assert_eq!(jit[i], native, "name_eq{:?}: native != JIT", (a, b));
    }
    // ARMED: the two equal rows prove the FULL WALK returns true through the
    // in-module byte compares; the two unequal rows prove the hash fast-path.
    assert_eq!(jit[0], 1, "equal names must compare equal (full walk)");
    assert_eq!(
        jit[1], 0,
        "different names must compare unequal (hash fast-path)"
    );
}

/// THE PRIZE, part 2 — the mutual-recursor scenario DE-MODELED: the cross-type
/// IH rec name comes from `rec_name_of_constructed` — ind names built
/// in-module, REAL Name equality selects, rec name = the fold CONTINUED on the
/// matching ind name. No pre-interned RecPair table crosses the boundary. The
/// returned Name is bit-identical to the real kernel's
/// `Name::from_string("Tree.rec"/"Forest.rec")`.
#[test]
fn str2_rec_scenario_native_eq_jit() {
    let results = run_name_root(
        SCENARIO_TRUST_IR,
        "rec_scenario JIT",
        "str_stage2_rec_scenario_root",
        &[0, 1],
    );
    let expects = [
        ("Tree.rec", GOLDEN_TREE_REC),
        ("Forest.rec", GOLDEN_FOREST_REC),
    ];
    for (i, (dotted, golden)) in expects.iter().enumerate() {
        let (native_comps, native_hash) = native_from_string_uncached(dotted);
        let (comps, hash, node_hashes) = &results[i];
        assert_eq!(
            *hash, native_hash,
            "scenario({i}): JIT hash != native {dotted}"
        );
        assert_eq!(
            *hash, *golden,
            "scenario({i}): JIT hash != clean-kernel golden {dotted}"
        );
        assert_eq!(
            comps, &native_comps,
            "scenario({i}): components != native {dotted}"
        );
        let expect_chain = recompute_hash_chain(comps);
        assert_eq!(
            node_hashes, &expect_chain,
            "scenario({i}): per-node chain != production recompute"
        );
    }
    // NEGATIVE CONTROLS (armed): the CROSSED expectation — head=Tree must NOT
    // produce Forest.rec (proves the in-module equality actually selected),
    // and neither result may be the dead fallback.
    assert_ne!(
        results[0].1, GOLDEN_FOREST_REC,
        "negative control must FAIL: head=Tree returning Forest.rec should disagree"
    );
    let (_, dead_hash) = native_from_string_uncached("Dead.rec");
    assert_ne!(
        results[0].1, dead_hash,
        "head=Tree must not hit the dead fallback"
    );
    assert_ne!(
        results[1].1, dead_hash,
        "head=Forest must not hit the dead fallback"
    );
}
