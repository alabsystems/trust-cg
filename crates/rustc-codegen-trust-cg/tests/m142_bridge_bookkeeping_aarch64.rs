// Compiled only on an aarch64-apple-darwin host: another host builds this
// target with no test in it, never one that passes without running (L06-P10).
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Differential regressions for the two AGGREGATE-DEREF-STORE ADDRESSING defects:
// the memory-backed-source LEAF READ and the WHOLE-POINTEE STORE. Both wrote or
// read an aggregate field at a byte rustc's own layout does not put it at, and
// neither existing guard could see either of them.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// (1) `aggregate deref store field <n> out of layout range`, and its SILENT twin.
//     `(*p) = move v` reads each of the destination slot's trust-ir fields out of
//     the source's slot. Those fields are the FLATTENED SCALAR LEAVES of the
//     source type, and `lower_memory_aggregate_construct` wrote them at their own
//     rustc LAYOUT offsets — but the reader chose its addressing model from the
//     RUST TYPE'S KIND (`is_struct_or_tuple`) and then indexed a TOP-LEVEL-FIELD
//     offset table by the LEAF index. For any type whose leaf count differs from
//     its field count that ran out of range (`StringError(String)` is 1 field /
//     3 leaves; `core::io::error::Custom` is 4 fields / 5 lanes), and WHERE THE
//     TWO COUNTS COINCIDE IT SILENTLY READ A LEAF OUT OF ANOTHER FIELD'S BYTES.
//     The addressing model is now decided by the SLOT — are its trust-ir fields
//     this type's flattened leaves, type for type? — with the per-LEAF offsets
//     coming from `enumerate_scalar_leaf_offsets` (via
//     `flattened_leaf_layout_offsets`), and a uniformity check guarding the
//     lane-tiling arm that the kind test had no check on at all.
//
//     Two shapes, and they fail in the two different ways:
//       * `OuterMixed(Mixed { x: u8, y: u8, z: u64 })` — 1 top-level field, 3
//         leaves. REFUSED on the pre-fix backend with `aggregate deref store
//         field 1 out of layout range`.
//       * `Outer { z: Zst, q: Inner { a: u64, b: u64 } }` — 2 top-level fields
//         (both at layout offset 0, the ZST occupying no bytes) and 2 leaves (at
//         0 and 8). The counts COINCIDE, so nothing ran out of range: leaf 1 was
//         copied from offset 0 and the program returned 30 instead of 35. That
//         is the case an out-of-range refusal can never catch.
//
// (2) `[TCG-LANE-OFFSET-MISMATCH]` — the WHOLE-POINTEE-STORE direction.
//     `*p = P { .. }` through `&mut P` stored each field through `InsertField` on the
//     DECLARATION-ORDER trust-ir lane tuple, whose byte offsets are the natural-C
//     packing of the lanes. That is the wrong byte for any pointee whose rustc layout
//     is not that packing — a `#[repr(packed)]`/`#[repr(packed(N))]` TIGHTENING, an
//     over-aligned field, or an ordinary `repr(Rust)` REORDERING — and it was the
//     surviving half of a two-way hazard: the `(*r).field` READ and FIELD-STORE of the
//     same pointee are routed to the rustc-exact byte walker, and
//     `lower_memory_aggregate_construct` materializes the slot at
//     `variant_layout.fields.offset(i)`, so a `#[repr(packed)]` object was WRITTEN at
//     `m@0/a@8/b@16` and READ at `m@0/a@1/b@9` — the last field landing OUT OF BOUNDS
//     of the 13-byte object, silently, with no diagnostic. Neither existing guard
//     could see it: the read routing bails out on `place.projection.len() < 2` and a
//     whole-pointee store's projection is a bare `[Deref]`, and the
//     `[TCG-LANE-OFFSET-MISMATCH]` tripwire sits after `aggregate_deref_field_index`,
//     which answers `None` for a bare `[Deref]`.
//     `whole_pointee_store_layout_offsets` now stores each field at
//     `enumerate_scalar_leaf_offsets`' rustc offset whenever that disagrees with the
//     lane packing, leaves the agreeing majority on the untouched lane-offset
//     field store, and REFUSES by name for a known-mismatched pointee it cannot address
//     exactly.
//
// CONTROL — RE-MEASURED 2026-09-27 against PRISTINE `origin/main` `e985b634b`
// (`aarch64-apple-darwin`, -Copt-level 0 AND 3, `-Ztrust-ir-cg-args=no-proof-certs`).
// Every value below is the one the first port measured on `e46434fcd`, so none of
// main's five intervening `fix(bridge): preserve ...` commits touches either
// defect:
//
//     witness (in isolation)           LLVM   pre-fix trust-cg
//     OuterMixed leaf read               46   REFUSED "aggregate deref store field 1
//                                             out of layout range"
//     Outer{Zst,Inner} leaf read         35   30      (SILENT)
//     Rt reordered whole store           30   35      (SILENT)
//     Pk packed whole store              30   111     (SILENT)
//     [Pe; 2] packed-array whole store   56   119     (SILENT)
//
//     and the three programs as this file actually spells them:
//     test (1)   deref_store              46   REFUSED
//     test (1b)  deref_store_zst          35   30      (SILENT)
//     test (2)   whole_store             120   99      (SILENT)
//
// A passing run of this file therefore measures the fix, not an untouched path.
//
// MUTATION-PROVED. Forcing `whole_pointee_store_layout_offsets` to answer `Ok(None)`
// reproduces 35 / 111 / 119 exactly; restoring the pre-fix kind-based routing
// reproduces the refusal and the 30. Forcing only the EXACT path off — leaving the
// recursive `inline_contains_lane_offset_mismatched_aggregate` refusal arm live —
// makes all three whole-store shapes REFUSE by name, the array included. That last
// one is the point: an earlier version of the fix asked
// `scalar_field_aggregate_trust_ir_fields` for the leaf list, which answers `None`
// for an ARRAY, so `*p = [Pe, Pe]` through `&mut [Pe; 2]` had neither an exact path
// nor a refusal and stayed silently wrong.
//
// DELIBERATELY NOT COVERED HERE. The same whole-store shape with a user `Drop` in
// the pointee (`#[repr(packed)] struct Pk { m: u8, a: A, b: u32 }` where `A: Drop`)
// is refused on this tree for an unrelated and pre-existing reason —
// `TerminatorKind::Drop of type that needs drop: Pk (only Box<T>/Vec<T>/
// BTreeMap<K,V>/String with a no-drop payload is lowered)` — so it cannot witness
// this defect either before or after. `Pk` below carries no `Drop`; the drop-glue
// framing of the original report was incidental, and the packed WRITE/READ
// disagreement it exposed is exactly what `Pk` measures.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = host_target_support::AARCH64_TARGET;

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_m142_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn write_panic_stubs(dir: &Path, objs: &[PathBuf]) -> PathBuf {
    let mut nm = Command::new("nm");
    nm.arg("-u");
    for obj in objs {
        nm.arg(obj);
    }
    let nm = nm.output().expect("nm");
    let mut seen = std::collections::BTreeSet::new();
    let mut stubs = String::from("#include <stdlib.h>\n");
    for line in String::from_utf8_lossy(&nm.stdout).lines() {
        let sym = line.trim().trim_start_matches('U').trim();
        if toolchain_support::is_abort_stub_symbol(sym) && seen.insert(sym.to_owned()) {
            let c = sym.strip_prefix('_').unwrap_or(sym);
            stubs.push_str(&format!(
                "void {c}(void) __asm__(\"{sym}\"); void {c}(void){{ abort(); }}\n"
            ));
        }
    }
    let stubs_path = dir.join("stubs.c");
    std::fs::write(&stubs_path, stubs).expect("write stubs");
    stubs_path
}

/// Compile `body` (after the shared preamble and any crate-level `attrs`) at `opt`, through the trust-cg
/// backend when `dylib` is `Some`, link it with abort stubs for the diverging
/// `core` entries, run it, and return the exit code.
///
/// A compile or link failure is a test FAILURE, never a skip, on BOTH sides. Case
/// (1) REFUSED on the pre-fix backend, so treating a refusal as a coverage gap
/// would make this file pass against the very defect it pins.
///
/// PROOFS-OFF DIAGNOSTIC: the trust-cg side passes the backend's
/// `no-proof-certs` knob, so a pass is a native differential against LLVM and
/// never certified-object evidence; with certificates on, these framed
/// programs meet the AArch64 proof-promotion refusal (`[TCG-PROOF-465]`, the
/// proof wall of ledger L07-P2).
fn compile_link_run(stem: &str, attrs: &str, body: &str, opt: &str, dylib: Option<&Path>) -> i32 {
    let dir = workdir(stem);
    let src_path = dir.join("prog.rs");
    let src = format!(
        "#![no_std]\n#![no_main]\n{attrs}\
         #[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! {{ loop {{}} }}\n\
         use core::hint::black_box as bb;\n{body}\n"
    );
    std::fs::write(&src_path, src).expect("write source");

    let mut cmd = toolchain_support::rustc_command();
    cmd.arg("--crate-type").arg("bin");
    if let Some(dylib) = dylib {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(&backend_arg);
        cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    cmd.args(["--target", TARGET, "-Cpanic=abort", "-Coverflow-checks=off"])
        .arg("-Ccodegen-units=1")
        .arg(format!("-Copt-level={opt}"))
        .arg("--emit=obj")
        .arg("--out-dir")
        .arg(&dir)
        .arg(&src_path);
    let output = cmd.output().expect("failed to spawn the build compiler");
    assert!(
        output.status.success(),
        "{stem} (opt={opt}, backend={}): failed to compile. stderr: <<<{}>>>",
        if dylib.is_some() { "trust-cg" } else { "llvm" },
        String::from_utf8_lossy(&output.stderr)
    );

    let objs: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("read workdir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "o"))
        .collect();
    assert!(
        !objs.is_empty(),
        "{stem} (opt={opt}): no object file produced"
    );

    let stubs_path = write_panic_stubs(&dir, &objs);
    let bin = dir.join("bin");
    let mut link = Command::new("cc");
    link.arg("-o").arg(&bin);
    for obj in &objs {
        link.arg(obj);
    }
    link.arg(&stubs_path);
    let link = link.output().expect("cc link");
    assert!(
        link.status.success(),
        "{stem} (opt={opt}): link failed. stderr: <<<{}>>>",
        String::from_utf8_lossy(&link.stderr)
    );

    let run = Command::new(&bin).output().expect("run compiled binary");
    let _ = std::fs::remove_dir_all(&dir);
    run.status.code().expect("process terminated by signal")
}

fn differential_program(stem: &str, body: &str, expected: i32) {
    differential_program_with_attrs(stem, "", body, expected)
}

/// `differential_program`, plus `attrs` — extra CRATE-level inner attributes, emitted
/// straight after `#![no_std] #![no_main]` and before any item, which is the only
/// position `#![feature(..)]` is accepted in.
///
/// A case that needs one must ALSO require the channel: `#![feature(..)]` is E0554 on
/// a stable/beta channel, and this harness compiles with whatever compiler built the
/// backend. See `require_feature_gates`.
fn differential_program_with_attrs(stem: &str, attrs: &str, body: &str, expected: i32) {
    // The backend knob option, Darwin rust-std, `cc` and `nm` are required
    // here; a missing one fails the case by name instead of returning early.
    darwin_native::require(stem, &["cc", "nm"]);
    let dylib = ensure_dylib_built();
    for opt in ["0", "3"] {
        let llvm = compile_link_run(stem, attrs, body, opt, None);
        let trust = compile_link_run(stem, attrs, body, opt, Some(&dylib));
        assert_eq!(
            llvm, expected,
            "{stem} (opt={opt}): LLVM oracle returned {llvm}, expected {expected}"
        );
        assert_eq!(
            trust, llvm,
            "{stem} (opt={opt}): trust-cg returned {trust} but LLVM returned {llvm} (miscompile)"
        );
    }
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// (1) `(*p) = move v` where `v`'s LEAF count differs from its top-level FIELD
/// count (REFUSED before the fix), and where the two counts COINCIDE but the
/// offset tables disagree (SILENTLY WRONG before the fix).
#[test]
fn m142_deref_store_leaf_offsets_match_llvm() {
    differential_program(
        "deref_store",
        "#[derive(Copy, Clone)] struct Three { a: u64, b: u64, c: u64 }\n\
         #[derive(Copy, Clone)] struct One(Three);\n\
         #[derive(Copy, Clone)] struct Mixed { x: u8, y: u8, z: u64 }\n\
         #[derive(Copy, Clone)] struct OuterMixed(Mixed);\n\
         #[inline(never)] fn store_one(p: &mut One, v: One) { *p = v; }\n\
         #[inline(never)] fn store_mixed(p: &mut OuterMixed, v: OuterMixed) { *p = v; }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut d1 = One(Three { a: 0, b: 0, c: 0 }); \
            store_one(&mut d1, One(Three { a: bb(1u64), b: bb(2u64), c: bb(3u64) })); \
            let mut d2 = OuterMixed(Mixed { x: 0, y: 0, z: 0 }); \
            store_mixed(&mut d2, OuterMixed(Mixed { x: bb(4u8), y: bb(5u8), z: bb(6u64) })); \
            let s1 = (d1.0.a*100 + d1.0.b*10 + d1.0.c) as i32; \
            let s2 = (d2.0.x as i32)*10 + (d2.0.y as i32) + (d2.0.z as i32); \
            ((s1 + s2) & 0x7f) as i32 }",
        // 123 + 51 = 174; 174 & 0x7f = 46
        46,
    );
}

/// (1b) The SILENT half of the same defect: a ZERO-SIZED first field makes the
/// top-level FIELD count equal the flattened LEAF count while the two offset
/// tables still disagree, so nothing ran out of range — leaf 1 was simply copied
/// from offset 0 instead of 8.
#[test]
fn m142_deref_store_equal_count_leaf_offsets_match_llvm() {
    differential_program(
        "deref_store_zst",
        "#[derive(Copy, Clone)] struct Zst;\n\
         #[derive(Copy, Clone)] struct Inner { a: u64, b: u64 }\n\
         #[derive(Copy, Clone)] struct Outer { z: Zst, q: Inner }\n\
         #[inline(never)] fn store_outer(p: &mut Outer, v: Outer) { *p = v; }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut d = Outer { z: Zst, q: Inner { a: 0, b: 0 } }; \
            store_outer(&mut d, Outer { z: Zst, q: Inner { a: bb(3u64), b: bb(5u64) } }); \
            ((d.q.a * 10 + d.q.b) as i32) & 0x7f }",
        // 3*10 + 5 = 35
        35,
    );
}

/// (2) The WHOLE-POINTEE STORE `*p = P { .. }` into a pointee whose rustc field
/// offsets DISAGREE with the declaration-order trust-ir lane packing, in the three
/// shapes each measured SILENTLY WRONG on the unpatched backend at -Copt-level 0
/// AND 3: an ordinary `repr(Rust)` REORDERING with no `repr` attribute at all
/// (35 vs LLVM's 30 in isolation), a `#[repr(packed)]` TIGHTENING (111 vs 30), and
/// an ARRAY of packed elements (119 vs 56). Together, as written below, the
/// unpatched backend returned **99** where LLVM returns **120**.
///
/// HOW IT FAILS IF THE GUARD IS REMOVED. Make
/// `whole_pointee_store_layout_offsets` answer `Ok(None)` and every field is
/// written at the lane offset again: `Rt`'s three fields go into a layout rustc
/// reordered, `Pk`'s `a`/`b` land 7 bytes past their rustc offsets (`b` out of
/// bounds of the 13-byte object), and the array's second element is written at 16
/// instead of 9. Make only `flattened_leaf_layout_offsets` answer `Ok(None)` and
/// the compile REFUSES with `[TCG-LANE-OFFSET-MISMATCH] whole-pointee store` for
/// all three — never a wrong value.
#[test]
fn m142_whole_pointee_store_layout_offsets_match_llvm() {
    differential_program(
        "whole_store",
        "static mut ACC: u64 = 0;\n\
         #[inline(never)] fn bump(v: u64) { \
            unsafe { ACC = ACC.wrapping_mul(31).wrapping_add(v); } }\n\
         struct Rt { m: u8, a: u64, b: u32 }\n\
         #[repr(packed)] struct Pk { m: u8, a: u64, b: u32 }\n\
         #[repr(packed)] #[derive(Copy, Clone)] struct Pe { m: u8, a: u64 }\n\
         #[inline(never)] fn set_rt(p: &mut Rt, k: u64) { \
            *p = Rt { m: 9, a: k, b: 0xAABBCCDD }; }\n\
         #[inline(never)] fn set_pk(p: &mut Pk, k: u64) { \
            *p = Pk { m: 9, a: k, b: 0xAABBCCDD }; }\n\
         #[inline(never)] fn set_arr(p: &mut [Pe; 2], k: u64) { \
            *p = [Pe { m: 9, a: k }, Pe { m: 4, a: 0xAABBCCDD }]; }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let k = bb(0x0102030405060708u64); \
            let mut y1 = Rt { m: bb(0u8), a: bb(1u64), b: bb(0u32) }; \
            set_rt(&mut y1, k); bb(&y1); \
            bump(y1.m as u64); bump(y1.a); bump(y1.b as u64); \
            let mut y2 = Pk { m: bb(0u8), a: bb(1u64), b: bb(0u32) }; \
            set_pk(&mut y2, k); bb(&y2); \
            bump(y2.m as u64); bump(y2.a); bump(y2.b as u64); \
            let mut y3 = [Pe { m: bb(0u8), a: bb(1u64) }, Pe { m: bb(0u8), a: bb(2u64) }]; \
            set_arr(&mut y3, k); bb(&y3); \
            bump(y3[0].m as u64); bump(y3[0].a); bump(y3[1].m as u64); bump(y3[1].a); \
            ((unsafe { ACC } & 0x7f) as i32) }",
        // Measured from the LLVM oracle at both opt levels.
        120,
    );
}

// The lane cases below (ported from `lane/integration-2026-09-14-g`) run through the
// same harness, `no-proof-certs` included.

/// A capture-less (ZST-env) closure called BY VALUE with a by-value aggregate
/// argument, in both of rustc's register placements for one.
#[test]
fn m142_zst_env_closure_byval_aggregate_arg_matches_llvm() {
    differential_program(
        "closure_abi",
        "#[derive(Copy, Clone)] struct Big { a: u64, b: u64, c: u64, d: u64 }\n\
         #[derive(Copy, Clone)] struct Pair { s: u64, al: u64 }\n\
         #[inline(never)] fn apply_big<F: FnOnce(Big) -> i32>(f: F, v: Big) -> i32 { f(v) }\n\
         #[inline(never)] fn apply_pair<F: FnOnce(Pair) -> i32>(f: F, v: Pair) -> i32 { f(v) }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let x = apply_big(|b: Big| (b.a*1000 + b.b*100 + b.c*10 + b.d) as i32, \
                              Big { a: bb(1u64), b: bb(2u64), c: bb(3u64), d: bb(4u64) }); \
            let y = apply_pair(|p: Pair| (p.s*10 + p.al) as i32, \
                               Pair { s: bb(5u64), al: bb(6u64) }); \
            ((x + y) & 0x7f) as i32 }",
        // 1234 + 56 = 1290; 1290 & 0x7f = 10
        10,
    );
}

/// Require that a `#![feature(..)]`-carrying case can be compiled at all by the
/// compiler that built the backend. On a stable/beta channel it is E0554. This file is
/// compiled only on aarch64-apple-darwin, where the bridge pin must be the Trust channel
/// (`scripts/check_darwin_aarch64_bridge.py` refuses any other), so another channel
/// FAILS the case by name; it used to skip, which passed without running (L06-P10).
///
/// Every soundness-critical assertion in the flat-leaf and from-residual cases below is
/// FEATURE-FREE and does not depend on this requirement; only the const-eval-select
/// case needs `core::intrinsics::const_eval_select` to SPELL its MIR shape at all.
fn require_feature_gates(stem: &str) {
    let channel = toolchain_support::pinned_toolchain();
    assert!(
        toolchain_support::is_trust_channel(&channel),
        "{stem}: channel `{channel}` is not `{}`, so the `#![feature(..)]` this case needs \
         is E0554; on aarch64-apple-darwin a missing prerequisite fails. The read-path half \
         of the same defect is covered feature-free by `m142_flat_leaf_field_index_matches_llvm`.",
        toolchain_support::TRUST_CHANNEL
    );
}

/// The MIR-FIELD-INDEX vs FLAT-LEAF-INDEX read/write of a SCALARIZED aggregate.
///
/// `lower_recursive_scalar_field_aggregate_operands` binds a scalarized aggregate whose
/// every leaf it can flatten at a running FLAT LEAF index — ZST fields contributing
/// none, a nested scalar-field aggregate expanded depth-first — while
/// `projected_field_index`, the single resolver BOTH the read (`place_to_value`) and the
/// write (`scalar_place_binding`) path go through, returned the MIR FIELD index. For
/// every aggregate where the two disagree, `o.k` read (and wrote) a DIFFERENT leaf of
/// the same local at the same trust-ir type.
///
/// `Out { i: In2 { a, b }, k }` is the smallest disagreement: `k` is MIR field 1 and
/// FLAT leaf 2, so `o.k` resolved to leaf 1 — `b`. `OutZ` adds a `()` between them, so
/// `k` is MIR field 2 and still FLAT leaf 2, which is the ZST-shift half of the same
/// arithmetic. The third case WRITES `o.k` and then passes the whole aggregate BY VALUE
/// (packed from the flat leaves), so a write to the wrong leaf corrupts `b` and shows
/// up in a field the write never named. The fourth is the OTHER projection spelling the
/// resolver serves — `[Downcast, Field]`, a single-variant enum's payload
/// (`match E::V(In2 { a, b }, k) { E::V(_, k) => k }`) — which took the identical wrong
/// leaf and which a fix applied only to the bare `[Field]` arm would leave wrong.
///
/// HOW IT FAILS IF THE FIX IS REVERTED. Make `resolved_scalar_field_index` return
/// `Ok(Some(mir_field))` unconditionally (its pre-fix body) and this program returns
/// **91** at `-Copt-level=0` and **46** at `-Copt-level=3` against LLVM's **34** —
/// measured 2026-09-26, `aarch64-apple-darwin`, on the unpatched lane tip AND on a
/// patched tree with only that function reverted. A SILENT wrong value at both opt
/// levels, never a refusal.
#[test]
fn m142_flat_leaf_field_index_matches_llvm() {
    differential_program(
        "flat_leaf_index",
        "#[derive(Copy, Clone)] struct In2 { a: u64, b: u64 }\n\
         #[derive(Copy, Clone)] struct Out { i: In2, k: u64 }\n\
         #[derive(Copy, Clone)] struct OutZ { i: In2, z: (), k: u64 }\n\
         enum E { V(In2, u64) }\n\
         #[inline(never)] fn sum(o: Out) -> u64 { o.i.a * 1000 + o.i.b * 100 + o.k }\n\
         #[inline(never)] fn read_k(a: u64, b: u64, k: u64) -> u64 { \
            let o = Out { i: In2 { a, b }, k }; o.k }\n\
         #[inline(never)] fn read_kz(a: u64, b: u64, k: u64) -> u64 { \
            let o = OutZ { i: In2 { a, b }, z: (), k }; o.k }\n\
         #[inline(never)] fn write_k(a: u64, b: u64, k: u64) -> u64 { \
            let mut o = Out { i: In2 { a, b }, k }; o.k = k + 1; sum(o) }\n\
         #[inline(never)] fn enum_field(a: u64, b: u64, k: u64) -> u64 { \
            let e = E::V(In2 { a, b }, k); match e { E::V(_, k) => k } }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let r1 = read_k(bb(1u64), bb(2u64), bb(7u64)); \
            let r2 = read_kz(bb(3u64), bb(4u64), bb(9u64)); \
            let r3 = write_k(bb(5u64), bb(6u64), bb(20u64)); \
            let r4 = enum_field(bb(8u64), bb(11u64), bb(30u64)); \
            ((r1 * 1000000 + r2 * 10000 + r3 * 100 + r4) & 0x7f) as i32 }",
        // r1 = 7, r2 = 9, r3 = 5000 + 600 + 21 = 5621, r4 = 30;
        // 7_000_000 + 90_000 + 562_100 + 30 = 7_652_130; & 0x7f = 34.
        34,
    );
}

/// `?` whose `From` conversion is NOT the identity.
///
/// `FromResidual::from_residual` is INTERCEPTED (the real body is `#[track_caller]`),
/// and the interception modeled only an IDENTITY `From` — anything else failed closed,
/// costing three `library/alloc` roots (`RawVecInner::{grow_exact, grow_amortized,
/// shrink_unchecked}`, whose `?` converts `TryReserveErrorKind` into
/// `TryReserveError`). A real conversion's semantics is its own body, so the
/// interception now DECLINES (`FromResidualLowering::NotModeled`) and the ordinary
/// direct-call path emits the real `from_residual`, inside which the real `From::from`
/// runs. Nothing about the conversion is modeled or assumed.
///
/// `convert` is the payload-carrying arm and `convert_z` the TAG-ONLY one (a
/// `Result<(), ZST>` destination is a bare tag scalar, a different code path with its
/// own identity check). `same` (identity `From`) and `opt` (`Option`) are CONTROLS: both
/// stay on the synthesized interception, and a change that moved them onto the real
/// body — or broke it — shows up here. The last row takes the `Ok` path, so a lowering
/// that wrote `Err` unconditionally is caught too.
///
/// HOW IT FAILS IF THE FIX IS REVERTED. Restore the memory-path `is not the identity`
/// `Err` and this program does not compile at `-Copt-level=0` — measured 2026-09-26,
/// `from_residual payload conversion `Kind` -> `Wrap` is not the identity`, a failed
/// root. `-Copt-level=3` does NOT discriminate: the inliner folds `from_residual` into
/// its caller before the interception sees the call, so the assertion that carries this
/// case is the `opt=0` one.
#[test]
fn m142_from_residual_non_identity_from_matches_llvm() {
    differential_program(
        "from_residual_convert",
        // The Err/Ok choice rides a `bool` PARAMETER rather than a comparison: a
        // materialized comparison result lowers to `AArch64::CSet`, which has no proof
        // mapping yet ([TCG-PROOF-465]) and would make this case red for a reason that
        // has nothing to do with `from_residual`. Measured: with `if x > 100` the
        // `opt=3` compile failed on exactly that.
        "#[derive(Copy, Clone)] struct Kind(u64);\n\
         #[derive(Copy, Clone)] struct Wrap { kind: Kind, tag: u64 }\n\
         impl From<Kind> for Wrap { #[inline(never)] fn from(kind: Kind) -> Wrap { \
            Wrap { kind: Kind(kind.0 * 2), tag: 7 } } }\n\
         #[derive(Copy, Clone)] struct ZA;\n\
         #[derive(Copy, Clone)] struct ZB;\n\
         impl From<ZA> for ZB { fn from(_: ZA) -> ZB { ZB } }\n\
         #[inline(never)] fn leaf(x: u64, bad: bool) -> Result<u64, Kind> { \
            if bad { Err(Kind(x)) } else { Ok(x) } }\n\
         #[inline(never)] fn convert(x: u64, bad: bool) -> Result<u64, Wrap> { \
            let v = leaf(x, bad)?; Ok(v + 1) }\n\
         #[inline(never)] fn same(x: u64, bad: bool) -> Result<u64, Kind> { \
            let v = leaf(x, bad)?; Ok(v + 2) }\n\
         #[inline(never)] fn leaf_z(bad: bool) -> Result<(), ZA> { \
            if bad { Err(ZA) } else { Ok(()) } }\n\
         #[inline(never)] fn convert_z(bad: bool) -> Result<(), ZB> { leaf_z(bad)?; Ok(()) }\n\
         #[inline(never)] fn opt(x: u64, bad: bool) -> Option<u64> { \
            let v = if bad { None } else { Some(x) }?; Some(v + 3) }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let a = match convert(bb(3u64), bb(true)) { \
                Ok(v) => v, Err(e) => e.kind.0 * 10 + e.tag }; \
            let b = match same(bb(4u64), bb(true)) { Ok(v) => v, Err(e) => e.0 * 100 }; \
            let c = match convert_z(bb(true)) { Ok(()) => 1u64, Err(ZB) => 2u64 }; \
            let d = match opt(bb(6u64), bb(true)) { Some(v) => v, None => 9u64 }; \
            let e = match convert(bb(200u64), bb(false)) { Ok(v) => v, Err(_) => 0 }; \
            ((a + b * 3 + c * 5 + d * 7 + e * 11) & 0x7f) as i32 }",
        // a = 3*2*10 + 7 = 67, b = 400, c = 2, d = 9, e = 201;
        // 67 + 1200 + 10 + 63 + 2211 = 3551; & 0x7f = 95.
        95,
    );
}

/// The by-value aggregate call argument read from a PROJECTED SUB-PLACE of a
/// SCALARIZED base — the `const_eval_select((layout, zeroed), ct, rt)` shape.
///
/// The reason it needs a feature gate (the program needs
/// `core::intrinsics::const_eval_select` to SPELL the shape — ordinary source spells it
/// with a temp at every opt level, and the backend's own interception is what emits
/// `rt(move (_4.0: Lay3), move (_4.1: u64))`), so the case is guarded on the channel
/// rather than on nothing.
///
/// The sub-place LOADER was already right; what refused was its SIBLING-READ
/// precondition, which demanded that the base's MIR field indices COINCIDE with its
/// flat leaf indices — false for every `(aggregate, scalar)` tuple, hence
/// `Global::{alloc,grow,shrink}_impl`. With `projected_field_index` mapping MIR -> flat
/// (the flat-leaf case above) the precondition is met a second way and the three roots compile.
///
/// HOW IT FAILS IF THE FIX IS REVERTED. Make `recursive_flat_binding_in_force` answer
/// `Ok(false)` and the compile REFUSES at `-Copt-level=0` — `by-value aggregate call
/// argument 0 uses a projected operand`. Keep that but revert
/// `resolved_scalar_field_index` to the MIR index and it COMPILES and returns **80**
/// against LLVM's **85**: `k` (flat 3) read at MIR index 1 picks up `b`. That pair is
/// the whole argument for why the read had to be fixed FIRST, and why relaxing the
/// precondition alone would have been a miscompile.
#[test]
fn m142_const_eval_select_projected_byval_arg_matches_llvm() {
    require_feature_gates("const_eval_select_projected_arg");
    differential_program_with_attrs(
        "ces_projected_arg",
        "#![feature(core_intrinsics)]\n#![feature(const_eval_select)]\n\
         #![allow(internal_features)]\n",
        "#[derive(Copy, Clone)] struct Lay3 { a: u64, b: u64, c: u64 }\n\
         const fn ct3(l: Lay3, k: u64) -> u64 { l.a * 1000 + l.b * 100 + l.c * 10 + k }\n\
         fn rt3(l: Lay3, k: u64) -> u64 { l.a * 1000 + l.b * 100 + l.c * 10 + k }\n\
         #[inline(never)] const fn sel3(l: Lay3, k: u64) -> u64 { \
            core::intrinsics::const_eval_select((l, k), ct3, rt3) }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            (sel3(Lay3 { a: bb(1u64), b: bb(2u64), c: bb(3u64) }, bb(7u64)) & 0x7f) as i32 }",
        // 1000 + 200 + 30 + 7 = 1237; & 0x7f = 85. The MIR-index read answers 1232 -> 80.
        85,
    );
}
