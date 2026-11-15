#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: the FAT-POINTER (`&[T]` / `&str`) and ARRAY lane fixtures.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHY THIS FILE EXISTS. `tests/bridge_corpus/lane_types-slices-str-arrays_{1,2,
// 3}.rs` were authored as the fat-reference / array lane's own corpus and then
// referenced by NO harness: `grep`ping the `tests/` tree for their names
// returned only themselves, so nothing compiled them, nothing ran them, and a
// regression in the machinery they cover would have been invisible on every
// host. They are the three host-native fixtures for the shapes this lane's
// guard protects (a `{data,len}` fat pointer as a by-reference pointee field,
// subslice reborrows, and nested-array pointees), which is exactly the
// machinery a wrong fat-leaf lane count corrupts.
//
// THE GATE. Each fixture is compiled BY THE BRIDGE and BY LLVM at the same
// optimization level, run, and compared on STDOUT and EXIT CODE — the
// `dyn_fat_leaf_differential.rs` doctrine, for the same reason (panic text
// legitimately differs between the two backends).
//
//   * bridge output differs from LLVM        -> HARD FAIL (a miscompile).
//   * bridge FAILS CLOSED with a named
//     `[TCG-...]` diagnostic                 -> INCOMPLETE row, reported, not a
//                                               failure. Fail-closed is a
//                                               legitimate backend outcome.
//   * bridge crashes / refuses with no named
//     diagnostic                             -> HARD FAIL.
//   * fewer than `COMPILED_FLOOR` rows
//     COMPILE                                -> HARD FAIL.
//
// The floor is what stops this from degrading into a test that passes because
// everything refuses: an INCOMPLETE row is honest, but a harness made entirely
// of INCOMPLETE rows measures nothing. NEVER lower the floor to make the gate
// pass — a newly-refusing fixture is a coverage regression to fix.
//
// MEASURED (backend built from this tree against the 2026-09-14 stage1
// `0cb693917a`, trust-cg `9da5e237`): fixture 2, fixture 3 and
// `fix_o_fat_leaf_deref_store` COMPILE and MATCH at both opt levels; fixture 1
// fails closed with `[TCG-ARG-ABI]` on the `Option<(&u8, &[u8])>::map` closure
// argument — the census's rank-1 refusal class, which is not this lane's and is
// tracked separately. Hence a floor of 6 of the 8 rows.
//
// HOST-NATIVE: no `--target` is passed, so this runs wherever the crate builds.

use std::path::{Path, PathBuf};
use std::process::Command;

/// Every fixture is run at BOTH: `-O0` is the un-inlined shape (real fat-pointer
/// parameters and returns), `-O2` is the shape after rustc's inliner has folded
/// the aggregates and re-materialized the fat pointers, which is where a
/// lane-offset mistake usually surfaces.
const OPT_LEVELS: &[&str] = &["-Copt-level=0", "-Copt-level=2"];

/// Of `cases().len() * OPT_LEVELS.len()` rows, at least this many must COMPILE.
///
/// RAISED 6 -> 11 on 2026-09-27 with the DEREF-BASE-ADDRESS lane (seven fixtures
/// after `fix_dst_prefix_fat_leaf_store_refuses`). Both numbers were MEASURED by
/// running this target on this host — pack toolchain `pkg/store/trust/9192`
/// (`targo --unverified test --release --locked`), aarch64-apple-darwin:
///
///     lane tip `572c4ce34`, 4 cases        4/8   RED: below the floor of 6
///     tip + this lane, 12 cases           11/24
///
/// READ THE FIRST ROW BEFORE TRUSTING THE SECOND. The floor of 6 was taken on
/// another stage1 (`0cb693917a`), where `fix_o_fat_leaf_deref_store` compiled at
/// both levels. On this host it is INCOMPLETE at both — `read_named`,
/// `read_cursor` and `read_holder` refuse on the host-wide `[TCG-PROOF-465]`
/// opcode-proof gap, identically with and without this lane — so this target was
/// already red here before the lane existed. The lane does NOT fix that; its two
/// rows are still in the INCOMPLETE list. The floor is set to the measured 11 so
/// that a regression in any of the new rows (including the vtable-tail CAPABILITY
/// row, which only the floor can see) fails it by name; when the AArch64
/// opcode-proof inventory closes `[TCG-PROOF-465]`, `fix_o_fat_leaf_deref_store`
/// and the new rows' `-O2` halves become live and this should RISE (to at least
/// 12), never fall.
///
/// The eleven, at `-Copt-level=0` unless marked: `lane_types_slices_str_arrays_2`
/// (O0+O2), `lane_types_slices_str_arrays_3` (O0+O2),
/// `fix_dst_ref_whole_prefix_read`, `fix_dst_raw_ptr_prefix_rw` (O0+O2),
/// `fix_dst_ref_prefix_enum_and_nested_reads`,
/// `fix_dst_ref_prefix_tag_and_index_discriminant`, `fix_dst_ref_prefix_enum_payload`
/// (O2 only: its O0 `payload` refuses on `[TCG-PROOF-465]`), and
/// `fix_dyn_tail_prefix_fat_leaf_rw`. `fix_dst_prefix_fat_leaf_store_refuses` and
/// `fix_dst_ref_fat_leaf_into_aggregate_refuses` are INCOMPLETE BY DESIGN (a named
/// refusal is their correct outcome; reverted, they DIVERGE).
const COMPILED_FLOOR: usize = 11;

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_fatlane_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

struct Run {
    code: i32,
    stdout: String,
}

/// Compile `src` (with the bridge when `backend` is `Some`), run it, and return
/// its exit code + stdout. `Err` carries the compiler's stderr tail.
fn compile_and_run(
    dir: &Path,
    name: &str,
    src: &str,
    opt: &str,
    backend: Option<&Path>,
) -> Result<Run, String> {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(name);

    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin", "-Cpanic=abort", "-Ccodegen-units=1"]);
    cmd.arg(opt);
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
    }
    cmd.arg("-o").arg(&bin).arg(&src_path);
    let output = cmd.output().expect("spawn the compiler");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    let run = Command::new(&bin).output().expect("run compiled binary");
    let code = run
        .status
        .code()
        .expect("compiled program exited via signal, not an exit code");
    Ok(Run {
        code,
        stdout: String::from_utf8_lossy(&run.stdout).into_owned(),
    })
}

/// The bridge's own named refusal tag, if this stderr is a fail-closed refusal
/// rather than a crash. An ICE, a panic, or a refusal with no `[TCG-...]` tag is
/// NOT an honest INCOMPLETE and must fail the gate.
fn named_refusal(stderr: &str) -> Option<String> {
    if stderr.contains("internal compiler error") || stderr.contains("panicked at") {
        return None;
    }
    let start = stderr.find("[TCG-")?;
    let end = stderr[start..].find(']')? + start + 1;
    Some(stderr[start..end].to_owned())
}

struct Case {
    name: &'static str,
    what: &'static str,
    src: &'static str,
}

fn cases() -> Vec<Case> {
    vec![
        Case {
            name: "lane_types_slices_str_arrays_1",
            what: "fat-reference RETURNS (`-> &[u8]` / `-> &str`) and SUBSLICE \
                   reborrows (`[first, rest @ ..]`, `[head @ .., last]`), whose \
                   lengths are runtime values computed from the `{data,len}` \
                   pair",
            src: include_str!("bridge_corpus/lane_types-slices-str-arrays_1.rs"),
        },
        Case {
            name: "lane_types_slices_str_arrays_2",
            what: "ARRAY shapes: a `[T; 0]` ZST unsized to an empty `&[u8]`, a \
                   `[u8; 4]` by value, and a `[u8; 16]`-field struct read \
                   element-wise through the memory-aggregate slot",
            src: include_str!("bridge_corpus/lane_types-slices-str-arrays_2.rs"),
        },
        Case {
            name: "lane_types_slices_str_arrays_3",
            what: "a NESTED-ARRAY pointee (`&[[u8; 4]; 3]`) walked with RUNTIME \
                   indices over both strides",
            src: include_str!("bridge_corpus/lane_types-slices-str-arrays_3.rs"),
        },
        Case {
            name: "fix_o_fat_leaf_deref_store",
            what: "STORING a `{data,meta}` fat pointer into an aggregate field \
                   THROUGH a `&mut` reference (`(*p).field = <fat>`) — the \
                   `core::net::parser::Parser { state: &[u8] }` cursor shape, \
                   plus a `&str` field and a `&dyn` field whose vtable lane is \
                   dispatched through after the store",
            src: include_str!("bridge_corpus/fix_o_fat_leaf_deref_store.rs"),
        },
        Case {
            // [TCG-THIN-REF-DST] The SIBLING of the row above, and the one it did
            // NOT cover: the same `(*p).field = <fat>` store, but through a
            // reference whose POINTEE IS UNSIZED (a slice-tail DST struct). The
            // row above stores through a `&mut Parser` — a THIN reference — so it
            // exercises the branch and never the predicate that admits it.
            //
            // This row is expected to be an INCOMPLETE (a named
            // `[TCG-MIR-UNSUPPORTED] … DST prefix field store of non-scalar leaf`
            // refusal), NOT a compiled match: the two-lane store through a
            // slice-tail-DST base is not modelled. It is here because BEFORE the
            // fix the bridge COMPILED it and lost the write, and a lost wide
            // prefix write is an executed out-of-bounds READ — so a regression
            // shows up as `assert_eq!(bridge.stdout, oracle.stdout)` failing with
            // `oob len 64 sum 448` against `oob len 2 sum 3`, not as a silent
            // change of refusal tag. Do NOT "fix" this row by making it compile
            // unless the store really addresses the DATA lane.
            name: "fix_dst_prefix_fat_leaf_store_refuses",
            what: "a WIDE (`&[u8]`) PREFIX field stored through a slice-tail \
                   DST's own FAT reference (`(*h).i.s = v` on \
                   `h: &mut H<'_, [u32]>`), NEXT TO the scalar prefix store \
                   (`(*h).i.n = k`) the prefix arm admits — the dropped-write \
                   shape whose stale longer length is an out-of-bounds read",
            src: include_str!("bridge_corpus/fix_dst_prefix_fat_leaf_store_refuses.rs"),
        },
        Case {
            // [TCG-DEREF-BASE-ADDR] The READ direction of the row above, and the
            // witness that refuted slice-assign v2: `get_i(h: &H<[u32]>) -> Inner
            // { h.i }` beside `set_a(h, v) { h.i.a = v }`. The whole-aggregate
            // deref-read arm took `h`'s one bound value as the pointee's address
            // because the old thin/fat ENUMERATION called a slice-tail DST
            // reference thin. Reverted, this row is a hard STDOUT divergence
            // (`get_i <stack address> 3 <garbage>` vs LLVM `get_i 4242 2 3`).
            name: "fix_dst_ref_whole_prefix_read",
            what: "a WHOLE-AGGREGATE read of a sized prefix field through a \
                   slice-tail DST reference (`[u32]` and `str` tails), each next \
                   to a scalar prefix store through the same kind of reference",
            src: include_str!("bridge_corpus/fix_dst_ref_whole_prefix_read.rs"),
        },
        Case {
            // [TCG-DEREF-BASE-ADDR] The RAW-POINTER spelling of the two rows
            // around it (`*const` / `*mut H<[u32]>`), and the one whose `-O2` row
            // is observable: v2 printed `raw 0 6132459600 0 0` at `-O2` for LLVM's
            // `raw 1 77 3 42`. Reverted, both rows diverge.
            name: "fix_dst_raw_ptr_prefix_rw",
            what: "a scalar prefix store, a whole-prefix read and a discriminant \
                   read through a raw pointer to a slice-tail DST",
            src: include_str!("bridge_corpus/fix_dst_raw_ptr_prefix_rw.rs"),
        },
        Case {
            // [TCG-DEREF-BASE-ADDR] The other readers of the same prefix bytes:
            // a discriminant, an enum payload read after a prefix store, and a
            // whole prefix aggregate read into a SCALARIZED temp. Each walked a
            // `Deref`-led place from a slot-backed DST reference's OWN slot, over
            // the reference's `ScalarPair`, and printed garbage at the unpatched
            // tip (the header lists the three measured wrong answers).
            name: "fix_dst_ref_prefix_enum_and_nested_reads",
            what: "`discriminant((*h).e)`, `match (*h).e` after `(*h).r.hi = v`, \
                   and `Outer { inner: (*h).i }` through slice-tail DST \
                   references — every value a prefix byte a wrong base would \
                   misread",
            src: include_str!("bridge_corpus/fix_dst_ref_prefix_enum_and_nested_reads.rs"),
        },
        Case {
            // [TCG-DEREF-BASE-ADDR] The two discriminant arms the row above does
            // not reach: a TAG-ONLY enum and a RUNTIME-INDEXED enum element in a
            // DST prefix. On the unpatched tip this program PANICKED the backend
            // (`Field(2)` on the reference's two-field `ScalarPair`), and `tag`
            // alone was a silent `tag 30 30 30` for `tag 30 20 10`.
            name: "fix_dst_ref_prefix_tag_and_index_discriminant",
            what: "`match (*h).k` on a tag-only enum, `match (*h).arr[k]` with a \
                   runtime index, and a tag-only match after a prefix store, \
                   through slice-tail DST references",
            src: include_str!("bridge_corpus/fix_dst_ref_prefix_tag_and_index_discriminant.rs"),
        },
        Case {
            // [TCG-DEREF-BASE-ADDR] An aggregate enum PAYLOAD read from a DST
            // prefix. Reverted, the `-O0` row PANICS the backend (no `[TCG-…]`
            // tag, so `named_refusal` rejects it as a crash) and the `-O2` row
            // diverges (`payload 0 0` vs `payload 405 7`).
            name: "fix_dst_ref_prefix_enum_payload",
            what: "`match (*h).e { E::A(inner) => .. }` on `h: &H<[u8]>`, the \
                   payload an aggregate",
            src: include_str!("bridge_corpus/fix_dst_ref_prefix_enum_payload.rs"),
        },
        Case {
            // [TCG-DEREF-BASE-ADDR] A WIDE prefix field read into a SCALARIZED
            // temp (`W { k: 9, s: h.i.s }`) — the shape that reaches
            // `lower_memory_fat_leaf_use`'s deref-base branch. A silent wrong
            // LENGTH at the unpatched tip (`wrap 9 2 346` vs `wrap 9 6 21`, both
            // opt levels); expected to be an INCOMPLETE now. Reverted, both rows
            // diverge.
            name: "fix_dst_ref_fat_leaf_into_aggregate_refuses",
            what: "a `&[u8]` prefix field read through `h: &H<'_, [u32]>` into a \
                   temp that flows by value into an aggregate",
            src: include_str!("bridge_corpus/fix_dst_ref_fat_leaf_into_aggregate_refuses.rs"),
        },
        Case {
            // [TCG-DEREF-BASE-ADDR] CAPABILITY pin, the other direction: the same
            // three base-address sites must KEEP admitting a VTABLE-tailed struct
            // reference, whose one bound value IS the data lane. slice-assign v2
            // withdrew `set_s` by asking sizedness at the fat-leaf store. A
            // regression here is an INCOMPLETE row, which only `COMPILED_FLOOR`
            // can see — that is why the floor counts this row.
            name: "fix_dyn_tail_prefix_fat_leaf_rw",
            what: "a whole-prefix read, two WIDE prefix reads (one into a \
                   scalarized temp) and a WIDE prefix store through \
                   `t: &T<'_, dyn Er>` — LLVM-exact on the unpatched tip, and \
                   must stay so",
            src: include_str!("bridge_corpus/fix_dyn_tail_prefix_fat_leaf_rw.rs"),
        },
        Case {
            // [TCG-DEREF-BASE-ADDR] The fail-closed refuter's crash pin: a nested
            // prefix AGGREGATE read (`let c = h.s.i`) beside the prefix store this
            // lane admits. The walk-from-slot arm of `lower_memory_aggregate_use`
            // folded the `Deref`-led projection over the REFERENCE's layout and
            // PANICKED the backend. Reverted (no-`Deref` gate removed), the bridge
            // compile is a panic with no `[TCG-…]` tag, which `named_refusal`
            // turns into a hard failure. With the gate each row must MATCH LLVM
            // or refuse by name.
            name: "fix_dst_prefix_nested_aggregate_read_no_ice",
            what: "a store into a slice-tail DST's sized prefix followed by whole \
                   nested-aggregate reads of that prefix (`h.s.i`, `h.s`, an \
                   `i128` leaf), and the same read with no store",
            src: include_str!("bridge_corpus/fix_dst_prefix_nested_aggregate_read_no_ice.rs"),
        },
    ]
}

#[test]
fn fat_pointer_lane_fixtures_match_llvm() {
    let dylib = ensure_dylib_built();
    let mut compiled = 0usize;
    let mut incomplete: Vec<String> = Vec::new();
    for case in cases() {
        for opt in OPT_LEVELS {
            let dir = workdir(&format!("{}_{}", case.name, opt.len()));
            let oracle = compile_and_run(&dir, case.name, case.src, opt, None)
                .unwrap_or_else(|e| panic!("{} ({opt}): LLVM oracle failed: <<<{e}>>>", case.name));
            match compile_and_run(&dir, case.name, case.src, opt, Some(&dylib)) {
                Ok(bridge) => {
                    compiled += 1;
                    assert_eq!(
                        bridge.stdout, oracle.stdout,
                        "{} ({opt}): STDOUT differs from LLVM for {}",
                        case.name, case.what
                    );
                    assert_eq!(
                        bridge.code, oracle.code,
                        "{} ({opt}): exit code differs from LLVM for {}",
                        case.name, case.what
                    );
                }
                Err(stderr) => {
                    let tag = named_refusal(&stderr).unwrap_or_else(|| {
                        panic!(
                            "{} ({opt}): trust-cg failed WITHOUT a named [TCG-...] \
                             refusal, which is a crash rather than a fail-closed \
                             outcome: <<<{stderr}>>>",
                            case.name
                        )
                    });
                    incomplete.push(format!("{} ({opt}): {tag}", case.name));
                }
            }
            let _ = std::fs::remove_dir_all(&dir);
        }
    }
    let total = cases().len() * OPT_LEVELS.len();
    eprintln!("fat-pointer lane rows: {compiled}/{total} COMPILED+MATCHED");
    for row in &incomplete {
        eprintln!("  INCOMPLETE {row}");
    }
    assert!(
        compiled >= COMPILED_FLOOR,
        "only {compiled}/{total} rows compiled, below the committed floor of \
         {COMPILED_FLOOR}. A newly-refusing fixture is a coverage regression — \
         fix it rather than lowering the floor. Incomplete rows: {incomplete:?}"
    );
}
