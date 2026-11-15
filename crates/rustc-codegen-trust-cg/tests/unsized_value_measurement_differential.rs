#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: the UNSIZED-VALUE lane — `size_of_val` / `align_of_val`
// reached through a generic body, `<Chars>::as_str`, the `repr(transparent)`
// WIDE-POINTER CARRIER build, a SCALAR STORE into a slice-tail DST's SIZED
// PREFIX, and the iterator-adapter DESTINATION-IDENTITY gate.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHY THIS FILE EXISTS. Both fixtures pin lowerings whose whole content is a
// NUMBER the program never prints directly in a form a compile-time check could
// see: a size, an alignment, a remainder length. A wrong stride, a missed
// round-up, or a remainder measured in code points instead of bytes all COMPILE
// and all produce a plausible answer, so the only gate that can see them is a
// differential one against LLVM on the same source.
//
// THE GATE (the `fat_pointer_lane_differential.rs` doctrine):
//
//   * bridge output differs from LLVM        -> HARD FAIL (a miscompile).
//   * bridge FAILS CLOSED with a named
//     `[TCG-...]` diagnostic                 -> INCOMPLETE row, reported, not a
//                                               failure.
//   * bridge crashes / refuses with no named
//     diagnostic                             -> HARD FAIL.
//   * fewer than `COMPILED_FLOOR` rows
//     COMPILE                                -> HARD FAIL.
//
// NEVER lower the floor to make the gate pass: these fixtures are the only
// executable evidence that the `size_of_val` / `align_of_val` arms, the
// `Chars::as_str` widening, and the WIDE-POINTER DST addressing lane are RIGHT
// rather than merely accepted. A newly refusing row is a coverage
// regression to fix.
//
// THREE ROWS PIN A REVERTED MISCOMPILE, NOT JUST A REFUSAL. All measured at
// `-Copt-level=0`:
//
//   * `fix_dst_prefix_field_borrow` (2026-09-26) — `&raw mut (*p).a` through a
//     `*mut Hdr<[u8]>` COMPILED and SIGSEGV'd, and the `&mut (*p).a` spelling of
//     the same statement COMPILED and lost the store entirely (LLVM
//     `a=90 b=72623859790382856 c=65261`, the bridge `a=0 b=0 c=0`, and the shared
//     read returned `6130182576`). Reverting the lane therefore makes this row die
//     on a SIGNAL (`compile_and_run`'s `.code().expect(...)`) or diverge in stdout
//     — a HARD failure either way, never an INCOMPLETE.
//   * `fix_dyn_raw_ptr_reborrow` (2026-09-26) — refused with `memory-backed
//     aggregate assignment Rvalue::RawPtr`.
//   * `fix_dyn_tail_dst_prefix_field_borrow` (2026-09-27) — the VTABLE-metadata
//     twin, and the inverse pin: it COMPILED and MATCHED before the wide-deref-base
//     refusal existed, the refusal's first spelling (keyed on EVERY wide pointer)
//     WITHDREW it, and the narrowing restored it. It is here so that narrowing
//     cannot be undone silently. See `COMPILED_FLOOR`.
//
// That is the whole point of putting them here rather than in a bespoke target:
// the floor and the LLVM oracle make them impossible to quietly lose.
//
// WHAT IS NOT PINNED HERE, ON PURPOSE. No fixture pins a callee-keyed
// WITHDRAWAL of the `[TCG-STRIDE-ITER-METHOD]` refusal for a non-std callee
// (the draft fixture `fix_user_fn_takes_bridge_cursor.rs` did, and was
// removed): that guard's hazard is a LAYOUT disagreement, and a callee gate
// would also withdraw the refusal for a NON-LOCAL non-std callee -- a body
// LLVM compiled against std's real layout. The guard is withdrawn only by a
// layout certificate (`chars_cursor_layout_disagreement` for `Chars`,
// `slice_stride_iter_layout` for the slice stride iterators): it does not
// refuse a helper that receives a certified state, and it refuses one whose
// certificate fails. See the guard's "DELIBERATELY NOT GATED ON THE CALLEE"
// comment.
//
// MEASURED 2026-09-25 (backend built from this tree against the 2026-09-14
// stage1 `0cb693917a`, host aarch64-apple-darwin). Of the 6 rows:
//
//   * `fix_size_align_of_val` and `fix_chars_as_str` COMPILE and MATCH LLVM at
//     `-Copt-level=0` — the two rows the floor is taken over;
//   * the same two are INCOMPLETE at `-Copt-level=2` with `[TCG-PROOF-465]`, a
//     refusal that is not about this lane: `AArch64::CSet` (size/align) and
//     `AArch64::Csinc` (inside the O2-inlined
//     `core::str::validations::next_code_point`) have no opcode-proof mapping on
//     this host;
//   * `fix_user_as_str_not_intercepted` is INCOMPLETE at BOTH levels with
//     `[TCG-STRIDE-ITER-METHOD]`, which is its CORRECT outcome — it is the
//     miscompile pin, not a coverage row, and it must never be counted toward
//     the floor.
//
// The `-O2` gap is pre-existing and host-wide, not a property of these fixtures:
// as a CONTROL, the UNMODIFIED `lane_self-host-no-interception_{1,2}.rs` corpus
// fixtures refuse with the SAME `[TCG-PROOF-465]` on this host at `-O0` as well,
// which is why every stride/iterator harness in this tree is `_x86`. When the
// AArch64 opcode-proof inventory gains `CSet` and `Csinc` the two `-O2` coverage
// rows become live and the floor should RISE to 4 — never to 6.
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
/// Measured 2026-09-26 (4 cases x 2 levels = 8 rows): all FOUR `-O0` rows COMPILE
/// and MATCH; all four `-O2` rows are INCOMPLETE, so the floor is 4.
///
/// CORRECTION TO THE MEASURED BLOCK ABOVE, and read it before you trust a tag here.
/// This harness echoes only the classification TAG, and every `-O2` row now reports
/// the OUTER `[TCG-MIR-UNSUPPORTED]`, which hides the real bullets. Hand-compiled
/// with the replica invocation against the pack toolchain
/// (`pkg/store/trust/9192/bin/trustc`, backend built by the same `targo` that runs
/// these tests), the `-O2` cause is NOT `[TCG-PROOF-465]`:
///
///   fix_chars_as_str               `core::str::validations::next_code_point::
///                                   <slice::Iter<u8>>`, inlined at O2
///   fix_chars_cursor_crosses_to_std the same, PLUS `Rvalue::Ref aggregate source
///                                   is unsupported ADT: slice::Iter<u8>` / `: Chars`
///
/// Both are pre-existing O2 inlining gaps in the general lowering path, unrelated to
/// the `Chars` certificate (which is what makes the `-O0` rows compile). The
/// `[TCG-PROOF-465]` `CSet` class named in the block above is real — it is what
/// refuses a `Chars::size_hint` guest on the SELFHOST stage1 driver — but it is not
/// the reason these `-O2` rows are incomplete on this toolchain. Do not propagate
/// either claim without re-running the replica.
///
/// The floor is over COMPILED+MATCHED rows only, so it is indifferent to which
/// pre-existing gap refuses the `-O2` half.
///
/// It was 2 until the `Chars` LAYOUT-AGREEMENT CERTIFICATE landed. Two rows moved
/// from INCOMPLETE to COMPILED+MATCHED and that is why the floor rose:
/// `fix_chars_cursor_crosses_to_std` (new) and `fix_user_as_str_not_intercepted`,
/// whose own header already anticipated this — "if a later change makes the genuine
/// std `Chars::as_str` reachable THROUGH a user wrapper, this row may legitimately
/// start compiling — but only with the LLVM-matching `sentinel` hash. The MATCH
/// assertion is what must hold, not the refusal." It compiles and returns
/// `hash("SENTINEL")`, so its miscompile pin is INTACT and now stronger: the row is
/// live evidence rather than a refusal.
///
/// RAISED 4 -> 8 on 2026-09-27 with the WIDE-POINTER DST ADDRESSING lane (three
/// new fixtures, `fix_dst_prefix_field_borrow`, `fix_dyn_tail_dst_prefix_field_
/// borrow`, `fix_dyn_raw_ptr_reborrow`). Measured on FIVE separately-built
/// backends from the same tree at tip `fe9683845`, 7 cases x 2 levels = 14 rows:
///
///     pre-lane tip                                  5   and `fix_dst_prefix_
///                                                       field_borrow` @-O0
///                                                       DIVERGED from LLVM
///                                                       (a hard failure, which
///                                                       is the lane's own pin)
///     lane, wide-base refusal keyed on EVERY
///       wide pointer                                7   `fix_dyn_tail_dst_
///                                                       prefix_field_borrow`
///                                                       INCOMPLETE with
///                                                       [TCG-WIDEPTR-DEREF-BASE]
///     lane, refusal narrowed at the `&`/`&mut`
///       site only                                   7   same row INCOMPLETE,
///                                                       untagged `&raw` fall-
///                                                       through instead
///     lane, refusal narrowed at BOTH sites
///       (committed)                                 8
///
/// So this constant is the gate on that narrowing, and it is a TWO-SIDED gate:
/// reverting EITHER site drops the count to 7 and the assertion below fails by
/// name. The eight are, at `-Copt-level=0`: `fix_size_align_of_val`,
/// `fix_chars_as_str`, `fix_dst_prefix_field_borrow`,
/// `fix_dyn_tail_dst_prefix_field_borrow`, `fix_dyn_raw_ptr_reborrow`,
/// `fix_user_as_str_not_intercepted`, `fix_chars_cursor_crosses_to_std`; plus
/// `fix_dyn_raw_ptr_reborrow` at `-Copt-level=2`.
///
/// Every other `-O2` row is INCOMPLETE for a host-wide reason that is not this
/// lane's — see the correction above. Do not lower this number to make a gate
/// pass; a row that stops compiling is the regression.
///
/// RAISED 8 -> 11 on 2026-09-27 with the SLICE-ASSIGN lane (three fixtures:
/// `fix_wide_ptr_carrier_build`, `fix_dst_prefix_field_store`,
/// `fix_mem_take_is_not_iter_take`, each pinning one `library/alloc` census
/// refusal the lane closed). Measured by RUNNING this target — pack toolchain
/// `pkg/store/trust/9192` (`targo --unverified test --release --locked`), backend
/// built from the lane tree at tip `572c4ce34` plus the lane patch — 10 cases x 2
/// levels = 20 rows, 11 COMPILED+MATCHED: the eight above, unchanged, plus the
/// three new fixtures at `-Copt-level=0`. All nine `-Copt-level=2` INCOMPLETE rows
/// report the outer `[TCG-MIR-UNSUPPORTED]`; hand-compiled with the replica
/// invocation, each of the new three refuses exactly ONE function, its own
/// `main`, on the host-wide `[TCG-PROOF-465]` opcode-proof gap — not on anything
/// this lane touches.
const COMPILED_FLOOR: usize = 11;

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn workdir(stem: &str) -> PathBuf {
    let dir =
        std::env::temp_dir().join(format!("tcg_unsizedmeasure_{stem}_{}", std::process::id()));
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
            name: "fix_size_align_of_val",
            what: "`size_of_val` / `align_of_val` monomorphized inside a generic \
                   `T: ?Sized` body (the only shape that survives rustc's \
                   `LowerIntrinsics` const-fold) over a sized ADT with padding, \
                   `[u8]`, `[u32]` (stride 4), an ASCII and a multi-byte `str`, a \
                   `repr(transparent)` `CStr` whose metadata includes the nul, a \
                   ZST, and empty slice/str cursors",
            src: include_str!("bridge_corpus/fix_size_align_of_val.rs"),
        },
        Case {
            name: "fix_chars_as_str",
            what: "`<Chars>::as_str()` — the unyielded remainder of the bridge's \
                   own `{ ptr, end }` cursor — read before the first `next`, after \
                   every 1/2/3/4-byte advance, on an exhausted cursor, on a \
                   second cursor advanced to a different offset, and on an empty \
                   source",
            src: include_str!("bridge_corpus/fix_chars_as_str.rs"),
        },
        Case {
            name: "fix_dst_prefix_field_borrow",
            what: "a borrow of a SIZED PREFIX FIELD of a slice-tail DST through \
                   the DST's own `{ data, len }` wide pointer, in BOTH spellings \
                   (`&raw mut (*p).f` and `&mut (*p).f`) plus a shared read, with \
                   `repr(Rust)`-reordered field widths so declaration-order \
                   addressing disagrees with rustc's at every field",
            src: include_str!("bridge_corpus/fix_dst_prefix_field_borrow.rs"),
        },
        Case {
            // THE VTABLE-METADATA TWIN of the row above, and the floor row that
            // makes the wide-deref-base refusal's NARROWING un-revertable.
            // Measured 2026-09-27 at `-Copt-level=0`: the over-broad
            // (every-wide-pointer) refusal makes this row INCOMPLETE with
            // `[TCG-WIDEPTR-DEREF-BASE]`; the narrowed refusal COMPILES it and
            // MATCHES LLVM. That holds for EITHER half of the narrowing —
            // reverting only the `&`/`&mut` site or only the `&raw` site refuses
            // this same crate, because `fill_ref` and `fill_raw` are both in it.
            //
            // THE OTHER DIRECTIONS OF THE SAME HAZARD, probed separately on
            // 2026-09-27 and deliberately NOT in this fixture because each is
            // refused by a DIFFERENT, still-live guard in all three lanes (pre-lane
            // tip, over-broad refusal, narrowed refusal), so none of them is opened
            // by the narrowing:
            //
            //   * a WIDE SIBLING field of the same prefix (`s: &'static [u8]`
            //     beside `n: u64`), borrowed and assigned through the same wide
            //     base -> `Rvalue::Ref source projection is not scalar-bindable`,
            //     identically in all three lanes;
            //   * an ARRAY ELEMENT in the prefix (`&mut (*p).arr[2]`) -> refused,
            //     identically in all three;
            //   * an ENUM PAYLOAD in the prefix -> `Rvalue::Ref aggregate source is
            //     unsupported ADT`, identically in the pre-lane tip and the
            //     narrowed lane (the over-broad refusal MASKED it with
            //     `[TCG-WIDEPTR-DEREF-BASE]`, which is a diagnostic regression the
            //     narrowing also repairs);
            //   * the LENGTH-metadata class at the same offsets and both spellings
            //     -> the `fix_dst_prefix_field_borrow` row above, which is where
            //     the refusal that MUST fire is pinned.
            name: "fix_dyn_tail_dst_prefix_field_borrow",
            what: "a borrow of a SIZED PREFIX FIELD of a DST whose TAIL is `dyn \
                   Trait` — the `core::error::Request` `Tagged<dyn Erased>` shape \
                   — in BOTH spellings (`&mut (*p).f` and `&raw mut (*p).f`), at \
                   three `repr(Rust)`-reordered offsets, through an ENTRY-ARG base \
                   AND through a `&mut *p` local reborrow, with the `dyn` payload \
                   read back and DISPATCHED after every write so a prefix store \
                   that overran the tail cannot pass",
            src: include_str!("bridge_corpus/fix_dyn_tail_dst_prefix_field_borrow.rs"),
        },
        Case {
            name: "fix_dyn_raw_ptr_reborrow",
            what: "`&raw const (*r)` on a `&dyn Trait` into a slot-backed \
                   `*const dyn Trait` — the `Box::<dyn Error + Send + Sync>::\
                   into_raw` shape — dispatched afterwards through two distinct \
                   impls so a single-lane or lane-swapped store cannot pass",
            src: include_str!("bridge_corpus/fix_dyn_raw_ptr_reborrow.rs"),
        },
        Case {
            // The MISCOMPILE PIN for `lower_str_chars_as_str`'s identity
            // conjunct (`is_real_str_chars_as_str_callee`). Today both rows are
            // INCOMPLETE (`[TCG-STRIDE-ITER-METHOD]`, the correct fail-closed
            // outcome); delete the conjunct and they COMPILE and diverge from
            // LLVM, which this gate reports as a hard failure. Never counted
            // toward the floor.
            //
            // READ THIS BEFORE TRUSTING IT AS THE WHOLE PIN: this fixture's
            // `as_str` is LOCAL to the compiled crate, so the SELF-HOST rule
            // (`std_def_is_interceptable`, locality only) already refuses it —
            // the weaker, REFUTED crate-name conjunct passes this row too. The
            // row that separates the two lives in
            // `a_crate_named_hashbrown_does_not_get_its_as_str_intercepted`
            // below, which is the refuting witness itself.
            name: "fix_user_as_str_not_intercepted",
            what: "a USER `fn as_str(&Chars) -> &str` — the same method NAME and \
                   the same RECEIVER TYPE as `core::str::Chars::as_str`, a \
                   different definition site — whose body must NOT be replaced \
                   by the bridge's cursor remainder",
            src: include_str!("bridge_corpus/fix_user_as_str_not_intercepted.rs"),
        },
        Case {
            // The LAYOUT-AGREEMENT CERTIFICATE row (2026-09-26). A cursor the
            // BRIDGE wrote is read by STD's OWN bodies — `Chars::next_back`
            // (backward UTF-8 decode off the `end` word), the real trait-default
            // `Chars::try_fold` reached through `skip_while`/`find`, `Rev<Chars>`,
            // `clone`, and a by-value crossing of a function boundary. Every one
            // of those was refused by `[TCG-STRIDE-ITER-METHOD]` before
            // `chars_cursor_layout_disagreement` PROVED the two words are where
            // std keeps them; revert the certificate and this row stops compiling,
            // which drops the count below the floor and names this fixture.
            //
            // It is a MISCOMPILE pin as well as a coverage row: if a later change
            // moved the bridge's cursor words, or std's, while the certificate
            // still passed, these rows would COMPILE and DIVERGE — which this gate
            // reports as a hard failure, not an incomplete row.
            name: "fix_chars_cursor_crosses_to_std",
            what: "a bridge-written `{ ptr, end }` `Chars` cursor handed to STD's \
                   OWN bodies — `next_back`'s backward UTF-8 decode, the real \
                   `try_fold` behind `skip_while`/`find`, `Rev<Chars>::next`, \
                   `clone`, and a by-value function-boundary crossing — which are \
                   correct only if the bridge's two words are where std keeps them",
            src: include_str!("bridge_corpus/fix_chars_cursor_crosses_to_std.rs"),
        },
        Case {
            // Closes `memory-backed slice assignment Rvalue::Aggregate` — 4 of
            // `library/alloc`'s 37 failed roots on 2026-09-26. The fixture's
            // header carries the measurement and the mutation that breaks it.
            name: "fix_wide_ptr_carrier_build",
            what: "the `repr(transparent)` WIDE-POINTER CARRIER build \
                   (`Unique::<T>::new_unchecked`'s `Carrier { p: <wide ptr>, \
                   _m: PhantomData }`) for `[u8]` (stride 1), `[u32]` (stride 4) \
                   and a multi-byte `str` — every printed row carries the LENGTH \
                   lane, so a data-only store prints 0",
            src: include_str!("bridge_corpus/fix_wide_ptr_carrier_build.rs"),
        },
        Case {
            // Closes `memory slice assignment into projected place` — 1 of
            // `library/alloc`'s 37 failed roots on 2026-09-26
            // (`PolymorphicIter::<[MaybeUninit<char>]>::next_back`).
            name: "fix_dst_prefix_field_store",
            what: "a SCALAR STORE into the nested SIZED PREFIX of a slice-tail \
                   DST through its FAT reference (`(*h).r.end = v`, the \
                   `self.alive.end` write verbatim), read back through the \
                   ORIGINAL sized value alongside a tail element store, so a \
                   wrong base or a wrong offset changes stdout",
            src: include_str!("bridge_corpus/fix_dst_prefix_field_store.rs"),
        },
        Case {
            // Closes `iterator take inner argument is not memory-backed` — 1 of
            // `library/alloc`'s 37 failed roots on 2026-09-26
            // (`<alloc::vec::Drain<u8> as Drop>::drop`). Also the identity pin
            // for the structural-adapter dispatch: `mem::take` must reach its
            // real body, and `.take(n)` / `.skip(n)` must still be modelled.
            name: "fix_mem_take_is_not_iter_take",
            what: "`core::mem::take::<slice::Iter<u8>>` — the same item NAME, the \
                   same real-`core` provenance and a destination that resolves as \
                   an iterator chain, but NOT `Iterator::take` — lowered from its \
                   own body, with a genuine `.take(3)` / `.skip(2)` in the same \
                   program",
            src: include_str!("bridge_corpus/fix_mem_take_is_not_iter_take.rs"),
        },
    ]
}

#[test]
fn unsized_value_measurement_fixtures_match_llvm() {
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
    eprintln!("unsized-measurement lane rows: {compiled}/{total} COMPILED+MATCHED");
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

/// THE REFUTATION PIN, and the only in-tree row that can tell the identity guard
/// from the name-keyed one it replaced.
///
/// HISTORY. `lower_str_chars_as_str` was first landed with
/// `is_std_collection_method_callee` as its provenance conjunct — locality plus
/// `tcx.crate_name(krate) in {std, core, alloc, hashbrown}`, a STRING COMPARE
/// against a name the person compiling chooses. An adversarial lane refuted it by
/// compiling this exact library as an rlib with `--crate-name hashbrown`: the
/// guard was fully present, and the program still returned the bridge's cursor
/// remainder instead of the library's real body. Measured (FNV as below):
///
///   LLVM oracle                    hash("SENTINEL")  = 15763585847121849335
///   base, unpatched                REFUSED, `[TCG-STRIDE-ITER-METHOD]`
///   name-keyed conjunct            hash("bcdef")     = 11585393754820217191
///   identity conjunct (this tree)  REFUSED, `[TCG-STRIDE-ITER-METHOD]`
///
/// WHY IT CANNOT BE A `bridge_corpus` FIXTURE. The corpus rows are single files
/// compiled on their own; this witness needs a SECOND crate, compiled first, with
/// a chosen `--crate-name`. `fix_user_as_str_not_intercepted.rs` is the closest a
/// single file gets, and it is NOT a substitute: its `as_str` is LOCAL, so
/// locality alone refuses it and the refuted conjunct passes it too.
///
/// THE GATE. LLVM is the oracle. The bridge may REFUSE with a named `[TCG-...]`
/// diagnostic (today's outcome, fail-closed and correct) or COMPILE and MATCH
/// LLVM. Compiling and DIVERGING is the miscompile and fails hard — that is what
/// deleting the identity conjunct produces.
#[test]
fn a_crate_named_hashbrown_does_not_get_its_as_str_intercepted() {
    const WITNESS_LIB: &str = "#[inline(never)]\n\
                               pub fn as_str<'a>(_it: &core::str::Chars<'a>) -> &'a str {\n\
                               \x20   \"SENTINEL\"\n\
                               }\n";
    const WITNESS_MAIN: &str = "extern crate hashbrown;\n\
        fn hash(s: &str) -> u64 {\n\
        \x20   let mut h: u64 = 1469598103934665603;\n\
        \x20   for b in s.as_bytes() {\n\
        \x20       h = (h ^ *b as u64).wrapping_mul(1099511628211);\n\
        \x20   }\n\
        \x20   h\n\
        }\n\
        fn main() {\n\
        \x20   let s = \"abcdef\";\n\
        \x20   let mut it = s.chars();\n\
        \x20   it.next();\n\
        \x20   println!(\"witness   hash={}\", hash(hashbrown::as_str(&it)));\n\
        \x20   println!(\"sentinel  hash={}\", hash(\"SENTINEL\"));\n\
        \x20   println!(\"remainder hash={}\", hash(\"bcdef\"));\n\
        }\n";

    let dylib = ensure_dylib_built();
    let dir = workdir("hashbrown_witness");

    // The witness library: an ORDINARY crate, named `hashbrown` on the command
    // line and nothing more.
    let lib_src = dir.join("fake.rs");
    std::fs::write(&lib_src, WITNESS_LIB).expect("write witness library");
    let rlib = dir.join("libhashbrown.rlib");
    let mut lib_cmd = toolchain_support::rustc_command();
    lib_cmd.args(["--crate-type", "rlib", "--crate-name", "hashbrown"]);
    lib_cmd.args(["-Cpanic=abort", "-Copt-level=0"]);
    lib_cmd.arg("-o").arg(&rlib).arg(&lib_src);
    let lib_out = lib_cmd.output().expect("spawn the compiler");
    assert!(
        lib_out.status.success(),
        "the `--crate-name hashbrown` witness library did not build: <<<{}>>>",
        String::from_utf8_lossy(&lib_out.stderr)
    );

    let main_src = dir.join("witness_main.rs");
    std::fs::write(&main_src, WITNESS_MAIN).expect("write witness main");

    let compile_main = |backend: Option<&Path>, out: &Path| -> Result<Run, String> {
        let mut cmd = toolchain_support::rustc_command();
        cmd.args(["--crate-type", "bin", "-Cpanic=abort", "-Ccodegen-units=1"]);
        cmd.arg("-Copt-level=0");
        let mut extern_arg = std::ffi::OsString::from("hashbrown=");
        extern_arg.push(&rlib);
        cmd.arg("--extern").arg(extern_arg);
        cmd.arg("-L").arg(&dir);
        if let Some(dylib) = backend {
            let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
            backend_arg.push(dylib);
            cmd.arg(backend_arg);
        }
        cmd.arg("-o").arg(out).arg(&main_src);
        let output = cmd.output().expect("spawn the compiler");
        if !output.status.success() {
            return Err(String::from_utf8_lossy(&output.stderr).into_owned());
        }
        let run = Command::new(out).output().expect("run compiled binary");
        Ok(Run {
            code: run
                .status
                .code()
                .expect("compiled program exited via signal, not an exit code"),
            stdout: String::from_utf8_lossy(&run.stdout).into_owned(),
        })
    };

    let oracle = compile_main(None, &dir.join("witness_llvm"))
        .unwrap_or_else(|e| panic!("LLVM oracle failed on the witness: <<<{e}>>>"));
    assert!(
        oracle
            .stdout
            .contains("witness   hash=15763585847121849335"),
        "the LLVM oracle did not return the witness library's own body; this test \
         is measuring something else. stdout: <<<{}>>>",
        oracle.stdout
    );

    match compile_main(Some(&dylib), &dir.join("witness_bridge")) {
        Ok(bridge) => {
            assert_eq!(
                bridge.stdout, oracle.stdout,
                "A crate merely NAMED `hashbrown` had its own `as_str` body \
                 REPLACED by the bridge's `Chars` cursor remainder. This is the \
                 refuted name-keyed guard, not a new bug: restore \
                 `is_real_str_chars_as_str_callee` in `lower_str_chars_as_str` \
                 rather than relaxing this assertion."
            );
            assert_eq!(
                bridge.code, oracle.code,
                "witness exit code differs from LLVM"
            );
            eprintln!("hashbrown witness: COMPILED and MATCHED LLVM");
        }
        Err(stderr) => {
            let tag = named_refusal(&stderr).unwrap_or_else(|| {
                panic!(
                    "the witness was refused WITHOUT a named [TCG-...] diagnostic, \
                     which is a crash rather than a fail-closed outcome: <<<{stderr}>>>"
                )
            });
            eprintln!("hashbrown witness: INCOMPLETE {tag} (fail-closed, correct)");
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// How a compiled program ended: an exit CODE, or the SIGNAL that killed it. A
/// `panic=abort` panic is `SIGABRT` under LLVM (`abort()`), and the bridge's
/// overflow trap must end the same way — so a pin compares the pair, and a
/// program LLVM aborts is a legitimate expected outcome here (the shared
/// `compile_and_run` above treats any signal as a harness failure).
#[derive(Debug, PartialEq, Eq)]
struct Ending {
    code: Option<i32>,
    signal: Option<i32>,
    stdout: String,
}

/// Compile `src` with the shared flags plus `flags`, run it, and report how it
/// ended. `backend = Some(..)` compiles with the bridge; `no_certs` then also
/// passes the `no-proof-certs` knob (the census default lane) — never to LLVM.
/// `Err` carries the compiler's stderr.
fn compile_and_run_ending(
    dir: &Path,
    name: &str,
    src: &str,
    flags: &[&str],
    backend: Option<&Path>,
    no_certs: bool,
) -> Result<Ending, String> {
    use std::os::unix::process::ExitStatusExt;
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(if backend.is_some() {
        format!("{name}_bridge")
    } else {
        format!("{name}_llvm")
    });
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin", "-Cpanic=abort", "-Ccodegen-units=1"]);
    cmd.args(flags);
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
        if no_certs {
            cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
        }
    }
    cmd.arg("-o").arg(&bin).arg(&src_path);
    let output = cmd.output().expect("spawn the compiler");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    let run = Command::new(&bin).output().expect("run compiled binary");
    Ok(Ending {
        code: run.status.code(),
        signal: run.status.signal(),
        stdout: String::from_utf8_lossy(&run.stdout).into_owned(),
    })
}

/// A MISCOMPILE pin of the `.sum()` / `.product()` lane: one fixture, compiled with
/// its own flags. The bridge must either REFUSE it with a named `[TCG-...]`
/// diagnostic or compile a binary that ends EXACTLY as LLVM's does (stdout, exit
/// code, killing signal). Compiling into a binary that diverges is what each row
/// exists to catch.
struct ReductionPin {
    name: &'static str,
    src: &'static str,
    flags: &'static [&'static str],
    /// Run the bridge WITHOUT proof certificates: a multiply-overflow check emits
    /// `AArch64::CSet`, which this host's opcode-proof inventory cannot map
    /// (`[TCG-PROOF-465]`, pre-existing and not this lane's), and that refusal
    /// would mask a mutation of the guard the row pins.
    no_certs: bool,
    guards: &'static str,
}

/// The `sum`/`product` reduction pins (2026-09-27). Two families:
///
///   * IMPL IDENTITY (`std_sum_product_arith`): the modeled loop takes its operator
///     from the `Sum`/`Product` impl rustc SELECTED — saturating for `Saturating`,
///     wrapping for `Wrapping`, overflow-CHECKED for a primitive (a panic under
///     `-Coverflow-checks`, a wrap without) — instead of from the accumulator's
///     scalar type, which on the base made every one of them a wrapping op;
///   * REVERSED ORDER (`rfold_reduction_order_blind`): at `-O2`/`-O3` a
///     `.rev()...sum()` is an `rfold`, which visits the items BACK TO FRONT; the
///     forward-drive shortcut is kept only where the order is unobservable.
///
/// Measured 2026-09-27 on this tree's backend (the lane commit has the numbers):
/// reverting the impl-identity arithmetic makes the `Saturating` product and the
/// primitive overflow rows DIVERGE (base: `0` for `u64::MAX`; `3`, exit 0, for an
/// abort); reverting the order fix makes the back-to-front rows ABORT where LLVM
/// prints (checked step, forward drive), and the effect-order row print its
/// closure's effects FRONT TO BACK.
fn reduction_pins() -> Vec<ReductionPin> {
    const CHECKED_O2: &[&str] = &["-Copt-level=2", "-Coverflow-checks=on"];
    const CHECKED_O3: &[&str] = &["-Copt-level=3", "-Coverflow-checks=on"];
    const DEBUG_O3: &[&str] = &["-Copt-level=3", "-Cdebug-assertions=on"];
    let sat_product = include_str!("bridge_corpus/fix_saturating_product_std_impl.rs");
    let back_to_front = include_str!("bridge_corpus/fix_rfold_checked_sum_back_to_front.rs");
    let overflows_back =
        include_str!("bridge_corpus/fix_rfold_checked_sum_overflows_back_to_front.rs");
    let product_back = include_str!("bridge_corpus/fix_rfold_checked_product_back_to_front.rs");
    let effect_order = include_str!("bridge_corpus/fix_rfold_map_effect_order.rs");
    let overflow_sum = include_str!("bridge_corpus/fix_primitive_sum_overflow_checked.rs");
    vec![
        ReductionPin {
            name: "fix_saturating_product_std_impl",
            src: sat_product,
            flags: &["-Copt-level=0"],
            no_certs: true,
            guards: "the unsigned saturating MUL of `emit_std_reduction_step` (the base \
                     printed `0` for `u64::MAX`)",
        },
        ReductionPin {
            name: "fix_primitive_sum_overflow_checked_o0",
            src: overflow_sum,
            flags: &["-Copt-level=0"],
            no_certs: true,
            guards: "the overflow-CHECKED integer step (`-O0` enables overflow checks; \
                     the base wrapped, printed `3` and exited 0 where LLVM aborts)",
        },
        ReductionPin {
            name: "fix_primitive_sum_overflow_unchecked_o0",
            src: overflow_sum,
            flags: &["-Copt-level=0", "-Coverflow-checks=off"],
            no_certs: true,
            guards: "the checked step's `-Coverflow-checks=off` arm, which must WRAP \
                     like LLVM rather than abort",
        },
        ReductionPin {
            name: "fix_rfold_checked_sum_back_to_front_o2",
            src: back_to_front,
            flags: CHECKED_O2,
            no_certs: true,
            guards: "`rfold_reduction_order_blind`'s ARITHMETIC conjunct (a checked sum \
                     driven forward aborts on `MAX + 1`)",
        },
        ReductionPin {
            name: "fix_rfold_checked_sum_back_to_front_o3",
            src: back_to_front,
            flags: CHECKED_O3,
            no_certs: true,
            guards: "the same, at `-O3`",
        },
        ReductionPin {
            name: "fix_rfold_checked_sum_back_to_front_debug_o3",
            src: back_to_front,
            flags: DEBUG_O3,
            no_certs: true,
            guards: "the same, with overflow checks enabled by `-Cdebug-assertions=on`",
        },
        ReductionPin {
            name: "fix_rfold_checked_sum_overflows_back_to_front_o3",
            src: overflows_back,
            flags: CHECKED_O3,
            no_certs: true,
            guards: "the back-to-front drive's OTHER direction: LLVM aborts, a forward \
                     drive prints `i64::MAX` (the base did, in every lane)",
        },
        ReductionPin {
            name: "fix_rfold_checked_product_back_to_front_o3",
            src: product_back,
            flags: CHECKED_O3,
            no_certs: true,
            guards: "the ARITHMETIC conjunct for `product` (a checked product driven \
                     forward aborts on `2 * (MAX / 2 + 1)` before the `0` arrives)",
        },
        ReductionPin {
            name: "fix_rfold_map_effect_order_o2",
            src: effect_order,
            flags: &["-Copt-level=2"],
            no_certs: true,
            guards: "`rfold_reduction_order_blind`'s USER-CODE conjunct (a forward \
                     drive calls the `map`/`filter` closure front to back)",
        },
        ReductionPin {
            name: "fix_rfold_map_effect_order_o3",
            src: effect_order,
            flags: &["-Copt-level=3"],
            no_certs: true,
            guards: "the same, at `-O3`",
        },
    ]
}

/// Of the `reduction_pins()` rows, at least this many must COMPILE (and, by the
/// assertions, MATCH LLVM) — so that the gate cannot pass by every row refusing.
/// Measured 2026-09-27 with this target on the pack toolchain; see the lane
/// commit. Do not lower it to make the gate pass.
const REDUCTION_PIN_COMPILED_FLOOR: usize = 8;

#[test]
fn sum_product_reduction_pins_hold() {
    let dylib = ensure_dylib_built();
    let mut compiled = 0usize;
    let mut refused: Vec<String> = Vec::new();
    let pins = reduction_pins();
    for pin in &pins {
        let dir = workdir(&format!("pin_{}", pin.name));
        let oracle = compile_and_run_ending(&dir, pin.name, pin.src, pin.flags, None, false)
            .unwrap_or_else(|e| panic!("{}: LLVM oracle failed: <<<{e}>>>", pin.name));
        match compile_and_run_ending(
            &dir,
            pin.name,
            pin.src,
            pin.flags,
            Some(&dylib),
            pin.no_certs,
        ) {
            Ok(bridge) => {
                assert_eq!(
                    bridge, oracle,
                    "{} ({:?}): the bridge COMPILED this pin and it ends differently \
                     from LLVM. The guard it pins — {} — has been lost.",
                    pin.name, pin.flags, pin.guards
                );
                compiled += 1;
                eprintln!(
                    "pin {} ({:?}): COMPILED and MATCHED LLVM {oracle:?}",
                    pin.name, pin.flags
                );
            }
            Err(stderr) => {
                let tag = named_refusal(&stderr).unwrap_or_else(|| {
                    panic!(
                        "{} ({:?}): refused WITHOUT a named [TCG-...] diagnostic, which \
                         is a crash rather than a fail-closed outcome: <<<{stderr}>>>",
                        pin.name, pin.flags
                    )
                });
                eprintln!(
                    "pin {} ({:?}): REFUSED {tag} (fail-closed)",
                    pin.name, pin.flags
                );
                refused.push(format!("{} {:?}: {tag}", pin.name, pin.flags));
            }
        }
        let _ = std::fs::remove_dir_all(&dir);
    }
    assert!(
        compiled >= REDUCTION_PIN_COMPILED_FLOOR,
        "only {compiled}/{} reduction pins compiled, below the committed floor of \
         {REDUCTION_PIN_COMPILED_FLOOR}: a pin that stops compiling proves nothing \
         about the guard it names. Refused: {refused:?}",
        pins.len()
    );
}
