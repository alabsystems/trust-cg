#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a FAT POINTER AS A MEMORY LEAF — `&dyn Trait`
// (`{data, vtable}`) and `&[T]` / `&str` (`{data, len}`) held inside an
// aggregate, a closure environment, a tuple or an `Option`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT THIS PINS. The memory-aggregate leaf model used to admit only SINGLE
// SCALARS (plus a `&[T]`/`&str` special case), so every aggregate carrying a
// `&dyn Trait` field failed closed with `Ty::dyn …` — measured as the second
// largest refusal class of a `library/core` census (66 roots). A `&dyn Trait`
// is a `BackendRepr::ScalarPair` exactly like a slice fat pointer, differing
// only in what the second lane MEANS, so the leaf model now admits BOTH
// metadata kinds and places each lane at the offset `tcx.layout_of` reports
// (`fat_ptr_metadata_offset`) rather than at an assumed `+ pointer_size`.
//
// Each program below is compiled BY THE BRIDGE and BY LLVM at the SAME
// optimization level, run, and compared. A dropped vtable lane, a truncated
// fat pointer, a lane written at the wrong offset, or a torn (data-without-
// metadata) read shows up as different STDOUT or a different exit code.
//
// WHY STDOUT AND EXIT CODE ONLY: panic text legitimately differs between the
// two backends (panic machinery, formatting of the location), so the
// comparison is deliberately restricted to the values a correct program
// prints and the status it exits with.
//
// HOST-NATIVE: no `--target` is passed, so this runs on whatever host builds
// the crate (unlike the x86-pinned differentials, which need an x86 host and
// its rust-std). A single codegen unit keeps every function in one object, as
// the other differentials do.
//
// READ THIS BEFORE TRUSTING A GREEN OR A RED (measured 2026-09-26 on this host —
// aarch64-apple-darwin — with the backend built from this tree against the
// 2026-09-14 stage1 `0cb693917a`). This harness HARD-FAILS on any refusal, and
// ALL SEVEN ORIGINAL cases below refuse with `[TCG-PROOF-465]` at
// `-Copt-level=0` — `no proof mapping for opcode CSet`, measured one by one —
// because each of their impls computes `self.0 * self.0` / `self.0 * 3 + 1` and
// the multiply's overflow check lowers to an `AArch64::CSet` this host's
// opcode-proof inventory does not carry. (At `-Copt-level=2` six of the seven do;
// `dyn_leaf_local_addr` compiles, and `dyn_leaf_struct_field` refuses on `Csel`
// rather than `CSet`.) That is a HOST-WIDE proof-inventory
// gap, NOT a property of the fat-leaf lane — the same refusal is what makes nine
// unrelated differential targets red, and hand-compiling any of those corpus
// files with the bridge reproduces it with no fat-pointer diagnostic at all. Do
// NOT read this target's red as evidence about the leaf model, and do NOT delete
// or weaken a case to clear it: the fix is the opcode-proof inventory.
//
// The FIRST FOUR cases are ordered first deliberately, and are ARITHMETIC-FREE by
// construction (every method returns a constant or a plain field read), so they
// COMPILE and RUN on this host at BOTH opt levels today and the harness reaches
// them before the `CSet` wall. They are the executable evidence for the
// 2026-09-26 dyn/vtable rung, each pinning a shape that FAILED CLOSED on the
// unpatched tree:
//   * `dyn_supertrait_vptr_upcast` — `VtblEntry::TraitVPtr` emission plus the
//     non-prefix upcast's run-time vptr load, at the MINIMAL shape (one slot, one
//     level) that mirrors the `library/alloc` root this cleared
//     (`core::error::Error: Debug + Display`);
//   * `dyn_supertrait_vptr_nested` — the same lane at its widest: TWO vptr slots,
//     a RECURSIVELY emitted nested table, a chained upcast through both, and an
//     address-taken `&dyn` source;
//   * `dyn_fat_ptr_narrowed_to_thin` — `*mut dyn Trait as *mut ()`;
//   * `box_slice_default_carrier_unsize` — `Unique<[T; 0]> -> Unique<[T]>`.
// Revert any one of those backend changes and its case is the FIRST panic this
// target reports, with `trust-cg REFUSED` and the named diagnostic — which is
// exactly how it is distinguished from the pre-existing `CSet` wall.
//
// Three more arithmetic-free cases follow them, for the 2026-09-27 `Box<dyn Error>`
// rung of the `library/alloc` census, and sit before the `CSet` wall for the
// same reason:
//   * `adt_pointer_unsize_into_slot` — an ADT `Unsize` (`Box`'s shape, not
//     intercepted) into a slot: `adt_pointer_unsize_plan`. Reverted, it refuses
//     with `memory-backed aggregate assignment Rvalue::Cast [cast
//     PointerCoercion(Unsize, Implicit) ...]`;
//   * `box_dyn_drop_heap_layout` — dropping a `Box<dyn Trait>` under a heap check:
//     `lower_deref_field_dyn_fat_ptr_transmute`, `is_box_dyn_glue_payload_drop`
//     and the `dyn` arm of `lower_size_align_of_val_intrinsic`. Reverted, the
//     shim refuses with `[TCG-POINTEE-DYN-VALUE]` (or, with only the transmute
//     and the admission in place, `Box::drop` with `[TCG-SIZE-OF-VAL-UNSIZED]`);
//   * `dyn_raw_ptr_layout` — `Box::drop`'s un-inlined `-O0` opening
//     (`lower_dyn_fat_to_fat_ptr_cast`, then the same `dyn` `size_of_val` arm).
//     Reverted, `size_of_boxed` refuses with `[TCG-POINTEE-DYN-VALUE]` at the
//     `PtrToPtr`, or `size_raw` with `[TCG-SIZE-OF-VAL-UNSIZED]`.

use std::path::{Path, PathBuf};
use std::process::Command;

/// Every case is run at BOTH of these. `-O0` exercises the un-inlined shape
/// (real `&dyn` parameters, real aggregate constructions); `-O2` exercises the
/// shape after rustc's inliner has folded the aggregates and re-materialized
/// the fat pointers, which is where a lane-offset mistake usually surfaces.
const OPT_LEVELS: &[&str] = &["-Copt-level=0", "-Copt-level=2"];

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_dynleaf_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

struct Run {
    code: i32,
    stdout: String,
}

/// Compile `src` (with the bridge when `backend` is `Some`), run it, and return
/// its exit code + stdout. `Err` carries the compiler's stderr tail: the bridge
/// FAILS CLOSED on a shape it cannot lower, which is a legitimate outcome for
/// the backend in general but a test failure here, since these programs are
/// exactly the shapes this lane added.
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
        return Err(String::from_utf8_lossy(&output.stderr)
            .lines()
            .rev()
            .take(10)
            .collect::<Vec<_>>()
            .join(" | "));
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

struct Case {
    name: &'static str,
    what: &'static str,
    src: &'static str,
}

fn corpus() -> Vec<Case> {
    vec![
        Case {
            name: "dyn_supertrait_vptr_upcast",
            what: "a vtable carrying a SUPERTRAIT VPTR slot (`trait Sub: Alpha + \
                   Beta`, so one supertrait rides the single-inheritance prefix \
                   and the OTHER needs a `VtblEntry::TraitVPtr` pointer to its own \
                   table) plus BOTH upcast directions: the NON-PREFIX `&dyn Sub -> \
                   &dyn Beta`, which must LOAD the new vtable out of that slot at \
                   the index `supertrait_vtable_slot` names, and the PREFIX `&dyn \
                   Sub -> &dyn Alpha`, which must keep taking the identity copy. \
                   Each impl returns a distinct constant, so a slot read at the \
                   wrong index, a nested table that was never emitted, or a load \
                   wired onto the prefix case too all print a different number",
            src: include_str!("bridge_corpus/dyn_supertrait_vptr_upcast.rs"),
        },
        Case {
            name: "dyn_supertrait_vptr_nested",
            what: "the supertrait-vptr lane at its WIDEST: `Top: Mid + A3` over \
                   `Mid: A1 + A2`, so the `<Q as Top>` vtable carries a vptr slot \
                   AND the `<Q as Mid>` table it points into carries a second one \
                   (emission is recursive, and the depth cap has to be above 1 for \
                   this to compile at all). Covers what the one-slot case cannot \
                   see: two slots (so index arithmetic that happens to land on the \
                   only slot is caught), a CHAINED upcast `Top -> Mid -> A2` that \
                   must agree with the direct `Top -> A2`, the PREFIX upcasts that \
                   must still take the identity copy, and an upcast whose source is \
                   an ADDRESS-TAKEN `&dyn` (halves read out of a memory slot, not \
                   out of projected SSA bindings)",
            src: include_str!("bridge_corpus/dyn_supertrait_vptr_nested.rs"),
        },
        Case {
            name: "dyn_fat_ptr_narrowed_to_thin",
            what: "`*mut dyn Trait as *mut ()` — the VTABLE-metadata twin of the \
                   `*const [T] as *const T` narrowing, which is in the MIR of \
                   `NonNull::<dyn Trait>::new_unchecked` at every opt level via \
                   `assert_unsafe_precondition!`'s null probe. The thin result must \
                   be the DATA lane (reading the VTABLE lane prints a code address \
                   where `42` belongs), the address must be the object base (field \
                   `b` reads `99`, not `42`), and the SOURCE's two lanes must \
                   survive the transmute into `NonNull<dyn Trait>` that follows",
            src: include_str!("bridge_corpus/dyn_fat_ptr_narrowed_to_thin.rs"),
        },
        Case {
            name: "box_slice_default_carrier_unsize",
            what: "`Unique<[T; 0]> -> Unique<[T]>` — a `PointerCoercion::Unsize` \
                   whose destination is a `#[repr(transparent)]` CARRIER of a \
                   `{data, len}` fat pointer rather than the bare pointer, which is \
                   the whole body of `<Box<[T]> as Default>::default`. Two element \
                   widths, so a length scaled by `size_of::<T>()` or taken from the \
                   destination type rather than the source array diverges on at \
                   least one row",
            src: include_str!("bridge_corpus/box_slice_default_carrier_unsize.rs"),
        },
        Case {
            name: "adt_pointer_unsize_into_slot",
            what: "an `Unsize` coercion between two instances of ONE pointer-wrapping \
                   ADT into a slot-backed destination — `Box`'s exact shape (a \
                   `NonNull<T>` beside a 1-ZST, `CoerceUnsized`, NOT intercepted), \
                   which is what `Box` is inside `library/alloc`. Sized -> `dyn` \
                   (a NEW vtable), `dyn A + Send + Sync -> dyn A` (the OLD vtable \
                   kept), the NON-PREFIX upcast (vtable LOADED from the vptr slot), \
                   the PREFIX upcast (kept), and `[u8; 3] -> [u8]` (length = the \
                   source `N`). Every row names the method actually dispatched or \
                   the length/byte actually read, so a lane at the wrong offset, a \
                   kept vtable that should have been loaded (or the reverse) or a \
                   wrong length prints a different value",
            src: include_str!("bridge_corpus/adt_pointer_unsize_into_slot.rs"),
        },
        Case {
            name: "box_dyn_drop_heap_layout",
            what: "DROPPING an owning `Box<dyn Trait>` — rustc's \
                   `drop_in_place::<Box<dyn Trait>>` shim (the box pointer read \
                   through `&mut Box`, the payload's virtual drop, NULL-slot skip) \
                   and `<Box<dyn Trait> as Drop>::drop` (`Layout::for_value_raw` = \
                   the vtable's SIZE and ALIGN words) — under a recording \
                   `#[global_allocator]`: a 32/8 payload with a user `Drop`, a \
                   `repr(align(32))` 64/32 payload with no drop glue, and a ZST that \
                   must NOT be freed. A wrong size/align would corrupt a real \
                   allocator silently; here it prints",
            src: include_str!("bridge_corpus/box_dyn_drop_heap_layout.rs"),
        },
        Case {
            name: "dyn_raw_ptr_layout",
            what: "the `*mut dyn Trait` statements `<Box<dyn Trait> as Drop>::drop` \
                   makes at `-O0` inside `library/alloc` — `Unique::as_ptr`, the \
                   fat -> FAT `*mut dyn -> *const dyn` `PtrToPtr`, and \
                   `Layout::for_value_raw` — plus `size_of_val_raw` / \
                   `align_of_val_raw` of a bare `dyn Trait`. Two payloads that \
                   differ in BOTH size and alignment (24/8 and 16/16), so a vtable \
                   slot off by one, a size/align swap or a constant answer prints a \
                   different number (plus two identity-`Unsize` controls \
                   dispatched through the cast pointer)",
            src: include_str!("bridge_corpus/dyn_raw_ptr_layout.rs"),
        },
        Case {
            name: "dyn_leaf_closure_upvar",
            what: "a closure capturing a `&dyn Trait` upvar — by value and, one \
                   level up, BY REFERENCE (`&&dyn Trait`, the shape \
                   `core::fmt::builders::DebugTuple::field`'s `and_then` closure \
                   carries). The env is a memory aggregate with a fat leaf, and the \
                   `&env` parameter is typed as a thin pointer to its lane tuple",
            src: include_str!("bridge_corpus/dyn_leaf_closure_upvar.rs"),
        },
        Case {
            name: "dyn_leaf_struct_field",
            what: "a struct holding a `&dyn Trait` FIELD, constructed, passed by \
                   value, returned, and read back both from the owned local and \
                   THROUGH a `&Holder` reference (the `core::fmt::Formatter { buf: \
                   &mut dyn Write }` shape). A dropped vtable lane dispatches the \
                   wrong impl",
            src: include_str!("bridge_corpus/dyn_leaf_struct_field.rs"),
        },
        Case {
            name: "dyn_leaf_option_match",
            what: "`Option<&dyn Trait>` constructed, passed, matched, and mapped \
                   through a closure (the `<Option<&dyn Error>>::and_then` / \
                   `Error::source` shape). The `None` niche lives in the data half \
                   of the fat pointer",
            src: include_str!("bridge_corpus/dyn_leaf_option_match.rs"),
        },
        Case {
            name: "dyn_leaf_local_addr",
            what: "an ADDRESS-TAKEN local `&dyn Trait` (`&d`, whose referent must \
                   occupy a real 16-byte slot the unsize mirrors both halves into) \
                   and a `&&dyn Trait` passed as a real function argument",
            src: include_str!("bridge_corpus/dyn_leaf_local_addr.rs"),
        },
        Case {
            name: "dyn_leaf_fat_in_aggregate",
            what: "BOTH metadata kinds in one aggregate and one tuple — `&dyn \
                   Trait` (`{data, vtable}`) beside `&[i64]` and `&str` \
                   (`{data, len}`) — stored into and reloaded from a struct and a \
                   tuple, so each lane must land at the offset rustc's layout \
                   reports",
            src: include_str!("bridge_corpus/dyn_leaf_fat_in_aggregate.rs"),
        },
        Case {
            name: "raw_ptr_to_dyn_fat_ptr",
            what: "a THIN raw pointer / `NonNull` whose POINTEE is ITSELF a \
                   `&dyn Trait` fat pointer (`NonNull<&dyn Debug>`, \
                   `*mut &dyn Debug`, `slice::Iter<&dyn Debug>`) — deref + \
                   dispatch, `.add(1)` stride, `as_ref`/`from_ref`/`PartialEq`, \
                   slice iteration, and a `&dyn` beside a `&[T]` and a `&str` \
                   with scalars after each. `&&dyn Trait` already typed this \
                   pointee as the real 16-byte two-lane image; the RAW-pointer \
                   arm never asked, so a dropped vtable, an 8-byte stride, or a \
                   lane at an assumed `+8` all show up as different STDOUT",
            src: include_str!("bridge_corpus/raw_ptr_to_dyn_fat_ptr.rs"),
        },
        Case {
            name: "fat_leaf_slice_str_no_dyn",
            what: "the SAME `{data, len}` leaf shape with NO `&dyn` field beside \
                   it — the isolation the case above lacks. A `&dyn` field makes \
                   the by-reference pointee FLATTENING fail (there is no `dyn` \
                   scalar mapping) and so forces the whole aggregate onto the \
                   rustc-layout byte path; without one the flattening succeeded \
                   and gave each `&[T]` / `&str` field ONE lane, leaving every \
                   later field 8 bytes off",
            src: include_str!("bridge_corpus/fat_leaf_slice_str_no_dyn.rs"),
        },
        Case {
            name: "dyn_slice_iter_raw_ptr",
            what: "a THIN raw pointer whose pointee is a `&dyn Trait` fat pointer \
                   (`*const &dyn`, `*mut &dyn`, `NonNull<&dyn>`) — the cursor of \
                   `slice::Iter<'_, &dyn Trait>` that `debug_tuple_fields_finish` \
                   walks — typed as the two-lane `{data, vtable}` image behind the \
                   thin pointer: a 16-byte stride, a two-lane `*q` load and store, \
                   `ptr == end`, `offset_from_unsigned`, plus a `&[&dyn Trait; N]` \
                   array reference typed from the rustc layout",
            src: include_str!("bridge_corpus/dyn_slice_iter_raw_ptr.rs"),
        },
    ]
}

#[test]
fn fat_pointer_memory_leaves_match_llvm() {
    let dylib = ensure_dylib_built();
    for case in corpus() {
        for opt in OPT_LEVELS {
            let dir = workdir(&format!("{}_{}", case.name, opt.len()));
            let oracle = compile_and_run(&dir, case.name, case.src, opt, None)
                .unwrap_or_else(|e| panic!("{} ({opt}): LLVM oracle failed: <<<{e}>>>", case.name));
            let bridge = compile_and_run(&dir, case.name, case.src, opt, Some(&dylib))
                .unwrap_or_else(|e| {
                    panic!(
                        "{} ({opt}): trust-cg REFUSED or failed to compile {}: <<<{e}>>>",
                        case.name, case.what
                    )
                });
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
            let _ = std::fs::remove_dir_all(&dir);
        }
    }
}
