# Darwin x86-64 `library/core` census — 2026-09-27

> **Payload removed.** The gzipped captures this record committed (logs,
> certificates, objects and archives) are no longer in the tree. The last
> commit that contains them is `ea8492fd9315ed8863af166657fed1b75bcf2c93`; recover one with
> `git show ea8492fd9315:<path>`. References below to retained files and
> inventories describe that commit.

Two rows, same host and toolchains as the
[2026-09-22 census](../2026-09-22-darwin-x86-64-census/README.md) (native
stage-1 `trustc 1.99.0-dev (d7f143f3b 2026-09-21)`, bridge built on this host
against the stage-1 `stage0-sysroot`, `-Ztrust-verify=off`, O0,
`-Cpanic=abort`, one CGU). The bridge build records the toolchain AY
(`ay 0.27.0+build.10530`, `stage0-sysroot/bin/ay`, sha256 `9a149c35…`), and
Clean resolves through `store/clean/current` to a carcara-capable
`clean 1.2.0`. Nothing here is a completion claim.

| Row | trust-cg | Mode | Failed roots | Distinct reasons |
| --- | --- | --- | --- | --- |
| `core-x86_64-darwin-O0-lowering-35c463d81` | `35c463d81` | `-Ztrust-ir-cg-args=no-proof-certs` (lowering only, NO proof claim) | 3 | 3 |
| `core-x86_64-darwin-O0-proof-slice1-bc8624b4d` | `bc8624b4d` | proofs required (the bridge default) | 3212 | 4 |
| `core-x86_64-darwin-O0-proof-slice2-d0278d3b9` | `d0278d3b9` | proofs required | 3078 | 2 |
| `core-x86_64-darwin-O0-lowering-31ceceb19` | `31ceceb19` | lowering only (no proof claim) | **0** | 0 |
| `core-x86_64-darwin-O0-proof-31ceceb19` | `31ceceb19` | proofs required | 3078 | 1 |
| `core-x86_64-darwin-O0-proof-slice3-94652175d` | `94652175d` | proofs required | 2887 | 1 |
| `core-x86_64-darwin-O0-proof-db6c150ee` | `db6c150ee` | proofs required | 2708 | 1 |
| `core-x86_64-darwin-O0-proof-73e5a69f5` | `73e5a69f5` | proofs required | 2114 | 2 |
| `core-x86_64-darwin-O0-proof-336a49f14` | `336a49f14` | proofs required | 1817 | 1 |
| `core-x86_64-darwin-O0-proof-90ccb1b0b` | `90ccb1b0b` | proofs required | 1626 | 1 |
| `core-x86_64-darwin-O0-proof-ac0481810` | `ac0481810` | proofs required | 1272 | 1 |
| `core-x86_64-darwin-O0-proof-main-f6dcad152-ay12713` | `f6dcad152` (AY 12713 overlay; later rows of slices 12-15 are in their records) | proofs required | 447 | 1 |
| `core-x86_64-darwin-O0-proof-slice12-landing-ay12713` | `fca48f987` (slice 12 on `f6dcad152`; [record](../2026-10-05-darwin-x86-64-census-slice12/README.md)) | proofs required | 373 | 1 |
| `core-x86_64-darwin-O0-proof-main-a902ea9ef-ay12713` | `a902ea9ef` (slices 1-13 and 15) | proofs required | 377 | 1 |
| `core-x86_64-darwin-O0-proof-slice14-ay12713` | `ffdfb2b23` (slice 14 on `a902ea9ef`; [record](../2026-10-09-darwin-x86-64-census-slice14/README.md)) | proofs required | 342 | 1 |
| `core-x86_64-darwin-O0-proof-main-2854ce3e3-ay12713` | `2854ce3e3` (its bridge spells array-element addresses as `ArrayGep`, outside the body lane) | proofs required | 813 | 2 |
| `core-x86_64-darwin-O0-proof-slice16-ay12713` | `5b5b1d105` (slice 16 on `2854ce3e3`; [record](../2026-10-14-darwin-x86-64-slice16-parts/README.md)) | proofs required | 763 | 2 |
| `core-x86_64-darwin-O0-proof-main-cb390e657-ay12713` | `cb390e657` (slices 1-16) | proofs required | 743 | 2 |
| `core-x86_64-darwin-O0-proof-arraygep-ay12713` | `d12c627fb` (OD-185/186 on `cb390e657`; [record](../2026-10-15-darwin-x86-64-arraygep/README.md)) | proofs required | 235 | 2 |
| `core-x86_64-darwin-O0-proof-main-6191f3621-ay12713` | `6191f3621` (slices 1-16, OD-185/186) | proofs required | 232 | 2 |
| `core-x86_64-darwin-O0-proof-slice17-ay12713` | `ac8424004` (slice 17 on `6191f3621`; [record](../2026-10-15-darwin-x86-64-slice17-indexed/README.md)) | proofs required | 191 | 2 |
| `core-x86_64-darwin-O0-proof-main-4a65bc3cf-ay12713` | `4a65bc3cf` (slices 1-17, OD-185/186) | proofs required | 187 | 1 |
| `core-x86_64-darwin-O0-proof-slice18-ay12713` | `ab1f6051d` (slice 18 on `4a65bc3cf`; [record](../2026-10-19-darwin-x86-64-slice18-spelling/README.md)) | proofs required | 114 | 1 |
| `core-x86_64-darwin-O0-proof-main-d0ecc859f-ay12713` | `d0ecc859f` (slices 1-18) | proofs required | 114 | 1 |
| `core-x86_64-darwin-O0-proof-ay13556` | `f0113c522` (QUALIFIED_AY build 13556 on `d0ecc859f`; [record](../2026-10-19-darwin-x86-64-ay13556-requalification/README.md)) | proofs required | 106 | 1 |
| `core-x86_64-darwin-O0-proof-main-bf5d4b2c9-ay13556` | `bf5d4b2c9` (slices 1-18, OD-185..190) | proofs required | 108 | 1 |
| `core-x86_64-darwin-O0-proof-slice20-ay13556` | `104f7bf39` (slice 20 on `bf5d4b2c9`; [record](../2026-10-26-darwin-x86-64-slice20-rules/README.md)) | proofs required | 90 | 1 |
| `core-x86_64-darwin-O0-proof-main-5d732f441-ay13556` | `5d732f441` (slices 1-18, 20) | proofs required | 89 | 1 |
| `core-x86_64-darwin-O0-proof-slice19-ay13556` | `427a6f3d6` (slice 19 on `5d732f441`; [record](../2026-10-26-darwin-x86-64-slice19-spelling/README.md)) | proofs required | 48 | 1 |
| `core-x86_64-darwin-O0-proof-main-c4885af82-ay13556` | `c4885af82` (slices 1-20, OD-185..197) | proofs required | 48 | 1 |
| `core-x86_64-darwin-O0-proof-slice21-ay13556` | `401db9e46` (slice 21 on `c4885af82`; [record](../2026-10-26-darwin-x86-64-slice21-fp-atomics/README.md)) | proofs required | 36 | 1 |
| `core-x86_64-darwin-O0-proof-main-20649afe9-ay13556` | `20649afe9` (slices 1-21) | proofs required | 36 | 1 |
| `core-x86_64-darwin-O0-proof-slice22-ay13556` | `b596e62fe` (slice 22 on `20649afe9`; [record](../2026-10-27-darwin-x86-64-slice22-i128-division/README.md)) | proofs required | 23 | 1 |
| `core-x86_64-darwin-O0-proof-main-1fb7620a5-ay13556` | `1fb7620a5` (slices 1-22, OD-210 to OD-223; built with a local engineering targo from Trust `13bb1758dc`, no sealed-toolchain claim) | proofs required | 23 | 1 |
| `core-x86_64-darwin-O0-proof-slice23-ay13556` | `f2a032c4d` (slice 23 on `1fb7620a5`; [record](../2026-10-27-darwin-x86-64-slice23-arith-pairing/README.md)) | proofs required | **20** | 1 |
| `core-x86_64-darwin-O0-proof-i128-const-shift-ay13556` | `6607d0f6b` (OD-215, the I128 constant-shift fold, on `e74f215c6`; [record](../2026-10-27-darwin-x86-64-i128-const-shift/README.md)) | proofs required | 20 | 1 |
| `core-x86_64-darwin-O0-proof-i128-mulo-divfree-ay13556` | `682862195` (OD-224, the division-free x86-64 I128 checked multiply, on `6607d0f6b`; [record](../2026-11-02-darwin-x86-64-i128-mulo-divfree/README.md)) | proofs required | 20 | 1 |
| `core-x86_64-darwin-O0-proof-main-7ee0def54-ay13556` | `7ee0def54` (slices 1-23, OD-205 to OD-225; [record](../2026-11-03-darwin-x86-64-o2-census/README.md)) | proofs required | 20 | 1 |
| `core-x86_64-darwin-O2-proof-main-7ee0def54-ay13556` | `7ee0def54` (`-Copt-level=2`, the first O2 row; its attribution to x86 passes is in the [record](../2026-11-03-darwin-x86-64-o2-census/README.md)) | proofs required | 582 | 2 |
| `core-x86_64-darwin-O0-proof-slice24a-ay13556` | `4c54514eb` (slice 24a, the merged-chain quotient, on `7ee0def54`; [record](../2026-11-04-darwin-x86-64-slice24a-chain-quotient/README.md)) | proofs required | 20 | 1 |
| `core-x86_64-darwin-O2-proof-slice24a-ay13556` | `b342de091` (slice 24a at its final head; landed as `52923dad6`) | proofs required | 378 | 2 |
| `core-x86_64-darwin-O2-proof-loop-knobs-65f5e6cdb-ay13556` | `65f5e6cdb` (main `af1b44f07`, OD-230 and OD-231, plus the OD-232 knobs off; failed roots and all 910 objects byte-identical to the slice 24a row; [record](../2026-11-04-darwin-x86-64-o2-loop-census/README.md)) | proofs required | 378 | 2 |
| `core-x86_64-darwin-O0-proof-slice25-ay13556` | `d92b944fe` (slice 25, scaled-index rows and memory-destination `add`/`xor`, on `70c2ddde5`; records and traces byte-identical to the slice 24a row; [record](../2026-11-04-darwin-x86-64-slice25-sib-rows/README.md)) | proofs required | 20 | 1 |
| `core-x86_64-darwin-O2-proof-slice25-ay13556` | `d92b944fe` (slice 25; 124 promoted, none newly failing; one root stated in parts and refuted in one part, no credit) | proofs required | **254** | 2 |
| `core-x86_64-darwin-O2-proof-main-b30110fcd-ay13556` | `b30110fcd` (main, slice 25 landed; failed roots, refusals and all 1034 code objects byte-identical to the slice 25 row; knob ceilings: LICM and rotation off 111, with if-conversion off too 163; [record](../2026-11-06-darwin-x86-64-o2-knob-ceilings/README.md)) | proofs required | 254 | 2 |
| `core-x86_64-darwin-O0-proof-slice24c-ay13556` | `38feaf386` (slice 24c, if-converted regions stated over segments, on `a617488aa`; failed-root and refusal records byte-identical, and every keyed trace line identical, to the slice 25 row; [record](../2026-11-05-darwin-x86-64-slice24c-segments/README.md)) | proofs required | 20 | 1 |
| `core-x86_64-darwin-O2-proof-slice24c-ay13556` | `38feaf386` (slice 24c; 39 promoted against the slice 25 row, none newly failing, every one stated over segments; the slice 25 row's refuted root unchanged, no credit) | proofs required | **215** | 2 |
| `core-x86_64-darwin-O3-proof-slice25-ay13556` | `d92b944fe` (slice 25's bridge at `-Copt-level=3`, the first O3 row, run after slice 24c's O3 census as its baseline; two roots stated in parts and refuted in one part, no credit) | proofs required | 267 | 2 |
| `core-x86_64-darwin-O3-proof-slice24c-ay13556` | `38feaf386` (slice 24c; 6 promoted against the slice-25 O3 row, none newly failing; the same two refuted roots, no credit) | proofs required | 261 | 2 |
| `core-x86_64-darwin-O0-proof-od233-ay13556` | `c76048fa3` (OD-233, defined cut inputs, on `b30110fcd`; failed roots, refusals and every emitted object byte-identical to the slice 25 row, 59 functions defining inputs; [record](../2026-11-05-darwin-x86-64-od233-defined-cut-inputs/README.md)) | proofs required | 20 | 1 |
| `core-x86_64-darwin-O2-proof-od233-ay13556` | `c76048fa3` (OD-233; `core::wtf8::slice_error_fail` promoted, none newly failing, no refuted body) | proofs required | **253** | 2 |
| `core-x86_64-darwin-O0-proof-s24c-od233-ay13556` | `49748f126` (slice 24c, OD-233 and OD-235 combined, on `75ab22445` with the bridge's frame-pointer arm; failed-root and refusal records byte-identical to the slice 24c and OD-233 rows; 41 static-data objects differ, their anchors non-external by `main`'s `9b0e8a3b1`; [record](../2026-11-07-darwin-x86-64-s24c-od233-combined/README.md)) | proofs required | 20 | 1 |
| `core-x86_64-darwin-O2-proof-s24c-od233-ay13556` | `49748f126` (the combination; 1 promoted against the slice 24c row, its refuted `wtf8` root, and 39 against the OD-233 row, none newly failing, no refuted body; knob ceilings: LICM off 129, LICM and rotation off 91) | proofs required | **214** | 2 |
| `core-x86_64-darwin-O3-proof-s24c-od233-ay13556` | `49748f126` (the combination; 2 promoted against the slice 24c O3 row, its two refuted roots, none newly failing, no refuted body) | proofs required | 259 | 2 |

## Lowering row

Down from 13 on `b397eb9aa` (and 18 on `874c4b3ef`), with no new reason string
and no ICE. The three left:

- `core::sync::atomic::atomic_load::<i128>` and `::<u128>` — a 128-bit atomic
  needs `LOCK CMPXCHG16B`, which the x86-64 backend does not have;
- `core::panic::Location::caller` — `caller_location` needs the
  `#[track_caller]` hidden-argument ABI, which the bridge does not implement
  for locally codegened functions.

## Proof row

3209 of the 3212 roots are `[TCG-PROOF-465]`; the other three are the lowering
roots above. The previous proof census of record (r23, `874c4b3ef`, same host)
had 3341 roots, 3323 of them `[TCG-PROOF-465]`. The difference is the x86-64
source-bound whole-body theorem, slice 1 (114 roots now promote with every row
`Formal` from a replayed, Clean-checked body theorem) plus the lowering fixes
(15 roots).

The first uncovered row of 3128 of the 3209 is a reconstructed `Copy`, i.e.
statistical evidence the E0.2 rule refuses. Opcode occurrence across the 3209
(roots containing at least one uncovered row of that opcode): `MovRR` 3024,
`Lea` 2436, `AddRR` 2266, `MovRM` 1978, `MovMR` 1878, `MovRR32` 1583, `CmpRI`
1175, `Jcc` 1158, `AndRI` 1024. Roots blocked by exactly ONE opcode: `MovRR`
217 (mostly pointer-typed copies and call wrappers — `ptr::cast`,
`NonNull::cast`), `MovRR32` 65 (narrow carriers: `bool`/`i8` returns), `Lea`
3; by exactly `{MovRR, MovRR32}`: 59. Those are the next body-lane slices
(pointer and narrow carriers, then direct calls); memory, flags and control
flow follow.

## Slice 8, narrow loads and the x86 fixes on main (`ac0481810`)

Main at `ac0481810` carries:

- body-theorem slice 8 (integer aggregates of 1 to 16 bytes in general
  registers, see `../2026-10-02-darwin-x86-64-census-slice8/`);
- the zero-extending narrow loads (`reports/2026-09-30-movzx-narrow-loads/`);
- the x86 loop-head aligner and i128 stack-oracle fixes
  (`reports/2026-10-02-x86-i128-stack-abi/`).

**Build.** The bridge was built from `ac0481810`; the dylib sha256 is
`727e6e3baeb72a6852f5e9115d58a21d25a246e4485d0e3f262c31e38c35edab`. The
flags are those above plus `-Ztrust-ir-cg-args=x86-body-dump=<dir>`, which
writes the SMT2 query of each body theorem that does not replay Valid; 466
queries were written, kept out of tree for the AY work.

**Run.** The census started at 622132 free pages and took 6439 s. There was
no resource-budget refusal and no harness error.

**Result.** 1272 failed roots, every one `[TCG-PROOF-465]`; the failed-root
file has sha256
`6324132b6451dbeb0e811f90f2ed65d291c0e3c180a2ab7aef57d4600a443657`.

Against `90ccb1b0b` (1626), 355 roots promote and one newly fails:
`core::fmt::builders::DebugMap::finish`. The narrow loads re-extend a
zero-extended byte there, and the toolchain AY (0.27.0 b10530) does not
certify the resulting `extract`/`zero_extend` term within its budget. The
same query certifies with the AY word-level branch that is landing on AY
main.

By the first failing function, the remaining roots are:

| Class | Roots |
| --- | ---: |
| bound but not AY-certified | 468 |
| over 16 blocks / a path over 256 instructions | 183 + 88 |
| checked arithmetic | 97 |
| loops | 61 |
| `i128` parameters / results | 60 + 15 |
| floating-point parameters / results | 20 + 18 |
| a slot address escaping other than into a call | 34 |
| non-scalar loads | 29 |
| `CallIndirect` | 23 |

## Remaining classes on `90ccb1b0b`, by failed root

Each of the 1626 failed roots names the first function whose proof entry is
not verified. That function is looked up by its full emitted name, including
any `__trust_cg_private.<cgu>.<n>.` prefix, among the census's
`x86-body-trace` lines. A root blocked by more than one function counts once,
under the first. Fixing that function can expose the next one. Reproduce with
[`root_classes.py`](root_classes.py) `<census-out-dir>`.

| Class of the named function | Roots | Plan |
| --- | ---: | --- |
| bound, but AY does not certify the replay | 402 | AY: the word-level `bvmul` gap and the strict-certification wall (some of these are load-induced, since this census ran at load 16) |
| non-scalar register parameters | 303 | slice 8 |
| non-scalar results | 234 | slice 8 |
| over 16 blocks / a path over 256 instructions | 168 + 78 | raise the DAG bounds |
| checked arithmetic | 87 | overflow-flag observables |
| other call shapes | 76 | per shape |
| loops | 47 | invariant-based slice |
| a slot address escaping other than into a call / a non-scalar load or extend / an inconsistent type hint | 32 + 31 + 27 | per rule |
| `CallIndirect`, `CtPop`, `Bnot`, atomics, guards, variable shifts, `Udiv`/`Urem`, no observable, and singletons | about 150 | per opcode |

## Remaining classes on `336a49f14` and the plan

Per-function body-lane classes from that census's `x86-body-trace` lines
(3447 functions traced, 1568 replay Valid; a root can contain several
functions):

| Class (first refusal) | Functions | Plan |
| --- | ---: | --- |
| call to an sret callee | 423 | slice 7: calls through memory (in progress) |
| other call shapes (slot address escaping into a call, non-scalar call result) | 249 | slice 7 (escaping slots); slice 8 (non-scalar results) |
| bound, AY does not certify (`self-check-rejected`, `unproved_steps`) | 245 | AY word-level gap: 32/64-bit `bvmul` equivalences; AY's 3 s certification wall is fixed on AY main (toolchain bump pending) |
| non-scalar register parameters (small enums/structs in LIR aggregate types) | 235 | slice 8 |
| non-scalar results | 227 | slice 8 |
| control flow over 16 blocks / a path over 256 instructions | 102 + 33 | raise the DAG bounds |
| no observable (effect-free bodies: trivial `drop_in_place`, ZST constructors, `cold_path`) | 73 | an ABI-preservation observable (RSP and callee-saved registers restored, no call, no store outside the frame) |
| checked arithmetic (`CheckedU/Sadd/sub/mul`) | 80 | overflow-flag observables |
| loops | 40 | invariant-based slice |
| `Store`/`Load` outside the trace, `CallIndirect`, `CtPop`, `Bnot`, guards, `AtomicLoad`, variable shifts, `Udiv`/`Urem` | ~150 | per-opcode additions |

## Slice 7 on main (`90ccb1b0b`)

Body-theorem slice 7 (calls through memory: return buffers, `&mut`
out-parameters, escaped private slots and retention; see LIMITATIONS.md) is
merged with its mutation-probe record and the boundary-zeroing sampler
(`../2026-10-01-darwin-x86-64-census-slice7/`).

**Build.** The bridge was built from `dbde47e61`. That tree differs from
`90ccb1b0b` only in test and documentation files, so no bridge input
changed. Dylib sha256:
`331425bdeb50b4c0ccd29f9640252e001c019d7fa17d982f8c22b7b7fbf6dcef`. The
flags and toolchain are those above.

**Run.** The census started at 848662 free pages and took 3881 s of wall
time. There was no resource-budget refusal and no harness error.

**Result.** 1626 failed roots, every one `[TCG-PROOF-465]`. The failed-root
file `<scratch>/runs/census-main-90cc/failed_roots.jsonl` has sha256
`4f41fb62e4bebfbb1898233e76a290568ad1374239e3901e6efc4f9be22bd619`; its
lines sorted have `2b89b133bfdd66aee8f1c9a144136a3d2d77dca9f7e7f5c5884fa719ac72de73`.

| Compared with | Its roots | Promoted | Newly failing |
| --- | ---: | ---: | ---: |
| `336a49f14` | 1817 | 191 | 0 |
| The slice-7 branch census | 1634 | 10 | 2 |

The branch census is
`../2026-10-01-darwin-x86-64-census-slice7/`, run before the trust-ir pin move
`8cf20223 -> 8a0d54c0` reached the branch. The two newly failing roots are
not lowering changes:

- `core::panicking::panic_display::<&str>`
- a `decode_repr` closure

Each body is still bound: the same 83 rows in the first, and 87 → 88 rows in
the second. In the branch census each replayed `Valid`; here each replayed
`none (no independently checked proof)`.

This census overlapped an AY release build, and load reached 16 on four
cores. Under that load, the toolchain AY's strict certification (3 s of wall
clock per proof-producing bit-blast, retried three times) answers
`self-check-rejected` for bodies that certify at rest. The count is
therefore an upper bound under load. Two fixes follow:

- The negative memo now records a certification failure only from fresh
  solves that had the processor.
- The deadline itself is fixed on AY main; it reaches this toolchain with
  the next AY move.

## Slice 6 on main (`336a49f14`)

Body-theorem slice 6 (acyclic control flow: a LIR DAG of at most 16 blocks and
16 paths, paired with the machine by TV-1 provenance, one claim per source path
over the shared EFLAGS model) is merged, after the lowering fix for
`<VaListInner as Debug>::fmt` (`269e07a4d`) and the negative memo
(`17642d03c`). Bridge rebuilt from the pushed main (dylib sha256 `05a601b609a128ba3cc920fb41da2b81f0413ac89513ff25de9b871bfe215234`); stage-1
trustc `d7f143f3b`, O0, `-Cpanic=abort`, one CGU, proofs required,
`x86-body-trace`; census started at 975504 free pages, wall 3093 s, no
resource-budget refusal, no harness error.

1817 failed roots, every one `[TCG-PROOF-465]` (no lowering refusal): the
sorted root list (out of tree, `<scratch>/runs/census-main-336a/failed_roots.jsonl`)
has sha256 `810382733dc0c1e1bba8edf9aea852c4dcde47ddfd7213003c9f49a31b815b8e`. Against `73e5a69f5` (2114) that is 297 fewer; slice 6's own
controlled census measured 2114 -> 1816 (298 promoted, 0 newly failing). Wall
fell from slice 6's 7054 s to 3093 s with the negative memo on main.

## Slice 5 and exact bool loads on main (`73e5a69f5`)

Body-theorem slice 5 (scalar pairs, symbol addresses, branch-free compares; the
pair-call bool lane reads bit 0 alone) and exact bool loads (a loaded bool is its
byte read as `!= 0`, admitted into the body theorem) are merged. The bridge was
rebuilt from the pushed main; census wall 3994 s at 1396413 free pages, no
budget refusal, no harness error. 2114 roots: 2113 `[TCG-PROOF-465]` and one
LOWERING refusal, `<core::ffi::va_list::VaListInner as Debug>::fmt` ("Place
deref memory store from Rvalue::Ref": `&(*_1).3` through an unbound thin
reference argument). That root lowered at `db6c150ee` (it was a proof root),
became `[TCG-DYN-REF-IDENTITY]` after main's `1048f47f3`, and is this refusal
now: a bridge lowering regression on main, not from slice 5.

## Slice 4 on main (`db6c150ee`)

The memory slice of the body theorem (private stack slots, incoming memory as an
Ackermann-reduced access trace, StructGep, sret) is merged with its review fixes:
2708 roots, all `[TCG-PROOF-465]`, no harness error, bridge rebuilt from the pushed
main (dylib digest in `backend.sha256`). Against the slice-4 branch's own census
(2727, `reports/perf/2026-09-28-darwin-x86-64-census-slice4/`), 23 roots newly
promote and 4 newly fail: `core::panicking::{panic_in_cleanup,
panic_cannot_unwind}`, `core::cell::lazy::panic_poisoned` and
`core::slice::sort::shared::smallsort::panic_on_ord_violation`. They are not a
slice-4 regression: on the branch their bodies had no value observable, while on
main the location argument makes instruction 0 a `GlobalRef` to a `.const.alloc`,
which the body domain does not admit yet (the `GlobalRef`/`ExternRef` gap).

## Slice 3 row (`94652175d`)

The direct-call slice of the body theorem (and the bool call-result selector
fix) is merged: 3078 -> 2887 roots, all `[TCG-PROOF-465]`, 191 newly promoted
(every one contains a direct call), 0 newly failing, no ICE; the lowering census
stays at 0. Rebuilt from the merged main, the root set equals the branch's.

## Lowering complete (`31ceceb19`)

With the 128-bit atomic load (one zeroing `LOCK CMPXCHG16B` pseudo, admitted only
on a guaranteed-CX16 baseline) the lowering census reaches **0 failed roots**:
every externally required `library/core` function lowers on x86-64 Darwin, with
no ICE. This is a lowering measurement (`no-proof-certs`), not a proof claim: with
proofs required all 3078 roots are `[TCG-PROOF-465]` — the two atomic roots now
lower and join the proof wall like every other function.

## Slice 2 row (`d0278d3b9`)

Slice 2 of the body theorem (pointer and narrow carriers, immediate/bitwise/shift/
LEA/multiply arithmetic) is merged; 3076 of the 3078 roots are
`[TCG-PROOF-465]` and 2 are `atomic_load::<i128/u128>` (`[TCG-REGALLOC-063]`).
Against the slice-1 row: 3212 -> 3078. The slice-2 branch alone measured 3043; the
difference is 40 `#[track_caller]` diverging panic helpers
(`panicking::panic_const::*`, `option::unwrap_failed`,
`cell::panic_already_borrowed`, ...) that now forward their caller's `&Location`
(the panic-location fix and the hidden-argument ABI) instead of passing a
constant. Their body is no longer an argument-less call-then-trap; the one
uncovered row is the `MovRR` of the forwarded parameter into the call's argument
register, which the direct-call slice is designed to credit.

## Environmental note

A first proof-row run under memory pressure produced 3400
`[TCG-COMPILE-DRIVER] invalid execution resource budget: host reports N
available bytes, less than one 33554432-byte large-stack slot` roots: with one
CGU, a single refused large-stack slot fails every root. That run was
discarded and rerun with ~11 GB free; the archived row is the rerun.

Each row keeps `gap_table.md`, `provenance.json` (home directory shortened to
`~`), `failed_roots.jsonl.gz` and the bridge's `backend.sha256`.
