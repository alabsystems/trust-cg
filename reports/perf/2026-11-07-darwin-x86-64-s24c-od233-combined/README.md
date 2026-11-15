# Darwin x86-64 body theorem — slice 24c and OD-233 combined, with OD-235's fold, 2026-11-07

The lane `feat/x86-body-slice24c-od233` carries three changes to the x86-64
source-bound whole-body theorem (`crates/trust-cg-verify/src/x86_source_bound_body.rs`
and `x86_source_bound_body/split.rs`), measured together on one bridge:

| Ruling | Rule | Record |
| --- | --- | --- |
| OD-228 | slice 24c: a machine block that lowers a single-entry region of LIR blocks (an if-converted diamond or switch) is paired with every source path through it, stated over segments | [slice 24c](../2026-11-05-darwin-x86-64-slice24c-segments/README.md) |
| OD-233 | a cut input the source brings, on every edge into its cut, as one term over the run's fixed inputs is defined as that term, and the term is claimed on every edge | [OD-233](../2026-11-05-darwin-x86-64-od233-defined-cut-inputs/README.md) |
| OD-235 | OD-188's exact fold spells `bvudiv x 2^k` as `bvlshr x k` and `bvurem x 2^k` as `bvand x (2^k - 1)` | this record, *OD-235* |

Each of slice 24c and OD-233 was censused alone on its own base. This
record is the census of the combination as it lands, on `main` at
`75ab22445`, at `-Copt-level=0`, `2` and `3`, and the four knob censuses
that are step 0 of the slice-26 design.

Host: the shared x86_64 Mac (8 logical CPUs, Darwin 22.6, i7-7920HQ), other
lanes building throughout. The bridge was built by `build_bridge.t011.sh`
(`targo --unverified build --release`, the local overlay
`x86-stage1-ay13556-t011`, `-j2`, through `build-slot` at
`BUILD_SLOT_MEM_GB=6`; no proof claim about the build). Each census is
`census_t011_dylib.sh` (the overlay's `trustc`, `-Ccodegen-units=1
-Cpanic=abort -Ztrust-verify=off`, the knobs `diag-json`, `x86-body-trace`,
`x86-body-dump` and `solve-trace`) with the replayer pair AY 0.27.0 build
13556 and Clean 5f09e36c (the overlay's `bin/ay` and `bin/clean`). The
`trust-cg rev` line in each census's `gap_table.md` names the `~/trust`
superproject's submodule, not the bridge; the bridge's commit is
`s26base.bridge-commit.txt`. Payloads are out of tree;
[PAYLOADS.md](PAYLOADS.md) binds each by size and SHA-256.

## The lane

First-parent history from `origin/main`:

| Commit | What |
| --- | --- |
| `49af2948d` | slice 24c's head (OD-228, its review round and census record) |
| `1dd613436` | merge of `feat/x86-body-od233` (`86dea33f6`, OD-233 and its census record) |
| `1d1d71da0` | merge of `origin/main` |
| `71c5eb19e` | OD-235: the division fold and its unit test |
| `5a49bb594` | merge of `origin/main` (the integrate landing); gates 1-5 green here |
| `49748f126` | merge of `fix/bridge-classify-frame-pointers` (`bc1e5d672`: `origin/main` `75ab22445` and the bridge's frame-pointer arm) |

The first census run, on `5a49bb594`, stopped at its bridge build
(`census-combined-5a49bb594-E0004.log`, `DRIVER-EXIT 8`): `main`'s
`ed1c150c7` added `CompileError::Aarch64FramePointersUnsupported`, and the
bridge's `classify_compile_error`, which has no default arm, did not name
it (E0004). The root workspace's gates do not build the bridge, so `main`'s
own bridge did not compile either. `bc1e5d672` gives the variant the
compile driver's code, with a test of the variant and a raise-site test
through `Compiler::compile`; the lane took it by merge, and the census ran
on `49748f126`.

## The bridge

`49748f126`, built with `CARGO_TARGET_DIR` unset: `Finished release … in
35m 07s`, SHA-256 `e974e53b…` (`e974e53bd84854b5cd06d3bbf00ef805590fed557f095aec72e1c4a361fa4c4d`).
Every census copied it as `runs/s26base-<census>.dylib`; the eight copies
hash the same and are hard links of one file.

## Censuses

`scripts/census-combined.sh`, run 2026-11-07 22:19 to 2026-11-08 02:24
(`census-combined.log`, ending `STEP0-DONE` and `DRIVER-EXIT 0`), one
`build-slot` job per census, one at a time. The comparisons are
`census_compare.py` (slice 15's record) against the named census; a
promoted root fails in the named census and not here, a newly failing one
the reverse.

| Census | Opt | Knobs | Failed roots | Against | Its roots | Promoted | Newly failing | Refuted bodies | Wall |
| --- | ---: | --- | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| `census-s26base-base` | 2 | — | **214** | slice 24c (`census-o2-s24c`) | 215 | 1 | 0 | 0 | 1149 s |
| | | | | OD-233 (`census-o2-od233`) | 253 | 39 | 0 | 0 | |
| `census-s26base-o0` | 0 | — | **20** | slice 24c (`census-o0-s24c`) | 20 | 0 | 0 | 0 | 3143 s |
| `census-s26base-o3` | 3 | — | **259** | slice 24c (`census-o3-s24c`) | 261 | 2 | 0 | 0 | 874 s |
| `census-s26base-l` | 2 | `no-x86-licm` | 129 | OD-233 (`census-o2k-od233-l`) | 177 | 48 | 0 | 0 | 1151 s |
| | | | | `main` `b30110fcd` (`census-o2k-m301-l`) | 178 | 49 | 0 | 0 | |
| `census-s26base-lr` | 2 | `no-x86-licm no-x86-loop-rotate` | 91 | `census-o2k-m301-lr` | 143 | 52 | 0 | 0 | 2407 s |
| `census-s26base-r` | 2 | `no-x86-loop-rotate` | 213 | `census-o2k-m301-r` | 253 | 40 | 0 | 0 | 1065 s |
| `census-s26base-all` | 2 | the two, `no-x86-ifconvert`, `no-x86-cmov-swap` | 89 | `census-o2k-m301-all` | 91 | 2 | 0 | 0 | 1722 s |
| `census-s26base-tir` | 2 | `dump-trust-ir=…/tir-s26base` | 214 | `census-s26base-base` | 214 | — | — | 0 | 1068 s |

No census of the eight has a refuted body. Slice 24c's O2 census had one
(`core::wtf8::slice_error_fail`, refuted in one part) and its O3 census
two (that one and `core::str::pattern::StrSearcher::new`, `replay=Invalid
(refuted)` on both codegen attempts): all three are the promotions above,
each now `bound … replay=Valid`. The O2 promotion is the one OD-233's own
census made (`wtf8`); the O3 pair is `wtf8` and `StrSearcher::new`.
Against OD-233's O2 census, the 39 promoted (30 refused there for a
machine block that lowers rows of several LIR blocks, 9 for a LIR block
that has no machine block; each Valid here) are exactly the 39 roots slice
24c's census promoted against slice 25's.

O0: the failed-root and refusal records are byte-identical to slice 24c's
and OD-233's O0 censuses. Of the 3,426 emitted objects, 41 differ from
both; all 41 are static-data objects (`DECIMAL_PAIRS`, the Unicode tables,
the `flt2dec` power tables, two `Waker` vtables), in which the static's
`.static.anchor` function symbol is now non-external. That is `main`'s
`9b0e8a3b1` (x86-64 Mach-O spells an unreferenced module-local definition
as a non-external symbol), merged in `49748f126`, not a change of this
lane.

The dump run (`tir`) is the plain O2 census with `dump-trust-ir`; its
failed-root and refusal records are byte-identical to `base`'s. Its 1,288
TrustIR containers (`tir-s26base`, each a `.trust_irbin` and its `.json`)
are the source of slice 26's `core` replicas (its design, §5.1).

### What is left at O2

The 214: 211 `[TCG-PROOF-465]` (the body theorem did not credit a required
function) and 3 `Rvalue::RawPtr` lowering refusals (`net::ip_addr`'s
`Display` helpers, unchanged). By the class of the function each
`PROOF-465` root names (slice 24c's `root_classes.py`): 168 merged block
not contracted (slice 26's loops), 9 no observable (OD-115), 4 several LIR
blocks in one machine block, 4 `SbbRR` rows, 3 slot address escapes, 3
`Setcc` rows, 2 `RolRCl` rows, and the rest one to three each. Four bodies
bind and are not certified: `Lemire::from_u64` for `f32` and for `f64`
(`replay=Unknown`, the FP abstraction's model is no counterexample),
`<[usize]>::as_chunks::<4>` (Clean refused AY's `unsat`) and
`intrinsics::fallback::wide_mul_u128` (AY `TIMEOUT`, OD-206's negative
memo). The O0 floor is the same 20 roots, all OD-115 no-observable.

## OD-235

**Before.** In the `no-x86-licm` census on OD-233's own bridge
(`census-o2k-od233-l`, 2026-11-07), `<core::slice::ascii::EscapeAscii as
Display>::fmt` (Valid on the slice-25 bridge) failed: part 2 of 7 at AY
`TIMEOUT` on both codegen attempts. That part (3884 B) holds one
`(bvudiv s41 (_ bv1 64))`, a divisor OD-233's defined input made constant;
offline AY build 13556 answers `unsat` in 50.1 s (0 conflicts), and in
0.2 s with the term spelled `s41` or `(bvlshr s41 (_ bv0 64))`
(`g-sefrt/escape/replay.log`: part 2 `unknown` at 30 s, the six others
`unsat` in 46-298 ms).

**After.** In `census-s26base-l`, `EscapeAscii`'s `Display::fmt` replays
Valid on both codegen attempts and is one of the 48 roots promoted against
`census-o2k-od233-l` (the one whose class there was "bound, no
independently checked proof"). The census has no newly failing root and no
refuted body.

**Goldens.** Gate 1 on `5a49bb594` (511 passed, 0 failed): the slice-18,
slice-19 and slice-22 re-render tests reproduce every earlier golden with
the fold, and OD-233's in-parts golden test passes.

## Gate G-SEFRT

Slice 26's design holds S26a to `core::str::slice_error_fail_rt` (its
§4.5). In `census-s26base-l` both codegen attempts state it in parts and
replay Valid: `defined cut inputs bytes=112 items=8`, `stated in parts=9`,
`bound rows=1306 replay=Valid`; and `bytes=128 items=4`, `parts=8`, `bound
rows=1334 replay=Valid`. The trace counts the defined bytes (112 and 128,
the design's check being `bytes >= 8`); which slots they are is not in the
trace, so the slot-68 half of the gate stays with the design's fixture F27.

## OD-233b

The text OD-233b would act on (`split.rs` `cut_pairing`: "no machine row
writes a register as the definition of") occurs as often as in the
censuses this lane combines: O2 2 (slice 24c 2, OD-233 2), O3 24 (slice 24c
24), `l` 20 (`census-o2k-od233-l` 20), O0 0; `lr` 26, `r` 2, `all` 26. The
combination exposes no new instance.

## Step 0 of slice 26

The knob censuses on the combined base, against its plain O2 census (214):

| Knobs off | Failed roots | Fewer than the base | On `main` `b30110fcd` (base 254) |
| --- | ---: | ---: | ---: |
| LICM | 129 | 85 | 178 (76 fewer) |
| rotation | 213 | 1 | 253 (1 fewer) |
| LICM and rotation | 91 | 123 | 143 (111 fewer) |
| those and if-conversion, cmov swap | 89 | 125 | 91 (163 fewer) |

None of the four comparisons with the base has a newly failing root. The
design's bound for S26a on the combined base, 76 plus the 11 roots it
shares with slice 24c (≤ 87), holds: LICM alone accounts for 85.

## Reproduce

`scripts/census-combined.sh <worktree at the lane head> <tag>` (in tree);
it needs `build_bridge.t011.sh`, `census_t011_dylib.sh` and the t011
overlays named in PAYLOADS.md. The comparisons are
`python3 -I census_compare.py <named census> <this census> <out dir>`.
