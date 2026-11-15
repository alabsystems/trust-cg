# Darwin x86-64 `library/core` proof census at O2: the loop and if-conversion ceilings on slice 25 — 2026-11-06

This record repeats the
[2026-11-04 loop census](../2026-11-04-darwin-x86-64-o2-loop-census/README.md)
on the base that slice 25 (OD-227) landed on, as that record's *Not measured*
section asks. It turns x86 passes off through tracked opt-outs and counts the
O2 census roots each configuration promotes. Nothing here is a completion
claim. A census counts fail-closed roots. A function's object is emitted only
when every row of it has Formal credit from an AY-refuted, Clean-checked body
theorem. A knob run is a diagnostic of what a slice could reach: it is not a
shipping configuration, and its promotions are credits of different code.

## Setup

- **Host:** the x86_64 Mac of the
  [2026-09-27 census](../2026-09-27-darwin-x86-64-census/README.md).
- **Compiler:** the t011 root overlay's `trustc`
  (`rustc 1.99.0-dev (d7f143f3b 2026-09-21) (trustc 0.1.0)`).
- **Proof tools:** AY 0.27.0 build 13556, Clean 5f09e36c.
- **Flags:** `-Ztrust-verify=off`, `-Cpanic=abort`, `-Copt-level=2`, proofs
  required (the bridge default), `x86-body-trace` on.
- **Bridge:** main `b30110fcd` (slice 25 landed), built in a detached
  worktree with the 2026-11-04 record's `lane/build_bridge.t011.sh`
  (`--unverified`; no sealed-toolchain claim; 61 min). The dylib SHA-256 is
  `9f8567d7…0e759461`. Before every census, that record's
  `lane/check_dylib_tools.sh` confirmed the drat-trim path embedded in the
  dylib. Both scripts, and `lane/census_t011_dylib.sh`, are byte-identical to
  the copies that record keeps.
- **Reproducer:** `lane/census.sh` builds the bridge, then runs the four
  censuses. Comparisons use `census_compare.py`
  ([slice 12 record](../2026-10-05-darwin-x86-64-census-slice12/README.md)),
  `root_classes.py`
  ([census table](../2026-09-27-darwin-x86-64-census/README.md)) and slice
  25's `census_s25.py`
  ([record](../2026-11-04-darwin-x86-64-slice25-sib-rows/README.md)).

## The control: main at `b30110fcd` is slice 25's census

`o2-m301` runs the bridge with no knob. Against slice 25's O2 census
(`o2-s25`, code `d92b944fe`, 254 roots):

- `failed_roots.jsonl` and `refusals.jsonl` are byte-identical;
- all 1034 emitted code objects are byte-identical.

The crate's one trust-witness file (`obj/trust-witness/*.twit`) differs. Each
item key changes in two hash fields, one of which is shared by every item.
That fits a hash of the backend build, which differs, but the fields were not
decoded here. So merging origin/main (OD-230 to OD-232, with the knobs off)
into slice 25 changed no `core` code object at O2, and the slice-25 census
stands for the landed head.

## The measurement

| run | knobs | failed roots | promoted against plain | wall |
| --- | --- | ---: | ---: | ---: |
| `o2-m301` | — | 254 | — | 831 s |
| `o2k-m301-lr` | `no-x86-licm`, `no-x86-loop-rotate` | 143 | **111** | 1489 s |
| `o2k-m301-all` | lr + `no-x86-ifconvert`, `no-x86-cmov-swap` | 91 | **163** | 1324 s |
| `o2k-m301-allbm` | all + `no-x86-block-merge` | 87 | 167 | 1674 s |

- **No comparison has a newly failing root or a named mismatch.**
- **Slice 26's ceiling on this base is 111 roots** (lr), up from 36 on slice
  24a's base. The 36 are among the 111. The other 75 still failed in the
  2026-11-04 record's k3 run (the same knobs on slice 24a's base), each at
  a row that slice 25 admits: 32 at the stack-slot scan, 29 `MovzxRM8Sib`,
  9 `MovRM32Sib`, 2 `AddMR` and one each of `MovMR8Sib`, `MovMR32Sib` and
  `MovRMSib`.
- **The combined ceiling of slices 24c and 26 is 163** (all). The slice 26
  design predicted exactly this figure as the ceiling on top of slices 25 and
  24c (`~/tcg-scratch/s26-design/README.md`, *Answers*). With if-conversion
  off alone, slice 24c's ceiling census on this base promoted 41 (slice 24c's
  record). Since 111 + 41 = 152, the two passes interact in 11 roots, where
  both must be stated.
- The promoted sets nest: lr's 111 are a subset of all's 163. All but one of
  all's 163 are among allbm's 167; that one root stays failing with block
  merging off as well.
- With no knob, every promoted root first refused at a merged machine block
  (`machine block Block(N) lowers rows of several LIR blocks; not contracted:
  …`). With the passes off, the named function binds and replays Valid.
  - lr's 111: 53 are "LIR block Block(N) is entered from […], not from
    Block(N) alone", 55 are "the predecessor Block(N) of LIR block Block(N)
    ends in a Brif" (or "a Switch"), and 3 are "not on the chain".
  - all's 163: 90 a Brif or Switch predecessor, 61 entered from several,
    9 "has no machine block" and 3 not on the chain.

  `census_s25.py`'s `followup.txt` for each run has the exact texts, with
  and without the quotient suffix.
- **What the 91 remaining roots (all) refuse first.**
  - 17 + 2: no machine row of a loop header's entry edge writes the copy into
    its parameter.
  - 12 + 1: no machine row defines a value live across a cut point.
  - 9: no observable.
  - 6: bound but not independently checked.
  - 7 Setcc, 5 SbbRR and 2 AdcRR: a flags reader whose flags no row of its
    block wrote.
  - 4 + 1 + 2 + 1: a slot address used as data.
  - 2 RolRCl and 1 LeaSib rows.
  - the other 19:
    - 2 refuted (below);
    - 3 refused by the bridge before the backend;
    - 2 "machine blocks … both lower LIR block", and 2 where the edge
      copies into a loop header would begin in another LIR block;
    - 10 LIR-side texts: the acyclic domain (3 + 2), type hints (3), a
      block parameter and an unbounded index.

  The loop-edge and live-across-cut texts are the next classes once the
  passes are stated.

## Refuted bodies

These are never credits. A refutation keeps the function's object out of the
build.

- **`core::wtf8::slice_error_fail`** (two codegen attempts, 555 and 571 bound
  rows) is refuted in every run, as in slice 25's census. It is the known
  cut-interface artefact of OD-227's record, for which OD-233 is reserved.
- **`core::str::slice_error_fail_rt`** (1306 and 1334 bound rows, stated in
  9 and 8 parts, or 8 and 8 in `allbm`) is refuted in the three knob runs only, with its parts
  dumped. With no knob it is refused at a merged machine block before it
  binds. The OD-233 design (`~/tcg-scratch/od233-design/README.md`, §7)
  names it as the next instance of the wtf8 shape to watch. It is **not
  diagnosed in this record**. It must be diagnosed as either a miscompile of
  the opt-out configuration or a statement artefact before any slice credits
  a body that LICM or rotation changed.
  The [2026-11-07 record](../2026-11-07-darwin-x86-64-o2-licm-rotation-split/README.md)
  diagnoses it as a statement artefact of the wtf8 class, produced by LICM
  off alone. With the assumption half of OD-233's rule, applied by hand, its
  failing parts are unsat. Whether OD-233's implementation closes it is not
  yet measured.

## Not measured

- The split of lr between LICM and rotation on this base: on slice 24a's base
  rotation alone decided nothing, and with LICM off it decided 15 more. The
  [2026-11-07 record](../2026-11-07-darwin-x86-64-o2-licm-rotation-split/README.md)
  has since measured it: 76 by LICM off alone, 1 by rotation off alone, 34
  only with both.
- O0: none of these passes runs at O0, so the O0 floor (20 roots, OD-115) is
  not re-measured.
- Slice 24c's own census, and OD-233's: both lanes are still building.

## Payloads

Out of tree, bound in [PAYLOADS.md](PAYLOADS.md).
