# Darwin x86-64 `library/core` proof census at O2: what LICM and rotation decide — 2026-11-04

This record is slice 26's pre-build measurement
(`~/tcg-scratch/s26-design/README.md` §7, item 4 of S26-0). It turns x86 loop
passes off through tracked opt-outs and counts the O2 census roots that each
configuration promotes. LICM and the full unroller get their opt-outs in
OD-232 (`no-x86-licm`, `no-x86-loop-unroll`). Nothing here is a completion
claim. A census counts fail-closed roots. A function's object is emitted only
when every row of it has Formal credit from an AY-refuted, Clean-checked body
theorem.

## Setup

- **Host:** the x86_64 Mac of the
  [2026-09-27 census](../2026-09-27-darwin-x86-64-census/README.md).
- **Compiler:** the t011 root overlay's `trustc`
  (`rustc 1.99.0-dev (d7f143f3b 2026-09-21) (trustc 0.1.0)`).
- **Proof tools:** AY 0.27.0 build 13556, Clean 5f09e36c.
- **Flags:** `-Ztrust-verify=off`, `-Cpanic=abort`, `-Copt-level=2`, proofs
  required (the bridge default), `x86-body-trace` on.
- **Bridge:** `65f5e6cdb` (main `af1b44f07`, which carries OD-230 and OD-231,
  plus the OD-232 lane), built with `lane/build_bridge.t011.sh`
  (`--unverified`; no sealed-toolchain claim): `lk.dylib`, SHA-256
  `7adef435…a6563b`. Before every census, `lane/check_dylib_tools.sh`
  confirmed the drat-trim path embedded in the dylib.
- **Reproducer:** `lane/run.sh` (the lane's gates, the bridge, then the six
  censuses over `lane/census_t011_dylib.sh`). Comparisons use
  `census_compare.py`
  ([slice 12 record](../2026-10-05-darwin-x86-64-census-slice12/README.md)).
  Every one reports **0 newly failing roots, 0 named mismatches and 0 refuted
  bodies**.

## The control: OD-230, OD-231 and OD-232 change no `core` object at O2

`o2lk-plain` runs the lane's bridge with no knob. Against slice 24a's O2
census (`o2-s24a-f`, code `b342de091`, 378 roots):

- its `failed_roots.jsonl` is byte-identical;
- all 910 emitted objects are byte-identical.

So in `core` at O2 no loop header has the shapes OD-230's rotation fix refuses
or copies differently. No pure call sits off a loop's first-iteration path.
The new knobs, all off, change nothing.

## The measurement

| run | knobs | failed roots | promoted against plain |
| --- | --- | ---: | ---: |
| plain | — | 378 | — |
| k1 | `no-x86-loop-rotate` | 378 | 0 |
| k2 | `no-x86-licm` | 357 | 21 |
| k3 | `no-x86-licm`, `no-x86-loop-rotate` | 342 | **36** |
| k4 | k3 + `no-x86-strength-reduce`, `no-x86-loop-unroll` | 342 | 36 |
| k5 | `no-licm-pointer-loads`, `no-x86-strength-reduce` | 378 | 0 |

- **The slice 26 ceiling at this base is 36 roots** (k3). This is the bound
  OD-229 quotes; the design's 63 was an upper estimate. It clears the
  design's re-scope threshold of about 15.
- k2's 21 are a subset of k3's 36. Rotation alone decides nothing (k1). With
  LICM off, rotation decides 15 more: in those functions both passes changed
  the loop, and both must be stated.
- Of k3's 36, 35 were refused as "machine block Block(N) lowers rows of
  several LIR blocks", and one as a row outside the body domain. With the
  passes off, each binds and replays Valid.
- Strength reduction and the full unroller hide no further root behind LICM
  and rotation (k4). Neither the pointer-base arm nor strength reduction
  decides a root with LICM's other tiers on (k5).
- Wall per census: 669 s to 876 s.

## Not measured

- The base: slice 25 (OD-227) and slice 24c (OD-228) have not landed. Their
  rows change what the remaining roots refuse first. The design asks for this
  measurement on the base those slices land on; repeat it then.
  Repeated on slice 25's base in the
  [2026-11-06 record](../2026-11-06-darwin-x86-64-o2-knob-ceilings/README.md):
  the ceiling there is 111.
- O0: neither LICM nor the unroller runs at O0, so the O0 floor (20 roots,
  OD-115) is not re-measured here.

## Payloads

Out of tree, bound in [PAYLOADS.md](PAYLOADS.md).
