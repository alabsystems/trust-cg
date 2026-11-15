# Darwin x86-64 `library/core` proof census at O2, and its attribution to x86 passes — 2026-11-03

This is the first O2 census of record on this host, plus five attribution
censuses. Each attribution census turns off x86 machine passes through the
tracked opt-outs that `lane/o2-pass-knobs` adds (`-Ztrust-ir-cg-args=no-x86-…`).
Nothing here is a completion claim. A census counts fail-closed roots. A
function's object is emitted only when every row of it has Formal credit from
an AY-refuted, Clean-checked body theorem.

## Setup

- **Host:** the x86_64 Mac of the
  [2026-09-27 census](../2026-09-27-darwin-x86-64-census/README.md).
- **Compiler:** the t011 root overlay's `trustc`
  (`rustc 1.99.0-dev (d7f143f3b 2026-09-21) (trustc 0.1.0)`).
- **Proof tools:** AY 0.27.0 build 13556, Clean 5f09e36c.
- **Flags:** `-Ztrust-verify=off`, `-Cpanic=abort`, proofs required (the bridge
  default), `x86-body-trace` on.
- **Bridges:** each was built with `lane/build_bridge.t011.sh` (`--unverified`;
  no sealed-toolchain claim).
  - `7ee0def54` (main): `o2-7ee0.dylib`, sha256 `6b7998ed…97e9`.
  - `85d236b37` (main plus the knob lane): `knobs.dylib`, sha256
    `1d2d1941…a78d`.
- **Preflight:** before every census, `lane/check_dylib_tools.sh` confirmed
  that the drat-trim path embedded in the dylib exists. The first O2
  measurement lacked that check: see "Against the first O2 measurement" below.
- **Reproducers:** `lane/chain_7ee0.sh` (bridge, then O2 and O0) and
  `lane/chain_attrib.sh` (the five attribution censuses), both over
  `lane/census_t011_dylib.sh`.

| Row | trust-cg | Mode | Failed roots | Distinct reasons | Objects | Wall |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| `core-x86_64-darwin-O0-proof-main-7ee0def54-ay13556` | `7ee0def54` | O0, proofs required | **20** | 1 | 3426 | 1633 s |
| `core-x86_64-darwin-O2-proof-main-7ee0def54-ay13556` | `7ee0def54` | O2, proofs required | **582** | 2 | 706 | 417 s |
| `o2k-plain` (control) | `85d236b37` | O2, no knob | 582 | 2 | 706 | 412 s |
| `o2k-nbm` | `85d236b37` | O2, `no-x86-block-merge` | 378 | 2 | 910 | 550 s |
| `o2k-nrot` | `85d236b37` | O2, `no-x86-loop-rotate` | 582 | 2 | 706 | 344 s |
| `o2k-nifc` | `85d236b37` | O2, `no-x86-ifconvert`, `no-x86-cmov-swap` | 579 | 2 | 709 | 407 s |
| `o2k-nall` | `85d236b37` | O2, all seven: the five new opt-outs plus `no-x86-ifconvert` and `no-x86-cmov-swap` | 334 | 2 | 954 | 492 s |

- **O0.** The O0 row is still the OD-115 floor of 20 roots, all with no
  observable. OD-225 (proof-claiming compiles skip `ir_inline` and
  `lir_unsigned_range`) changed no O0 root, as it should: neither pass runs
  at O0.
- **Comparisons.** Every comparison below uses `census_compare.py`
  ([slice 12 record](../2026-10-05-darwin-x86-64-census-slice12/README.md)).
  Every one reports **0 newly failing roots, 0 named mismatches and 0
  refuted bodies**.

## The control: the knobs change nothing by default

`o2k-plain` runs the knob lane's bridge with no knob. Against
`7ee0def54`'s O2 census:

- its `failed_roots.jsonl` is byte-identical;
- all 706 emitted objects are byte-identical.

Two runs of one configuration also produce byte-identical failure records.
A changed record between two configurations is therefore an effect of the
configuration, not noise.

## Against the first O2 measurement

The first O2 census (585 roots, code `4d658f4c6`) ran a dylib whose embedded
drat-trim checker had been deleted with its worktree. 17 of its roots were
`[TCG-PASSVAL-067]` refusals: a missing checker, reported as a solver timeout.
The diagnostic now names the missing checker (CHANGELOG, OD-225's lane), and
the census scripts refuse such a dylib.

Against that census, `7ee0def54` promotes 3 roots and adds no new failure.
The 17 PASSVAL roots now fail on their own O2 refusals.

First refusal per root (`root_classes.py`, 2026-09-27 record):

| class | `7ee0def54` | first measurement |
| --- | ---: | ---: |
| machine blocks do not correspond to LIR blocks | 346 | 335 |
| a row references a stack slot through a scaled index | 118 | 113 |
| a machine row outside the body domain (SIB loads and stores, `AddMR`, …) | 92 | 88 |
| no observable (OD-115) | 9 | 9 |
| inconsistent type hint | 1 | 7 |
| no traced function: the bridge's `Rvalue::RawPtr` refusal (3), and at first the 17 missing-checker `[TCG-PASSVAL-067]` | 3 | 20 |
| other: escaping slot address, cyclic or two-entry LIR, block parameter, `IndexedUnbounded`, bound but not certified | 13 | 13 |

The type-hint class fell from 7 to 1 because OD-225 stopped
`lir_unsigned_range` from folding branches in proof-claiming compiles.

## Attribution

| opt-out | promoted | newly failing | failure records that changed but still fail |
| --- | ---: | ---: | ---: |
| `no-x86-block-merge` | **204** | 0 | 38 of 378 |
| `no-x86-loop-rotate` | 0 | 0 | 58 of 582 |
| `no-x86-ifconvert` + `no-x86-cmov-swap` | 3 | 0 | 56 of 579 |
| all seven | 248 | 0 | — |

- **`X86BlockMerge`** is the largest single cause. Turning it off promotes 204
  roots and adds no failure. Its shape is a machine block lowering a merged
  LIR chain. Slice 24a (an exact merged-chain quotient in the body theorem)
  is aimed at exactly that shape. Its design estimated 120–175 promotions
  among the B1 first hits. This census bounds what removing the shape gives:
  204, measured without the merge.
- **`X86LoopRotate`** decides no root's outcome. The knob does take effect:
  58 refusals move (for example, `DecimalSeq::left_shift`'s refusing row
  moves from 96 to 94). But no root promotes, and no root newly fails. Rotated
  loops are refused for other reasons first.
- **If-conversion and cmov-swap** together decide 3 roots.
- **With all seven off**, 334 roots remain:
  - 128 stack-slot SIB rows and 92 out-of-domain rows, the scope of slice 25
    (SIB memory rows and RMW rows);
  - 84 machine blocks that still lower rows of several LIR blocks, plus 1
    pair of machine blocks lowering one LIR block. These come from passes
    outside the seven (for example LICM's pure-only tier and the cross-block
    seeding of CSE and slot forwarding);
  - 9 OD-115 bodies and the LIR-side and bridge residue.

The attribution censuses are diagnostics. A configuration with passes turned
off is not a shipping configuration, and its promoted roots are not credit at
O2's default.

## Attribution, second round: the backend's own pass levels

Three more censuses from the same knob bridge (`85d236b37`) and
`lane/chain_attrib2.sh`. Each keeps `-Copt-level=2`, so rustc's MIR
optimizations still run.

| Row | Backend | Failed roots | Promoted | Newly failing | Objects | Wall |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `o2k-b0` | `-Ztrust-ir-cg-args=opt-level=0`: no x86 machine pass | **36** | 546 | 0 | 1254 | 3474 s |
| `o2k-b1` | `opt-level=1` | 388 | 196 | 2 | 900 | 556 s |
| `o2k-nmax` | O2 with every pass opt-out that exists: the seven above plus `no-x86-vectorize`, `no-x86-strength-reduce`, `no-x86-slot-forward`, `no-x86-bce`, `no-x86-xorshift-demanded-bits`, `no-partial-unroll`, `no-const-addr-unroll` | 332 | 250 | 0 | 956 | 447 s |

- **The MIR-level O2 shapes cost 16 roots.** With no x86 machine pass,
  rustc's O2 MIR (inlining, the `&&value` format chains) leaves 36 roots
  against O0's 20: the same 9 no-observable bodies, bound-but-uncertified
  bodies, and the `Rvalue::RawPtr` and LIR-side residue. **The other 546 O2
  roots come from the backend's x86 machine passes.**
- **The passes no knob turns off.** With all 14 knobs off, 332 roots remain.
  The passes without an opt-out (`X86Peephole`'s SIB folds, constant folding,
  copy propagation, CSE, DCE, LICM's pure-only tier) make them:
  - 128 stack-slot SIB rows and 91 out-of-domain rows (slice 25);
  - 85 machine blocks that lower rows of several LIR blocks.
- **The O1 backend** is a different schedule, not a subset of these
  censuses. It names 2 roots that O2 does not:
  - `core::str::traits::check_range`, at its machine row 84;
  - `<Formatter as Write>::write_char`, at its machine row 10.
  Both are out-of-domain rows, not a mismatch and not a refutation.
- **Not a proposal to ship O0 under proofs.** Backend O0 is a measurement of
  where the O2 gap comes from. The route stays the theorem slices (24a
  merged chains, 25 SIB and RMW rows, then the several-block rows the
  remaining passes make), not a slower proof-mode schedule.

## Payloads

The census directories, bridges, dumps and logs are out of tree, bound in
[PAYLOADS.md](PAYLOADS.md) by size and SHA-256. `lane/payloads_o2.py`
regenerates the table.
