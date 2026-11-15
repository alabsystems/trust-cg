# Darwin x86-64 `library/core` proof census at O2: LICM against rotation on slice 25, and the `slice_error_fail_rt` refutation — 2026-11-07

This record closes two items the
[2026-11-06 knob-ceiling record](../2026-11-06-darwin-x86-64-o2-knob-ceilings/README.md)
left open:
- how slice 26's 111-root ceiling splits between LICM and loop rotation;
- what the body `core::str::slice_error_fail_rt`, refuted in that record's
  knob runs, is.

Nothing here is a completion claim. A knob run is a diagnostic of what a slice
could reach: it is not a shipping configuration, and its promotions are
credits of different code. A refutation is never a credit.

## Setup

The host, compiler, proof tools, flags and bridge are the knob-ceiling
record's:
- main `b30110fcd`;
- bridge SHA-256 `9f8567d7…0e759461`;
- AY 0.27.0 build 13556 and Clean 5f09e36c;
- `-Copt-level=2`, proofs required, `x86-body-trace` on.

Each census runs a copy of the bridge under its own tag. The two new copies
(`o2k-m301-l.dylib`, `o2k-m301-r.dylib`) are byte-identical to
`o2-m301.dylib`, as are the `lr`, `all` and `allbm` copies. The two new
censuses ran one after the other, by `lane/run_censuses.sh`:

| run | knob | failed roots | wall |
| --- | --- | ---: | ---: |
| `o2k-m301-l` | `no-x86-licm` | 178 | 2882 s |
| `o2k-m301-r` | `no-x86-loop-rotate` | 253 | 819 s |

`l` took 2882 s (22:40 to 23:28) against 819 s for `r`. The cause was not
recorded.

`lane/compare.sh` compares each census with the plain census `o2-m301` (254)
and with `o2k-m301-lr` (both knobs, 143). It uses the knob-ceiling record's
three tools: `census_compare.py`, `root_classes.py` and `census_s25.py`.

## The split

| comparison | promoted | newly failing | named mismatches |
| --- | ---: | ---: | ---: |
| `l` against plain | 76 | 0 | 0 |
| `r` against plain | 1 | 0 | 0 |
| `lr` against `l` | 35 | 0 | 0 |
| `lr` against `r` | 110 | 0 | 0 |

The sets nest: `l`'s 76 and `r`'s 1 are among `lr`'s 111. So of slice 26's
111 roots:
- **76** are promoted once LICM alone is off;
- **1** once rotation alone is off: `core::num::imp::bignum::Big32x40::mul_pow5`,
  whose whole loop sits in one machine block;
- **34** only when both are off.

No root is promoted by either knob alone in both censuses. All 111 bind and
replay Valid in `lr`.

On slice 24a's base, the 2026-11-04 record found that both knobs promoted 36
roots: LICM off alone promoted 21, and rotation off added 15 more on top of
LICM off. The split of those 36 is unchanged on this base: the 21 are
LICM-alone here, and the 15 still need both. The other 75 of the 111 still
failed on slice 24a's base at a row that slice 25 admits.

**The shapes in plain.** `s26-rebase/per_root.tsv` holds one row per root. In
the plain census, every one of the 111 first refuses at a merged machine
block:

| shape of the merged block in plain | roots | LICM alone | only both | rotation alone |
| --- | ---: | ---: | ---: | ---: |
| LICM moved body rows into the preheader block | 57 | 25 | 32 | 0 |
| LICM moved header rows into the preheader block | 53 | 51 | 2 | 0 |
| rotated header | 1 | 0 | 0 | 1 |

**What the 35 refuse with LICM off alone.**
- 33 refuse at a merged block of rotated-loop shape: the header's test sits in
  the latch.
- 2 refuse at rotation's block duplication:
  - `core::num::imp::dec2flt::decimal_seq::DecimalSeq::left_shift`: "machine block
    … continues to LIR blocks …";
  - `core::slice::memchr::memchr`: "machine blocks … both lower LIR block …".

**What the 110 refuse with rotation off alone.** Each keeps its plain LICM
shape at the same machine block.
- For 99, the refusal text is byte-identical to plain's.
- 11 differ:
  - 10 of the `skip_search` / `binary_search_by` and conversions-lookup family
    list 2 member LIR blocks instead of 4 (`[1, 5]` against
    `[1, 5, 14, 15]`), over the same 12 rows: with rotation off, the
    merged-chain quotient chains `Block(5) = [5, 14, 15, 16]`;
  - `Big8x3::mul_pow5` (in `bignum::tests`) keeps members `[2, 5]`; only its
    quotient changes.

So rotation does not create these merged blocks: with it off, all 110 keep
theirs at the same machine block.

## `core::str::slice_error_fail_rt` is a statement artefact

**Where it is refuted.** `l`, `lr`, `all` and `allbm` refute it: LICM off
alone produces it. Plain and `r` do not. In plain, the function first refuses
at a merged machine block (`Block(23)` lowers LIR blocks `[54, 56]`) before it
binds. It fails in every census and is not one of the 111.

**The replays.** Every dumped part of the three knob-ceiling runs was replayed
on AY 13556 with `(get-model)` (`lane/replay.sh`). In each run, parts 2 and 3
are sat and every other part is unsat.

The function is compiled in two codegen attempts, each traced:
- the first binds 1306 rows, stated in 9 parts (8 in `allbm`);
- the second binds 1334 rows, stated in 8 parts.

The second attempt's part files overwrite the first's in the census dump.
`lane/corerun.sh` re-ran the `lr` compile of core with the same compiler,
bridge bytes, flags and knobs, plus `trace-peephole-entry`, and snapshotted
every dump version. The re-run's trace lines for this function equal the
census's, counterexample included. Its parts match the census dump:
- the second attempt's 8 parts are byte-identical;
- the first attempt's parts 1–7 and 9 are byte-identical; its part 8 is its
  own.

The first attempt's parts replay the same way: 2 and 3 sat, the rest unsat.
`corerun.sh` writes beside itself, so it runs from a copy under
`~/tcg-scratch/sefrt-diag/corerun/`, never from `lane/`. Its snapshot
directory was sorted into the per-attempt directories by hand, and no lane
script does that step.

**The mechanism.** The source is `library/core/src/str/mod.rs`, plus the
function's runtime MIR under the census flags.
- `len` (`PtrMetadata` of `s`) is an immutable local. The only place its
  address is taken is the diverging `panic_fmt` blocks, so it is memory-backed
  in slot 68.
- On the machine side, the only store to slot 68 is `Block 0`'s
  `MovMR [v73+0], v120`, with `v73 = Lea [slot68+0]`. `v120` is `s.len`,
  reached through two store/reload levels in the machine rows. The slot's
  address escapes only as copies into blocks 1, 3 and 20, which call
  `panic_fmt`.
- The compares the counterexamples break use copies of `v120`, which the
  statement carries as `e_rsi`. Blocks 15, 21 and 44 reload slot 68 and
  compare that.
- At the cuts `Block(2)`, `Block(6)` and `Block(9)`, slot 68's eight bytes
  are free byte inputs. The cell is stored from a reload, so it is not
  leaf-closed.

**The counterexamples.**
- Part 2: `e_rsi = 0`, `e_rcx = 1` and slot 68 holding 2^56. The source takes
  the in-bounds edge and the machine the panic edge.
- Part 3: `begin` equals slot 68's value but not `e_rsi`.

Both need slot 68 to differ from `e_rsi`. No run can produce that: every run
stores `s.len` into slot 68 once, in `Block 0` before its branch, and nothing
writes the slot afterwards. So this is not a miscompile. It is the class of
`core::wtf8::slice_error_fail`, the cut-interface gap reserved for OD-233.

**Under OD-233's rule.** OD-233 defines a cut input that the source fixes for
the run as its source term, and claims it on every edge. `lane/synth.py`
applies the assumption half of that rule to one dumped part, spelled as the
OD-233 design spells wtf8's part 2:
- it defines slot 68's bytes as the bytes of `p1`, with `p1 = e_rsi` bound by
  hand;
- it adds no per-edge claims and changes nothing else.

Its `wrong` mode replaces `e_rsi` by `e_rsi + 1` in the machine-side compares
that the counterexamples break: 2 in part 2, 5 in part 3.

| query | AY 13556 | certificate | Clean 5f09e36c |
| --- | --- | --- | --- |
| part 2 defined | unsat (662 ms) | strict, trust-free, 0 unproved steps | fully verified (0.33 s) |
| part 3 defined | unsat (4624 ms) | strict, trust-free | fully verified (0.53 s) |
| part 6 defined (already unsat; non-regression) | unsat | strict | fully verified |
| `allbm` part 3 defined | unsat (2895 ms) | strict, trust-free, 0 unproved steps | not run |
| part 2 defined, machine `len + 1` | **sat** | — | — |
| part 3 defined, machine `len + 1` | **sat** | — | — |
| `allbm` part 3 defined, machine `len + 1` | **sat** | — | — |

For this record's fact check, `lane/synth.py` regenerated all seven queries
byte-identically, and they were re-run on AY 13556
(`sefrt-diag/synth-recheck/`). The verdicts and certificate fields are the
same. The timings differ: 614, 3715, 2603 and 3705 ms for the four defined
queries.

With the definition, the queries are unsat. With the broken machine compares
mutated to `len + 1`, they are sat. The per-edge claims are not part of these
queries.

**Not established.** It was not measured whether OD-233's implementation
derives this definition and discharges its per-edge claims. On the machine
side, the value passes through two store/reload levels. At `b30110fcd`, the
closed-term node bound in `split.rs` is checked before normalization. Until
OD-233's bridge replays this function Valid in an LICM-off census, a slice
must not credit a body that LICM changed. The revised slice 26 design
(out of tree) makes that a gate of its LICM step.

## Not measured

- These censuses on the current main: the trust-ir pin and the LIR adapter
  moved after `b30110fcd`.
- O0: neither pass runs at O0.
- OD-233's bridge on `slice_error_fail_rt`.

## Payloads

Out of tree, bound in [PAYLOADS.md](PAYLOADS.md).
