# Darwin x86-64 `library/core` — slice 24c (if-converted regions as segments), 2026-11-05

Slice 24c of the x86-64 source-bound whole-body theorem
(`crates/trust-cg-verify/src/x86_source_bound_body.rs`) states a machine
block that lowers a single-entry region of LIR blocks over its **segments**:
the diamond or two-way switch `X86IfConvert` folds into its head's block
(with any chain the block merge joined to it) is paired with every source
path through the region. It targets the OD-226 declines that stop 116 of
census-o2-s24a-f's 378 failed roots first, and the nine roots whose arms are
all stamp-silent (`LIR block b has no machine block`), as designed in
`~/tcg-scratch/s24c-design/README.md` (angle B: §2 the rule, §3 the
refusals, §5 the controls, §8 the plan; M2, the routeless-edge claim of
§2.9, is ruled and specified, not built).

| Ruling | Rule | Design |
| --- | --- | --- |
| OD-228 | a segment `(h, m, S)` chosen by the stamps and re-derived by `segment::check`; `lowering` one to one (`h` to `m`), `m`'s successors exactly the exit targets, `m` walked once per exit target from `h`'s entry against the effect member's program, members walk nothing, no cut inside a segment or at a parameterized exit target | §2.1-§2.8 |

Host: the shared x86_64 Mac (8 logical CPUs, Darwin 22.6, i7-7920HQ), other
lanes building and replaying throughout; every build through
`scripts/trust_cargo.sh` with the local overlay `x86-stage1-ay13556-t011`
(`targo --unverified`, `-j2`, through `build-slot` at `BUILD_SLOT_MEM_GB=6`;
no proof claim about any build). One `build-slot` hold ran a queue of job
files (`scripts/server.sh`), since the slot was lost between separate jobs.
Replayer pair: AY 0.27.0 build 13556 with Clean 5f09e36c (the overlay's
`bin/ay` and `bin/clean`). Branch `feat/x86-body-slice24c` (worktree
`~/tcg-scratch/wt-s24c`) from `a617488aa` (slice 25 merged with
`origin/main` `12ebba653`, so OD-232 is in the base). The fails-before record
ran in a detached worktree at `a617488aa` (`~/tcg-scratch/wt-s24c-base`).
Payloads are out of tree; [PAYLOADS.md](PAYLOADS.md) binds each by size and
SHA-256. The same day a review round (20 findings) amended the slice; its
dispositions are in *Review round*, and every count below is the amended
head's unless it says otherwise.

## Census: the ceiling

The census of the slice-24c head is the next section (*Census: the
slice-24c head*). This section is the ceiling the design's §7 "Before
building" asks for, measured first, on the slice-25 base: slice 25's
release bridge (`~/tcg-scratch/runs/o2-s25.dylib`, copied byte for byte as
`o2k-s25-nifc.dylib`, SHA-256 `2e47fae1…`) compiled `core` at O2 with
`no-x86-ifconvert` and `no-x86-cmov-swap` (census-o2k-s25-nifc, 873 s,
budget refusals 0), and the read-only analysis `scripts/ceiling.sh` compared
it with the same bridge's default census, census-o2-s25:

| | census-o2-s25 | census-o2k-s25-nifc |
| --- | ---: | ---: |
| failed roots | 254 | 213 |
| promoted | | 41 |
| newly failing | | 0 |
| named mismatches | | 0 |
| refuted bodies | 1 | 1 (the same) |

- **Every promoted root is a slice-24c candidate** whose named function
  binds `replay=Valid` without if-conversion. By its first refusal in
  census-o2-s25: 24 `; not contracted: … ends in a Brif` (7 if-converted
  diamonds with both arms named, 17 with one arm named and the other
  stamp-silent), 8 `… ends in a Switch` (two-way `Switch` diamonds, both
  arms named) and 9 `LIR block b has no machine block` (all arms
  stamp-silent). None comes from the 98 two-entry roots (97 LICM header
  rows, 1 rotation), the 5 off-chain roots, the 21 LICM body-row `Brif` or
  `Switch` declines or `other`. At the function level 1000 functions are
  Valid on both sides, 41 go from refused to Valid, 252 stay refused, and
  the 4 uncertified bodies and the 1 refuted body are unchanged.
- **Candidates.** The design's classifier (`work/classify.py`, in
  `ceiling_s25.py`) with the no-machine-block roots finds 46 functions (46
  roots). One, `Big32x40::mul_pow5`, is a false positive: its machine block
  3 lowers LIR `[4, 5, 12]`, and `4 -> 5 -> 12 -> 4` is a single-block loop,
  which C3 refuses (its trace is byte-identical with if-conversion off, and
  `ceiling_s25.py` tags it `[LOOP]`). Of the 45 others, 41 bind without
  if-conversion (7 of 9 two-armed `Brif` diamonds, 17 of 19 one-armed, 8 of
  8 `Switch`, 9 of 9 all-silent), and every root of those 41 promotes. The
  4 that do not bind are the S24a base's 4 (`dragon::format_shortest` and
  the `Big8x3`/`Big32x40` `Debug::fmt`, next stopped by an LICM header-row
  block; `run_utf8_validation`, by an LICM body-row `Brif` block). All 43
  S24a-base candidates are still candidates with the same shape; slice 25
  unmasked 3 more (`TypeId::trait_info_of_trait_type_id`, a two-way
  `Switch`, and `dec2flt::lemire::compute_product_approx`, one arm, both
  binding; and `mul_pow5`). The ceiling is 41: the S24a base's 39 and 2.
- **The refuted body** is `core::wtf8::slice_error_fail` (two trace lines,
  bound rows 555 and 571, two codegen attempts), the same function and rows
  as census-o2-s25: OD-227's cut-interface completeness gap, OD-233's slice.
  It is not a slice-24c finding and gets no credit.
- **What 41 means.** Slice 24c takes the O2 count from 254 to **no lower
  than 213**. The census ran on code with no if-converted block, so 41 is an
  upper bound: on default O2 a segment must state the if-converted block
  itself (the `cmov` judged against the source's join), the parts route's
  plans (5 S24a-base candidates were stated in parts with every pass off)
  and any refusal the if-converted form masks decide how many it reaches.
  The slice-24c head's census reaches 39 of the 41 (215 failed roots; the
  next section).
- **The classifier.** The census's first-refusal classes come from the
  O2-keyed `root_classes.py` copied into `scripts/` (SHA-256 `0a2f4d4f…`,
  slice 25's `b30110fcd` version, whose O2 keys, `; not contracted: ` and
  `lowers rows of several LIR blocks` among them, come before the legacy
  substring keys). The header of `scripts/ceiling.sh` says the copy is the
  file "at a617488aa"; it is not: `a617488aa`'s
  `reports/perf/2026-09-27-darwin-x86-64-census/root_classes.py` is the
  legacy version (`3bd9c5fc…`), whose `('a loop', 'loop')` key precedes
  every O2 key and would count the LICM header-row roots, which carry N3
  (`… is a loop header`), as `loop`. The scripts are kept byte-identical to
  the ones that ran (`SHA256SIZES.txt`). With the O2-keyed copy, the
  slice-25 base's 204 `merged block not contracted` and 9 `no machine
  block` roots become 172 and 0 under nifc. The census record commits the
  O2-keyed classifier to the tree, byte for byte slice 25's `b30110fcd`
  version plus one key after the legacy ones, N11's (`both have calls,
  accesses, rounding operations, stops or indexed accesses`, classed
  `segment: effects in two members (N11)`), with a comment; the head's
  census reads the in-tree file (`scripts/analyse.sh`). Other refusals of
  pairs stated over segments keep the older classes (at O3, a loop-carried
  `MovRR` is a machine-row class, and the cut pairing's `no machine row
  writes a register …` falls to `other:`). The comment was reworded after
  the census ran (it named every refusal over segments; the list holds only
  N11's); the code is as it ran. Rerun with the reworded file, the
  classifier prints `s24c-run/census/o2/root_classes{,.base}.txt`, and
  `census_segments.py` writes `s24c-run/census/o2/segments/` and
  `s24c-run/diag-o3/compare/segments/` (and prints `segments.log`), byte
  for byte.
- **Payloads.** The census directory
  `~/tcg-scratch/runs/census-o2k-s25-nifc`, its log
  `s24c-run/logs/census-o2k-s25-nifc.log`, the comparison in
  `s24c-run/census/nifc/` (`compare.txt`, `promoted.txt`,
  `newly_failing.txt`, `slice15_transitions.tsv`, both `root_classes`
  tables, `ceiling.log`) with the attribution in
  `ceiling/{ceiling.txt,candidates.tsv,roots.tsv}`, and the size and SHA-256
  of every input and output in `SHA256SIZES.txt`, are bound in
  [PAYLOADS.md](PAYLOADS.md). The S24a-base nifc comparison the design's
  addendum cites as `s24c-run/census/nifc/` (378 -> 339) moved, byte for
  byte, to `s24c-run/census/nifc-s24a/`.

## Census: the slice-24c head

`scripts/census.sh` (one `build-slot` hold, 2026-11-07, its log
`s24c-run/logs/census-s24c.log`) built the release bridge at `38feaf386`
(`build_bridge.t011.sh`, 79 min; `38feaf386` changes no build input from
`cfbaf6369`, the review round's code) and ran the O2, O0 and O3 `core`
proof censuses from that one dylib (SHA-256 `ca167574…`, copied byte for
byte as `o2-s24c.dylib`, `o0-s24c.dylib` and `o3-s24c.dylib`) with
`census_t011_dylib.sh`: the overlay's `trustc 1.99.0-dev (d7f143f3b
2026-09-21)`, `-Copt-level=N -Ccodegen-units=1 -Cpanic=abort
-Ztrust-verify=off`, proofs required (the bridge default), the
`x86-body-trace` and `x86-body-dump` arguments, the overlay's replayer
pair (above). `scripts/analyse.sh` (read-only) then compared O2 and O0 with
slice 25's censuses, the named baselines, from slice 25's bridge at
`d92b944fe` (`runs/o2-s25.dylib`, `2e47fae1…`; the base `a617488aa` is that
head with `origin/main` `12ebba653` merged, whose OD-230/231 change no
`core` O2 object and whose OD-232 knobs are off by default: the census
table's loop-knobs row), and applied the stop rule (`scripts/stop_rule.py`)
to all three. The O3 baseline came after the stop (*The O3 stop*). Wall
times are of a shared host and are not compile-time evidence.

| | O0 | O2 | O3 |
| --- | ---: | ---: | ---: |
| baseline | census-o0-s25 | census-o2-s25 | census-o3-s25 (run after the stop) |
| failed roots, baseline -> slice 24c | 20 -> 20 | 254 -> **215** | 267 -> 261 |
| promoted | 0 | 39 | 6 |
| newly failing | 0 | 0 | 0 |
| named mismatches | 0 | 0 | 0 |
| refuted trace lines (both sides) | 0 | 2 (the known `slice_error_fail` attempts) | 4 (the stop) |
| emitted objects, baseline -> slice 24c | 3426 -> 3426 | 1034 -> 1073 | 1021 -> 1027 |
| budget refusals | 0 | 0 | 0 |
| wall, slice 24c (baseline) | 5968 s (2465 s) | 2750 s (909 s) | 948 s (957 s) |

- **O2: 254 -> 215.** The 39 promoted roots' functions bind `replay=Valid`
  stated over segments (a `segments=` line; census-o2-s25 has none): by
  kind set 29 diamond, 9 silent and 1 diamond+silent, no chain-only (44
  segments, 32 diamond and 12 silent; 34 functions with one, 5 with two).
  By first refusal in census-o2-s25: 22 `; not contracted: … ends in a
  Brif`, 8 `… ends in a Switch` and 9 `LIR block b has no machine block`
  (the 9 silent ones). Every promoted root is a ceiling promotion (by
  `ceiling_s25.py`'s shape 13 both arms named, 17 one arm, 9 all-silent),
  and none is promoted here that the ceiling did not promote. The ceiling's
  other 2 are the `FloatExt::integer_decode` pair (`f32`, `f64`), now
  refused by N11 (`LIR blocks Block(0) and Block(1) in the segment of
  Block(0) both have calls, accesses, rounding operations, stops or indexed
  accesses (over segments: …)`): design §9's one-effect-member limit, which
  the design knew no candidate to need. No promoted root's function is
  refuted.
- **The O2 classes** (the in-tree `root_classes.py`, its N11 key included):

  | first refusal | census-o2-s25 | census-o2-s24c |
  | --- | ---: | ---: |
  | merged block not contracted | 204 | 168 |
  | LIR block with no machine block | 9 | 0 |
  | several LIR blocks in one machine block | 0 | 4 |
  | segment: effects in two members (N11) | 0 | 2 |
  | no observable | 9 | 9 |
  | bound, no certified proof: 2 `replay=none (no independently checked proof)` (`as_chunks`, Clean refused AY's proof; `wide_mul_u128`, AY timeout) and 2 `replay=Unknown (FP abstraction …)` (the two `Lemire::from_u64`) | 4 | 4 |
  | bound and refuted: `core::wtf8::slice_error_fail` (`replay=Invalid (refuted)`) | 1 | 1 |
  | machine row outside the body domain: `SbbRR` | 4 | 4 |
  | 12 other classes, each unchanged: 3 `(no fn in message)`, 3 slot address escapes, 3 `Setcc`, 3 past the parts bound, 2 `RolRCl`, 2 `machine blocks M and M' both lower`, 2 loop header entered from several edges, 5 single roots | 23 | 23 |
  | total | 254 | 215 |

  `root_classes.py` prints the two `bound` rows as one class, `bound, not
  certified (AY)`, 5 on each side (`s24c-run/census/o2/root_classes.txt`
  and `root_classes.base.txt`): it sends every `replay=` line but
  `replay=Valid` there, the refuted one included. They are split here by
  the five functions' last trace lines in each census's `stderr.log`, so
  that the refuted body is not counted as uncertified (slice 25's record
  writes the same 5 as `bound with no certified proof (4 as before, and the
  refuted body)`).

  The 36 roots that leave `merged block not contracted` are 30 promoted,
  2 now refused by N11, and 4 that now stop at `several LIR blocks in one
  machine block`: `dragon::format_shortest` and the `Big8x3`/`Big32x40`
  `Debug::fmt` with N3, and `run_utf8_validation` with N1, the four
  candidates the ceiling found stopped next at an LICM block. OD-226's
  note, appended only to a refusal at the machine block it is about, is
  gone from their text. The 9 that leave `no machine block` are all
  promoted.
- **The remaining 215 by chooser decline.** 172 last lines carry `; no
  segment:`: 100 N3 (`LIR block H is a loop header`: the LICM header-row
  roots), 71 N1 (`… is entered from [..], and … is not in the segment of
  …`) and 1 C3 (`… branches back to its head`: `Big32x40::mul_pow5`, the
  ceiling's single-block loop). 2 are refused over segments (N11, above);
  no failed root names a function whose theorem is stated over segments.
- **The refuted body at O2** is the known one, `core::wtf8::slice_error_fail`
  (`bound rows=555` and `571`, its two codegen attempts), as in
  census-o2-s25, and the 7 dumped queries of the two O2 censuses are byte
  for byte the same, its three parts among them: OD-233's gap, no credit,
  its object not emitted. A dump directory keeps one file per part per
  function, and a later codegen attempt overwrites an earlier one's: the
  files are each function's last attempt (by their mtimes, in the order of
  the second attempts' trace lines), so the three parts on disk are the
  571-row attempt's; the 555-row attempt's parts were not kept, and its tie
  to the baseline rests on the identical trace lines.
- **O0: 20 -> 20, byte-identical.** `failed_roots.jsonl` and
  `refusals.jsonl` are byte for byte census-o0-s25's; 3457 traced functions
  and 7160 keyed trace lines on each side, none changed (`trace_diff.py`,
  slice 25's no-verdict-change check, byte for byte its `b30110fcd` copy),
  so no function is stated over segments at O0. What differs is the
  unkeyed replay lines, which name no function: `outcome=Timeout` 22 -> 31
  and negative-memo hits 27 -> 29 (`kind=timeout` 15 -> 18,
  `kind=self-check-rejected` 12 -> 11; `outcome=Unknown` 24 -> 24), in 8
  functions (`o0_outcomes.py`; `trace_diff.txt`'s anomalies, the stop rule's
  `NOTE:` lines), each with the same verdict lines on both sides (`bound …
  replay=Valid`). An `outcome=Timeout` line is a replay that reached its
  wall-clock deadline, or a negative-memo hit that reuses one, before a
  fallback decided; a `kind=self-check-rejected` hit reuses a recorded
  self-check rejection instead of running AY again. The run took 5968 s
  against the baseline's 2465 s. These lines are not records, and the stop
  rule prints them as notes.
- **O3: 261.** The design's three counts (§7, M2's trigger), each as failed
  roots at first refusal, functions by last line and trace lines:
  `continues to LIR blocks` 0, 0, 0; `has no route` 0, 0, 0; `has no row
  attributed` 0, 0, 0 (`o3_counts.py`). The routeless-edge claim (OD-228
  (c)) has no census demand at O3 either. Against the O3 baseline (below)
  the 6 promoted roots' functions bind `replay=Valid` over diamond
  segments (7 segments), and of the 261, 191 last lines carry `; no
  segment:` (141 N3, 29 N1, 21 `… ends in a Return`) and 14 are refused
  over segments (9 N11, 4 the cut pairing's `no machine row writes a
  register as the definition of …`, 1 a loop-carried `MovRR`). 0 named
  mismatches; 4 refuted trace lines, the stop.

### The O3 stop

The stop rule stops on a newly failing root (O2 and O0), a named mismatch,
a refuted body other than the two known O2 attempts of
`core::wtf8::slice_error_fail` (rows 555 and 571), or any O0 change. It
held at O0 and O2 and fired at O3 (`s24c-run/census/stop_rule.txt`) on four
`replay=Invalid (refuted)` trace lines of census-o3-s24c (stderr lines 957,
981, 2447 and 2483): `core::str::pattern::StrSearcher::new` at `bound
rows=521`, both codegen attempts (one merged chain, stated in parts=2), and
`core::wtf8::slice_error_fail` at `bound rows=528` and `544`, O3's two
attempts (parts=3). When the rule ran there was no O3 census of the base:
it compared against no earlier O3 census. The baseline, census-o3-s25, was
produced afterwards from slice 25's dylib (`runs/o2-s25.dylib`, copied
byte for byte as `o3-s25.dylib`) under the same flags
(`s24c-run/diag-o3/base_o3.sh`, 957 s): the first O3 baseline on this base,
in the ruling's words. That dylib is slice 25's head `d92b944fe`, not the
branch base `a617488aa`: the merge between them brings OD-230 (a rotated
loop test reads what the header read, `x86_rotate.rs`; a pure call moves
ahead of a loop only from the first iteration's path, `x86_licm.rs`) and
OD-231's and OD-232's tracked opt-outs (off by default). The base
equivalence above is measured at O2 only (the loop-knobs row); at O3 it is
not measured. What is measured at O3 is the delta: 267 -> 261 is the 6
promotions alone, each with a `segments=` line, 0 newly failing, emitted
objects 1021 -> 1027, and no verdict change of a function bound on both
sides (`diag-o3/compare/compare.txt`).

A dump directory keeps one file per part per function, and a later
codegen attempt overwrites an earlier one's. The dumped parts named below
(and the AY models in `diag-o3/ay/`, made from `dump-o3-s24c`) are each
function's last attempt, by their mtimes in the order of the second
attempts' trace lines: `StrSearcher::new`'s second 521-row attempt,
`slice_error_fail`'s 544-row attempt at O3 and its 571-row attempt at O2.
The 528-row attempt's parts (and the 555-row attempt's at O2) were not
kept; their tie to slice 25 rests on the identical trace lines (ground 1).

**Ruling** (the orchestrator, 2026-11-07; recorded, not re-decided here):
none of the four lines is caused by slice 24c, and the stop does not block
landing. A refutation is never credit: both functions are failed roots at
O3 and neither's object is emitted, with either dylib. The grounds, each
checked against the files:

1. census-o3-s25 has the same four lines; both functions' trace lines (ten
   on each side) are identical, and the 9 dumped queries of the two O3
   censuses, both functions' five parts among them (each function's last
   attempt), are byte for byte the same.
2. Against census-o3-s25, slice 24c goes 267 -> 261: 6 promoted, all over
   diamond segments (by first refusal before: 2 `… ends in a Brif`, 2 `…
   ends in a Switch`, 2 `… is entered from [..]`), 0 newly failing, 0 named
   mismatches (`s24c-run/diag-o3/compare/`).
3. `slice_error_fail` at O3 refutes part 2 of 3: the 544-row attempt's
   part 2 is byte for byte the known O2 refuted part 2, the 571-row
   attempt's (SHA-256 `104676bd…` in `dump-o2-s25`, `dump-o2-s24c`,
   `dump-o3-s24c` and `dump-o3-s25`), with the known model (slot 37's bytes
   `0x0100000000000000`, `e_rsi = 0`, `e_rdx = 0`, `e_rcx = 1`; parts 1 and
   3 unsat; `s24c-run/diag-o3/ay/`): the OD-233 cut-interface class, as
   slice 25's record diagnoses it at O2. Its standalone reproducer
   (`diag-o3/wtf8/lib.rs`, a byte copy of slice 25's `diag-wtf8/lib.rs`) is
   refuted at O3 at 544 rows through both dylibs, its three dumped parts
   byte for byte the census's.
4. `StrSearcher::new` at O3 is a further instance of the same class,
   diagnosed from its rows (the pre-RA rows,
   `diag-o3/strsearcher/s24c-o3-peephole/peephole.log`): block 0 stores the
   needle registers (`rcx`, `r8`) into slot 2 and copies them into slot 6
   through slot 2's forwarded loads, so slot 6's stored values are load
   results and its bytes are free at the cut, while block 2, whose only
   predecessor is block 0, calls `TwoWaySearcher::new` with the forwarded
   registers, and the cut carries them exactly, as `e_rcx` and `e_r8`. Part
   2's whole obligation is `slot6[0..8] = e_rcx` and `slot6[8..16] =
   e_r8`; AY's model has slot 6's bytes 0..7 = `0x0100000000000000` and
   `e_rcx = e_r8 = 0`. It needs `slot6 != needle`, which no run reaches:
   one store, one edge, no write in between. It is not a miscompile. Part 1
   is unsat. The function has no `segments=` line, and at O2 it binds
   `replay=Valid` in one part (530 rows) in census-o2-s25 and
   census-o2-s24c. A verbatim copy of it and the `TwoWaySearcher` items it
   calls (`diag-o3/strsearcher/lib.rs`) reproduces both: at O3, 521 rows in
   two parts, refuted, through both dylibs, its two dumped parts byte for
   byte the census's; at O2, 530 rows in one part, `replay=Valid`.

Whether OD-233's rule closes `StrSearcher::new` at O3 is not measured in
this lane; it will be measured on the combined S24c + OD-233 bridge.

**Method, from this stop on:** a lane that adds an O3 census runs its O3
baseline (the base dylib at O3) in the same session, before reading the
stop rule.

**Payloads** ([PAYLOADS.md](PAYLOADS.md)): the census log, the dylib, the
three census directories with their driver outputs and dumped queries, the
baselines (slice 25's dylib `runs/o2-s25.dylib` and its byte copies
`o0-s25.dylib`, `o2k-s25-nifc.dylib` and `o3-s25.dylib`; census-o2-s25 and
its dumps, census-o0-s25; census-o3-s25 and its dumps), the comparison in
`s24c-run/census/{o2,o0,o3}` and `stop_rule.txt`, and the stop's diagnosis
in `s24c-run/diag-o3/`, every file under it (`FILES.txt` indexes it: the O3
baseline and its comparison, the AY models, both reproducers with their
traces, dumps, emitted objects, witnesses and TrustIR containers, the
pre-RA rows and the lowering-only object), with slice 25's
`s25-run/diag-wtf8/lib.rs`, of which `diag-o3/wtf8/lib.rs` is a byte copy.
The census directories' `obj/` subdirectories are not bound.

## Soundness notes first

- **The stamps choose; the check decides.** `segment::choose` reads the TV-1
  stamps and is untrusted; `segment::check` re-derives every clause of the
  rule from the LIR and the machine's stamps in every build, and a chooser
  output it does not re-derive is a construction refusal (no claim). The
  forged-output controls (W16) give the check one forged output per clause
  a forged output can reach first (C1's dead head and unlaid machine block,
  C0's unnamed head, named outsider, bodiless block, shared machine block,
  overlap and entry from a member, the member order, C2's outside entry,
  C3's backward edge, C5's returning member, the exits, C6's exit into a
  loop header, C7's dispatch row, and the entry as a member, which the
  order clause refuses), each refused by its clause's text; each clause has
  a mutant (`s24c-check-*`) that the forged output it guards then fails.
- **`lowering` stays one to one.** Only the head maps to `m`; members map to
  nothing, so no correspondence, cut pairing or stamp search can read a
  member's machine rows as its own. No production path reads `machine_of`
  (member to `m`): every stamp search and the cut pairing read `lowering`;
  only two test mutants substitute it. With the parts bans off, a cut at the
  join pairs nothing and refuses, and with `machine_of` in its place the
  same cut is stated and refuted (`s24c-cut-pairing-machine-of`).
- **Exits, not routes.** `m`'s successors must equal the region's exit
  targets (N7). An exit `m` cannot take is refused by name; the
  routeless-edge claim (M2) that could credit it is not built.
- **Members walk nothing, and the theorem re-checks it.** `build_theorem`'s
  member guard (C11) refuses a member that ends in `Return` or `Trap`, a
  member with an event and no walk, and a walk on any member but the effect
  member `E`, which it re-derives from the units' own programs, every build
  (the theorem states a unit's stop and in-bounds claims under that unit's
  guard, so `m`'s walk on another member would claim them only on some
  runs). With the walk kept by the last member (`s24c-walk-on-member`) the
  guard refuses P1's DAG theorem by name; under the guard as first written
  (`s24c-guard-one-walker`: at most one walk, on any member) the same
  misplaced walk is stated.
  With the chooser's trap decline off and the guard off together
  (`s24c-member-any-terminator,s24c-theorem-guard-off`), W17's trapping arm
  is stated and holds: the trap is dropped, so the two clauses are the
  guards against exactly that.
- **One effect member.** Every call, incoming access, rounding operation,
  stop and indexed access of `S` lies in one member every run passes (N10,
  N11). The hazard the rule guards is a machine block that runs a
  non-dominating member's effect on every path: W4s (the then arm's call
  speculated into `m`) and W9s (its `div`) are refused by N10. With the
  rule's dominance clause off in the DAG encoding and the member guard,
  which re-runs the rule, off too (`s24c-effect-off-spine,
  s24c-theorem-guard-off`), W4s's theorem is stated and holds on samples:
  the speculated call is credited, so the two are the guards against
  exactly that. With the whole rule off (`s24c-effects-off`) or two effect
  members allowed (`s24c-two-effect-members`), each with the guard off,
  W5's and N11's DAG theorems stop in the builder, which finds no walked
  access or call to pair with the source's (*Mutants*). A machine-only
  speculated `#DE` (W9m, an unstamped `div`
  by a value that is zero exactly on the else path) is refuted by the
  effect member's stop claims; a machine-only incoming load (W5l) is never
  credited. The dropped-effect edits (W4, W5, W9: an edited source, an
  unedited machine) are named mismatches or N10, never a credit.
- **Flags never cross a member.** The walk resets flags at every machine
  block boundary as before; inside `m`, X86IfConvert re-emits the head's
  compare immediately before the `cmov` in P1, P2, P5, P6 and P9 (stamped
  with the head's compare), and
  ForceSign's `cmov` reads the head's `test` across both arms' rows (the
  `s24c-flags-reset-at-members` control).
- **Composition with OD-226.** The rule runs on the stated LIR: the source,
  or OD-226's quotient when its correspondence needs one. OD-226's
  `; not contracted:` note is appended only to a refusal at the machine
  block the note is about (`first_note_at`), so a segment refusal elsewhere
  never carries a stale decline: N7's refusal carries the note, N6's and
  "both lower"'s do not, each asserted.
- **The parts bans are complete for the cut pairing.** A cut's pairing
  reads `lowering`, which names no machine block for a non-head member, so
  any point where a live value has every LIR definition in such a member
  (a join's parameter, defined by the arms' edge copies, at any point it is
  live, or a value a chain member defines) pairs nothing. The bans name
  every such point (N13, `Ban::Defined`) besides the member points and the
  parameterized exit targets, the planner avoids them, and a test policy's
  point there refuses by its own text; the pieces' re-chosen segments must
  equal the segments the bans were derived from. P12 (the forked tail) is
  stated in two parts only because of it: with the liveness clause off
  (`s24c-parts-defined-no-ban`) the plan cuts in chain `A`, where the join's
  value is live, and the cut pairing refuses (`no machine row writes a
  register as the definition of …, live across cut point …`).
- **The stamps are untrusted, and perturbed.** Every one-row restamp of
  every wrong lowering of `REFUTED24C` and of W4s, W5l and W9s (to
  unattributed, or to each LIR block at the row's index, clamped; 574
  restamps) is refuted on samples (238) or refused (336), never stated and
  holding, and none of the eight shapes' 641 restamps panics (296 still
  hold, 345 are refused; `a_restamped_row_never_credits_a_wrong_lowering`).
- **Not trusted:** the stamps, the chooser, X86IfConvert, X86CmovSwap and
  their inversion admission, every machine pass. **Trusted in addition:**
  no assumption; the generator's trusted code grows by `segment::check`, the
  segment branch of `block_correspondence_over`, `walk_head` and its effects
  rule, `internal_joins` (C10), `walk_region`'s member arm (members skipped,
  `walked before its head` refused), `machine_path`'s member skip, the
  member guard and `segment::in_dag` (the segments it guards), the DAG
  claim floor over segments (the `fewer than two claims` guard is skipped
  over segments; a DAG with no claim is `NoObservable`), the parts bans and
  their liveness clause, and the pieces' segment-equality guard.

## The rule

On the stated LIR (design §2.1-§2.5; `segment.rs`):

- **C0 (stamps).** `m` names `h`; every block `m` names is a member and has
  a body; `m` lowers one segment; segments are disjoint.
- **C1-C3.** `h` is live; `m` is laid out and is neither a jump-table nor a
  search block; every member but `h` is live, is not the entry or a loop
  header, and every live edge into it is from `S`; no member branches to
  `h`; the members start at `h` in topological order.
- **C5.** Every member ends in `Jump`, `Brif` or `Switch` (N5).
- **C7-C9.** No exit enters a loop header (N8); `m` reaches no dispatch or
  search block (N9); every event of `S` is in one member every run passes
  (N10, N11).
- **C10.** No internal join whose private bytes OD-192 leaves dead (N12).
- **Statement.** `m` walked whole, once per exit target, from `h`'s entry
  state, against the effect member's program; each exit claims the machine
  edge under its source guard; internal edges claim nothing; a DAG over
  segments whose claims are all operand claims has no observable (OD-115);
  per path, consecutive members take no machine step.
- **Parts.** No cut point at a non-head member point or at `(h, i > 0)`
  (`a cut point in LIR block b, which the segment of h states inside
  machine block M`), at `(z, 0)` for an exit target with parameters (`… an
  exit target of the segment of h whose parameters machine block M
  copies`), or at any other point where a value is live whose every LIR
  definition is in a non-head member (`a cut point at instruction i of LIR
  block b, where v is live, which only members of the segment of h define
  …`): N13, a policy refusal; the planner never plans one.

A chooser decline is appended to the correspondence refusal it explains as
`; no segment: …`; a refusal of a pair stated over segments names them,
`… (over segments: Block(h)=[members]; …)`, inside OD-226's `(over the
merged-chain quotient: …)`.

## Fixtures

`crates/trust-cg-verify/src/x86_source_bound_body_slice24c_tests.rs`. Every
positive fixture's LIR comes from the trust-ir adapter (`ModuleBuilder`,
translated with an explicit permit). The machine rows of eight (P1-P6, P8,
P9) come from the real selector and the real O2 pipeline
(`run_x86_optimization_passes`; O3 for P9), asserted to contain a `cmov` (a
pipeline that if-converts nothing fails the fixture by name); P11's from the
selector and `X86BlockMerge` alone (OD-226's `D5` pair), so the chain kind
is certified only on a stream no pipeline produced (no O1-O3 theorem over
segments is of the chain kind); P7 is two encodings of P1, not a fixture;
P8s and P12 are the real O2 output with the same `cmov` assertion. No
positive fixture is hand-edited.

| id | shape | segments (kinds) |
| --- | --- | --- |
| P1 `AlignOffset` | `if c < 8 { a + 5 } else { 9 }`: LEA and MovRI arms | 1 (diamond) |
| P2 `WrappingAbs` | `if x < y { y - x } else { x }` (signed): one computing arm, one silent | 1 (diamond) |
| P3 `SelectUnpredictable` | `if c < a { a } else { b }`: both arms silent | 1 (silent) |
| P4 `ForceSign` | a two-way `Switch` of a `u8` onto 10 and 20 | 1 (diamond) |
| P5 `IntegerDecode` | `y = a + b; br n; n: if y < c { y + 1 } else { 7 }` (block merge, then if-conversion; OD-226 declines it) | 1 (diamond) |
| P6 `LoopDiamond` | a bottom-tested loop whose header `h(i, acc)` computes `s = acc + i` and is the diamond `if s < n { s + 3 } else { acc }` into the latch | 1 (diamond), its head a loop header |
| P7 | P1 under the path and the DAG encodings | 1 each |
| P8 `LongDiamond` | P1 whose join `j(v)` computes `v + 7` and heads a 140-block chain: past the single-query block bound, the production parts route (one part over OD-226's quotient) | 1, plus OD-226's chain |
| P8s `ShortTail` | P1 whose join computes `v + 7` and heads a 3-block chain: one query over OD-226's quotient | 1, plus OD-226's chain |
| P9 `JoinContinues` (O3) | P1 whose join continues (`if v < b { v } else { v + 1 }`), merged into the if-converted block: an internal join | 1 (diamond), two exit targets |
| P11 `AbsorbedParams` | OD-226's `D5` pair (a member declaring a parameter, which the quotient declines); selector and `X86BlockMerge` only | 1 (chain) |
| P12 `ForkedTail` | P1 whose join `w = v + 7` branches (`w < 100`) to a 122-block chain that adds to `a` and returns `x + v`, where the join's value stays live, and a 162-block chain that adds to `a` into `y` and branches on `y < b` to return `y` or `b` (a region of it keeps that branch's claim once its identities drop): past the single-query bounds, the production planner states it in parts, cutting only where the join's value is dead | 1, in two or more parts |

The composition ([`composition24c`]; replayed and credited by the
qualification lanes): the O2 pipeline over five earlier slices' fixtures,
`s9 Diamonds5` (5 segments), `s9 SlotJoin` (4, private slot bytes), `s17
IndexedAcrossJoin` (an indexed access inside a segment), `s16
DiamondChain` (34 segments) and `s24 PartialMerge` (a segment over a
partial merge), with P8s and P12.

P10 (an `X86CmovSwap` triangle) is not built (*Deviations*).

The wrong lowerings and refusal controls (design §5.3, labelled hand edits
of real streams; none credited):

| id | edit | outcome |
| --- | --- | --- |
| W1 | `cmov` cc inverted | stated, refuted on samples and by AY |
| W2 | `cmov` deleted | stated, refuted |
| W3 | a live block `w` enters the then arm | N1 |
| W4 | the then arm calls, the machine does not (a dropped call) | N10 |
| W4s | the design's W4: the then arm's call speculated into `m` (TwoCalls' O2 stream, its head call restamped as the arm's) | N10 |
| W5 | the then arm's incoming store dropped | N10 |
| W5l | a machine-only incoming load in `m` (unstamped `mov [p]`), the source loads nothing | never credited |
| W6 | the then arm's private store dropped, its byte read later | stated, refuted |
| W7 | the Switch's cases swapped | stated, refuted |
| W8 | the then arm returns (the machine never returns there) | N5 |
| W9 | a `div` in the then arm, the machine does not divide (a dropped `div`) | N10 |
| W9s | the design's W9: the arm's `div` speculated into `m` (the selector's `udiv` rows, stamped with the arm) | N10 |
| W9m | the design's machine-only W9: an unstamped `div` in `m` by `k = (c < 8) ? 1 : 0`, zero exactly on the else path | stated, refuted (the effect member's stop claims) |
| W10 | a top-tested loop, rotated (the latch carries the header's test); the correct real O2 output, a refusal control, not a wrong lowering | `branches back to its head` |
| W14 | OD-226's folded branch (`folded_brif`) | stated, refuted (the verdict transition) |
| W15 | P8 with a cut at the join `(j, 0)` (policy) | N13 (`whose parameters machine block M copies`) |
| W16 | forged chooser outputs, one per clause | the check's refusal, by its clause's text |
| W17 | the else arm traps | N5; with C5 off, C11 (`Construction`) |
| N3 | the real O2 output of a loop whose header's invariant `a * b` X86LoopInvariantCodeMotion hoists into the preheader's machine block | N3 (`LIR block H is a loop header`), after the several-blocks refusal |
| N6 | P1 with a dead copy of its if-converted block laid out after it (synthetic) | the copy declined, `is in the segment of`; the pair refused, with no `; not contracted:` note |
| N7 | P1 whose else arm also exits to a returning block, which a synthetic machine block lowers | N7, with OD-226's note |
| N8 | the real O2 output of an entry that jumps to a block `p(w)` entering a bottom-tested loop: `X86BlockMerge` joins the entry and `p` (OD-226's quotient declines the chain: `p` declares a parameter), whose segment would exit into the loop header (a diamond whose join is a loop header is refused before the chooser: the header is entered from both arms, and the lane admits one entering edge) | N8 |
| BL | P1 with a copy of the join's machine block, every row stamped with the then arm, laid out last | `machine blocks M and M' both lower LIR block t`, no note |
| N11 | a call in the head and one in the then arm | N11 |
| N12 | P9's internal join with an OD-192 dead byte injected (at its rule) | N12 |
| N13 member | P8 with a cut inside the then arm (policy) | N13 (`states inside machine block`) |
| N13 live | P12 with a cut in chain `A`, where the join's value is live (policy) | N13 (`where v is live, which only members … define`) |
| SH2, SH3 | P2 and P3 with zero tests (`x < 0`, `c != 0`): the selector's `test` is unstamped, so the block names no head | `has no machine block`, `has no row attributed to a LIR instruction` (kept refused) |

## Fails-before

On `a617488aa` in `~/tcg-scratch/wt-s24c-base`,
`fails-before/make_fails_before.py` copies the fixture section (everything
above the controls marker) with one recording test, `s24c_fails_before`,
which records every fixture, P7, P8 (the production route and both policy
points), P8s, P12 (the production route and its policy point), the seven
composition subjects and every case of `CASES24C`, prints the O0 owners
record (`S24C_O0` lines), and fails if any fixture, P8s, P12 or
composition subject is stated, if a fixture does not build, or if a
slice-24c text appears. The review round's copy (`job18.log`, copy 3,
SHA-256 `332cd44d…`) passed: every one refuses there, with the code before
slice 24c's texts:

- P1, P2, P4-P9, P8s, P11, P12 (both routes), the seven composition
  subjects, W1-W10, W4s, W5l, W9s, W9m, W14, W17, BL, N3 and N8: `the
  machine blocks do not correspond one to one with the LIR blocks: machine
  block B lowers rows of several LIR blocks [..]` (with OD-226's `; not
  contracted: …` where it applies);
- P3 and SH2: `LIR block b has no machine block (merged, if-converted or
  removed)`; SH3: `machine block B has no row attributed to a LIR
  instruction`;
- P7 (both encodings) and P8 (production and both policy points): the
  several-blocks refusal.

The O0 owners record (`slice24c_o0_owners.txt`, 537 rows: 522 stated, 15
refused, each with the SHA-256 of its theorem or refusal text) is the
`S24C_O0` lines of copy 2's run (`job8.log`); copy 3's 537 lines are byte
for byte the same. The first copy (`job6.log`) did not compile (a borrow
in the recording test). C11's first rule is the fails-before record of
F1's fix: under `s24c-guard-one-walker` the misplaced walk is stated
(`the_member_guard_re_derives_the_effect_member`).

## The solver-free gate

`x86_source_bound_body::tests::slice24c::` (17 tests, 1 ignored printer;
`job16.log` on the review round's tree):

- `owner_states_every_segment_shape`: every shape stated over its segments,
  of its kind (WrappingAbs a diamond, no exemption), holding on samples;
  `segment_theorems_are_deterministic`; `both_encodings_state_a_segment`
  (P7);
- `every_named_segment_refusal_is_named`: N1 (its three texts), N3, N5, N5
  (trap), N8, N10 (call, store, division, speculated call, speculated
  division), N7 (with OD-226's note), N11, "both lower" (no note), N13
  (join, member, live); N12 at its rule; the 17 forged outputs (W16); W17
  by N5;
- `the_member_guard_refuses_a_trapping_member` (C11, under
  `s24c-member-any-terminator`) and
  `the_member_guard_re_derives_the_effect_member` (C11's `E`: the walk kept
  by the last member is refused by name; under the first rule,
  `s24c-guard-one-walker`, the same walk is stated);
- `every_forged_segment_is_refused_by_its_clause`: each of the 17 forged
  outputs refused by its own clause's text (`S24C_FORGED 17 cases`);
- `wrong_segment_lowerings_are_never_credited`: W1, W2, W6, W7, W9m and W14
  stated and refuted on samples; W3, W4, W4s, W5, W5l, W8, W9, W9s, W10 and
  W17, and SH2, SH3, BL, N3 and N8, never credited;
- `the_parts_route_states_a_segment`: P8 past `fits_one_query`, stated in
  parts by the production planner in one part, holding; P12 past it,
  stated in two parts, holding;
- `the_composition_is_stated_over_segments`: the seven composition subjects
  stated over their segments and holding (`S24C_COMPOSITION`: 5, 4, 1, 34,
  1 and 1 segments in one query; P12's 1 in 2 parts), and P7's path
  theorem byte-identical to P1's;
- `a_restamped_row_never_credits_a_wrong_lowering`: every one-row restamp
  of the six refuted wrong lowerings and of W4s, W5l and W9s (574 restamps)
  is refuted on samples (238) or refused (336), none stated and holding;
  of the eight shapes' 641 restamps, 296 still hold and 345 are refused,
  none panicking (`S24C_PERTURB`);
- `slice_twenty_four_c_smt2_is_canonical_per_shape`: the golden text
  (`slice24c_snapshots.smt2`, 8 theorems), pinned by digest (`2fecb948…`,
  unchanged by the review round);
- `o0_is_untouched_by_segments`: every O0 fixture of slices 1-25 and every
  slice-24c source through the selector gives the recorded outcome byte for
  byte, and the chooser picks no segment at O0;
- `a_segment_never_names_a_correct_machine_a_mismatch` (the F18 analog):
  the O1, O2 and O3 pipelines over every fixture of slices 1-25: 1466
  theorems built, 47 over segments, every one holding on samples, no
  correct machine named a mismatch (`SLICE24C_OPT built=1466
  over_segments=47`);
- `the_segments_trace_line_precedes_the_parts_and_bound_lines` (a child
  process);
- the mutants and the neutral mutant (below).

Slice 24a's module (`slice24::`, 18 tests) passes with its quotient-level
controls (gate 1).

## Mutants

Each rule has a test-only switch in the OD-226 seam (`quotient::mutant`,
`mutated` a constant `false` outside `cfg(test)`).
`every_slice24c_mutant_fails_a_control` runs every control unmutated
(each holds), then each configuration against its controls; each of the
31 configurations fails every control it is run against (35 pairs;
`job16.log`, the `S24C_MUTANT` lines):

| switch | control that fails | how |
| --- | --- | --- |
| `s24c-entering-any` (the chooser's C2 counts nothing) | N1 (W3) | the decline is gone; the check refuses (`is not single-entry`) |
| `s24c-effects-off` (no C9) | N10 store (W5) | another refusal (the walk's access trace) |
| `s24c-effect-off-spine` (no dominance in C9) | N10 call (W4) | a named mismatch: the machine makes 0 calls where the source makes 1 |
| `s24c-two-effect-members` | N11 | a named mismatch: 1 call where the source makes 2 |
| `s24c-effect-off-spine,s24c-theorem-guard-off` | W4s never credited (DAG) | **stated and holds**: the call speculated into `m` is credited |
| `s24c-effects-off,s24c-theorem-guard-off` | W5 never credited (DAG) | the builder finds no walked access to pair with the source's (`paired access`, a panic the control catches) |
| `s24c-two-effect-members,s24c-theorem-guard-off` | N11 never credited (DAG) | the builder finds no walked call to pair (`paired call`, a panic) |
| `s24c-member-any-terminator` (C5 off) | N5 trap (W17) | refused by the walk instead |
| `s24c-member-any-terminator,s24c-theorem-guard-off` (C5 and C11 off) | the trap member (W17, DAG) | stated and holds: the trap arm is dropped |
| `s24c-walk-on-member` (the walk kept by the last member) | P7's DAG encoding | refused by C11 (`carries a walk, and the effects rule picks member`) |
| `s24c-member-rewalk` | P1-P4 hold | refused (`has no route`) |
| `s24c-flags-reset-at-members` | P4 holds | refused (the `cmov` reads unmodelled flags) |
| `s24c-parts-no-ban` | N13 join (W15) | refused by the cut pairing instead |
| `s24c-parts-defined-no-ban` (the bans' liveness clause off) | P12 in two parts | the plan cuts in chain `A`; the cut pairing refuses (`no machine row writes a register as the definition of …, live across cut point …`) |
| `s24c-cut-pairing-machine-of` | W15 with the bans off is refused by the cut pairing | stated and refuted |
| `s24c-equality-to-subset` (N7 a subset test) | N7 | refused by the walk's `has no route` (no claim) |
| `s24c-chooser-wrong-head` | P3 holds | the check's refusal (`does not name its head`) |
| `s24c-chooser-overlap` (no N6) | N6 | two segments chosen |
| `s24c-check-off` | N6 with the overlap decline off is refused by the check | refused by the correspondence instead (no claim) |
| `s24c-check-c1` | forged: dead head | refused by the named clause instead |
| `s24c-check-named` | forged: named outside | refused by the exits clause instead |
| `s24c-check-shared` | forged: shared machine block | refused by the overlap clause instead |
| `s24c-check-overlap` | forged: overlap | refused by the head-entry clause instead |
| `s24c-check-head-entry` | forged: arm head | refused by the members-start clause instead |
| `s24c-check-order` | forged: out of order; entry as member | the first accepted; the second refused by the entry clause |
| `s24c-check-entering-any` | forged: entered from outside | accepted |
| `s24c-check-terminator` | forged: past the join | accepted |
| `s24c-check-backward` | forged: loop inside | accepted |
| `s24c-check-exits` | forged: exits differ | accepted |
| `s24c-check-loop-exit` | forged: exit into a loop header (N8's chain) | accepted |
| `s24c-check-dispatch` | forged: dispatch | accepted |

Of the three C9 rows with the member guard off, only the first fails on
the hazard itself (the speculated call
credited); the other two stop in the builder, which pairs each source event
with a walked one and has none to pair once both guards are off (an
invariant `expect`, unreachable with either guard on).

`the_kind_label_mutant_is_neutral`: with every segment labelled a diamond
(`s24c-kind-diamond`), every fixture's theorem is byte for byte the same,
every case's outcome is the same, and the switch is wired: P3's segment
reads `[diamond]` instead of `[silent]`.

## Qualification

The three `slice24c_qualification::` lanes, each in a process of its own
with the overlay's AY and Clean (`TCG_X86_BODY_QUALIFY_AY`,
`TCG_EXTERNAL_CLEAN_CHECKER`, `--exact --test-threads=1 --nocapture`), every
replayed and refuted query dumped (`job17.log` on the review round's tree,
`qual-dump-r2/`; gate 2 below repeats them on the committed head, where
`s9 SlotJoin O2` missed the deadline and the replay count is 14):

- **Replay.** 18 replayed units, 15 `result=Verified`: the eight shapes
  (`AlignOffset` 491 ms, `WrappingAbs` 2028, `SelectUnpredictable` 448,
  `ForceSign` 270, `IntegerDecode` 712, `LoopDiamond` 1893, `JoinContinues`
  4434, `AbsorbedParams` 283), the composition's `s9 SlotJoin O2` (30584,
  four segments), `s17 IndexedAcrossJoin O2` (685), `s24 PartialMerge O2`
  (2442), `ShortTail` (7612), both parts of `ForkedTail in parts` (16902
  and 3123) and P7's DAG encoding of P1 (478), so every kind certifies
  (`kinds={"chain": true, "diamond": true, "silent": true}`). P7's path
  theorem is asserted byte-identical to P1's and not replayed again (F14):
  each count is of distinct theorems.
- **The gaps.** Three units are `Timeout` at the 30 s deadline,
  `PENDING(solver-capacity)`, each recorded in
  `KNOWN_UNCERTIFIED_SLICE_TWENTY_FOUR_C` with its offline answer, its rows
  unverified, never credited, never refuted:
  - `LongDiamond in parts` (P8). Offline (`job12.log`), the dumped query
    with a 300 s budget gets `unknown` / `(:reason-unknown timeout)` at
    300.2 s with the lane's strict-proof arguments and again at 300.3 s
    verdict-only (the 1-minute load 15.5 at the start, 10.9 at the end, on
    8 logical CPUs): it is the decision, not the proof, that runs out. The
    query is one equality of two 141-add tails: the source's join value is
    `(ite (= c0x0t2 #b1) 9 s1)` (its edge guard, `c0x0t2 = (s0 = 0)`,
    `s0 = (bvult e_rsi 8)`) and the machine's is the `cmov`'s
    `(ite (not (bvult e_rsi 8)) 9 s1)`, equal but not the same term, so
    nothing after it is shared and AY bit-blasts both chains (slice 24a's
    `LongChain (production parts)` query, by contrast, has no `bvadd` left
    in it, 527 bytes, and verifies in 1 ms).
  - `s9 Diamonds5 O2` (five segments in one query) and `s16 DiamondChain
    O2` (34): the same spelling at every join (the source's edge-guard
    `ite`, the machine's flag `ite`), so no join value is shared. Offline
    (`offline/r1/`), each dumped query with a 300 s budget gets `unknown` /
    `(:reason-unknown timeout)` (300.2 s and 300.4 s, at 1-minute loads of
    14.2 and 25.3 at the start).
- **Deadline-bound.** `s9 SlotJoin O2` (four segments with private slot
  bytes) needs about the whole deadline: it certified in the lane at 29.5 s
  (`job15.log`) and 30.6 s (`job17.log`, AY within its 30 s, Clean after);
  offline at the 30 s budget (`offline/r1/`, `offline/r2/`) AY answered
  unsat after 29.6 and 24.0 s at load 15-16, `unknown` after 55.9 s and
  unsat after 43.0 s at load 24-26 (past its own timeout), and `unknown` at
  30.6 s three of three with three replays at once (load 43); at 300 s
  unsat in 25.9 s. It is in `DEADLINE_BOUND_HERE_BY_HOST` for this host
  with both answers (`Verified`, `Timeout`), as slice 20's `I128` shifts
  are, and the explicit 300 s lane can now build its theorem
  (`deadline_bound_case` reads the slice-24c subjects).
- **Refutation.** W1, W2, W6, W7, W9m and W14, each `CounterExample` (99
  to 194 ms).
- **Credit.** Thirteen bodies credited through the production route: the
  eight shapes (`AlignOffset` 11 rows, `WrappingAbs` 9,
  `SelectUnpredictable` 7, `ForceSign` 10, `IntegerDecode` 13,
  `LoopDiamond` 18, `JoinContinues` 15, `AbsorbedParams` 16), `s9 SlotJoin
  O2` 46, `s17 IndexedAcrossJoin O2` 25, `s24 PartialMerge O2` 13,
  `ShortTail` 15 and `ForkedTail in parts` 303 (both parts), each report
  binding the pair; the three gaps take their recorded branch (no failure,
  no export); W1-W10, W4s, W5l, W9s, W9m, W14, W17, SH2, SH3, BL, N3 and N8
  credit 0 rows.

Before the gaps were recorded (`job15.log`, round 1 of the review), the
replay and credit lanes failed on exactly those outcomes (`the certified
slice-24c set changed on this host`), and P12 was one part. At
`cdfda5a59` (`job11.log`) the same lanes failed on the long diamond's
outcome alone, recorded at `5f1419253`.

## Gates

Every Cargo run went through `scripts/trust_cargo.sh` with the overlay's
`targo`, in the lane's own target directory, under `BUILD_SLOT_MEM_GB=6
build-slot` (one hold per queue run, `scripts/server.sh`). Gates 1 to 4
read the review round's committed head `177d144b1` (`job19.log`,
`GATES="1 2 3 4" DUMP=…/qual-dump-g2 zsh scripts/gates.sh`, which ends `the
gates read 177d144b1…`); gate 6 read the same head (`gate6-*-r2.log`) and
again the review round's final tree (`gate6-*-r3.log`), whose only change
from `177d144b1` was the review round's record text, `PAYLOADS.md` and the
evidence counts in OD-228 and LIMITATIONS. The census record (2026-11-07)
changes no build input either (`crates/`, the manifests, the lock, the
toolchain pin and `.cargo` are as at `177d144b1`), so gates 1 to 5 stand
for it; gate 6 read its commit `ad02a8f06` with a clean tree
(`gate6-*-r5.log`: `check_fmt: OK`, `docs-exit=0`, `matrix-exit=0`), and
again the fact-check fixes' commit `87d0107b6` (record text,
`PAYLOADS.md`, `payloads24c.py` and one comment of the in-tree
`root_classes.py`) with a clean tree (`gate6-*-r6.log`: the same three
results). Gate 5 was not rerun:
the review round changes no `trust-cg-lower` file (its last run, at
`cdfda5a59`, `job11.log`: `test result: ok. 2133 passed; 0 failed; 1
ignored`).

| gate | command (see `scripts/gates.sh`) | result at `177d144b1` |
| --- | --- | --- |
| 1 | `trust_cargo.sh test -p trust-cg-verify --lib -j2 -- x86_source_bound_body::tests:: --skip negative_memo --skip host_qualification --skip verifier_credits --skip canonical_migration` | `test result: ok. 499 passed; 0 failed; 29 ignored` (the 17 `slice24c::` and 18 `slice24::` tests among them; every earlier golden digest unchanged) |
| 2 | `slice24c::` with `--nocapture`, then the three `slice24c_qualification::` lanes with AY/Clean, one per process | module `test result: ok. 17 passed; 0 failed; 1 ignored` (every mutant fails its controls); replay 14 of 18 units `result=Verified`, the three recorded gaps `Timeout` and `s9 SlotJoin O2` `Timeout` this run (30.0 s), settled as deadline-bound (`X86_BODY_DEADLINE_BOUND label=s9 SlotJoin O2 outcome=Timeout`), no `FAILED`; refutation lane 6 `CounterExample`; credit lane 13 bodies credited (`s9 SlotJoin O2` 46 rows: its own replay there certified) and every wrong lowering and refusal control 0 rows; all three `test result: ok` |
| 3 | the three `slice25_qualification::`, three `slice24_qualification::`, four `slice23_qualification::` and four `slice22_qualification::` lanes, one per process | 14 of 14 `test result: ok`, no `FAILED`; the replay lanes print 81 (slice 25), 26 (slice 24), 9 + 3 generalizations (slice 23) and 14 (slice 22) `result=Verified`, the refutation lanes 25, 3, 11 and 12 `CounterExample`; their other outcomes are the recorded gaps their tables settle |
| 4 | `trust_cargo.sh test --no-fail-fast -p trust-cg-codegen --test x86_source_bound_body --test must_refuse_corpus --test e2e_x86_64_differential --test e2e_x86_64_triple_oracle --test e2e_x86_64_mixed_width_shift --test e2e_x86_64_i128_stack_abi --test e2e_x86_64_internal_multi_result --test e2e_x86_64_sib_rmw -j2` with AY/Clean | `x86_source_bound_body` 11 passed, `must_refuse_corpus` 5, `e2e_x86_64_differential` 17, `e2e_x86_64_triple_oracle` 9, `e2e_x86_64_mixed_width_shift` 9, `e2e_x86_64_i128_stack_abi` 3, `e2e_x86_64_internal_multi_result` 13, `e2e_x86_64_sib_rmw` 2; 0 failed |
| 6 | `TRUST_TARGO=<pkg 6808 targo> bash scripts/check_fmt.sh`; `python3 scripts/check_documentation.py --check`; `TRUST_TARGO=<overlay targo> python3 scripts/full_test_matrix_hosts.py --check` | all three pass (`check_fmt: OK`, `docs-exit=0`, `matrix-exit=0`) |

The lint gate (`scripts/check_tippy.sh`) was not run: no `tippy` runs on
this host (UNAVAILABLE, not a pass). Before the review round, gates 1 and
3 to 5 read `cdfda5a59` and gate 2 `5f1419253` (`job11.log`,
`job13.log`): gate 1 `495 passed`, gate 2's module 13 tests and its replay
10 of 11 units (P1's query counted twice, F14).

## Review round

A review of `36f5ebd18` raised 20 findings (soundness, wiring, tests and
documentation lenses). Each was checked against the code; every one but
part of F5 is real, and each real one is fixed with a control that fails
without the fix (a mutant of the test seam, or the code before the fix):

| # | finding | real | what changed |
| --- | --- | --- | --- |
| F1 | C11 never re-derives `E`: a walk on any single member passes | yes | `guard_members` re-derives `E` with `effect_member` over the units' own programs and refuses a walk on any other member (`… carries a walk, and the effects rule picks member E`). `s24c-walk-on-member` (the walk kept by the last member) is refused by name (`the_member_guard_re_derives_the_effect_member`) and fails P7's DAG control; under the first rule (`s24c-guard-one-walker`) the same walk is stated: the fails-before record |
| F2 | no machine-only faulting or effectful row speculated into `m` | yes | W9m (an unstamped `div` by a value zero exactly on the else path: stated, refuted by the head's stop claims) and W5l (a machine-only incoming load: never credited); the machine-only speculated indexed load is not built |
| F3 | most clauses of `segment::check` unexercised, C3's backward edge among them | yes | one forged output per clause (17, `forged_cases`), each refused by its clause's text, and a mutant per clause (`s24c-check-c1`, `-named`, `-shared`, `-overlap`, `-head-entry`, `-order`, `-entering-any`, `-terminator`, `-backward`, `-exits`, `-loop-exit`, `-dispatch`), each failing the forged output it guards |
| F4 | N2 and N4 said to be refused by the check in a forged output; none was built | yes | the entry as a member is now forged (refused by the order clause, since the entry is first in the topological order); the check's doc and deviation 5 say which clauses are implied by earlier ones and are kept as their own guards |
| F5 | the pieces' check runs with the stated pair's `cfg`, and nothing checks the pieces' segments | partly | the first part is not real: inside `stated_in_parts` the plan loop rebinds `cfg` to the pieces' `cut_cfg` (`let (pieces, frame, cfg, sites, loops) = loop { … break (pieces, frame, cut_cfg, sites, loops) }`), so `restate` reads the pieces' control flow. The second is: the pieces' segments must now equal the segments the bans were derived from (`Construction` otherwise); no input reaches that refusal |
| F6 | the parts bans miss points where a value only non-head members define is live | yes | `Ban::Defined`: every point outside the segments where such a value is live (a join's parameter after `(z, 0)`, a value a chain member defines), by a backward liveness pass over `split::live_in`. P12 (the forked tail) is stated in two or more parts with it; with `s24c-parts-defined-no-ban` the planner cuts where the join's value is live and the cut pairing refuses |
| F7 | the LICM header-row roots carry N3, not N1; no N3 fixture; the in-tree classifier counts them as `loop` | yes | N3 from real O2 LICM output, its full text asserted after the several-blocks refusal; OD-228 says the LICM header-row roots carry N3; the O2-keyed `root_classes.py` is in `scripts/`, and the census record puts it in tree with N11's key (*Census*) |
| F8 | `machine_of` has no production consumer, but its doc names one | yes | the doc says no production path reads it and names the two mutants that do; the soundness note is corrected |
| F9 | N13 uses one text for two conditions | yes | three texts: inside a member or the head, the start of a parameterized exit target, and a point where a member-defined value is live (`Ban`) |
| F10 | the design's speculated W4 and W9 were replaced by dropped-effect edits; the C9 mutants are not killed on the hazard | yes | W4s (the arm's call speculated into `m`), W9s (its `div`) and W9m; the three C9 mutants, each with the member guard off, fail W4s, W5 and N11 in the DAG encoding: under the dominance mutant W4s is stated and holds (the hazard), under the other two the builder finds nothing to pair (*Mutants*); deviation 15; the soundness note corrected |
| F11 | `check`'s clauses have no negative control; the past-the-join case accepts any refusal; one mutant switches C2 off in both chooser and check | yes | as F3; the past-the-join needle is `member j ends in a Return`; the check's C2 has its own mutant (`s24c-check-entering-any`), and `s24c-entering-any` is the chooser's alone |
| F12 | the composition has no AY replay or credit | yes | the replay and credit lanes take `composition24c` (five earlier fixtures through the O2 pipeline, P8s and P12); two of them are recorded `Timeout` gaps and one is deadline-bound (*Qualification*) |
| F13 | no gate states a segment theorem in two or more parts | yes | P12, two parts by the production planner, holding on samples, each part replayed (*Qualification*); P8's control asserts its one part and its doc says so. P12 first ended in a plain return, and the planner's second region (chain `B`) then made no claim once its identities dropped, so it was stated in one part (`job14.log`); `B` now ends in a branch |
| F14 | "10 of 11 Verified" counts P1's query twice | yes | P7's path theorem is asserted byte-identical to P1's and not replayed; the counts are distinct theorems |
| F15 | three provenance claims overstate the evidence | yes | *Fixtures*: 8 from the O2 pipeline (P9 at O3), P11 from the selector and `X86BlockMerge`, P7 two encodings, the chain kind certified only on a non-pipeline stream, W10 a refusal control |
| F16 | the trusted list omits the DAG claim floor, `in_dag`, `internal_joins` and `walk_region`'s member arm | yes | the lists in OD-228, LIMITATIONS, CHANGELOG and here, with the bans' liveness clause and the pieces' equality guard |
| F17 | §3 rows without a control are undisclosed; no "both lower" control; the note rule unasserted | yes | "both lower" (BL) asserted with no note, N6 with no note, N7 with the note, N3 and N8 from real O2 output (N8 a merged chain into a loop header: a diamond whose join is a loop header is refused earlier, by the lane's loop admission, `job14.log`); OD-228 lists the rows with no chooser control (N2, N4, N9) |
| F18 | the design's stamp-perturbation campaign was not run | yes | `a_restamped_row_never_credits_a_wrong_lowering` |
| F19 | controls weaker than claimed: the empty past-join needle, WrappingAbs exempt from the kind check, the N1 needle shared with N4 | yes | the needle as F11; WrappingAbs expected `Diamond`, the exemption removed; N1 asserts `is entered from [` and `is not in the segment of` too |
| F20 | `machine_of` documented for stamp searches it is not used in | yes | as F8 |

## Deviations from the design

Each deviation is fail-closed or keeps the design's intent. None weakens a
refusal or relabels evidence.

1. **Silent heads.** The design's P2 (`wrapping_abs`'s `x < 0`) and P3
   (`c != 0`) test against zero, which the selector lowers to an
   **unstamped** `test`: the if-converted block names no head and stays
   refused (SH2, SH3). P2 and P3 compare two parameters instead; the zero
   tests are kept as refusal cases. A census root of this shape keeps its
   refusal (design §9: a stamp on the `test` is a selector change).
2. **P6 from real O2 output.** A pure-test loop header (a compare and a
   `jcc`) is copied into the latch's edge by X86LoopRotate, its arms are
   then entered twice and X86IfConvert converts nothing; a top-tested loop
   is rotated before any segment (W10). P6's header computes `s = acc + i`,
   live into the arm, so the rotation leaves it; its initial values differ
   (from `h(0, 0)` the entry edge's second copy reads the first's register
   with no stamp, refused at the loop entry edge as without segments).
3. **P10 not built.** An `X86CmovSwap` triangle needs C9's indexed-access
   placement on a real sort loop; no fixture was built, so no CmovSwap
   output is evidence here.
4. **W13 not built** (OD-226's `jcc` before a trap carrier, over a
   segment); slice 24a's own control for it passes unchanged.
5. **N2, N4 and N9 have no chooser fixture.** N2 (the entry as a member)
   and N4 (a named block the head does not reach) are unreachable through
   the chooser: the head is the named block first in topological order, so
   a named entry is the head; and a named block whose every live
   predecessor is a member is joined, so a missing one is declined by N1,
   N3, N5 or N6 first. In the check, a forged entry member is refused by the
   order clause (the entry is first in the topological order), and the
   unreached-member, entry-member, no-live-predecessor and
   branch-to-head clauses are implied by C2, the order clause and C0 (the
   check's doc says which); no forged output reaches them first, and each is
   kept as its own guard. N9 (a reached dispatch or search block) has no
   chooser fixture; the check's dispatch clause refuses a forged output (a
   row naming a jump table in `m`). N3 and N8 have real-O2 fixtures (the
   review round).
6. **The DAG claim floor.** Over segments, internal edges claim nothing, so
   a correct segment DAG can state one claim; the floor `fewer than two
   claims` is kept for a DAG over no segment, and a DAG over segments whose
   claims are all operand claims is `NoObservable` (OD-115).
7. **N6 is a chooser decline.** A named block another segment claimed is
   declined before the head is chosen (`is in the segment of {h} (machine
   block {M})`), and the check refuses overlapping segments independently
   (`is also in the segment of`). Its fixture is synthetic (a dead copy of
   P1's if-converted block).
8. **N7 with a synthetic machine block.** The returning block `r` of the
   N7 edit is lowered by a copy of the join's machine block restamped to
   `r` (no real pass leaves an unreachable machine block for it).
9. **The member guard's control runs under a mutant.** W17 is declined by
   N5 on clean code, so C11 is exercised with C5 off
   (`the_member_guard_refuses_a_trapping_member`).
10. **Slice 24a's verdict transitions.** `D5` and `D5 parts` are stated
    over a chain segment and hold; `D2 folded` is stated and refuted on
    samples; `D2` keeps its decline. Their builder rules are judged at the
    quotient (`quotient_refusal_control`: `Quotient::of` declines the chain
    with the expected first note, possibly contracting other chains, or its
    check refuses), and the owner outcome is pinned by
    `segment_transition`. The MUTANTS rows `link-any-terminator` and
    `allow-params` name the quotient-level controls.
11. **The O0 record is byte for byte.** Each row hashes the full theorem
    (every replayed unit) or the full refusal text; nothing is stripped.
12. **Mutant controls.** `s24c-flags-reset-at-members` is killed by P4, not
    P1 (P1's compare is re-emitted before its `cmov`);
    `s24c-chooser-wrong-head` by the check's refusal on P3, not by a forged
    W16 output; the design's `s24c-check-off` + `s24c-chooser-overlap` pair
    is two rows (the overlap decline killed by N6; the check killed by the
    overlap reaching it with the decline off); `s24c-equality-to-subset`
    is not removed as equivalent: it changes N7's text, and the walk's
    `has no route` still refuses the pair (no claim);
    `s24c-cut-pairing-machine-of` is judged with the bans off inside its
    control, since the bans refuse the cut first. An earlier neutral
    candidate (the exit targets walked in reverse) changed no byte (the
    walk's names are minted per row) and was dropped.
13. **No audit-map or encoding test of its own.** Segments rewrite neither
    the pair nor its coordinates: the stated pair is the original or
    OD-226's quotient, whose audit maps and encoding slice 24a's tests pin
    (passing).
14. **P8 replays as one part, and is a recorded gap.** The design's P8
    has the planner cut around its policy points; over OD-226's quotient
    the chain is one block and the region fits the budget (256 rows), so
    the production planner states it in one part, the whole tail on both
    sides. That part runs past the 30 s deadline and past 300 s offline,
    strict or verdict-only (*Qualification*): a recorded replayer gap,
    `PENDING(solver-capacity)`, its rows unverified, never credited. The
    policy points (N13) are refused by name as designed. The qualification
    lane's kind check now holds with recorded gaps too (every kind still
    certifies at least once). The multi-part statement the design's P8 was
    for is P12 (the review round): its tail forks into two chains (122 and
    162 blocks) whose rows, even over OD-226's quotient, exceed one part,
    so the planner must cut and avoid every banned point.
15. **The design's W4 and W9 are W4s, W9s and W9m.** The first build's W4,
    W5 and W9 paired an edited source (the arm calls, stores or divides)
    with the unedited machine: dropped effects, not the speculated effects
    the design names. They are kept as controls, and the design's are added
    (W4s, W9s and the machine-only W9m) with W5l (a machine-only load). W13
    (OD-226's `jcc` before a trap carrier, over a segment) and a
    machine-only speculated indexed load (refuted by the effect member's
    in-bounds claims) are not built.
16. **The stamp perturbation ran** (design §9), over the wrong lowerings
    as well as P1-P11, as one solver-free test.

## Reproducers and payloads

- `fails-before/make_fails_before.py`: `python3 -I make_fails_before.py
  <lane worktree> <base worktree>` writes the fails-before copy and
  registers it; the base worktree must be at `a617488aa`.
- `scripts/server.sh`: the queue run inside one `build-slot` hold (`BUILD_SLOT_MEM_GB=6
  build-slot -- bash server.sh`; each job file dropped into
  `~/tcg-scratch/s24c-run/queue/` runs in turn, its log in
  `~/tcg-scratch/s24c-run/logs/`).
- `scripts/gates.sh`: gates 1-5 (`GATES="1 2 3 4 5" zsh gates.sh`;
  `DUMP=<dir>` names the qualification dump directory).
- The census ceiling: `scripts/ceiling.sh` (with `ceiling_s25.py`,
  `census_compare.py` and the O2-keyed `root_classes.py`, each byte for
  byte the copy that ran; *Census: the ceiling*).
- The head's census (*Census: the slice-24c head*): `scripts/census.sh`
  (`BUILD_SLOT_MEM_GB=6 build-slot -- zsh census.sh`; it refuses unless
  `wt-s24c` is at `38feaf386` with no uncommitted build input, builds the
  bridge with `~/tcg-scratch/build_bridge.t011.sh` and runs
  `~/tcg-scratch/census_t011_dylib.sh` at O2, O0 and O3, both bound in
  PAYLOADS.md), then `scripts/analyse.sh` (read-only, rerunnable alone):
  slice 15's in-tree `census_compare.py`, slice 24a's `census_merged.py`,
  the in-tree `root_classes.py`, `census_segments.py` (the `segments=`
  attribution and the ceiling cross-check), `trace_diff.py` (slice 25's
  check, byte for byte) and `o0_outcomes.py` at O0, `o3_counts.py` at O3,
  and `stop_rule.py` over all three. Every script in `scripts/` is byte for
  byte the one that ran; the in-tree `root_classes.py` differs from the
  file that ran in one comment only (*Census: the ceiling*, the
  classifier). `census.sh`,
  `analyse.sh` and `o3_counts.py` ran before the O3 baseline existed: their
  "No O3 baseline exists" and "no baseline: the design's three counts
  only" are as of that run, and `census.sh`'s base equivalence speaks of
  O2 only. The O3 comparison is `diag-o3/base_o3.sh`'s. `stop_rule.py`'s
  docstring calls every unkeyed line a deadline miss; the O0 notes include
  `kind=self-check-rejected` memo hits (*Census: the slice-24c head*, O0).
- The O3 stop's diagnosis (out of tree, `~/tcg-scratch/s24c-run/diag-o3/`,
  indexed by its `FILES.txt`, bound in PAYLOADS.md): `diag.sh` (one
  `build-slot` hold) runs `repro.sh` (both reproducers through both dylibs
  at O3 and `StrSearcher::new` at O2, the pre-RA rows, the lowering-only
  object, and every dumped part with `(get-model)` on the overlay's AY)
  and then `base_o3.sh` (census-o3-s25 and `census_compare.py` against
  it); `compare/segments/` is `census_segments.py`'s output for the same
  pair, run after it by hand, with no ceiling argument and the in-tree
  classifier (its printout `compare/segments.log`): from
  `~/tcg-scratch`, `python3 -I
  wt-s24c/reports/perf/2026-11-05-darwin-x86-64-slice24c-segments/scripts/census_segments.py
  runs/census-o3-s25 runs/census-o3-s24c s24c-run/diag-o3/compare/segments
  "" wt-s24c/reports/perf/2026-09-27-darwin-x86-64-census/root_classes.py >
  s24c-run/diag-o3/compare/segments.log`. No script in `diag-o3/` records
  that command; rerun so, it reproduces all five files byte for byte (with
  the nifc ceiling's `roots.tsv`, as `analyse.sh` passes at O2,
  `segments.txt` gains a ceiling section).
- The composition's offline replays (`offline/r1/run.sh`,
  `offline/r2/run.sh`, bound below): each dumped query run as `ay Q` one
  process at a time (`r2`'s last three at once), with `:timeout 30000` or
  `:timeout 300000`.
- `scripts/payloads24c.py`: the PAYLOADS.md table (`scripts/write_payloads.sh`
  writes the file).
- The offline replay of the gap (`job12.sh` in the bound queue directory):
  the dumped `LongDiamond_in_parts.smt2` with `:timeout 300000`, run as
  `ay -smt2 Q --strict-proofs --proof P --proof-format alethe` and then as
  `ay -smt2 Q`, each under a 330 s wall alarm.

[PAYLOADS.md](PAYLOADS.md) binds the logs, the fails-before copies, the
qualification dumps, the offline replays, the ceiling census and its
comparison, the head's three censuses with their baselines, comparisons
and the O3 stop's diagnosis, the census helpers, and the job files by size
and SHA-256.
