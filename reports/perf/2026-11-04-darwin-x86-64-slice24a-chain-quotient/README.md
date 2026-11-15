# Darwin x86-64 `library/core` — slice 24a (the exact merged-chain quotient), 2026-11-04

Slice 24a of the x86-64 source-bound whole-body theorem
(`crates/trust-cg-verify/src/x86_source_bound_body.rs`, the new
`x86_source_bound_body/quotient.rs`, `x86_source_bound_body/split.rs` and the
`merged chains=` trace line in `x86_64_function_verifier.rs`) states a machine
block that `X86BlockMerge` made out of a chain of LIR blocks as one block: the
theorem is built over the exact contraction of the chain on the LIR, the
machine's stamps renumbered into its coordinates, by the unchanged slices 1 to
23, and binds the ORIGINAL pair. It targets the class that stops 334 of
census-o2-7ee0's 582 failed roots first (`machine block M lowers rows of
several LIR blocks`; 271 of them on one LIR chain), as designed in
`~/tcg-scratch/s24a-design/README.md` (§2 the rule, §3 the refusals, §5 the
controls, §8 the plan).

| Ruling | Rule | Design |
| --- | --- | --- |
| OD-226 | a chain of argument-free `Jump`s into blocks no other edge enters, which the stamps of one machine block name, is contracted into its head; the theorem over the quotient pair binds the original pair; `Quotient::check` re-derives the quotient from the original pair in every build | §2.1-§2.6 |

Host: the shared x86_64 Mac (4 cores, Darwin 22.6, i7-7920HQ), other lanes
building and replaying throughout; every build through `scripts/trust_cargo.sh`
with the local overlay `x86-stage1-ay13556-t011` (`targo --unverified`, `-j2`,
through `build-slot` at `BUILD_SLOT_MEM_GB=6`; no proof claim about any build).
Replayer pair: AY 0.27.0 build 13556 with Clean 5f09e36c (the overlay's
`bin/ay` and `bin/clean`). Branch `feat/x86-body-slice24a` (worktree
`~/tcg-scratch/wt-s24a`) from main `7ee0def54` (slices 1-23, OD-225). The
fails-before record ran in a detached worktree at `7ee0def54`
(`~/tcg-scratch/wt-s24a-base`). Payloads are out of tree;
[PAYLOADS.md](PAYLOADS.md) binds each by size and SHA-256.

## Census

The Darwin x86-64 `core` proof census (`scripts/census.sh`): one release
bridge built from the branch with `build_bridge.t011.sh`, run on the
overlay's `trustc` with AY 13556 and Clean 5f09e36c at the census budgets,
compared with census-o2-7ee0 and census-o0-7ee0 by slice 15's
`census_compare.py` and attributed by `scripts/census_merged.py`. The design
§7 stop conditions (no newly failing root, no named mismatch, no refuted
body; O0 unchanged) hold in every run:

| run | head | failed roots | promoted | newly failing | named mismatches | refuted bodies |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| O0 | `4c54514eb` | 20 → 20 | 0 | 0 | 0 | 0 |
| O2 | `4c54514eb` | 582 → 379 | 203 | 0 | 0 | 0 |
| O2 | `b342de091` (census fix) | 582 → 378 | 204 | 0 | 0 | 0 |

- **O0.** Each of the 3457 traced functions ends on the baseline's last
  trace line, byte for byte; none is stated over a quotient and no merged
  block declines. The census fix changes only the check, which runs only on
  a contracted quotient, so O0 was not re-run.
- **O2 at the final head.** 205 functions are stated over a quotient (a
  `merged chains=` line before their verdict): 204 bind and replay Valid,
  promoting 204 roots (197 that stopped at `lowers rows of several LIR
  blocks`, 7 at `has no machine block`); one,
  `<[usize]>::as_chunks::<4>`
  (`_RINvMNtCs7e1ihmkzmZ8_4core5sliceSj9as_chunksKj4_EB5_`), binds but Clean refuses AY's proof
  (`no independently checked proof`, a checker gap: no credit, still a
  failed root). 116 functions keep their merged block uncontracted with a
  named decline: 56 a member another block enters, 47 a `Brif` and 11 a
  `Switch` predecessor (a branch a machine pass folded), 2 a member off the
  chain. Of the 1298 traced functions, 954 end on the baseline's line byte
  for byte, 205 bind over the quotient, 7 end on the same refusal plus a
  `; not contracted:` note, and 132 on a refusal over a quotient (109 a
  partial contraction whose other chains decline, 23 a later rule); no
  function bound on both sides changed its verdict (`census/merged-f.txt`;
  `census/merged.txt` is the `4c54514eb` run, 133 refused over a quotient).
  The 378 failed roots: 125 a stack slot outside the frame, 116 the named declines, 99 a
  mixed-width machine row, 9 no observable, 4 bound without an
  independently checked proof, 22 other refusals, 3 untraced.
- **The census found a defect.** At `4c54514eb` one function,
  `core::num::dec2flt::parse::parse_inf_nan`, was refused with the check's
  `Construction` (`Block(21) changed`): `f64`'s `==` is not reflexive on its
  NaN constant (§9). At `b342de091` it binds and replays Valid; no other
  root moved.
- The design expected O2 to fall to about 410-460; it fell to 378.

## Soundness notes first

- **No assumption is added; the trusted code grows by `Quotient::check`.**
  The theorem over the quotient pair
  `(Q, X')` is the slices 1-23 theorem, built by their unchanged code; it
  gives `X' ⊑ Q`. `Q` is the source with each chosen chain contracted into
  its head: an argument-free `Jump` into a block no other edge enters, from
  any block, reachable or not, transfers control and does nothing else (the
  model `admit_blocks` already applies to every `Jump`, and slice 16 applies
  in reverse at every mid-block cut), so `⟦Q⟧ = ⟦L⟧`. `X'` is the machine with
  its TV-1 stamps renumbered and nothing else; stamps have no machine
  semantics, so `⟦X'⟧ = ⟦X⟧`. Hence `X ⊑ L`, and the theorem binds the
  ORIGINAL pair.
- **What grows is trusted checking code, not an assumption.**
  `Quotient::check` is part of the theorem generator's trusted code: the
  claim `⟦Q⟧ = ⟦L⟧` rests on it. It re-derives `Q` and `X'` from the
  original pair with its own entering-edge count (every `Jump`, `Brif`,
  `Switch` and `Invoke` target, the opcodes that name a block) and link
  test, in every build, before any use: each contracted edge is an
  argument-free `Jump` link of the original LIR into neither itself nor the
  entry, each head is the concatenation of its chain without the inner
  `Jump`s, every other block and every other field of the source is
  unchanged (an exhaustive destructuring of `Function` and `BasicBlock`;
  instructions compared exactly, an `Fconst` immediate by its bits), and
  the machine is unchanged but for stamps (exhaustive over
  `X86ISelBlock` and `X86ISelInst`; `X86ISelFunction`'s public fields by
  name, and all of it, crate-private tables included, through its canonical
  verifier identity once the original stamps are restored; that identity's
  writer in trust-cg-lower destructures `X86ISelFunction` exhaustively, so
  a field it does not write fails the build). A failure is `Construction`:
  no claim, never credit. With the builder's link rule broken, the check's
  `Jump` clause refuses a link over a folded `Brif` (D2 with no `jcc` row
  left) and its not-the-entry clause a no-parameter entry behind a dead
  `Jump` (`the_check_refuses_what_the_rules_decline`). With the `Jump`
  clause broken too, the folded `Brif` is credited over a quotient that
  drops the branch, so that clause is load-bearing; with the entry clause
  broken too, source admission refuses the quotient whose entry has no
  body (no claim; §4).
- **The stamps choose, and are not trusted.** Which chains are contracted is
  chosen from the stamps of each several-block machine block; a forged
  choice can make a correct body refuse, be refuted or fail closed, never a
  wrong one credited: `link` reads only the LIR, and the unchanged
  correspondence, walkers and `jcc` rules judge the quotient pair (W4, W7,
  W13 below).
- **Only where today's correspondence fails.** A pair whose block
  correspondence holds, or whose walk needs none (a one-path body whose
  machine has no `jcc`), is stated byte for byte as before. No fixture of
  slices 1-23 at O0 is contracted, and each one's outcome is the one the
  code before the slice records (`o0_is_untouched` compares the digest of
  every replayed unit or refusal with `slice24_o0_owners.txt`, recorded on
  `7ee0def54`); every digest-pinned golden of slices 1-23 is unchanged in
  the same gate. The `core` census at O0 is the Census section's.
- **Exact, but not only the original's regions.** On the parts route the
  quotient admits exactly what its pieces state, which can be more than the
  original pair's own region admission would: flags read across an old
  seam, a header copy found in the merged block, a join's edge-copy run
  measured over the merged block (D10 measures only the copies into a loop
  header). Each such piece is a theorem over `(Q, X')` like any other, so
  this widens what is stated, never what a statement means.
- **The encoding and route are the original's** (OD-191): the quotient is
  admitted with the original source's choice of per-path or DAG encoding and
  its long-chain trim, so contracting a chain never changes which encoding a
  body's theorem takes.

## 1. The rule (OD-226)

`X86BlockMerge` (`crates/trust-cg-opt/src/x86_block_merge.rs`) joins a
machine block into its one laid-out predecessor when that predecessor ends
in `jmp` to it: it pops the `jmp`, appends the rows, keeps every stamp, and
renumbers the blocks. The merged block lowers rows of several LIR blocks,
and slice 6's one-to-one block correspondence refuses it (census-o2-7ee0:
334 of 582 failed roots stop there first; design §1).

- **A link `x -> y`, on the LIR alone** (`quotient::link`): `x` ends in
  `Jump { dest: y }` with no argument or result, `y` is neither `x` nor the
  entry, and that `Jump` is the only edge into `y` from any block, reachable
  or not. The edges counted are every target a `Jump`, `Brif`, `Switch` or
  `Invoke` (its normal and unwind destinations, wherever it stands in its
  block) names.
- **The stamps choose the chains** (`Quotient::of`): the machine blocks whose
  stamps name two or more LIR blocks are taken first, then those naming one,
  each in layout order (jump-table dispatch blocks skipped). A block's chain
  is the longest path of links through the blocks it names and the blocks no
  row names (walked back from the named block with the smallest id, then forward), and it
  is contracted when it holds every named block, has two or more blocks,
  shares none with an earlier chain, its absorbed members declare no
  parameter, its tail does not branch to its head, its tail's edge copies
  into a loop header stay in the tail, and no row is stamped with a removed
  `Jump` or past a member's end. Otherwise the block keeps today's refusal,
  which now says why (`; not contracted: …`, declines D1-D10).
- **The quotient pair.** `Q` is the source with each chain's instructions
  concatenated under its head (the inner `Jump`s dropped; locations and
  trust-ir origins kept parallel; the absorbed blocks gone from the blocks,
  the layout and the origins). `X'` is the machine with every row's stamp
  `(member, i)`, in every block, renumbered to `(head, offset(member) + i)`.
- **Where it applies.** Only where the original pair has no block
  correspondence and its walk needs one, after the original pair's admission
  and machine skeleton (whole body) or bounds, frame, control flow and entry
  parameters (parts) ran unchanged. The theorem is built over `(Q, X')` by
  the unchanged code with the original's encoding, and binds `(L, X)`; the
  audit coordinates are mapped back; a cut piece's block id is above every
  original id (`rewrite_pieces`' floor, checked).
- **Diagnostics.** Every `Unsupported` refusal of the quotient route but the
  empty observable names its chains (`(over the merged-chain quotient:
  chains h=[…]; …)`, original ids): the walkers' and admission's refusals,
  the check's `Construction`, and the module route's trusted-routine
  refusals (`check_trusted_routines`, which runs on the stated owner). The
  verifier's trace prints `merged chains=K absorbed=N` before the `stated in
  parts` line, so the census parsers' last-line and next-line rules still
  hold (`the_merged_chains_trace_line_precedes_the_parts_and_bound_lines`).

## 2. Fixtures and fails-before

`crates/trust-cg-verify/src/x86_source_bound_body_slice24_tests.rs`. Every
fixture's LIR comes from the trust-ir adapter (`ModuleBuilder`, translated
with an explicit permit) and its machine rows from the real selector. 19 of
the 21 shapes are then merged by the real `X86BlockMerge`, asserted to merge
(an inherited `TCG_NO_X86_BLOCK_MERGE` cannot hollow a fixture), with a hand
edit only where the shape names one (a deleted copy row, a deleted final
`jmp` to the next laid-out block, a deleted compare: what copy propagation,
branch layout and CSE make). The other two are not `X86BlockMerge` output:
F11 and the encoding test's long-chain variant cut a LIR block where its
machine block has no seam (`split_lir`, the merge's exact inverse), and F17
merges its first chain by hand (`merge_machine`, `merge_once`'s join without
the renumbering) so that its second chain stays apart.

"Before" is the first refusal on `7ee0def54` (`fails-before.log`): *several*
is `machine block M lowers rows of several LIR blocks [..]`, *no block* is
`LIR block R has no machine block`. "Chains" is `merged_chains()` after the
slice (chains contracted, blocks absorbed; `print3.log`). "AY" is the
replay lane on AY 13556 with Clean 5f09e36c (`jobR1c.log`, after the
review; the first head's run is `jobC.log`); `=F3` marks a theorem
byte-identical to another fixture's (the golden's entries), which the
replayer answered in 0 ms.

| id | `Shape24` | what it pins | before | chains | AY |
| --- | --- | --- | --- | --- | --- |
| F1 | `EntryChain` | the entry heads a 2-chain into a `Brif` (per path) | several `[0, 1]` | (1, 1) | Verified, 235 ms |
| F2 | `JoinChain` | a join heads a 3-chain; the largest LIR id is absorbed | several `[3, 4, 5]` | (1, 2) | Verified, 130 ms |
| F3 | `JumpOnlyMember` | an interior `[Jump]` member no row names | several `[1, 4]` | (1, 2) | Verified, 162 ms |
| F3c | `SilentCopyMember` | a silent member holding a `Copy` (row deleted) | several `[1, 4]` | (1, 2) | Verified, =F3 |
| F4 | `SilentTail` | a silent tail, forward-filled (final `jmp` deleted) | no block (4) | (1, 1) | Verified, =F3 |
| F5t | `DenseSwitchTail` | a chain into a jump table (OD-181) | several `[0, 1]` | (1, 1) | Verified, 344 ms |
| F5s | `SparseSwitchTail` | a chain into a binary search (OD-191) | several `[0, 1]` | (1, 1) | Verified, 239 ms |
| F5s' | `SparseSwitchSilentMember` | a silent member before the `Switch` (phase order) | several `[0, 2]` | (1, 2) | Verified, =F5s |
| F6 | `LoopBodyChain` | a loop body chain, its tail the latch | several `[2, 4]` | (1, 1) | Verified, 1939 ms |
| F7 | `HeaderChain` | a loop header heads the chain | several `[1, 2]` | (1, 1) | Verified, 156 ms |
| F7b | `PreheaderChain` | a merged preheader defines a value the loop reads | several `[0, 1]` | (1, 1) | Verified, 11802 ms |
| F8 | `LatchTail` | the tail is a latch carrying the header's edge copies | several `[2, 4]` | (1, 1) | Verified, 146 ms |
| F9 | `SeamFlags` | `jcc` reads flags the head's `cmp` set (compare row deleted) | several `[0, 1]` | (1, 1) | Verified, 191 ms |
| F10 | `CallsAndMemory` | calls in two members, a store and a load across the seam | several `[1, 3]` | (1, 1) | Verified, 134 ms |
| F11 | `GuardThenDivide` | `GuardDivZero` and `Udiv` in two members (`split_lir`) | several `[1, 4]` | (1, 1) | Verified, 212 ms |
| F12 | `SeventeenBlocks` | 17 LIR blocks (DAG), 4 in the quotient; the last member returns its value times 3 (review) | several `[3..16]` | (1, 13) | Verified, 5395 ms |
| F12p | `PerPathChain` | two 4-block chains, per path either way | several `[3, 5, 6]` | (2, 6) | Verified, =F3 |
| F13 | `SilentHead` | a silent head, back-filled (phase Single) | no block (1) | (1, 1) | Verified, 2298 ms |
| F15 | `TenMembers` | a 10-member chain | several `[1, 3..11]` | (1, 9) | Verified, =F3 |
| F16 | `DeadChain` | F5s plus an unreachable merged chain laid out | several `[0, 1]` | (2, 2) | Verified, =F5s |
| F17 | `PartialMerge` | only the chain the stamps choose; `c1` falls through to `c2` | several `[1, 3]` | (1, 1) | Verified, =F3 |
| F14 | `JoinChain at j and k` (parts) | cut at a head and at an absorbed member's start | several `[3, 4, 5]` | (1, 2) | 1 part Verified, 134 ms |
| F14 | `LoopBodyChain at h and b2` (parts) | the loop body chain cut in parts | several `[2, 4]` | (1, 1) | 2 parts Verified, 152 and 1392 ms |
| R1 | entry behind a dead `Jump` (review) | `NoParamEntry` with a dead `[Jump entry]`: the entry heads its chain, the dead block absorbs nothing | several `[0, 1]` | (1, 1) | Verified, 129 ms |
| R2 | `LongChain` (review; production parts) | a diamond into a chain of 141 blocks, past the single-query bounds: the production planner cuts the merged block (two or more regions, one replayed part) | several `[3, 4, 5, …]` | (1, 140) | 1 part Verified, 0 ms |
| R3 | `RoutineChain` (review; in its module) | a merged chain dividing `u128`s, stated in its module trusting `__udivti3` | several `[2, 3]` | merged | not replayed (the trusted-routine route; slice 22's lanes replay that route) |

So 21 whole-body fixtures and 2 parts fixtures give the golden's 24
entries, of which 17 are distinct theorems. The other 7 are byte-identical
to F3 or F5s because the contraction erases what tells them apart (the
chain's length, its silent members, a dead chain, which encoding: every
claim of these bodies but the branch literals is discharged by value
numbering, so their per-path and DAG spellings coincide). They pin
`Quotient::of` and `Quotient::check` (`the_quotient_is_the_exact_contraction`),
not new theorem content. The replay lane adds R1 and R2: 26 units, 18
answered in more than 0 ms; R2's one part was answered in 0 ms, as the
byte-identical units were (its text is not in the golden).

**Refusal controls** (each asserts its text; `print3.log` prints every
one): D1 with a live and with an `(unreachable)` second predecessor; D2 (a
`Brif` predecessor) and, added in review, D2 over a folded `Brif` (its
compare and `jcc` rows deleted, its arms' rows appended, as constant
folding and the merge leave it, so no row names the `Brif`); D3 (a dead
`[Jump entry]`); D4 (a foreign member whose
predecessor another machine block lowers: the B2 shape); D5 on both routes
(`AbsorbedParams`); D6 (`DoWhile`); D7 (a row stamped with the removed
`Jump`); D8 (a stamp past a member's end); D9 (`DeadCycle`); D10
(`CopyAcrossSeam`); `both lower` over the quotient. On `7ee0def54` every
one of them refuses, with today's text and none with its slice-24a reason.
More named refusals sit in other tests: a builder fault the check catches
is `Construction(".. is not the exact contraction ..")` over the quotient;
a test policy's cut point at a removed `Jump` is refused (`which the
merged-chain quotient removes`); with the builder's link rule broken, the
folded `Brif` and the entry behind a dead `Jump` are the check's
`Construction` (`is not a link of the source`); a region past a test
policy's bound is named in original coordinates (`the region from
instruction 0 of block Block(1) has`); and the routine chain with no module
named is `TrustedRoutine` over the quotient (review).

**Wrong lowerings** (design §5.3; each refuted on samples, a named
mismatch or no claim, never stated and holding):

| id | wrong stream | solver-free | AY |
| --- | --- | --- | --- |
| W4 | `n`'s `sub` reads `b` for `a`, and every row of `n` restamped as `k`'s | stated, refuted on samples | CounterExample |
| W6 | `n`'s `sub` made an `add` | stated, refuted on samples | CounterExample |
| W7 | `n`'s `setcc`, which reads the head's `cmp` flags across the seam, inverted | stated, refuted on samples | CounterExample |
| W8 | a silent member's `store` row dropped | no claim (incoming-memory access trace differs) | not stated |
| W5a | `k`'s product moved before `j`'s add, which defines its operand | mismatch (`row 15 reads v7, which holds no defined value`) | not stated |
| W5b | `y`'s load moved before `x`'s store | no claim (access trace) | not stated |
| W13 | `cmp d, 0; je` inserted before the `GuardDivZero` carrier | no claim (`stop differently`) | no claim |
| W14 | D2 over a folded `Brif` (review): the machine drops the right arm | no claim (several LIR blocks; `ends in a Brif, not a Jump to it`) | not stated |

On `7ee0def54` every wrong lowering and every variant refuses with today's
correspondence text. The one-path control (a merged one-path body whose
machine has no `jcc`) is stated there, its walk needing no correspondence,
and its theorem digest is `8ee3e797…`, the digest the slice keeps
(`one_path_merged_bodies_keep_their_bytes`).

## 3. The solver-free gate

`x86_source_bound_body::tests::slice24::` (no solver; part of the
`x86_source_bound_body::tests::` gate): 18 tests, and the
`#[ignore]`d printer (`jobC.log`, and again inside gate 1 in `jobD.log`).

| test | what it checks |
| --- | --- |
| `owner_states_every_merged_shape` | every fixture is stated over its quotient (`merged_chains()` is `Some`), admitted by `pair_admits_x86_body_owner`, and its theorem holds on samples |
| `merged_shapes_are_deterministic` | two builds state the same text |
| `the_quotient_is_the_exact_contraction` | read through its maps alone, each quotient (every shape, the `f64`-constant and NaN-constant variants) is the contraction: each head the concatenation of its chain without the inner `Jump`s, `original ∘ to_quotient` the identity off the removed `Jump`s, the flattened `X'` the stream of `X`, each renumbered stamp naming an equal instruction |
| `audit_maps_are_in_original_coordinates` | every call site, access site and source definition of a merged owner, on both routes, names an instruction of the ORIGINAL source |
| `the_encoding_is_the_original_shapes` | F12 keeps its DAG encoding although its 4-block quotient alone would be stated path by path, F12p stays per path, and a one-path chain past the path bound keeps its long-chain trim |
| `one_path_merged_bodies_keep_their_bytes` | the one-path, `jcc`-free merged control's theorem is the digest the code before the slice states (`8ee3e797…`) |
| `o0_is_untouched` | over every fixture of slices 1-23 with a shape list (477), each outcome is the one recorded on `7ee0def54` in `slice24_o0_owners.txt` (462 stated: the SHA-256 of the replayed units; 15 refused: of the refusal text before `; not contracted:`), and none is contracted |
| `slice_twenty_four_smt2_is_canonical_per_shape` | the golden `slice24_snapshots.smt2` (24 entries), pinned by `SLICE_TWENTY_FOUR_SNAPSHOT_SHA256 = 47a91dcb…` |
| `a_merged_body_never_names_a_correct_machine_a_mismatch` | F18: the full O2 schedule over every fixture of slices 1-23 with a shape list and of slice 24a; every theorem built holds on samples and nothing correct is a mismatch; at least one O2 body is stated over a quotient (its counts were not re-printed on the final fixtures: the run that would print them waited behind another lane's census for the only build slot and was stopped) |
| `every_named_refusal_is_named` | the 14 refusal controls (D2 over a folded `Brif` added in review), and the builder fault as `Construction` over the quotient |
| `parts_state_merged_chains_at_heads_and_seams` | F14: both parts fixtures stated, every piece's id above the original pair's, regions = cuts + 1; a cut point at a removed `Jump` refused by name |
| `wrong_merged_lowerings_are_never_credited` | W4-W8, W13 and W14 (the folded `Brif`): each refuted on samples, a named mismatch or no claim, the kind printed (`S24_WRONG`) |
| `a_jcc_before_a_trap_carrier_is_never_credited` | W13 is `OverQuotient` whose reason is the route stop rule (`stop differently` or `whose fallthrough also reaches`), or is refuted on samples; any other refusal or a mismatch fails |
| `the_check_refuses_what_the_rules_decline` | with the builder's link rule broken (`link-any-terminator`, `allow-entry`), D2 over a folded `Brif` and a no-parameter entry behind a dead `Jump` are the check's `Construction` (`is not a link of the source`); with `allow-entry,check-off` the entry pair makes no claim (`S24_CHECK`) |
| `a_trusted_routine_refusal_over_the_quotient_names_its_chains` | a merged chain dividing `u128`s is stated in its module (trusting `__udivti3`), and with no module named its `TrustedRoutine` refusal names the chains |
| `the_parts_route_plans_and_bounds_a_merged_block` | a 140-member chain past the single-query bounds is stated in parts by the production planner over its quotient (two or more regions, holding on samples, audit in original coordinates), and a region past a test policy's bound is named in ORIGINAL coordinates |
| `the_merged_chains_trace_line_precedes_the_parts_and_bound_lines` | the verifier's body trace, in a child process: `merged chains=` is printed for a merged owner, before `stated in parts=` when there is one, and the last line is `bound rows=` |
| `every_mutant_fails_a_control` | §4 |

The digest-pinned goldens of slices 1-23 run in the same gate, unchanged.

## 4. Mutants

Each rule of the quotient and its wiring has a switch in
`quotient::mutant`, set per thread by a guard (`mutant::set`); no
environment variable activates one, so no inherited setting reaches a
qualification or credit lane. The seam is `#[cfg(test)]` code: outside the
test build `mutated` is the constant `false`, so the production code holds
no switch. `every_mutant_fails_a_control` first runs every control with no
mutant (all hold). It then runs each configuration of the table and
requires every control it names to fail, printing why
(`S24_MUTANT … killed by …: …`, the control's error or a captured panic's
message):

| configuration | control that fails |
| --- | --- |
| `link-any-terminator` | D2 and D2 folded (with the check on, the folded `Brif` is the check's `Construction`, not D2's text) |
| `link-any-terminator,check-off` | D2 folded is stated and holds: a wrong credit (`X'` refines the quotient that drops the branch, not `L`) |
| `link-any-terminator,check-any-terminator-link` | the same wrong credit, the check's `Jump` clause broken too |
| `check-any-terminator-link` | the check no longer catches the builder's `link-any-terminator` on D2 folded |
| `entering-live-only` | D1 unreachable |
| `allow-entry` | D3, and the entry behind a dead `Jump` is no longer stated (the check's `Construction`) |
| `allow-entry,check-off` | the entry behind a dead `Jump` is no longer stated (source admission: `the entry block has no body`, no claim) |
| `check-entry-link` | the check no longer catches the builder's `allow-entry` on the entry behind a dead `Jump` (source admission refuses it instead) |
| `allow-params` | D5 on the parts route |
| `allow-self-loop` | D6 |
| `allow-jump-stamp` | D7 |
| `copy-run-unchecked` | D10 |
| `rewrite-merged-block-only` | F5t and F5s stated (with `check-off`: F5s) |
| `no-forward-fill` / `no-backward-fill` | F4 / F13 stated |
| `single-first` | F5s' stated |
| `encoding-from-quotient` | the encoding control (F12, F12p, the long chain) and the golden (F12's last member returns its value times 3, so its DAG and per-path spellings differ) |
| `audit-in-quotient-coords` | the audit control on F10, and the region-bound refusal in original coordinates |
| `plan-over-original` | the long chain is no longer stated in parts over its quotient (the plan over the original finds no clean cut in the merged block: no claim) |
| `route-gate-off` | the one-path digest |
| `contract-all-rule-chains` | F17 is stated with (1, 1) chains (the owner refuses: `machine blocks … both lower LIR block …`) |
| `floor-off` | the first parts fixture's id floor |
| `original-first-match` | the audit control on F3 |
| `builder-wrong-offset` | the exact-contraction control on F2 (`Construction`) |
| `builder-wrong-offset,check-off` | the golden (it cannot be rendered: F5s refuses with `both lower`) |
| `builder-drop-member-instructions` (also with `check-off`) | the exact-contraction control on F2; with `check-off`, F2 stated (admission refuses: `uses undefined Value(8)`) |
| `builder-drop-value-types` (also with `check-off`) | the exact-contraction control on F10; with `check-off`, F10 stated (admission refuses: `has no scalar result type`) |
| `builder-const-pool` | the exact-contraction control on the `f64`-constant variant |
| `check-float-eq` (census fix) | the exact-contraction control on the NaN-constant variant (the old `==`: `the head Block(1) is not the concatenation of its chain`) |
| `builder-flip-zero` (census fix) | the same control (the check refuses the builder's `-0.0` → `0.0`: `Block(2) changed`) |

All 33 configurations of 27 switches are killed (`jobR4.log` prints each
kill's reason as an `S24_MUTANT` line; the test passes; `jobR1c.log` is
the run before the census fix, 31 configurations of 25). Where a decline's
mutant is now killed by the check's `Construction` rather than by its
control's own text (D1 unreachable, D5, D6, D7, D10, the stamp fills), the
check refuses the contraction the broken rule made. Four of the design's
rows changed when a mutant survived its control and was reviewed, and the
review corrected two kill mechanisms:

- `walk-original-source` was equivalent. The whole-body walk reads the
  source only for its signature, which the quotient keeps, and reads a cut
  body's definitions only on the parts route. So the switch was removed,
  and the code uses the quotient's source with no branch.
- `contract-all-rule-chains` was equivalent on the design's F17. A chain
  the machine kept apart keeps its `jmp` row, which is stamped with the
  `Jump`, so D7 declines it either way. F17 now has its second chain fall
  through (`c1`'s final `jmp c2` deleted, `c2` laid out next). The mutant
  contracts it, and the owner then refuses (`machine blocks Block(2) and
  Block(5) both lower LIR block Block(2)`), so the control, which requires
  F17 stated with (1, 1) chains, fails on that refusal: fail closed, as the
  design predicted, not a count compared on a stated theorem.
- `encoding-from-quotient` did not move the golden while F12's claims were
  discharged by value numbering. F12's last member now returns its value
  times 3 (review), a claim value numbering does not discharge, so its DAG
  and per-path spellings differ and the golden moves too.
- `builder-wrong-offset,check-off` is controlled by the golden. With the
  check off, wrong offsets make shapes refuse (F5s first: `machine blocks
  Block(0) and Block(3) both lower LIR block Block(0)`), so the golden
  cannot be rendered; the control's captured panic names the refusal. A panic counts as a kill only with its message
  printed.

## 5. Qualification

`x86_source_bound_body::tests::slice24_qualification::`, one test per
process (`scripts/qual.sh`), with `TCG_X86_BODY_QUALIFY_AY` and
`TCG_EXTERNAL_CLEAN_CHECKER` naming the overlay's AY 0.27.0 build 13556 and
Clean 5f09e36c (`X86_BODY_REPLAY_IDENTITY` in `jobR1c.log`, the run on
the review's final fixtures; `jobC.log` is the first head's):

- **Replay lane** (`host_qualification_replays_the_slice_twenty_four_body_theorems`):
  every one of the 26 units is `result=Verified`: 21 whole-body fixtures, 1
  part of `JoinChain at j and k`, 2 parts of `LoopBodyChain at h and b2`,
  and the review's R1 and R2 (the production plan's one part). 18 were
  answered in more than 0 ms; 7 are byte-identical to an earlier unit, and
  R2's part also returned in 0 ms. `KNOWN_UNCERTIFIED_SLICE_TWENTY_FOUR` is
  empty. The slowest unit is F7b (11.1 s), then F12 (5.4 s).
- **Refutation lane**
  (`host_qualification_refutes_the_slice_twenty_four_wrong_lowerings`): W4,
  W6 and W7 are `CounterExample` from AY (for example W4 at `e_rdi = 1,
  e_rsi = 0`). W13 is never stated (no claim). W5a (a named mismatch), W5b,
  W8 and W14 are not stated, so there is nothing to replay.
- **Credit lane**
  (`verifier_credits_every_bound_slice_twenty_four_row_with_the_replayed_body_theorem`):
  through `promotion_verifier` in `Enforce` mode, every row each fixture's
  owner covers is a body credit, rows lowering an absorbed member's
  instructions included. The exports equal the bound rows, and the report
  binds the ORIGINAL pair (`matches_x86_input`). No row of a stated wrong
  lowering is credited, and none is exported.
- **F16 exports nothing, merged or not.** The dead chain's live
  rows are credited, but no theorem claims its laid-out dead rows. Those
  rows are the report's only uncovered non-pseudo opcodes, so the opcode
  inventory is not promotable and nothing is exported. The lane asserts
  exactly that (`dead_rows_withhold_exports`): no failures, every uncovered
  row dead, no export. It asserts the same of the selector's unmerged
  stream of the same LIR, stated over the original pair with no quotient,
  so the withheld export comes from the existing export rule, not from the
  quotient.

The slice-22 and slice-23 qualification suites on this branch: every lane
passes (`jobD.log`). Slice 22 prints 14 `result=Verified` and slice 23
prints 12, its recorded gaps (`SremPaired`, `ScalarMulLeaf` and
`U8CarryingMulAdd` time out at 30 s; `U64OverflowingPowLeaf` is
`self-check-rejected`) as listed in `KNOWN_UNCERTIFIED_SLICE_TWENTY_THREE`.

## 6. Gates

Every Cargo run went through `scripts/trust_cargo.sh` with the overlay's
`targo`, under `BUILD_SLOT_MEM_GB=6 build-slot`. The first head is
`e7bd99db4`; the review head's code is `b342de091` (the review's fixes and
the census fix), whose gates ran on the committed tree (`jobR2f.log`,
`jobR3f.log`; gate 5 by hand, on the docs head). Gates 1, 2's replay lane and
4 also passed at `4c54514eb`, before the census fix (`jobR2.log`).

| gate | command (see `scripts/`) | first head | review head |
| --- | --- | --- | --- |
| 1 | `trust_cargo.sh test -p trust-cg-verify --lib -j2 -- x86_source_bound_body::tests:: --skip negative_memo --skip host_qualification --skip verifier_credits --skip canonical_migration` | 453 passed, 0 failed, 24 ignored (`jobD.log`) | 457 passed, 0 failed, 24 ignored, the 18 `slice24::` tests among them |
| 2 | `slice24::` (solver-free), then the three `slice24_qualification::` lanes with AY/Clean, `--test-threads=1`, one per process | 14 passed, 1 ignored; replay 24 `result=Verified`; refutation and credit lanes pass (`jobC.log`) | 18 passed, 1 ignored (in gate 1, and with `--nocapture` in `jobR4.log`); replay 26 `result=Verified`, no `FAILED`; refutation lane (W4, W6, W7 `CounterExample`, W13 no claim) and credit lane pass |
| 3 | the four `slice22_qualification::` and four `slice23_qualification::` lanes, one per process | 8 of 8 pass; slice 22 prints 14 `result=Verified`, slice 23 prints 12 (`jobD.log`) | not re-run (the review changes neither route: the wrapping applies only over a quotient) |
| 4 | `trust_cargo.sh test -p trust-cg-codegen -j2 --test x86_source_bound_body --test must_refuse_corpus --no-fail-fast` with AY/Clean | `must_refuse_corpus` 5 passed, `x86_source_bound_body` 11 passed (`jobD.log`) | `must_refuse_corpus` 5 passed, `x86_source_bound_body` 11 passed |
| 5 | `TRUST_TARGO=<pkg 6808 targo> bash scripts/check_fmt.sh`; `python3 scripts/check_documentation.py --check`; `TRUST_TARGO=<overlay targo> python3 scripts/full_test_matrix_hosts.py --check` | all three pass | all three pass at `4c54514eb` (`gate5-*-r.log`) and on the docs head after `b342de091` (`gate5-*-f.log`) |

The lint gate (`scripts/check_tippy.sh`) was not run. On this host the
overlay's `targo` has no `tippy`, and the package 6808 `targo` fails
`metadata` on this tree (`no matching package named ay-pb`; recorded
2026-11-03 for this host, not re-checked by this lane).

## 7. Deviations from the design

Each deviation is fail-closed or keeps the design's intent. None weakens a
refusal or relabels evidence.

- **Report directory.** It is `2026-11-04-darwin-x86-64-slice24a-chain-quotient`
  (the lane's task), not §5.5's `<date>-darwin-x86-64-slice24a-merged-chains`.
- **Mutants in tree, as test code.** §5.5 kept the mutants out of tree in
  `fails-before/mutate.py`. They are committed instead as the `#[cfg(test)]`
  seam `quotient::mutant`, so the campaign re-runs with the gate. The
  production build holds no switch.
- **The mutant table.**
  - `walk-original-source` was removed as an equivalent mutant.
  - `contract-all-rule-chains` is controlled by F17's chain count, on a
    fallthrough second chain.
  - `encoding-from-quotient` is controlled by the encoding check, not the
    golden.
  - `builder-wrong-offset,check-off` is controlled by the golden.
  - `builder-const-pool` runs with the check on only: its control is the
    check's `Construction` on the `f64`-constant variant.
  - `link-any-terminator,check-off` and `allow-entry,check-off` are
    controlled by two pairs only the check's `Jump` and not-the-entry
    clauses refuse (D2 over a folded `Brif`, a no-parameter entry behind a
    dead `Jump`), and the two clauses each have their own switch
    (`check-any-terminator-link`, `check-entry-link`), added in review.
  - `plan-over-original` (added in review) is controlled by a production
    parts plan over a 140-member chain.

  See §4.
- **`X86ISelFunction`'s crate-private tables.** `Quotient::check` cannot
  destructure them, because they are private to trust-cg-lower. It
  compares them through the function's canonical verifier identity once the
  original stamps are restored, and its public fields by name. The
  identity's writer (`write_canonical_verifier_identity`) destructures the
  struct exhaustively (review), so a field it does not render fails the
  build; its bytes are unchanged.
- **Fixture changes.**
  - F2 is stated path by path, not over a DAG: two paths are under the
    per-path bound.
  - F16 is built on F5s's DAG. The per-path encoding refuses any laid-out
    dead block, before and after the slice.
  - F12 is a diamond into a join heading a 14-block chain, so that a 17-block
    LIR has a 4-block quotient.
  - F17 has no B2 diamond. The B2 shape's decline is the D4 control.
  - D10 uses a copy temporary at the end of `b1` (`CopyAcrossSeam`), not a
    `split_lir` cut, which admission refuses (`redefines an SSA value`).
  - W4 is a wrong value plus the restamp. A restamp alone changes no
    machine semantics: stated and holding, which is sound.
  - W7 inverts the seam `setcc`, because the fixture's `jcc` is the `NE` of a
    bool test.
  - F7b (`PreheaderChain`) is added: a cut-interface value defined in an
    absorbed member.
- **`o0_is_untouched`.** §5.3 asks that every slice 6-23 fixture at O0 has a
  correspondence. Some fixtures of slices 1-23 have none for other reasons,
  so the test requires instead that none is contracted and that each
  outcome is the one recorded on `7ee0def54`
  (`crates/trust-cg-verify/tests/fixtures/x86_source_bound_body/slice24_o0_owners.txt`:
  per fixture, the SHA-256 of its replayed units or of its refusal's text
  before any `; not contracted:` note). The first version's floor, "more
  than half correspond", was replaced in review: it held by construction.
- **F14's regions.** The parts control also asserts regions = cuts + 1.
- **The parts caveat** (review): on the parts route the quotient admits
  exactly what its pieces state, which can be more than the original
  pair's region admission would (Soundness notes). The design states no
  such bound, and none is added: it would refuse exact pieces.
- **Not run.** The §5.6 stamp-perturbation campaign over merged chains. It
  is listed as open in the decision record.

## 8. Reproducers and payloads

The scripts in `scripts/` and `fails-before/` are the ones that ran, with
the absolute paths of the measuring host:

- `scripts/run.sh`: one `trust_cargo.sh test -p trust-cg-verify --lib -j2`
  in the lane worktree with the overlay's `targo`. `scripts/qual.sh` runs
  it once per test with the AY/Clean pair. Every job was run as
  `BUILD_SLOT_MEM_GB=6 build-slot -- bash <job>.sh`.
- `scripts/jobC.sh`: the golden rewrite
  (`TCG_X86_BODY_SNAPSHOT_WRITE=1`, then `scripts/pin_golden.py`, which
  pins the digest), the solver-free module, `scripts/base.sh` (fails-before)
  and the three qualification lanes.
- `scripts/base.sh`: in a detached worktree at `7ee0def54`, runs
  `fails-before/make_fails_before.py <lane> <base>`, which copies the slice-24
  fixture section unchanged with one recording test, then that test.
- `scripts/jobD.sh`: gates 1, 3 and 4.
- `scripts/jobE.sh`: the printer, with `--nocapture`.
- `scripts/jobR1.sh`: the review round on the fixed code: the golden
  rewrite and pin, the solver-free module with `--nocapture` (every
  `S24_MUTANT`, `S24_CHECK`, `S24_WRONG` and `SLICE24_O2` line), and the
  three qualification lanes.
- `scripts/fix1.sh`: the printer on the review's fixtures (`fix1.log`).
- `scripts/o0_record.py`: writes `slice24_o0_owners.txt` from the
  `S24_O0` lines of a fails-before run on `7ee0def54`.
- `scripts/jobR2.sh`: gates 1, 2's replay lane and 4 on the committed head;
  `scripts/jobR3.sh`: gate 2's refutation and credit lanes;
  `scripts/jobR4.sh`: the solver-free module with `--nocapture` and the
  three qualification lanes after the census fix.
- `scripts/chainR.sh` and `scripts/chainF.sh`: the review round's chains
  (fails-before on `7ee0def54`, the gates, the census), each step through
  `build-slot`; `chainF.sh` is the final head's.
- `scripts/census.sh`: the bridge built from the lane's committed head
  (refused if a build input is uncommitted), the `core` censuses from it
  (`OPTS`, default `2 0`; `SUFFIX` tags the run), slice 15's
  `census_compare.py` against census-o2-7ee0 and census-o0-7ee0, and
  `scripts/census_merged.py`, which attributes the functions stated over a
  quotient and the named declines.
- `scripts/payloads24a.py`: regenerates [PAYLOADS.md](PAYLOADS.md)'s table.

A mutant runs only under a guard in the test build
(`every_mutant_fails_a_control` sets each configuration on its thread); no
environment variable selects one.

## 9. Adversarial review (2026-11-04)

An adversarial review of the first head (`e7bd99db4`) made 20 claims. Each
was checked against the code; all 20 were real, none a soundness hole in
the stated theorem. The fixes are on this branch, each with a control that
fails before it (§4, `fails-before4.log`):

| # | claim | disposition |
| --- | --- | --- |
| 1, 11 | no control reaches the check's `Jump` or not-the-entry link clauses; the two `check-off` configurations repeated their twins (D7 and D5 decline first) | D2 over a folded `Brif` (no `jcc` row left) and a no-parameter entry behind a dead `Jump`; switches `check-any-terminator-link` and `check-entry-link`; `Caught`, `NeverCredited` and `Credited` controls; `the_check_refuses_what_the_rules_decline`. With both the builder's and the check's `Jump` rule broken, the folded `Brif` is credited wrongly, so the clause is load-bearing |
| 2, 15 | the census (design §7) was not run | run (Census section) |
| 3 | check (iii) destructures `X86ISelFunction` with `..` | the identity writer in trust-cg-lower destructures it exhaustively (bytes unchanged) |
| 4 | `TCG_S24_MUTANT` reaches every test build | the environment fallback is removed; only a thread guard activates a mutant |
| 5 | the W13 control accepts unrelated refusals and any mismatch | it requires `OverQuotient` whose reason is the route stop rule, or a refutation |
| 6, 17 | "nothing is trusted in addition" understates the trusted code | "no assumption; the theorem generator's trusted code grows by `Quotient::check`" in LIMITATIONS, CHANGELOG and here |
| 7 | the check's entering-edge count skips `Invoke` | both destinations of every `Invoke` are counted, in the check and the builder |
| 8 | a trusted-routine refusal and the check's `Construction` do not name the chains | both are wrapped in `OverQuotient`; `a_trusted_routine_refusal_over_the_quotient_names_its_chains` |
| 9, 16 | D10 measures only loop-header copies; the parts-route exactness caveat is missing | documented (Soundness notes, OD-226, LIMITATIONS, `copy_run_crosses`, `split.rs`): the wider statement is exact, so no refusal is added |
| 10 | the production parts planner over a quotient is untested | the 140-member chain (`planned_parts_control`), the region bound in original coordinates, and the `plan-over-original` switch |
| 12 | the original's encoding is not observable at the owner | F12's last member multiplies by 3: the golden moves under `encoding-from-quotient` |
| 13 | the `merged chains=` trace line is untested | a child-process test of the verifier's trace order (not a codegen O2 compile; the census is the pipeline's evidence) |
| 14 | `o0_is_untouched` compares no bytes and its floor assertion is a tautology | it compares every O0 outcome's digest with `slice24_o0_owners.txt`, recorded on `7ee0def54`; the floor sentence is gone |
| 18 | two recorded kill mechanisms are wrong, the kill lines are in no payload, a panic counts as a kill silently | the comments, §4 and OD-226 state the observed mechanisms; a panic's message is the kill's reason; `jobR1c.log` is bound |
| 19 | two fixtures are not `X86BlockMerge` output | 19 of 21 are; F11 is `split_lir`, F17 is merged by hand (§2) |
| 20 | W5a is a named mismatch, not "no claim" | the wrong lowerings are "refuted on samples, a named mismatch or no claim", the test prints the kind |

The review's F12 fix took three tries. Multiplying the join's value by 3
before the chain (`jobR1.log`) or on the left arm before the join
(`jobR1b.log`) left the multiply under the chain's 14 constant additions,
whose two spellings value numbering then no longer matches: AY timed out
on F12 at 30 s both times (solver capacity, never a counterexample), and
the replay and credit lanes failed on the unrecorded gap. F12's last member
now multiplies the chain's value by 3 before the return, so the chain is
one shared term on both sides and the claim left is `t * 3` against its
`lea` (`jobR1c.log`).

The census of the review head found one more defect, which the review had
not: `core::num::dec2flt::parse::parse_inf_nan` was refused with the check's
`Construction` (`Block(21) changed`) although its quotient was the exact
contraction. The check compared LIR instructions with `PartialEq`, and
`f64`'s `==` is not reflexive on the function's NaN constant; it also
equates `0.0` with `-0.0`, so a builder that flipped a zero's sign would
have passed. Fail closed either way, but not exact: `b342de091` compares an
`Fconst` immediate by its bits (`same_instruction`), with the NaN-constant
variant as its control and the switches `check-float-eq` and
`builder-flip-zero` (§4). The O2 census was re-run at that head (Census).
