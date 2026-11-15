# Darwin x86-64 `library/core` — slice 25 (scaled-index rows and memory-destination `add`/`xor`), 2026-11-04

Slice 25 of the x86-64 source-bound whole-body theorem
(`crates/trust-cg-verify/src/x86_source_bound_body.rs`) states the
scaled-index (SIB) load and store rows and the memory-destination `add`/`xor`
(read-modify-write, RMW) rows that `X86Peephole`'s address folds and its RMW
fusion produce at O1 and above. A SIB row is the address `LeaSib` computes,
by `LeaSib`'s own code, followed by its base-only sibling's access through the
unchanged code; an RMW row into incoming memory is the next two accesses of
the world trace, its load and its store of `old op src`. It targets the rows
that stopped 208 of census-o2-7ee0's 582 failed roots first (design §1:
118 at the stack-slot scan, 90 at the row domain), as designed in
`~/tcg-scratch/s25-design/README.md` (§2 the rule, §3 the refusals, §5 the
controls, §8 the plan).

| Ruling | Rule | Design |
| --- | --- | --- |
| OD-227 | `Op v, [b + i*s + d]` is `LeaSib t, [b + i*s + d]; Op v, [t]`, stated by `LeaSib`'s code (`sib_private`, `sib_bits`) and the unchanged access; `add`/`xor [m], r` of incoming memory is `mov t, [m]; op d, t, r; mov [m], d` paired event by event; a `MovRMSib` through a jump-table value stays slice 14's dispatch load, at scale 8 and displacement 0 only | §2.1-§2.6 |

Host: the shared x86_64 Mac (8 logical CPUs, Darwin 22.6, i7-7920HQ), other
lanes building and replaying throughout; every build through
`scripts/trust_cargo.sh` with the local overlay `x86-stage1-ay13556-t011`
(`targo --unverified`, `-j2`, through `build-slot` at `BUILD_SLOT_MEM_GB=6`;
no proof claim about any build). Replayer pair: AY 0.27.0 build 13556 with
Clean 5f09e36c (the overlay's `bin/ay` and `bin/clean`). Branch
`feat/x86-body-slice25` (worktree `~/tcg-scratch/wt-s25`) from main
`70c2ddde5` (slices 1-24a, OD-226): `6c036f1de` slice 25.0 (the scan names
its row), `6c8ea20c9` slice 25.1 (the byte-identical refactor and the
fixtures), `6436779f2` slice 25.2 (SIB and RMW rows), then the review round
(*Review round*, below: 20 findings, one of them a soundness fix). The first
fails-before record ran in a detached worktree at `6c036f1de`
(`~/tcg-scratch/wt-s25-base`); the review round's ran in the lane tree with
`crates/trust-cg-verify/src` checked out at `6c036f1de`. Payloads are out of
tree; [PAYLOADS.md](PAYLOADS.md) binds each by size and SHA-256.

## Census

**Slice 25 (run).** One release bridge built from the review round's head
`d92b944fe` (`scripts/census.sh`: `build_bridge.t011.sh`, then
`census_t011_dylib.sh` at O2 and O0; `o2-s25.dylib`, SHA-256
`2e47fae1…`), compared with the slice-24a head's censuses
(`census-o2-s24a-f`, `census-o0-s24a`) by slice 15's `census_compare.py`,
slice 24a's `census_merged.py`, `root_classes.py`, `scripts/firsthit.py`
and, at O0, `scripts/trace_diff.py`; `scripts/census_s25.py` makes the
follow-up tables (`followup/`).

| | O2 before | O2 after | O0 before | O0 after |
| --- | ---: | ---: | ---: | ---: |
| failed roots | 378 | **254** | 20 | 20 |
| promoted / newly failing | | 124 / 0 | | 0 / 0 |
| named mismatches | 0 | 0 | 0 | 0 |
| refuted bodies (lines) | 0 | 2 (one function) | 0 | 0 |
| wall time (shared host, load 8-13) | 494 s | 909 s | 1611 s | 2465 s |

At O0 `failed_roots.jsonl` and `refusals.jsonl` are byte-identical, and
`trace_diff.py` finds every function's trace identical (3457 functions,
7160 trace lines, 0 anomalies). The wall times are not a compile-time
measurement: the host ran other lanes throughout.

The 124 promoted roots by their first refusal on `census-o2-s24a-f`
(`firsthit.py`): 89 at the stack-slot scan (7 of them over the merged-chain
quotient), 16 at `MovRMSib`, 7 at `MovzxRM8Sib`, 5 at `MovRM32Sib`, 5 at
`AddMR`, 1 at `MovMR8Sib` and 1 at `MovMRSib`. Every one of them now binds
and replays Valid. 271 functions are stated over a quotient; 270 of them
replay Valid. No root ends at `has no row attributed`, at an indexed
access's `candidate offsets`, or at the new `outside its dispatch block`
refusal.

The 254 remaining roots by their first refusal (`root_classes.py`):

| first refusal | roots |
| --- | ---: |
| a merged block not contracted (OD-226's named declines): a member entered from several blocks 98, a `Brif` predecessor 89, a `Switch` predecessor 12, a member off the chain 5 | 204 |
| a LIR block with no machine block (merged, if-converted or removed) | 9 |
| no observable (OD-115) | 9 |
| bound with no certified proof (4 as before, and the refuted body) | 5 |
| other (`SbbRR` 4, `Setcc` 3, `RolRCl` 2, a slot address escaping 3, the acyclic or loop-header domain 5, the machine blocks' correspondence 2, and one each of 7 more texts) | 27 |

Where the unpromoted ones stop now (`followup/roots.tsv`, by their last
trace line). Of the 125 roots that stopped at the stack-slot scan, 89 are
promoted, and the other 36 stop later: 35 at a merged block not contracted,
1 at another block-correspondence refusal. Of the 92 roots that stopped at
a slice-25 row (a SIB load or store, or `AddMR`), 35 are promoted, and the
other 57 stop later: 53 at a merged block not contracted, 2 at `RolRCl`,
1 at a register live across a cut, and 1 is the refuted body. The 7 at
`SbbRR` and `Setcc` stop at the same rows (their text lists the larger
domain), and the other 154 keep their refusal text, numbers aside.

**The refuted body.** `core::wtf8::slice_error_fail` (one root; its two
codegen attempts are the two refuted lines,
`bound rows=555`/`571 replay=Invalid (refuted)`). It failed before, refused
at the `MovzxRM8Sib` row of `is_code_point_boundary`'s byte read, and it
fails after, with no credit either way. Slice 25 admits that row, so its
theorem is stated for the first time, in three parts (OD-182). Parts 1 and 3
are unsat on AY 13556. Part 2 (cut point `Block(2)`, the source's `if end >
len`) is sat. The counterexample is `e_rsi = 0`, `e_rdx = 0`, `e_rcx = 1`,
with slot 37's bytes `x2b37o0..7` = `0x0100000000000000`.

Slot 37 is the home of the `len` local, address-taken for `panic!("{len}")`.
Block 0 stores it once, `MovMR [slot37], v86`, where `v86` is `len` loaded
through the slot-24 copy of `s`. Block 2, whose only predecessor is block 0,
reloads `len` from slot 37 in the source. The machine instead compares the
register it stored there (`v91`, a copy of `v86`).

The cut makes the two sides disagree. It states slot 37's bytes as a free
item, because their stored LIR value is a load result, and the stored-byte
closure closes only a constant or a parameter (`split.rs`, the cut
interface's byte loop). Meanwhile it carries `v91` exactly as `e_rsi`, as
every machine register that is a function of the fixed inputs is carried.
Part 2's obligation `(x2b37 <u e_rcx) <-> (e_rsi <u e_rcx)` therefore
fails only where slot 37 differs from `len`. No run reaches such a state:
there is one store, one edge, and no write to slot 37 between them. The
lowering-only object (`movq %rax,-0x2a0(%rbp)`, then the register compare)
is right.

This is a completeness gap of the cut interface, not a miscompile. It is the
mechanism that refutes four fixtures in parts (*Fixtures*). Reserved as
OD-233. The standalone reproducer is in `diag-wtf8/` (*Reproducers and
payloads*): a verbatim 40-line copy of the function and its two helpers,
whose three dumped parts are byte-identical to the census's, together with
the TrustIR container, the pre-RA rows (from the no-codegen-effect
`trace-peephole-entry` knob), AY's replays and the disassembly.

New first refusals on the remaining roots: `RolRCl` (2 roots, earlier
`MovzxRM8Sib`), and one `no machine row writes a register as the
definition of Value(N), live across cut point` (earlier `MovMRSib`).

**Slice 25.0's diagnostic census (run).** One release bridge built from a
detached worktree at `6c036f1de` (`scripts/census_diag.sh`), the O2 `core`
census from it (tag `o2-s25d`), compared with the slice-24a head's O2 census
(`census-o2-s24a-f`, built at `b342de091`) by slice 15's
`census_compare.py` and `scripts/trace_diff.py`:

| | census-o2-s24a-f | o2-s25d |
| --- | ---: | ---: |
| failed roots | 378 | 378 |
| promoted / newly failing | | 0 / 0 |
| named mismatches / refuted bodies | 0 / 0 | 0 / 0 |
| failed-root records whose text changed | | 0 |
| functions whose last trace line is the scan's refusal | 125 | 125 (all 125 now name one row) |
| trace lines changed once the scan's detail is stripped | | 0 |

The scan's refusal now names its row, and `scripts/s_histogram.py`
(`histogram.md`) reads the first named row of each of the 125 functions
(7 of them inside a merged-chain quotient): every one is a SIB **load**
whose base is the stack slot, with a virtual 64-bit index and displacement
0. `MovRMSib [slot + v*8]` 60, `MovRM32Sib [slot + v*4]` 36,
`MovzxRM8Sib [slot + v*1]` 25, `MovRMSib [slot + v*1]` 4. The O2 payloads
carry no defining row of the index, so whether it is a constant is
undecided at O2; the same functions' O0 objects show a constant-index
`lea (b,i,K)` at the named row's scale for 103 of 123 (a heuristic over O0
machine code, not O2 evidence). 92 functions have one offending row, 33 two
or more.

## Soundness notes first

- **No new trusted semantics but `ADD`/`XOR r/m64, r64`.** The SIB effective
  address `base + index*scale + sext(disp)` mod 2^64 (Intel SDM Vol. 2A
  §2.1.5) was already trusted for `LeaSib` and the dispatch load; every SIB
  row shares `emit_sib_mem_operand`. Nothing a fold computed is used: the
  walk evaluates base and index at the row.
- **One spelling.** `LeaSib` and every SIB access call the same
  `sib_private`/`sib_bits` (slice 25.1 moved `LeaSib`'s arms out unchanged;
  `refactor_is_byte_identical` pins `LeaSib`'s refusal texts and every
  earlier golden digest is unchanged). `decomposition_equivalence` states
  every fixture both ways: the fused rows and their `lea; mov [t]`
  decomposition each hold, and every SIB fixture's theorem text is the
  decomposition's byte for byte.
- **No stamp is guessed.** The fused RMW row carries no TV-1 stamp (the
  fusion copies only the proof origin;
  `an_unstamped_read_modify_write_is_never_given_a_site`); an RMW of incoming
  memory pairs with the source's accesses by position, and one of private
  memory is refused by name. A SIB access's stamp sizes an indexed access's
  candidates only (slice 17); the S3 fixture holds with its stamp removed or
  pointed at another instruction.
- **The dispatch load stays a table read only through a table, in its own
  block.** Before slice 25 every admitted `MovRMSib` had scale 8 and
  displacement 0 (its only shape), and `machine_skeleton`'s dispatch idiom
  kept it in the table's dispatch block; now a virtual `MovRMSib` at any
  scale passes the row shape, and a register holding the table's address
  can reach a successor block, where the dispatch `jmp`'s route literal
  bounds no index. The walk's dispatch arm therefore checks scale 8,
  displacement 0 and the block (`dispatch_blocks`) itself, and a data load
  is never read as a table (`sib_routes_to_memory`). The block check is the
  review round's soundness fix: before it, a scale-8 read of a table in its
  first target block was stated as a table entry (the control `dispatch at
  scale 8 disp 0 in a target block`).
- **What is trusted after the theorem, and how weakly it is checked.**
  Frame-index elimination of a slot SIB base, slot prune and remap,
  register allocation's use-only classification of SIB stores and RMW rows,
  and the SIB presequencing replay are trusted with no per-compile check:
  `decode_check` compares the emitted bytes with the same post-lowering row
  (an encoder check), covers the integer SIB and RMW rows, and allowlists
  `MovsdRMSib`/`MovssRMSib`. `e2e_x86_64_sib_rmw` executes eleven O2
  fixtures against clang (execution evidence on chosen inputs).
- **Composition with OD-226.** `MergedScaled` is stated over the merged-chain
  quotient and holds; a walk refusal inside the quotient keeps its text first
  and names the chains (`scaled_index_rows_compose_with_the_merged_chain_quotient`).

## Fixtures

`crates/trust-cg-verify/src/x86_source_bound_body_slice25_tests.rs`. Every
fixture's LIR comes from the trust-ir adapter (`ModuleBuilder`, translated
with an explicit permit) and its machine rows from the real selector and
the real x86 O2 pipeline (`X86Pipeline::run_x86_optimization_passes`), which
makes the SIB and RMW rows; `every_fixture_has_its_row` asserts each row is
there, so an inherited opt-out knob cannot hollow a fixture. Two are
synthetic and labelled (`Shape25::synthetic`): `ByteMerge` (no selector path
emits `MovRM8`, so its `MovRM8Sib` is the real `MovzxRM8Sib` with its opcode
edited) and `AddCarry` (the fusion declines while the carry is live, so its
`mov; add; setc; mov` is fused by hand). "Row" is the real O2 row
(`fails-before3.log`); "AY" the replay lane (`jobQ.log`; `=X` marks a
theorem byte-identical to fixture X's, answered from the session memo).

| id | `Shape25` | row | AY |
| --- | --- | --- | --- |
| R1 | `ByteZext` | `MovzxRM8Sib [p + i*1]` | Verified, 81 ms |
| R2 | `U64Index` | `MovRMSib [p + t*1]`, `t = imul i, 8` | Verified, 84 ms |
| R3 | `ByteOffsetU64` | `MovRMSib [p + off*1]` | Verified, 93 ms |
| R4 | `U32Index` | `MovRM32Sib [p + t*1]`, `t = imul i, 4` | Verified, 95 ms |
| R2s | `U64Scaled` | `MovRMSib [p + i*8]` (a later `add` kills the `imul`'s flags, so the fold takes the scale) | Verified, 93 ms |
| R4s | `U32Scaled` | `MovRM32Sib [p + i*4]` (from `shl`) | Verified, 361 ms |
| R5 | `FieldU32` | `LeaSib b, [p + i*1]; MovRI c, 16; MovRM32Sib [b + c*1]` | Verified, =R4 |
| R5' | `FieldBelowU32` | R5 with `c = -16` | Verified, =R4 |
| R5d | `FieldDispU32` | `MovRI c, 16; LeaSib q, [p + c*1]; MovRM32Sib [q + i*1]` | Verified, 103 ms |
| R6 | `StoreByte` | `MovMR8Sib [p + i*1]` | Verified, 83 ms |
| R6 | `StoreU32` | `MovMR32Sib [p + t*1]` | Verified, 84 ms |
| R6 | `StoreU64` | `MovMRSib [p + t*1]` | Verified, 90 ms |
| R6s | `StoreScaled` | `MovMRSib [p + i*8]` | Verified, 91 ms |
| R7 | `F64Index` | `MovsdRMSib [p + t*1]` | Verified, =R2 |
| R7 | `F32Index` | `MovssRMSib [p + t*1]` | Verified, 125 ms |
| R8 | `ByteMerge` (synthetic) | `MovRM8Sib [p + i*1]` | Verified, 85 ms |
| R2m | `MergedScaled` | `MovRMSib [p + i*8]` in a merged block, over the quotient | Verified, 99 ms |
| S1 | `SlotConstU64` | `MovMRSib`/`MovRMSib [slot + t*1]`, `t = imul k, 8`, `k` constant | Verified, 94 ms |
| S2 | `SlotConstAcrossBlocks` | S1 with the constants in the entry and the accesses in a diamond (one `[slot + k*8]`) | Verified, 102 ms |
| S3 | `SlotGuardedByte` | `MovzxRM8Sib [slot + i*1]` under `i < 16` (indexed) | Verified, 156 ms |
| S4 | `SlotStoreReloadU32` | `MovMR32Sib [slot + k*4]`, `[slot + t*1]` and their reloads | Verified, 119 ms |
| S5 | `SlotCommuted` | `MovzxRM8Sib [i + a*1]`, `a` the slot's address (real: the index first) | Verified, =S3 |
| S6 | `SlotBigU32Table` | `MovRM32Sib [slot + t*1]`, 300 `u32`s, the stamp's site of modulus 4 | Verified, 195 ms |
| S7 | `SlotIndexedStore` (review round) | `MovMRSib` through the slot base at an index guarded by `i < 16` (an indexed store: slice 17's update), the `[u64; 16]` filled before and read back after by calls | Verified, 161 ms |
| S6m | `MergedBigU32Table` (review round) | S6 with its return in a block `X86BlockMerge` joins: the indexed load over the quotient, its stamp renumbered | Verified, =S6 |
| M1 | `AddInto` | `AddMR [p + 0], x` | Verified, 84 ms |
| M1f | `AddIntoField` | `AddMRSib [p + c*1], x`, `c = 16` | Verified, 85 ms |
| M2 | `XorInto` | `XorMR [p + 0], x` | Verified, 100 ms |
| M3 | `AddIntoIndexed` | `AddMRSib [p + i*8], x` | Verified, 395 ms |
| M3 | `XorIntoIndexed` | `XorMRSib [p + i*8], x` | Verified, =M3 add |
| M4 | `AddCarry` (synthetic) | `AddMR [p + 0], x; setc` | Verified, 237 ms |
| M1m | `MergedAddInto` (review round) | `AddMR [p + 0], x` in the `then` arm of a diamond whose `tail` `X86BlockMerge` joins to it, over the quotient | Verified, 103 ms |

The "AY" column of the first 29 rows is slice 25.2's `jobQ.log`; the review
round's replay on the merged head (`gates.log`, gate 2) verifies all 32
again. The golden
`tests/fixtures/x86_source_bound_body/slice25_snapshots.smt2` had 29 entries
and 24 distinct theorems at slice 25.2 (`U64Index`/`F64Index`,
`U32Index`/`FieldU32`/`FieldBelowU32`, `SlotGuardedByte`/`SlotCommuted` and
the two indexed RMW fixtures coincide: in the value-numbered spelling the
equal value terms drop out, leaving the same address claims). The review
round appends 10 entries and changes none of the 29: the three new fixtures
and the seven qualified edits (`;;;; edit …`), 39 entries and 27 distinct
theorems, pinned by digest (`2543c119…`). The three new theorems are
`SlotIndexedStore`'s, `MergedAddInto`'s and `S3 sum through an indexed
register`'s; `MergedBigU32Table` is `SlotBigU32Table`'s theorem over the
quotient, and every other edit is its fixture's theorem byte for byte: the
evaluator reduces `[f + i]` with `f = lea [slot]`, `[b + z*1]` with `b =
LeaSib [slot + i*1]` and `z = 0`, and `[b + 16]` with `[b + c*1]` at `c =
16`, to the same address term
(the one-spelling claim, seen from the theorem side; so the replay's
nonzero-displacement theorems are Verified as those fixtures' are).

## Fails-before

On `6c036f1de` (slice 25.0) in `~/tcg-scratch/wt-s25-base`,
`fails-before/make_fails_before.py` copies the fixture and edited-pair
section (everything above the controls marker) and adds one recording test,
`s25_fails_before`. `scripts/base.sh` (`COPY=copy5`) runs it in the base
tree's own target dir (`stage1-targets/wt-s25-base-own`). The test fails if
any fixture or edit is stated and holds. It passed (exit 0). Nothing that
slice 25 states holds on the code before it:

- **The 32 fixtures** all have their rows and all refuse:
  - the 17 SIB fixtures' rows: `machine row N is outside the body domain
    (…): Op with operands […] and flags InstFlags(READS_MEMORY)` (or
    `… carries flags …`). The scale-8 `MovRMSib` rows are the exception:
    `U64Scaled` and `MergedScaled` refuse in the walk's dispatch arm,
    which slice 14's shape admitted, with `MovRMSib outside the selector's
    jump-table dispatch`. `MergedScaled` adds the suffix `(over the
    merged-chain quotient: chains …)`.
  - the 8 slot fixtures' rows: `a row that references a stack slot outside
    a modelled `[slot + disp]` operand: block B row r, …` (S25.0's text).
  - the 7 RMW fixtures' rows: `AddMR`/`XorMR`/`AddMRSib`/`XorMRSib with
    operands […] carries flags InstFlags(HAS_SIDE_EFFECTS | READS_MEMORY |
    WRITES_MEMORY)`.
- **The 17 distinct edits** that a slice-25 control holds, or that a
  transition names, also refuse: the neutral edits, the qualified edits
  (which include the frame- and indexed-register bases of review #2 and the
  displacement folds) and the transitions. None holds. The SIB and RMW
  edits refuse with the body-domain text, and the S edits with the slot
  text.
- **The 32 fixtures stated in parts at every point** all refuse. 27 refuse
  with their whole text. Five slot fixtures refuse first on the LIR side
  (`SlotGuardedByte`, `SlotCommuted`, `SlotIndexedStore` and
  `MergedBigU32Table` with `IndexedUnbounded`; `SlotBigU32Table` with `a
  Load … through an indexed private stack address with 1197 candidate
  offsets (the lane admits 1024)`).
- **The 25 SIB fixtures' decompositions.** Each splits every scaled-index
  access into the rows slices 4 and 17 state: `lea t, [slot]` for a slot
  base, then `LeaSib t, [base + index*scale + disp]`, then the access
  through `[t + 0]`. The RMW fixtures have no record here, because their
  decomposition needs slice 25's opcode table.
  - Whole: 24 hold. `SlotCommuted` refuses with `LeaSib reads the private
    stack address in v9 as a value (the slot's address escapes)`.
  - In parts at the fixture's points:
    - 7 hold: `ByteZext`, `ByteOffsetU64`, `U64Scaled`, `U32Scaled`,
      `StoreByte`, `StoreScaled`, `MergedScaled`.
    - 7 refuse: `FieldU32` and `FieldBelowU32` with `MovRM32 reads v20001,
      which its loop carries paired with no loop-header parameter`, and
      the five LIR-side refusals above.
    - 11 are refuted on samples: `U64Index`, `U32Index`, `FieldDispU32`,
      `StoreU32`, `StoreU64`, `F64Index`, `F32Index` and `ByteMerge`
      (part 1 of 1), `SlotConstU64` (part 1 of 3), `SlotConstAcrossBlocks`
      (part 2 of 3) and `SlotStoreReloadU32` (part 1 of 2).

  So the four fixtures that slice 25 refutes in parts are already refuted
  in parts as decompositions before slice 25: the cut-interface gap
  (reserved as OD-233) predates this slice. Seven more decompositions are
  refuted in parts on the base, and their SIB fixtures hold in parts on
  the slice-25 head. This report does not measure whether those
  decompositions still fail in parts on the head. The refutations are
  verdicts of the split route and never credits. OD-233's lane measures
  the decompositions on its own head.

The record is `fails-before5.log` with the copy
`copy5_x86_source_bound_body_slice25_tests.rs`.
`fails-before5-unused-import.log` is the copy's first attempt, which did not
compile: it kept an import that only the controls use, and the build runs
with `-D warnings`. The generator now allows unused imports.
`fails-before4.log` (copy 4) is the earlier record. It covers the 29
fixtures that existed before the review round, has identical outcomes for
them, and records no edits, splits or decompositions. `fails-before3.log`
(copy 3) is the same section as copy 4 from before its comments were
corrected and formatted.

## The solver-free gate

`x86_source_bound_body::tests::slice25::` (24 tests, 2 ignored printers; 20
at slice 25.2, and the review round's
`the_scale_eight_movrmsib_transitions_are_the_designs`,
`a_scale_eight_movrmsib_is_routed_by_its_base`,
`a_constant_index_outside_its_slot_is_a_named_mismatch` and
`scaled_index_and_rmw_rows_are_stated_in_parts`):

- `owner_states_every_slice25_shape`, `every_fixture_has_its_row`,
  `refactor_is_byte_identical`, `sib_bits_is_the_sdm_effective_address`
  (the evaluator against the SDM sum on 4,000 random operand triples at
  every scale), `private_sib_matches_o0` (the private address of `[slot +
  I*s + d]` is O0's `lea [slot + d0]; LeaSib [. + I*s + d1]` for every split
  `d = d0 + d1`, at a term and a constant index), `decomposition_equivalence`;
- `every_wrong_sib_or_rmw_row_is_refuted`: 25 wrong lowerings, each refuted on
  samples through `theorem_without_affine_refusal` and by the owner (a named
  mismatch or a refuted theorem): displacement sign and size, scale at a
  nonzero index (4→2, 1→8, 8→4, slot 1→4), base/index swap at scales 4 and
  8, `movzx` to a merging byte load, the slot's constant index and
  displacement, `add`↔`xor`, the RMW source and base swapped, its
  displacement, the indexed RMW's displacement, `setc`→`seto` after `AddMR`,
  and the review round's six: a displacement or constant moved on each of
  the four frame- and indexed-register edits, and `SlotIndexedStore`'s
  displacement and scale;
- `a_wrong_width_is_never_credited`: 7 width and slot edits (an incoming
  access of the wrong width is unpaired, `AccessTrace`, no claim; a slot
  store into another declared slot);
- `neutral_edits_hold`: 15, each asserted to hold (swap at scale 1 on three
  fixtures, three correct displacement folds, scale changed at constant
  index 0, S3's stamp removed or moved, a compare before the `add`, and the
  review round's five: a loop load at a zero index, and a base through a
  frame register (scale 1 and 8) or an indexed register (a base and a
  sum)); 7 of them are `QUALIFIED_EDITS`, replayed on AY, and 3 edits are
  `TRANSITIONS`, each with its designed verdict;
- `out_of_domain_sib_and_rmw_rows_are_refused_by_name`: 47 named refusals
  (§3: physical index, base or value register, RBP and RSP bases, scale 3, a
  32-bit index, a proof origin, a private index at scale 4, two private
  components, an undeclared slot, a slot as an index (twice), on `LeaSib`, on
  `AddMR` and `AddMRSib`, RMW through a private address, a private address
  as the RMW source, RMW against a load-call-store, a store-load and a 4-byte
  source, `cmp; XorMR; setcc`, the dispatch at scale 4 displacement 16, a
  physical destination, a base holding the loaded entry, `MovsxdRMSib`,
  `MovdquRMSib`, `ImulRMSib`, a 1100-byte indexed table, an unbounded
  index, and the review round's 15, among them a table read outside its
  dispatch block, a constant index overflowing at scale 8, a stamp naming
  no site, a store wider than its register, a 32-bit destination, a table
  base as a `MovRM32Sib` base, `AddMRSib` through a private address, a
  stored private address as `SlotIndexedStore`'s value or under its
  update, a read over a stored private address, and a proof origin on
  `AddMR`);
- `scaled_index_and_rmw_rows_are_stated_in_parts`: every fixture stated in
  parts (OD-182) at every clean point: 21 hold (the replay lane replays
  them), 7 are refused, and 4 (`ByteMerge`, `SlotConstU64`,
  `SlotConstAcrossBlocks`, `SlotStoreReloadU32`) are refuted on samples
  exactly as their `lea; mov [t]` decompositions are (the split's own
  verdict, never a credit: the cut-interface gap of *Census*, reserved as
  OD-233); a cut between an RMW row's two source events refuses with
  `do not split cleanly`;
- `an_undefined_component_is_a_mismatch`, `a_mixed_or_carried_component_makes_no_claim`,
  `an_unbounded_slot_index_is_refused_and_its_claim_refutes_it`,
  `scaled_index_rows_compose_with_the_merged_chain_quotient`,
  `an_unstamped_read_modify_write_is_never_given_a_site`,
  `jump_table_loads_still_read_their_tables`,
  `a_slice25_body_never_names_a_correct_machine_a_mismatch` (every real
  fixture at O1, O2 and O3);
- the mutants (below) and the digest-pinned golden.

## Mutants

Each rule has a test-only switch in the OD-226 seam (`quotient::mutant`,
`mutated` a constant `false` outside `cfg(test)`, active only under a
thread's guard). `every_slice25_mutant_fails_a_control` runs every control
unmutated (each holds), then each switch against its controls; each of the
17 makes one fail (the merged head's gate-2 module run with `--nocapture`
in `gates.log`, the `S25_MUTANT` lines, which name the first control each
switch fails; `jobF.log` is the 16 of slice 25.2):

| switch | control that fails | how |
| --- | --- | --- |
| `s25-commute-every-scale` | S5 private index at scale 4 (refusal) | stated |
| `s25-no-commute` | `SlotCommuted` holds | refused (the slot's address read as a value) |
| `s25-disp-zero-extended` | R5' folded into the displacement (neutral) | named mismatch |
| `s25-scale-ignored` | `U32Scaled` holds | refuted on samples |
| `s25-slot-base-at-disp` | S4 constant index folded into the displacement (neutral) | named mismatch (`StackSlotBounds`) |
| `s25-every-movrmsib-to-memory` | the slice-14 jump-table fixtures hold | refused (the table's address read as a value) |
| `s25-dispatch-no-scale-check` | dispatch at scale 4 displacement 16 (refusal), run with `s25-dispatch-any-block` in the background (the control sits in a target block, where the block check would refuse first) | stated |
| `s25-dispatch-any-block` | dispatch at scale 8 displacement 0 in a target block (refusal) | stated |
| `s25-routing-operand-only` | R2 physical destination and its reader (refusal: a correct machine outside the virtual-only shape); R2 physical destination | the first stated, the second a named mismatch (`UndefinedRead`) |
| `s25-rmw-flags-not-clobbered` | `cmp; XorMR; setcc` (refusal) | stated |
| `s25-xor-stated-as-add` | `XorInto` holds; M1 add to xor refuted | refuted on samples |
| `s25-rmw-store-only` | `AddInto` holds | access trace refused |
| `s25-rmw-store-via-frame-of` | M1 source a private address (refusal) | stated |
| `s25-scan-exempts-index` | S3 slot as index (refusal) | refused at the row domain instead (a text-only kill: `sib_operand` admits only a virtual index, so no row with a slot index passes `check_row_shape`, and the scan's index check has no other reachable consequence) |
| `s25-no-declared-slot-check` | S3 undeclared slot base (refusal) | panics (a failed control) |
| `s25-indexed-stamp-wrong-row` | `SlotBigU32Table` holds | refused (1197 candidate offsets) |
| `s25-lea-sib-commutes` | `LeaSib`'s pinned refusal texts | stated |

`the_unnamed_ea_mutant_is_neutral`: with the effective address left
unnamed (`s25-unnamed-ea`), every fixture still holds, and the switch is
wired: the theorem texts of `U64Scaled` and `AddIntoIndexed` change under
it.

## Qualification

Each lane in a process of its own, on the merged head `a617488aa`
(`scripts/gates.sh`, gate 2 of `gates.log`; the replayed queries dumped to
`merged/qual-dump/`). Slice 25.2's first run (`scripts/jobQ.sh`,
`jobQ.log`: 29 of 29 Verified, 19 wrong lowerings refuted) is superseded.

- `host_qualification_replays_the_slice_twenty_five_body_theorems`: **81 of
  81 `result=Verified`** (the 32 fixtures whole, the 7 qualified edits, and
  the 42 parts of the 21 fixtures that hold in parts), no `FAILED`,
  `KNOWN_UNCERTIFIED_SLICE_TWENTY_FIVE` empty. Every family certifies: slot
  SIB load (S1-S6) and store (S1, S2, S4, S7), incoming SIB load (R1-R8) and
  store (R6), indexed SIB access (S3, S6, S7), `AddMR` (M1, M4, M1m),
  `XorMR` (M2), `AddMRSib` (M1f, M3) and `XorMRSib` (M3).
- `host_qualification_refutes_the_slice_twenty_five_wrong_lowerings`: all
  25 wrong lowerings stated and refuted by AY with a counterexample (none
  refused before a theorem).
- `verifier_credits_every_bound_slice_twenty_five_row_with_the_replayed_body_theorem`:
  every covered row of every fixture is body-credited through the production
  route, the exports bind the pair, and no row of a wrong lowering is
  credited.

## Gates

Every Cargo run went through `scripts/trust_cargo.sh` with the overlay's
`targo`, under `build-slot`, on the merged head `a617488aa` (slice 25 at
`d92b944fe` with `origin/main` `12ebba653` merged; the docs commit after it
changes no build input), in the lane's own target directory
(`scripts/gates.sh`, `gates.log`, 00:30-01:57):

| gate | command (see `scripts/gates.sh`) | result |
| --- | --- | --- |
| 1 | `trust_cargo.sh test -p trust-cg-verify --lib -j2 -- x86_source_bound_body::tests:: --skip negative_memo --skip host_qualification --skip verifier_credits --skip canonical_migration` | `test result: ok. 482 passed; 0 failed; 27 ignored` (the 24 `slice25::` tests among them; every earlier golden digest unchanged) |
| 2 | `slice25::` with `--nocapture`, then the three `slice25_qualification::` lanes with AY/Clean, `--test-threads=1`, one per process | module `test result: ok. 24 passed; 0 failed; 2 ignored`, with 17 `S25_MUTANT` lines (each switch fails a named control); replay 81 `result=Verified`, no `FAILED`; refutation lane 25 `CounterExample`; credit lane `ok` |
| 3 | the three `slice24_qualification::`, four `slice23_qualification::` and four `slice22_qualification::` lanes, one per process | 11 of 11 `test result: ok`; slice 24 prints 26 `result=Verified` (refutation 3 `CounterExample`), slice 23 prints 12 (9 and 3 generalizations; its refutation lane 11), slice 22 prints 14 (refutation 12); their other outcomes are the recorded gaps their tables settle |
| 4 | `trust_cargo.sh test --no-fail-fast -p trust-cg-codegen --test x86_source_bound_body --test must_refuse_corpus --test e2e_x86_64_differential --test e2e_x86_64_triple_oracle --test e2e_x86_64_mixed_width_shift --test e2e_x86_64_i128_stack_abi --test e2e_x86_64_internal_multi_result --test e2e_x86_64_sib_rmw -j2` with AY/Clean | `x86_source_bound_body` 11 passed, `must_refuse_corpus` 5, `e2e_x86_64_differential` 17, `e2e_x86_64_triple_oracle` 9, `e2e_x86_64_mixed_width_shift` 9, `e2e_x86_64_i128_stack_abi` 3, `e2e_x86_64_internal_multi_result` 13, `e2e_x86_64_sib_rmw` 2 (240 cases, 0 wrong); 0 failed |
| 5 | `trust_cargo.sh test -p trust-cg-lower --lib -j2` | slice 25.2's run (`jobG.log`): `test result: ok. 2133 passed; 0 failed; 1 ignored`; the landing train runs it again on the landed head |
| 6 | `TRUST_TARGO=<pkg 6808 targo> bash scripts/check_fmt.sh`; `python3 scripts/check_documentation.py --check`; `TRUST_TARGO=<overlay targo> python3 scripts/full_test_matrix_hosts.py --check` | run on the docs head (and by the landing train) |

Gate 4 prints the known host warning that the portable certificate sets
(`bound-memory`, `atomic-memory`, `neon-memory`) are disabled for this
host's `drat-trim` bytes: CERT-SKIP is declined and live discharge is kept,
as on `origin/main`.

The lint gate (`scripts/check_tippy.sh`) was not run: no `tippy` runs on
this host (UNAVAILABLE, not a pass).

## Deviations from the design

Each deviation is fail-closed or keeps the design's intent. None weakens a
refusal or relabels evidence.

- **Fixtures follow the real O2 output.** The fold takes an `imul`/`shl`
  into the scale only when the flags are dead after it in the block
  (`sib_fold_flags_dead`; a `ret`, call or branch counts as live), so the
  design's R2/R4/R7 `[v + v*8]`/`[v + v*4]` arise as `[p + t*1]` over the
  multiply's register; the scaled forms are pinned by the extra fixtures
  `U64Scaled`, `U32Scaled` and `StoreScaled` (a later `add` kills the flags).
  `FieldDispU32`, `FieldBelowU32` and `MergedScaled` (the OD-226 composition)
  are added too.
- **No real displacement.** Every real displacement is 0 at O2 (the design's
  R5 `[v + v*1 + 16]` and `AddMR [v + 16]` do not arise; a constant index
  stays in a register). The displacement controls therefore start from a
  correct hand fold (`folded_into_disp`, the S4 fold), which must hold
  (neutral), and edit it to refute; the displacement mutants are killed by
  those folds. They are labelled hand edits in the test.
- **Two synthetic fixtures**, `ByteMerge` and `AddCarry` (above), as §9
  allows for rows with no real pipeline fixture.
- **Width and kind edits never credited rather than refuted.** §5.5 lists
  `MovRM32Sib ↔ MovRMSib`, `MovsdRMSib → MovssRMSib` and the slot width
  edits among the refutations. On incoming memory a wrong width is refused
  before any theorem (`AccessTrace`: the pairing requires equal width), and
  on a slot the edit is a named `StackSlotBounds` or no claim, so these 7
  are `NEVER_CREDITED`: refused, a mismatch or refuted, never credited.
- **Routing applies to `MovRMSib` only.** `sib_routes_to_memory` decides
  between the data load and slice 14's dispatch load; no other SIB opcode
  ever had a dispatch form.
- **`s25-indexed-stamp-wrong-row`** is "the SIB row's stamp is not read"
  (the observable consequence of a stamp read from the wrong row: the site
  falls back to modulus 1). S3's 16 candidates stay within bounds either way,
  so its control is `SlotBigU32Table` (1197 candidate offsets past the
  lane's 1024 without the stamp's modulus 4).
- **`sib_address` names the effective address at its use.** The closure
  returns the term; the memory branch and the RMW arm name it as `LeaSib`
  names its result (`s25-unnamed-ea` removes the name and is neutral).
- **The dispatch controls** (`[table + i*4 + 16]` through the table's
  address, and a base holding the loaded entry) are an extra `MovRMSib` at
  the top of the table's first target block: any edit inside the dispatch
  block is refused earlier by `machine_skeleton`'s dispatch-idiom check
  (`jump table 0 outside the selector's dispatch idiom`), which never reaches
  the walk's scale check.
- **The carried control** uses slice 12's `LoadSum` with its load rewritten
  to `[t + z*1]`, `z` 0 from the entry and rewritten in the loop: the header
  fixpoint's first round walks the header without carried registers, so the
  `CountUp` construction (a SIB load the source does not make) is refused by
  the access trace first. The same machine without the loop's rewrite holds.
- **The big indexed table's refusal is the source's.** A 1100-byte
  indexed byte table refuses on the LIR side first (`… with 1100 candidate
  offsets (the lane admits 1024)`).
- **The RMW event-order variants** are sources renamed to `AddInto`'s name
  (the skeleton compares names first), and the 4-byte variant keeps
  `AddInto`'s signature, reading 4 bytes and storing 8.
- **Two slot-as-index controls**: the slot as both base and index (what
  `s25-scan-exempts-index` must break) and as the index under a register
  base.
- **`decomposition_equivalence` compares texts for SIB fixtures only.** An
  RMW decomposition names two more definitions, so its text differs; both
  hold.
- **One commit for S25.2 and S25.3.** The RMW arm uses `sib_address`, and
  the control tables, the mutant campaign and the golden are shared; an
  intermediate tree would carry a half campaign. The S25.1 commit carries
  the fixture section, so the fails-before reproducer reads a committed
  file.
- **Fails-before at `6c036f1de`**, slice 25.0 on top of main `70c2ddde5`
  (§5.6 names `0c8f408c8`, an older main).
- **Not done by this lane:** the `land_loop.sh` `EXTRA_QUAL`/`EXTRA_TESTS`
  edits (§8 step 8: `land_loop.sh` is the orchestrator's file; the slice-25
  qualification lanes and `e2e_x86_64_sib_rmw` are what they would add) and
  the fused row's stamp copy (S25b, deferred by the design). The census and
  the e2e target, first left out, were done in the review round.

## Execution

`crates/trust-cg-codegen/tests/e2e_x86_64_sib_rmw.rs` (review round, #14)
is the execution check of what runs after the theorem: frame-index
elimination of a slot SIB base, slot prune and remap, register allocation's
use-only reading of SIB stores and RMW rows, and the SIB presequencing
replay. Eleven of the slice-25 fixtures are compiled alone at O2 by the
production `Compiler`. Each object must contain the SIB or RMW instruction
its fixture is for (decoded by the host's LLVM-family `objdump`), and each
is linked with a C driver whose clang-compiled reference computes the same
result on the same inputs. That makes 240 cases, run in gate 4. This is
execution evidence on chosen inputs. It is not a proof, and not a check of
any other compile. `AddMR` followed by `setc` has no producer (the fusion
declines while the carry is live), so it keeps only its synthetic fixture.
The target is registered in `scripts/full_test_matrix_hosts.py` and
`scripts/check_linux_x86_64.py`.

## Review round

A review of the slice-25.2 head (`6436779f2`) raised 20 findings. Each was
checked against the code: 19 are real, one is real in part. Every change
fails closed. No refusal was weakened, no test was flipped and no evidence was
relabelled. The code, tests and docs are in commit `d92b944fe`. The records (census,
fails-before, gates, payloads) are in the docs commit after the merge of
`origin/main` (`a617488aa`).

| # | finding | real | what changed |
| --- | --- | --- | --- |
| 1 | OD-227 and LIMITATIONS say the newly exercised post-theorem lowering is "checked again by the per-compile `decode_check`" | yes | `decode_check` decodes the emitted bytes and compares them with the same post-lowering row. That makes it an encoder check: it cannot see a frame-index, slot-remap, register-allocation or presequencing fault, and it allowlists `MovsdRMSib`/`MovssRMSib` (`decode_check.rs`, the counted-with-reason list). OD-227, LIMITATIONS, the CHANGELOG and this report now say so, and they list those transforms as trusted with no per-compile check. `e2e_x86_64_sib_rmw` adds execution evidence (#14). |
| 2 | No SIB access or RMW goes through a register holding a private (frame or indexed) base, and `sib_address`'s frame and indexed arms are untested | yes | Holding edits: `S3 base through a frame register` (`lea f, [slot]; movzx [f + i*1]`), `S1 base through a frame register at scale 8` (constant index), `S3 base through an indexed register` (`LeaSib b, [a + i*1]; movzx [b + z*1]`) and `S3 sum through an indexed register` (`b = LeaSib [a + i*1]`, `[b + j*1]`). These sit in `QUALIFIED_EDITS`, and so also in `decomposition_equivalence`, the golden and the replay lane. Each has a refuting edit (`… at disp 1`, `… constant 2`, `… constant index 1`, `… disp 1`). The refusal `M3 through a private address` (`AddMRSib read-modify-writes a private stack slot`) covers an `AddMRSib` through a frame-holding base. |
| 3 | The `MovRMSib` verdict transition has no fixture | yes | `TRANSITIONS` and `the_scale_eight_movrmsib_transitions_are_the_designs` cover the four cases: a value base holds (`U64Scaled`), an undefined base is `UndefinedRead`, a frame-register base holds, and a mixed base is refused with the mixed text. The fails-before record carries the old refusal for each. |
| 4 | Neither census gate ran on the slice-25 head | yes | Both now run on `d92b944fe` (*Census*). |
| 5 | No slice-25 fixture is stated in parts (OD-182) | yes | `scaled_index_and_rmw_rows_are_stated_in_parts` states every fixture at every clean point. 21 fixtures hold in parts, and the replay lane replays them. Four fail in parts, and each fails exactly as its `lea; mov [t]` decomposition does (the split route's own verdict; never a credit). A cut between an RMW row's two source events refuses with `do not split cleanly before its instruction k`. |
| 6 | `BODY_OPCODES` and the routing doc say the jump-table `MovRMSib` is admitted "(its dispatch block only)", but the walk has no block check | yes | The fail-closed option was taken (#8), so the text is now true. |
| 7 | The stack-slot scan comment and the `AccessTarget` doc are stale | yes | Both now state slice 25's invariants. |
| 8 | A table read outside its dispatch block is stated as a table entry | yes (soundness) | Slice 25 lets a successor block read a register holding the table's address, and there the dispatch `jmp`'s route literal bounds no index. The walk's jump-table arm now refuses such a read (`MovRMSib reads jump table N outside its dispatch block`). The control `dispatch at scale 8 disp 0 in a target block` was stated before the fix and is refused after it. The mutant `s25-dispatch-any-block` removes the check. |
| 9 | No holding fixture has a frame- or indexed-register base | yes | The edits of #2 cover a constant and a variable index, with a refuting edit each. |
| 10 | No variable-index store into a slot | yes | `SlotIndexedStore` (S7) is a real O2 fixture. It has two refuting edits (`S7 store disp plus 8`, `S7 scale changed`), two refusals (`S7 stored value a private address`, `S7 update over a stored private address`), a fails-before record, a golden entry and a Verified replay. |
| 11 | Design §3/§5.5 refusals have no control | yes | Added: `S3 constant index overflows at scale 8` (`overflows a private stack offset`), `a_constant_index_outside_its_slot_is_a_named_mismatch` (`StackSlotBounds`), `S6 stamp names no site` (the machine side's 1197 candidates), `R6 store wider than its register`, `R2s 32-bit destination`, `dispatch table base as a MovRM32Sib base`, `S7 stored value a private address`, `S7 update over a stored private address`, `S3 read over a stored private address` and `M1 proof origin`. A "dead" candidate byte is set only by a split's cut (OD-184, `SlotByte::Dead`), so it is OD-184's control, not this slice's. |
| 12 | The S3 stamp edits were asserted only to be never wrong | yes | `neutral_edits_hold` now asserts that every neutral edit holds. |
| 13 | OD-227's transition text is narrower than design §2.4, and the fails-before list omits the `… and flags …` text | yes | Both rewritten. |
| 14 | No execution test exercises SIB or RMW rows | yes | `e2e_x86_64_sib_rmw` is in gate 4 and in both host registries (*Execution*). `AddMR` followed by `setc` has no producer, because the fusion declines while the carry is live. It keeps only its synthetic fixture. |
| 15 | Composition with OD-226 is shown for one incoming load only | yes | `MergedBigU32Table` holds over the quotient. With its stamp unattributed it refuses with the 1197 text and the quotient suffix. `MergedAddInto` (the fused `AddMR` over the quotient) also holds. |
| 16 | `every_fixture_has_its_row` checks opcodes, not the distinguishing operand | yes | `named_operand` checks each fixture's distinguishing operand: the slot base of the S fixtures, `SlotCommuted`'s index as the slot's `lea` (followed through copies), and scale 8 or 4 on the scaled fixtures. |
| 17 | The holding controls have no fails-before record, and no nonzero-displacement theorem is replayed | yes | The recorder now covers every neutral and qualified edit, every transition, every fixture in parts, and every SIB fixture's decomposition whole and in parts, all on `6c036f1de`. The replay lane replays the qualified edits, the displacement folds among them, and every one is Verified. |
| 18 | Some mutant kills only show which check fires first, and the neutral mutant is not shown to be wired | partly | `s25-routing-operand-only` is now killed first by `R2 physical destination and its reader`, a correct machine outside the virtual-only shape that the mutant states. `the_unnamed_ea_mutant_is_neutral` asserts that the switch changes the theorem texts of `U64Scaled` and `AddIntoIndexed`. Not real for `s25-scan-exempts-index`: `sib_operand` admits only a virtual index, so no row with a slot index passes `check_row_shape`. The scan's index check therefore has no reachable consequence of its own, and a control "whose row passes `check_row_shape`" cannot exist. That kill is recorded as text-only. |
| 19 | The census scripts hard-code slice 25.0's scan text | yes | `trace_diff.py` and `s_histogram.py` accept `operand or scaled-index base`, and OD-227 and the CHANGELOG record the text change. |
| 20 | The CHANGELOG's trusted list is short | yes | It now carries the post-theorem lowering and the scan text. |

## Reproducers and payloads

The scripts in `scripts/` and `fails-before/` are the ones that ran, with the
absolute paths of the measuring host:

- `scripts/run.sh`: one `trust_cargo.sh test -p trust-cg-verify --lib -j2`
  in the lane worktree with the overlay's `targo`; `scripts/qual.sh` runs it
  once per test with the AY/Clean pair. Every job ran as
  `BUILD_SLOT_MEM_GB=6 build-slot -- bash <job>.sh`.
- `scripts/module.sh`: build, then the slice-25 module (`MARK` names the
  build's marker); run with `TCG_X86_BODY_SNAPSHOT_WRITE=1` once to write the
  golden, whose digest was then pinned by hand after review.
- `scripts/suite.sh`: gate 1. `scripts/gate_s251.sh`: slice 25.1's gate.
- `scripts/base.sh`: the fails-before record in the detached worktree at
  `6c036f1de` (`fails-before/make_fails_before.py <lane> <base>`).
- `scripts/jobQ.sh`: the three qualification lanes. `scripts/jobG.sh`: gates
  1, 3, 4 and 5. `scripts/jobF.sh`: the final fails-before rerun, the module
  with `--nocapture` and the printers.
- `scripts/census_diag.sh`, `scripts/diag_analysis.sh`,
  `scripts/trace_diff.py`, `scripts/s_histogram.py`, `scripts/s_roots.py`,
  `scripts/o0_sib_sites.py`, `scripts/census_lib.py`: slice 25.0's diagnostic
  census and its analysis.
- `scripts/fix/`: the review round's jobs (`env.sh` the lane environment,
  `m2.sh` and `m4.sh` its module and gate runs, `module.sh`; `fin.sh` its
  final job, which was stopped in its bridge build and replaced by the
  three scripts below).
- `scripts/census.sh`: the slice-25 census (the bridge at `d92b944fe`, the
  O2 and O0 censuses and their comparisons); `scripts/census_s25.py`: its
  follow-up tables; `scripts/firsthit.py`: the S/R first hits.
- `scripts/base.sh` (`COPY=copy5`): the extended fails-before record, in the
  detached base worktree with its own target directory
  (`stage1-targets/wt-s25-base-own`; the first four records shared the lane's
  directory; each ran `s25_fails_before`, a test only the base copy has,
  and printed the base code's slice-24a domain text, so each ran the base
  tree's binary). The base worktree was removed after slice 25 landed. To
  run the script again, re-create it with `git worktree add --detach
  ~/tcg-scratch/wt-s25-base 6c036f1de`.
- `scripts/gates.sh`: gates 1 to 4 on the merged head `a617488aa` (slice 25
  with `origin/main` `12ebba653` merged), in the lane's own target directory.
- `diag-wtf8/` (out of tree, `~/tcg-scratch/s25-run/diag-wtf8/`, indexed by
  its `FILES.txt`): the refuted body's standalone reproducer (*Census*).
- `scripts/payloads25.py`: regenerates [PAYLOADS.md](PAYLOADS.md)'s table.
