# Darwin x86-64 `library/core` — slice 17 (private stack accesses at a non-constant offset; dead bytes at cut points), 2026-10-15

Slice 17 of the x86-64 source-bound whole-body theorem
(`crates/trust-cg-verify/src/x86_source_bound_body.rs`, its child modules
`x86_source_bound_body/indexed.rs` (new) and `x86_source_bound_body/split.rs`)
admits a private stack access whose offset is not a constant: a load, a store
or a direct call's argument through an `Iadd` of a private slot's address and
a computed index (`T[i]`, `&mut buf[i]`). It also leaves out of a cut point's
relation a private byte that is dead there (a loop header of slice 12 and a
cut point of slice 16 alike, one byte liveness for both). The design, the
measurement of the class (35 failed roots of census-s14 at the slot offset,
16 more with it behind another refusal: 51 functions) and the measured lift
are in `~/tcg-scratch/s17-design/` (README §1-§8); this record holds the
implementation, its soundness argument, the controls and their fails-before
evidence, the host qualification and the measured outcome on the 51. Rulings
OD-183 (indexed accesses) and OD-184 (dead bytes at a cut point) in
`docs/decision-record.md`. Host: the x86_64
Mac of the [slice-16 record](../2026-10-14-darwin-x86-64-slice16-parts/README.md)
(4 cores, 16 GB, shared; while the owner's census chain ran, every build ran
at `nice -n 19`, `-j1`, and no AY or solver ran), the local overlay
`x86-stage1-ay12713` (`targo --unverified`, no proof claim about any build),
AY 0.27.0 build 12713 with Clean 5f09e36c (the pair `QUALIFIED_AY` pins).
Branch `feat/x86-body-slice17-indexed`, from slice 16
(`feat/x86-body-slice16-size` at `5b5b1d105`, itself merged with main
`2854ce3e3`), with origin/main merged in as it moved: after the trust-ir
pins `8d304e36` and `dc2b8073`, slice 16's landing (`84055afb5`) and main's
per-host qualification view (`4c6ce87e8`, which slice 17's qualification
tests now read).

| Row | Bridge built from | AY | Bridge sha256 | Failed roots | Wall |
| --- | --- | --- | --- | ---: | ---: |
| `core-x86_64-darwin-O0-proof-main-6191f3621-ay12713` (baseline) | `main` `6191f3621` | 12713 | `94e646dd…` | 232 | 5729 s |
| `core-x86_64-darwin-O0-proof-slice17-ay12713` | this branch, `ac8424004` (slice 17 on `6191f3621`) | 12713 | `11290b17…` | **191** | 6673 s |

**41 roots promoted, 0 newly failing, 0 named mismatches, 0 bound bodies
refuted** (`census_compare.py` of the slice-12 record, payload `compare/`):
39 functions refused at a non-constant private stack offset (32 defined by a
`Bitcast`, 7 by an `Imul`), 1 at a cut entered with different stored slot
addresses (the dead-byte rule) and 1 bound body now certify; the dead-byte
rule's changed queries across the crate lose no root. Both rows were built by
`census12713.sh`, each bridge in its own tree, with no resource-budget refusal.
Payloads are out of
tree; [PAYLOADS.md](PAYLOADS.md) lists each with its size and SHA-256.

**In short.** On the design's 51 functions, 43 now build a theorem (34 of
the 35 census roots and 9 of the 12 behind a size bound; 30 in one query
and 13 in slice-16 parts on main 2854ce's dump after the `ArrayGep` merge)
and 39 certify offline on AY build 12713 with Clean within the live 30 s
budget; the rest stop by name. With main's `ArrayGep` admission (OD-185)
merged, an `ArrayGep` of a private slot at a variable index is this
slice's indexed address with the element size as its stride. Every in-bounds fact is a claim AY proves on both sides. Host
qualification chose the spelling: a load reads the design's low-bit select
(AY rejects its own proof of a 256-arm linear chain), and a theorem with an
in-bounds claim is value-numbered as one slice-16 part after its
bit-moving definitions are substituted (AY multiplies a constant stride
behind a definition name out as a variable product, and keeps a stored
value's 160 byte claims alive when the two sides name it differently).
Every fixture (20, four of them `ArrayGep`) and machine variant certifies
(0.4-2.3 s); 17 wrong lowerings are refuted by AY with counterexamples,
three of them by one in-bounds claim alone; 15 rule mutants each fail a
control; the robustness probe (before the merge) credits no wrong stream
among 254 mutants.

## The theorem

**Indexed addresses.** In the source walk (`admit_blocks`), an `Iadd` of a
private frame address `(slot, c)` and an `I64` value `d` that is no constant
of the chain and no private address is an INDEXED address
(`indexed::IndexedAddr`): no SMT term of its own, but the 64-bit offset term
`o = c + d` (wrapping; `indexed::offset_term`). It stays indexed through
`Copy`, a `Bitcast` to `I64`, an `Iadd` of a constant and a `StructGep`, and
is used only as a scalar load's or store's address or as a direct call's
argument. Anything else refuses by name: stored as data, returned, compared,
joined to a different address, carried by a loop header or across a slice-16
cut, passed to a C memory routine (`Memcpy`), offset by a second
non-constant, an aggregate access. The alignment modulus `l` is read from
`d`'s own definition (`indexed::modulus_of`: through copies to an `Imul` by a
constant or an `Ishl` by one, `l = 2^j` with `j` the multiplier's trailing
zeros, at most `2^32`; otherwise 1).

**`ArrayGep` (merged with OD-185).** Main's bridge spells array elements as
LIR `ArrayGep { elem_ty }(base, index)`, `base + index * s` with `s` the
element's natural-C size (OD-185). Over a frame address at an `I64` index
of the chain that is no constant, it is the same indexed address with
STRIDE `s` (`IndexedAddr::stride`; 1 for an `Iadd`): offset `o = c + d *
s`, spelled as OD-185 spells the product (`d * (s - 1) + d` for 3, 5 and
9, `IndexedAddr::offset`), modulus the index's own times the largest power
of two dividing `s` (`indexed::stride_modulus`). At a constant index it is
OD-185's exact offset (over an indexed base too). OD-185's refusals stay:
an index of another type, an element outside the layout model or of size
zero, an index that is itself a private address, an offset past `i64`. The
bound finder scales the index's range by `s`, the slice-16 planner's LIR
scan and the byte liveness track `ArrayGep` addresses, and on the machine
a scaled `lea` of a private address at an index the walk does not know as
a constant is an indexed address (at a known constant, OD-185's exact
offset).

**Candidates.** An access of `w` bytes (an argument: `w = 0`) into a slot of
`n` bytes has the candidate offsets `k` in `0..=n - w` with `k ≡ c (mod l)`
(`indexed::candidates`). An access with more than 256 candidates, or a
source whose accesses have more than 1024 together (arguments excluded: no
select reads one), refuses by name.

**Semantics** (one spelling, `indexed.rs`, which both walks call):

- a LOAD reads `select` over the candidates' reads `B(k)`, each exactly
  what a load at the constant offset `k` reads (slice 7's bytes, slice 9's
  merged bytes, slice 8's aggregate-parameter bytes, slice 13's `f_k`
  initial bytes; a stored private address or a dead byte among them
  refuses; a `bool` load needs every candidate's byte to be a readable
  `bool`, per candidate, as slice 15 rules). The select is the design's
  LOW-BIT select: with `k_i = r + i * 2^s` (`r < 2^s`), a balanced `ite`
  tree that tests bit `s + j` of `o` at depth `d - 1 - j`
  (`(ite (= ((_ extract b b) o) #b1) UPPER LOWER)`), so where `o` is a
  candidate its bits `s..s + d` are its index and the tree reads `B_i`.
  The first build stated the linear chain `(ite (= o k1) B(k1) (ite ...
  B(kN)))`; Qualification records why it was replaced;
- a STORE of `x` makes each byte `p` some candidate covers the `update`
  `(ite (= o k) byte_{p-k}(x) (ite ... old_p))` over the candidates covering
  it (`indexed::covering`), a new private byte (`SlotByte::Indexed`, named
  `ix{id}` and defined where the store runs, so a later read is one name),
  joined at a DAG join like slice 9's merged bytes and carried by a loop
  header like any byte;
- a CALL ARGUMENT through an indexed address is observed as `slot{s} + o`
  (`indexed::argument_term`, slice 13's slot address input plus the
  offset) on both sides, and its slot escapes (slice 7's callee contract).
  A value an indexed load reads from bytes a call may have written is
  tainted as slice 15 taints it (a derived access through it observes the
  escaped slots).

**The machine side.** The machine walk (`walk_rows`) tracks a register as
`RegValue::Indexed { slot, base, offset }` when its row is an `add` of a
frame register and a value (`AddRR`), an `lea` with a scaled index over a
frame or indexed register (`LeaSib`), or a constant `add`/`sub`/`lea`/copy of
an indexed register; the offset is the term its own rows compute (an
`imul` by a constant register, a `shl`, a `movzx`, whatever is there),
never matched against the source's shape. An access through such a register
is an `ite` select or update over the candidates of the source access its
row's TV-1 stamp names (same slot and width; else every offset in the slot,
which only sizes its select, its own claim checks it), with the same
`indexed.rs` functions. An indexed call argument is observed as
`slot{s} + o_machine`, and an argument register holding an address of
another slot than the source's is a named mismatch (`CallStackAddress`).

**The claim.** OD-84's, and: on every run on which the source is defined,
every indexed access (and argument) the source performs, and every one the
machine performs before the source stops, lies inside its slot at a
candidate offset. Each side states it for its own offset
(`indexed::in_bounds`: `(bvule o (n - w))` and, when `l > 1`,
`(= (bvand o (l - 1)) (c mod l))`): the source's under its access's block
guard where the source has not stopped by the access; the machine's under
its block's guard where the source runs at the block's start (slice 14's
stop terms). In-bounds is a CLAIM AY proves, never a premise.

**Dead bytes at a cut point** (OD-184). `split::live_bytes` is a backward
byte liveness over the LIR: a load gens the bytes it covers; a store at a
known offset kills them; an indexed access gens its whole slot; a call, a C
memory routine or an untracked access gens every slot that may have escaped;
any other use of a slot's address gens the slot. A private byte not live at
a loop header (slice 12's `LoopHeader::dead`) or a slice-16 cut point
(`CutInterface::dead`) is left out of the cut's relation and assumptions on
both sides and starts UNREADABLE (`SlotByte::Dead`, `MachineByte::dead`):
a source read of it refuses, a machine read of it makes no claim, and a join
of it with anything is unreadable; an edge bringing a dead marker into a
live byte refuses. This is the cut-point liveness slice 16's design called
for: one function for both slices.

**Admission: the bound finder** (`indexed::check_bounds`, admission only).
Every indexed load and store needs a bound its own region holds: a
dominating guard edge whose compare of the index against a constant implies
every offset is a candidate, or the index's own range (a narrow extension,
a mask, a logical shift right, a remainder by a constant, through the
admitted carriers). Without one the body refuses (`IndexedUnbounded`). The
finder only decides admission: the claim is proved by the solver whatever
it decides, so a wrong bound refuses or refutes, never credits. A slice-16
plan never cuts between a guard and its access (`indexed::guard_spans` bans
the span, and a cut that still separates them is blamed and replanned).

**Spelling.** A theorem that states an in-bounds claim is spelled as slice
16 spells a part, as one part (`split::unify_definitions`, then slice 9's
inlining with every claim that becomes an identity dropped; the plain
spelling when the claims would all drop or the structural check fails):
the two sides' offsets become one name and a constant stride is a constant
in the multiply. Each rewrite is equivalence-preserving under the
definitions and is the one slice 16 already trusts for parts; the choice
is host qualification's (below). A theorem without an in-bounds claim
keeps its spelling.

**What changes for other bodies.** A body without an indexed access keeps
its theorem byte for byte, unless one of its cut points has a dead byte:
then that byte's relation is gone (the only such earlier fixture is slice
12's `ByteBoolCarried`, whose header byte `s5` is overwritten before every
read; its golden digest moved with this commit and its theorem is
re-qualified below). Every other golden digest of slices 1-16 is unchanged.

## The claim and its soundness

**The select is exact where the claim holds.** The exactness lemma: where
`in_bounds(o)` holds, `o` is a candidate, `select` is the `w` bytes at `o`
and `update` is the store of `x` at `o`. It is swept against a concrete byte
array (`the_indexed_spelling_is_exact_on_every_candidate`: every slot size
to 64 and the sizes 100, 128, 255 and 256, width 0, 1, 2, 4 and 8, modulus 1
to 16 and every residue, each candidate, its neighbours, offsets past the
slot and wrapped ones), and both walks call exactly these functions.

**Why a claim and not a premise.** trust-ir makes an access outside its
allocation undefined (`checked_access`, `interpret.rs` 8816-8857 at
`cb6397762`), so a premise "the offset is in bounds" might look free. It is
not: trust-ir's `IntToPtr` resolves provenance by address
(`try_pointer_from_address`, 8775-8798), and the adapter lowers both a GEP
and integer pointer arithmetic to an LIR `Iadd` of the slot's address, so
an out-of-bounds LIR offset may be a DEFINED access to a neighbouring
allocation; a premise would waive exactly those runs. As a claim, the
theorem is false on any input where either side's offset leaves its
candidates.

**Induction.** Take a run on which the source is defined, and the first
indexed access (of either side, in program order of its region instance)
whose offset is not a candidate. Every term before it is exact (each earlier
select and update was at a candidate, where the lemma makes them the
memory's bytes), so its own in-bounds claim is evaluated on the actual
offset and is false: a Valid theorem has no such access. Hence on every run
every select and update is the memory, and OD-84's claim follows as in
slices 9 to 16. A machine access outside its slot cannot hide behind the
select (which reads some candidate's bytes for every offset), because its
own claim states the bound; an access between the candidates (misaligned)
cannot either, because the claim states the congruence.

**Dead bytes.** A byte dead at a cut point is overwritten before any read on
every path from the cut, and every read and escape is counted as a use (a
call, a C memory routine, an untracked access, an indexed access of the
slot), so its value at the cut cannot reach an observable. Leaving it
unreadable makes any actual read of it refuse (source) or make no claim
(machine), so a wrong liveness verdict refuses, never credits.

## Controls

Every test below runs without a solver (the library gate
`x86_source_bound_body::tests::slice17::`, 18 tests); the replay on AY and
Clean is in Qualification. Fixtures are real: LIR from the trust-ir adapter
(translated with an explicit `Permit`), the machine stream from the real
x86-64 instruction selector at O0.

**Correct lowerings** (`owner_builds_every_slice_seventeen_shape`: each
builds a theorem with in-bounds claims on both sides that holds on slice 9's
keyed sampler and slices 10-11's samplers; `slice_seventeen_theorems_are_deterministic`):

| Fixture | Shape | Exercises |
| --- | --- | --- |
| `NibbleTable` | `lo[(b >> 4)] \| hi[b & 15] << 8` over two 16-byte local tables | the index's own range (shift, mask), two slots |
| `BoundsCheckedTable` | `T[i]`, `T: [u8; 16]`, behind rustc's bounds check | a guard bound, the panic path a trap |
| `ScaledLoadU32` | `a[i]`, `a: [u32; 8]` | the `Imul` by 4 (an `imul` by a constant register), modulus 4 |
| `PairTableFields` | `t[i].0 + t[i].1`, `t: [(u64, u64); 3]` | stride 16, base offsets 0 and 8 |
| `IndexedStoreInLoop` | `a[i] = x` in a loop over `[u32; 40]`, then `a[0]` | updated bytes as loop-header bytes |
| `StoreThenConstRead` | `a[i] = x; a[0] + a[1]` | the update leaves unselected bytes as they were |
| `StoreThenIndexedRead` | `a[i] = x; a[j]` | a select over updated bytes, two offsets |
| `IndexedCallArgument` | `write(&mut buf[curr], d)` in a loop, then `finish(&buf, curr)` | the `slot{s} + o` argument, the escape, the observation at the next call |
| `FilledThenIndexed` | `fill(&mut a); a[i] = x; sum(&a)` over `[u32; 40]` | call-defined candidate bytes |
| `OctetsZip` | a local copy of a `[u8; 4]` aggregate parameter, `c[i] & 0x0f` in a loop | aggregate-parameter bytes (slice 8) as candidates |
| `PartlyWritten` | `buf[0..4] = x; buf[i]` for `i < 4` over `[u8; 8]` | never-selected candidates reading the frame's initial bytes |
| `F64Table` | `t[i & 31]`, `t: [f64; 32]` | a `movsd` load, a float bit pattern |
| `ScaleByThree` | `a[i][2]`, `a: [[u8; 3]; 4]` | the `Imul` by 3 against the selector's `lea [x + x*2]` (modulus 1) |
| `NarrowIndex` | `T[b as usize]`, `b: u8`, `T: [u8; 256]` | the index's `movzx`; a 256-arm select |
| `SliceTempInLoop` | `fmt::num`'s loop: `&buf[..]` rebuilt as a pointer-length pair each iteration | the pair's bytes dead at the header (OD-184); the indexed argument |
| `IndexedAcrossJoin` | `p = &T[i]; y = if c { 1 } else { 2 }; *p + y` | an indexed address live across a DAG join (the probe's crash, fixed) |
| `ArrayGepTable` | `a[i]` over `a: [u64; 4]`, every element by LIR `ArrayGep` | stride 8, the selector's `lea [b + i*8]` |
| `ArrayGepStride3` | `a[i][0]` over `[[u8; 3]; 4]` | stride 3, the selector's `lea [b + i*2]; add i` |
| `ArrayGepStride12` | `a[i][0]` over `[[u32; 3]; 4]` | stride 12, `imul i, 12; add b`, modulus 4 |
| `ArrayGepStore` | `a[i] = 7; a[0] + a[3]` over `[u64; 4]` | a store through a variable `ArrayGep` |

Two machine variants the selector does not emit at O0
(`every_slice_seventeen_machine_variant_holds`): `ScaledLoadU32` with the
scaled index as one `lea d, [frame + i*4]`, and `ScaleByThree` with the
multiply as `imul` instead of `lea [x + x*2]`. Both hold: the offset is
judged as a term, never by shape.

Further correct-lowering controls: `the_indexed_spelling_is_exact_on_every_candidate`
(the exactness lemma's sweep, 10,000+ in-bounds offsets checked);
`bit_moves_are_substituted_exactly` (the spelling's bit-move substitution
against evaluation, 2,000 inputs per claim);
`a_body_without_an_indexed_access_states_no_in_bounds_claim` (every slice-12
fixture); `the_slice_temp_bytes_are_dead_at_the_header_and_the_argument_is_observed`
(no header input for the pair's 16 bytes, the buffer's bytes live);
`byte_liveness_is_conservative`; `every_indexed_site_is_claimed_on_both_sides`;
`an_access_through_an_indexed_load_of_call_bytes_observes_the_escaped_slots`
(`IndexedTaint`: a pointer loaded through an indexed address from bytes a
call wrote is a derived access, slice 15); `an_indexed_address_live_across_a_dag_join_is_kept`.

**Refusals by name** (each a source or machine the rules must not state):

| Control | Input | Outcome |
| --- | --- | --- |
| `a_live_stored_address_at_a_header_is_still_refused_by_name` | `LiveSliceTemp`: the pair's pointer half read back at the top of the loop body (live at the header) | refused: slice 13's stored-address rule |
| `an_unbounded_index_is_refused_and_its_claim_refutes_it` | `Unbounded` (no guard), `OffByOneGuard` (`i <= 16` into 16 bytes) and `ArrayGepByteBound` (`i < 32` into `[u64; 4]`: a guard in bytes, not elements) | refused `IndexedUnbounded`; built without the bound finder, refuted on samples |
| `an_indexed_bool_read_of_an_unwritten_candidate_is_refused` | `BoolTable`: `a: [bool; 4]`, `a[0..3]` written, `a[i]` for `i < 3` | refused: a candidate byte no `bool` store wrote |
| `an_indexed_argument_into_another_slot_is_a_named_mismatch` | `SliceTempInLoop` with the argument formed from the pair's slot | `CallStackAddress` mismatch |
| `a_machine_read_of_a_dead_header_byte_makes_no_claim` | `PairReadBack` with the machine reading the stale pointer half where the source rebuilds it | no claim (a read of an unreadable byte) |

**Mis-models** (`every_slice_seventeen_refutation_is_refuted`: each wrong
lowering's theorem, built without the owner's affine refusal, or without the
bound finder for the out-of-bounds sources, is refuted on samples and never
credited by the owner; AY's verdicts are in Qualification):

| Mis-model | Fixture | What must refute it |
| --- | --- | --- |
| a wrong scale (`imul i, 2` for a `u32` element) | `ScaledLoadU32` | the value read, and the machine's congruence |
| a wrong base slot (the other table's frame register) | `NibbleTable` | the value read |
| an index off by one (`T[i + 1]`) | `BoundsCheckedTable` | the value, and at `i = 15` the machine's claim |
| a store to the wrong element (`a[i - 1] = x`) | `StoreThenIndexedRead` | the read, and at `i = 0` the machine's claim |
| a store clobbering its neighbour (8 bytes for a `u32`) | `StoreThenConstRead` | the neighbour's read |
| a missing zero extension of a `u8` index (the whole argument register) | `NarrowIndex` | the machine's claim (the caller's bits above) and the value |
| a sign extension for a zero extension (`movsx`) | `NarrowIndex` | the value at `b >= 128`, the machine's claim |
| a misaligned offset (`4i + 1`) | `ScaledLoadU32` | the value and the machine's congruence |
| a call argument one element off (`lea [frame + i + 1]`) | `IndexedCallArgument` | the argument item `slot{s} + o` |
| a load moved above the store it must see | `StoreThenIndexedRead` | the read |
| an indexed store of the wrong value | `StoreThenConstRead` | the reads |
| out of bounds on a defined path (`i <= 16` into 16 bytes, the selector's correct lowering) | `OffByOneGuard` | both sides' claims at `i = 16` (no premise excuses it) |
| out of bounds on a defined path, the machine in bounds (`mov d, frame` for the indexed `add`) | `UniformOffByOne` (a table of one repeated byte) | ONLY the source's claim: the values, the branch and the trap agree |
| a machine access 64 bytes past its slot | `UniformTable` | ONLY the machine's claim (the select reads a byte of the table, the same value, at every offset) |
| a misaligned read inside the slot (`4i + 1`) | `UniformScaled` (one repeated `u32`) | ONLY the machine's congruence |
| an `ArrayGep` element scaled by 4 for a `u64` | `ArrayGepTable` | the value read |
| a stride-3 element at `2i` (`lea [b + i*1]; add i`) | `ArrayGepStride3` | the value read |

The `Uniform*` sources make every wrong read return the right value, so each
of the last three is refuted by exactly one in-bounds claim: they are the
controls of the claim itself.

## Fails-before

`fails-before/mutate.py` guards each slice-17 rule behind
`TCG_S17_MUTANT=<name>` in the working tree (one test build serves every
mutant; the edits are undone afterwards and never committed), and
`fails-before/run_mutants.sh` runs the slice-17 library gate once per
mutant. On the final code, after the `ArrayGep` merge (payload
`mutants/`, with each run's log), the unmutated build passes all 18
slice-17 tests and every one of the 15 mutants fails at least one control
(the first 13 with the same verdicts as on the chain spelling before the
merge, payload `mutants_chain/`):

| Mutant (the rule disabled) | Controls that fail (the semantic one first) |
| --- | --- |
| `no-source-ib`: the source states no in-bounds claim | the mis-model "out of bounds on a defined path, the machine in bounds" holds; the claim counts of `owner_builds_every_slice_seventeen_shape`, `every_indexed_site_is_claimed_on_both_sides`, `an_indexed_address_live_across_a_dag_join_is_kept` |
| `no-machine-ib`: the machine states none | "a missing zero extension of a narrow index" holds (the first wrong lowering the test meets that holds: under the low-bit select the index's low byte reads the right element, so only the machine's claim sees the caller's bits above it; on the chain spelling it was "a machine access past its slot"); the same three claim counts |
| `ib-no-congruence`: the claim omits the congruence | "a misaligned read inside the slot" holds; the exactness sweep |
| `store-no-update`: an indexed store leaves its bytes | "a load moved above the store it must see" holds; the exactness sweep |
| `store-first-candidate`: only the first candidate's bytes updated | the exactness sweep |
| `candidates-one-short`: `k <= n - w - 1` | the exactness sweep; `BoolTable` admitted (its unwritten candidate is no longer one) |
| `arg-offset-unobserved`: an indexed argument observed as its slot's address alone | "a call argument one element off" holds; `the_slice_temp_bytes_are_dead_at_the_header_and_the_argument_is_observed` |
| `arg-slot-unchecked`: the machine's argument may name another slot | `an_indexed_argument_into_another_slot_is_a_named_mismatch` |
| `indexed-taint-dropped`: a value an indexed load reads is never tainted | `an_access_through_an_indexed_load_of_call_bytes_observes_the_escaped_slots` |
| `indexed-bool-unchecked`: a `bool` read through an indexed address admitted whatever its candidates' bytes | `an_indexed_bool_read_of_an_unwritten_candidate_is_refused` |
| `bound-finder-admits-all`: every indexed use admitted unbounded | `an_unbounded_index_is_refused_and_its_claim_refutes_it` |
| `dead-byte-ignores-loads`: the byte liveness counts no load as a read | `a_live_stored_address_at_a_header_is_still_refused_by_name`, `byte_liveness_is_conservative`, and three fixture controls (the dead marker reaches a read) |
| `dead-byte-keeps-value`: a machine byte dead at a header keeps its edge value | `a_machine_read_of_a_dead_header_byte_makes_no_claim` |
| `agep-stride-one`: an `ArrayGep` of a private slot at a variable index indexed with stride 1, not the element size | `owner_builds_every_slice_seventeen_shape` (the `ArrayGep` fixtures' theorems are refuted on samples); the byte-bound guard admitted |
| `bound-ignores-stride`: the bound finder scales the index by its own stride only | `an_unbounded_index_is_refused_and_its_claim_refutes_it` (the byte-bound guard `i < 25` into `[u64; 4]` admitted) |

`store-first-candidate` and `candidates-one-short` change the one select/update
spelling both walks call, so a correct pair stays equal under them and only
the exactness sweep sees them: that is why the spelling is trusted and swept
against a concrete byte array, and why both walks must call it (they do;
there is no other spelling). The first run of the mutants (payload
`mutants_first/`, chain spelling) found that the "machine in bounds" control did not need the
source's claim: its machine zeroed the index register that also fed the
bounds check, so the branch refuted it. The control now replaces only the
indexed `add` with a copy of the frame register, and `no-source-ib` fails it.
Likewise the first run on the `ArrayGep` merge (payload
`mutants_agep_first/`) found `bound-ignores-stride` failing no control: the
byte-bound guard was `i < 32`, which an 8-byte access refuses with or
without the stride. It is now `i < 25` (`i + 8 <= 32` holds, `8i + 8 <=
32` does not), and the mutant fails it.

## Robustness probe

`robustness/x86_source_bound_body_slice17_robust_tests.rs` (slice 12's
probe, with its concrete interpreters of the LIR and of the pre-RA x86
stream as the ground truth, `F64Table` left out) mutates every fixture's
selector output at O0 to O3 in the design's classes C19 to C24 and judges
each mutant by the owner, the samplers, AY with Clean, the verifier's
credit and the ground truth (payloads `robustness.log`, no replay, and
`robustness_replay_final.log`, every theorem replayed, on the final code):

| Class | Mutants | Theorem | Sampler refutes | AY countermodel | AY certifies | Credited | Ground-truth wrong: refused / mismatch / refuted / **credited** |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| C0 originals (O0 to O3) | 39 | 19 | 0 | 0 | 19 | 19 | 0 |
| C19 index register swapped | 64 | 27 | 26 | 26 | 1 | 1 | 56: 30 / 0 / 26 / **0** |
| C20 stride constant changed | 25 | 25 | 25 | 25 | 0 | 0 | 23: 0 / 0 / 23 / **0** |
| C21 displacement changed | 52 | 50 | 50 | 50 | 0 | 0 | 52: 2 / 0 / 50 / **0** |
| C22 base slot changed | 10 | 4 | 3 | 3 | 1 | 1 | 9: 5 / 1 / 3 / **0** |
| C23 index extension dropped or changed | 10 | 10 | 6 | 6 | 4 | 4 | 6: 0 / 0 / 6 / **0** |
| C24 bounds check `jcc` inverted | 54 | 21 | 21 | 21 | 0 | 0 | 51: 30 / 0 / 21 / **0** |
| **all** | 254 | 156 | 131 | 131 | 25 | 25 | 197: 67 / 1 / 129 / **0** |

No wrong stream is credited; AY finds a countermodel for every one the
samplers refute and for none they miss. The 25 credited are the 19 O0/O1
originals with a theorem and 6 mutants the ground truth judges correct:
`NibbleTable`'s `movzx` of an index below 16 replaced by `movsx` or a
16-bit `movzx` (four), an `OctetsZip` base register that is another copy of
the same slot's address, and a `PartlyWritten` index register that is a
copy of the index. Two correct mutants are refuted (C20:
`IndexedStoreInLoop` with a stride that writes past the slot while the
returned element is unchanged; the claim requires in-bounds stores). 20 of
the 39 originals (O1 to O3) are refused by name (below, Open gaps).

## Qualification (AY build 12713 with Clean)

The tool-gated tests ran on the qualification pair the tree pins
(`QUALIFIED_AY`: AY 0.27.0 build 12713, Clean 5f09e36c, through the
`x86-stage1-ay12713` overlay), one test per process (`census/qualify.sh`),
only after the owner's census chain had ended (12:55) and outside the
owner's quiet windows, on a host other lanes were compiling on. The final
run is on the `ArrayGep` merge (`49b4fd816`; payload
`qualification_agep/`, with every replayed query): slice 17's three tests,
main's two `ArrayGep` tests (`arraygep_qualification`, whose theorems the
merge leaves byte for byte) and slices 12 and 16, every one passing.
Earlier runs: `qualification/` (before the `ArrayGep` merge),
`qualification_last_merge/` (the merge of `4c6ce87e8`),
`qualification_lowbit_unnumbered/` and `qualification_vn/` (the earlier
spellings below).

**Three spelling steps, chosen here.** The first build stated a load's
select as the linear chain `(ite (= o k1) B1 (ite ...))`. Replayed offline,
the class's 133 queries (below) certified 118; the two 256-arm table
lookups of `escape_ascii<4>` and `escape_ascii<10>` came back from AY in
0.1 s with `computed UNSAT rejected by mandatory strict certification:
strict UNSAT proof validation failed: step t0 uses unverified trust rule`.
The same two queries rewritten by hand to the design's low-bit select (a
balanced tree on the offset's bits, `selects/balance.py`) certified (AY and
Clean, 12.6 s and 15.8 s), so the walks state that select
(`indexed::select`; OD-183). Next, the qualification fixtures with an
indexed store timed out at 30 s: `StoreThenIndexedRead` certifies offline
in 73 s, and in 3 s with its constant definitions substituted (`slow/`;
AY multiplies `(bvmul p0 s11)` with `s11 := 4` out as a product of two
variables), so a theorem that states an in-bounds claim is spelled as slice
16 spells a part (value numbering, inlining, identity dropping), which also
makes the two sides' offsets one name. Last, `FilledThenIndexed` still took
30-37 s and `IndexedStoreInLoop`'s proof was rejected by AY's own
self-check: the source's `p1 := x[31:0]` and the machine's `m0 :=
zext(x[31:0])` keep the 160 bytes of the stored array two spellings, so a
definition that only moves bits of variables is substituted first, with
three more exact extract identities (without them `NarrowIndex`'s
substituted narrow index is written out at every test of its 256-arm
select and AY cannot render the proof: `one surface override exceeds the
authored assume input-size bound`). Through the real builder the three
fixtures then certify in 0.7 s, 1.4 s and 1.4 s. On the class's queries:

| spelling | queries Verified (AY + Clean, 30 s) | Timeout | AY self-check rejected | functions with every query Verified |
| --- | ---: | ---: | ---: | ---: |
| linear chain | 118 of 133 | 13 | 2 (the 256-arm selects) | 35 of 43 |
| low-bit select | 120 | 13 | 0 | 37 |
| low-bit select, value-numbered | 122 | 11 | 0 | 39 |
| the same after the bit moves (final) | **122** | 11 | 0 | **39** |

No query verified by an earlier spelling fails a later one; the last step
changes 29 of the 133 queries (the single theorems; parts are slice 16's
spelling) and the class's outcome not at all, but it is what certifies the
qualification fixtures with indexed stores (below), and it halves the p90
time (8.0 s to 6.5 s). Selects AY certifies in the final spelling: up to
256 arms (`NarrowIndex`'s fixture; the two `escape_ascii` parts).

**Fixtures** (`host_qualification_replays_the_slice_seventeen_body_theorems`,
the canonical theorems through the real builder): all 20 fixtures (the four
`ArrayGep` ones 0.5-2.1 s) and both machine variants (`lea [frame + i*4]`;
`imul` by 3) Verified, 0.4-2.3 s each, `NarrowIndex`'s 256-arm select in
1.0 s; no recorded gap
(`KNOWN_UNCERTIFIED_SLICE_SEVENTEEN` is empty). The spelling steps were
qualified on them: before the bit-move substitution `FilledThenIndexed` took
30-37 s (a timeout under load) and `IndexedStoreInLoop`'s proof was rejected
by AY's own self-check (`computed UNSAT rejected by mandatory strict
certification: the provisional UNSAT verdict has no proof`); with the
substitution but without the extract identities, `NarrowIndex`'s proof could
not be rendered (`one surface override exceeds the authored assume
input-size bound`). Payloads `qualification_lowbit_unnumbered/`,
`qualification_vn/` hold those runs.

**Mis-models** (`host_qualification_refutes_every_slice_seventeen_mis_model`):
every one of the 17 is refuted by AY with a counterexample, each within
0.1-0.4 s:

| Mis-model | AY counterexample (the inputs that tell) |
| --- | --- |
| a wrong scale (`imul i, 2`) | `e_rdi = 2`: the source reads `a[2]`, the machine `a[1]` |
| a wrong base slot | `e_rdi = 12` (the nibble) |
| an index off by one | `e_rdi = 0` |
| a store to the wrong element | `e_rdi = 0, e_rsi = 1, e_rdx = 0` |
| a store clobbering its neighbour | `e_rdi = 0, e_rsi = 0` (the 8-byte store writes `a[1]` too) |
| a missing zero extension of a `u8` index | `e_rdi = 0xffff_ffff_ffff_ffff`: the caller's bits above the byte |
| a sign extension for a zero extension | `e_rdi = 128` |
| a misaligned offset (`4i + 1`) | `e_rdi = 6` |
| a call argument one element off | `e_rdi = 0` (the first iteration's argument) |
| a load moved above the store it must see | `e_rdi = e_rsi = 1` |
| an indexed store of the wrong value | `e_rdi = e_rsi = 0` |
| out of bounds on a defined path | `e_rdi = 16` |
| out of bounds on a defined path, the machine in bounds | `e_rdi = 16`: only the source's claim |
| a machine access past its slot | `e_rdi = 0`: only the machine's claim |
| a misaligned read inside the slot | `e_rdi = 0`: only the machine's congruence |
| an `ArrayGep` element scaled by 4 for a `u64` | `e_rdi = 1` (`a[1] = x + 1` against the bytes at offset 4) |
| a stride-3 `ArrayGep` element at `2i` | `e_rdi = 1` (offset 2 against 3) |

**Verifier credit** (`verifier_credits_every_bound_slice_seventeen_row_with_the_replayed_body_theorem`):
with the real tools, every covered row of every fixture is Formal under its
replayed body theorem, every function is promotable and its exports bind
the ABI (one per bound row); every refuted mis-model fails every covered
row and exports nothing.

**Slices 12 and 16 re-qualified** (the dead-byte rule changes slice 12's
`ByteBoolCarried`, and could change slice 16's parts): slice 12's replays
are unchanged but for it (`ByteBoolCarried` Verified, 4.5 s; the recorded
`EarlyExit` gap as before), and slice 16's parts and refutations give the
recorded outcomes (`LongChain`'s three parts time out, every refutation
refuted). Both tests pass, before and after the `ArrayGep` merge (payloads
`qualification/` and `qualification_agep/`).

**The dead-byte rule on the whole crate.** The 327 queries of the 132
functions whose theorem the rule changes (above) were replayed in both
spellings (payloads `replay_core_diff_s17.tsv`, `replay_core_diff_control.tsv`):
292 Verified in both, 3 Verified only in slice 17's spelling (timeouts in
slice 16's), 24 timeouts and 8 AY self-check rejections in both; none
certified by slice 16's spelling fails slice 17's.

## Measured outcome on the class (probe, then offline AY with Clean)

**The class.** The design's 51 functions (`s17-design/data/functions.tsv`):
A, 35 census-s14 roots whose first refusal is the slot offset; B, 12 with
it behind a size bound; C, 4 behind an `i128` loop-carried value.

**The input.** The fresh `core` trust-ir dump of the slice-16 record
(`runs/core-ir-s16`, main a902's bridge), and, as a cross-check, the
design's input, slice 9's dump (`runs/core-ir-s9`, re-spelled for the
pinned adapter as the slice-16 record describes). The probe
(`census/run_probe.sh`: the slice-16 record's probe, built from this
branch, one thread, no AY) ran this branch's owner over the 51, every built
theorem (every part) checked on 600 samples and written out; the control is
the slice-16 probe over the same dump. Payloads `fin_s16/`,
`measure_fin_s16.txt`, and the same for main 2854ce's dump (`fin_2854ce/`,
the dump of the bridge whose census was slice 16's landing baseline,
`census/dump_core_ir.sh`) and slice 9's (`fin_s9/`). Each merge of main
was followed by a probe run; the verdicts never changed, and the queries
changed only with this slice's own spelling commits.

| group | functions | control (slice 16) | slice 17: single query | in parts | refused (first refusal) |
| --- | ---: | --- | ---: | ---: | --- |
| A | 35 | 34 at the slot offset, 1 (`AsciiChar`'s `Debug::fmt`) at machine blocks not one to one with the LIR's | **29** | **5** | 1: `AsciiChar`'s `Debug::fmt`, the same |
| B | 12 | 10 at the slot offset, 1 (`fmt_decimal`) at a DAG join holding different stored addresses, 1 (`exp_u128`) at an `i128` division | 0 | **9** | 3: `parse_decimal_seq` and `Duration`'s `fmt_decimal` at a DAG join holding different stored private addresses, `exp_u128` at an `i128` division |
| C | 4 | 4 at an `i128` loop-carried value | 0 | 0 | 4: the same (the `u128` formatters) |
| **all** | **51** | 0 built | **29** | **14** | 8 |

**43 of the 51 build a theorem** (34 of A, 9 of B), every one holding on
the samplers; no mismatch is named and no theorem or part is refuted on
samples. The design's estimate was an upper bound of 42 (34 of A, 8 of B):
`exp_u64`, which the design expected to stop at a loop header with several
outside entries, is stated in 16 parts. On slice 9's dump the verdicts are
the same (43 built; `parse_decimal_seq` stops at a cut point instead of the
DAG join). The 20 `fmt::num` formatters (OD-184's beneficiaries) are all
built: their pair's 16 bytes are dead at the header.

**The theorems.** 133 queries: 29 single theorems and 104 parts of 14
functions (3 to 16 parts each); in the final spelling 4.0 KB at the median,
11.6 KB at p90, 59 KB at most (`Big32x40::from_u64`'s second part, its
160-byte array stored in a loop). Bound rows: median 284, at most 2,773. Selects (`census/select_arms.py` over
the first build's chain spelling, payload `arms_s16.tsv`; the arm count is
the candidate count, whatever the spelling): the largest per function is 256 arms (the two `escape_ascii`,
in a part), 65 (`number_of_digits_decimal_left_shift`), 32
(`pow10_fast_path<f64>`), 19 (the two `parse_long_mantissa`), 16 (8
functions: the hex tables, the `Ipv6Addr` operators, `pow10_fast_path<f32>`,
`try_fast_path`), smaller in the rest; the 20 `fmt::num` formatters state
no select (their indexed accesses are call arguments: an argument item and
its claims).

**The whole crate.** The same probe over every function of the fresh dump
(3,424), against the slice-16 probe: 44 functions newly built (the 43 and
one more whose cut point held a dead stored address, OD-184), none newly
refused, none refuted on samples, no named mismatch; payloads `core_s17/`,
`core_control/`. Of the 3,249 functions both build, the 3,045 without a cut
point (no loop, one query) have byte-identical queries; of the 204 with a
loop header or slice-16 cut, 132 differ (327 queries), each by dropped or
renumbered definitions, the dead bytes their cut points no longer relate.

**Offline certification.** Every query of the 43 (every part of the 14
in parts) replayed with AY build 12713 in its strict Alethe mode within the
live 30 s budget, then checked by Clean (`census/replay_dir.py`, two at a
time, on a host other lanes were compiling on; payloads `replay_fin_s16.tsv`,
`replay_fin_2854ce.tsv`, and for the earlier spellings
`replay_class_s16.tsv`, `replay_lowbit_s16.tsv`, `replay_vn_s16.tsv`):

| dump | built | queries Verified (AY + Clean) | functions with every query Verified | A | B |
| --- | ---: | ---: | ---: | ---: | ---: |
| main a902 (the slice-16 record's) | 43 | **122 of 133** (11 Timeout) | **39** | 32 of 34 | 7 of 9 |
| main 2854ce, before the `ArrayGep` merge | 41 | 104 of 116 (12 Timeout) | 37 | 31 of 33 | 6 of 8 |
| **main 2854ce, after the `ArrayGep` merge (final)** | **43** | **115 of 126** (10 Timeout, 1 `proof-unrenderable`) | **39** | 32 of 34 | 7 of 9 |

On the final code a Verified query took 1.4 s at the median and 4.3 s at
p90 (AY and Clean; 2854ce's dump; payload `replay_agep_2854ce.tsv`). The
four built functions not certified are `ptr::align_offset::mod_inv` (a
product of two variables, the class the design priced at 0.23),
`Big32x40::from_u64` (one part, its 160 bytes stored in a loop), `exp_u64`
(6 of 16 parts) and grisu's `format_exact_opt` (3 of 12 parts; one of
them AY answers `unknown`, `proof-unrenderable`, at 25.8 s): no credit.

**After the `ArrayGep` merge, on main 2854ce's dump** (the dump of the
bridge whose census was main's baseline; probe payload `agep_2854ce/`):
the three functions the merge was to reach are in reach. `hex_escape<4>`
(before: `inconsistent type hint`, the array returned through a slot
typed as the array, OD-186) and `escape_ascii<4>` (before: an `ArrayGep`
the lane did not admit) now build theorems, and every one of their
queries certifies (1 and 9). `parse_decimal_seq` now gets past its
`ArrayGep`s and stops, by name, at this slice's candidate cap: a store
through an indexed address of `Decimal`'s 768-byte digit array has 784
candidate offsets (the lane admits 256 per access). The queries of every
function built before the merge are byte-identical after it, on both
dumps. The remaining 8 refusals are each by name: the four `u128`
formatters (an `i128` loop-carried value), `exp_u128` (an `i128`
division), `fmt_decimal` (a DAG join of different stored private
addresses), `AsciiChar`'s `Debug::fmt` (machine blocks not one to one with
the LIR's) and `parse_decimal_seq` (the cap). In the main CGU of this dump
every one of the 754 `ArrayGep`s has a constant index and no private
base: no function of `core` here reaches the variable-index `ArrayGep`
path, which the fixtures and controls above cover. Against the design's
estimate (about 26 with slice 16 absent, 33 to 35 with it, upper bound
42): 43 built and 39 certified offline.

## Gates

- Whole x86 body library gate, solver-free (`x86_source_bound_body`,
  skipping the tool-gated qualification, credit, negative-memo and
  canonical-migration tests): 298 passed, 0 failed on the final code
  (`c09c2794f`: the `ArrayGep` merge, the byte-bound control fix and
  main's next two merges, the last with X-HOST-P13's `ay_bridge` changes),
  main's `ArrayGep` tests and every slice's golden digest test included
  (payload
  `gate_body.log`; main's `ArrayGep` golden digest is unchanged by the
  merge); 298 passed on `49b4fd816`, 282 on the code before the merge,
  281 on each earlier tree measured (`205ef5c95`, `acea63a31`,
  `89e6928c4`). The slice-17 filter alone: 18 passed (`gate_slice17.log`).
- The tool-gated tests of slices 12, 16 and 17 and of `ArrayGep` on the
  `ArrayGep` merge (one per process, AY build 12713 with Clean): all pass
  (Qualification); slice 17's three again on the final code (payload
  `qualification_final/`).
- Lint: `check_tippy.sh` cannot run on this host (below); two doc lines of
  this slice that rustdoc would read as list items, the class main's
  `4ad0173d0` fixed in OD-185's paragraph, were re-wrapped by hand.
- `scripts/check_fmt.sh` with `TRUST_TARGO` set to the installed package's
  `targo` (the package launcher on this host was rewritten, and a plain
  run fails at tool setup): OK.
- `python3 scripts/check_documentation.py --check`: OK.
- Lint (`targo tippy`) cannot run on this host: the overlay's `targo` has no
  `tippy`, and the installed package's `targo` (6808) cannot parse the
  pinned AY manifest (`unknown field compiler_timeout_secs`, then no
  package `ay-pb`; re-tried on the final code); it was not run.

## Open gaps

- **Census.** The row above (232 to 191) is the measurement that counts. The 43 built and their offline certification are measured on
  `core` dumps of main a902's and 2854ce's bridges; a census of a slice-17
  bridge is the measurement that counts (it also replays through the live
  protocol).
- **When AY ran.** The owner's census chain held the host from before this
  slice's first build until 12:55; no AY or solver ran before it
  ended, so the select certification was measured after the implementation,
  not before it (the design's fallback, a select on the offset's low bits,
  was to be taken if AY could not certify the real selects within 30 s:
  it was taken, see Qualification).
- **The rest of the class.** 8 of the 51 stay refused, each by name:
  `AsciiChar`'s `Debug::fmt` (machine blocks not one to one with the
  LIR's), `Duration`'s `fmt_decimal` (a DAG join of different stored
  private addresses), `exp_u128` (an `i128` division), the four `u128`
  formatters (an `i128` loop-carried value), and, on the current dump,
  `parse_decimal_seq` at this slice's candidate cap (on a902's dump at a
  DAG join of stored addresses).
- **Optimized machine code.** The robustness probe's originals at O1 to O3
  (20 of 39) are refused by name: a memory operand with a scaled index over
  a frame register (`movzx r, byte [frame + i*s]`, `MovzxRM8Sib`,
  `MovMR32Sib`), the three-operand `imul` by an immediate (`ImulRRI`), and
  machine blocks that merge LIR blocks. The census is O0, where every
  indexed access is an `add` of a frame register and a value; the SIB
  memory operand is the next machine form to admit (its offset is the same
  term an `lea` gives).
- **The trusted spelling.** Two rule mutants (`store-first-candidate`,
  `candidates-one-short`) change the one spelling both walks call, and only
  the exactness sweep sees them (a correct pair stays equal under a
  symmetric change): the sweep is the check of that trust (slots to 64
  bytes and of 100, 128, 255 and 256 bytes, moduli to 16). The theorem's
  spelling for in-bounds claims (bit-move substitution, value numbering,
  inlining, identity dropping) is likewise trusted, not checked by Clean:
  each rewrite is equivalence-preserving, slice 16's are swept by its unit
  tests and the bit-move substitution by `bit_moves_are_substituted_exactly`.
- **Parts keep slice 16's spelling.** A part of a function in parts is
  spelled by slice 16 (value numbering without the bit-move substitution),
  in-bounds claims or not, so as not to change the landed slice's theorems;
  11 of the class's 104 parts time out at 30 s (`exp_u64` 5,
  `format_exact_opt` 4, `Big32x40::from_u64` 1), and `mod_inv`'s single
  theorem is a product of two variables. Giving parts with an in-bounds
  claim this slice's spelling is the next step for them; it was not
  measured here.
- **`ArrayGep` at a variable index over a private slot has no real
  occurrence yet.** On main 2854ce's dump every `ArrayGep` has a constant
  index and a non-private base, so the stride path (and its two rule
  mutants) is exercised by the four fixtures, two wrong lowerings and the
  byte-bound control only; a census of a bridge that emits such an
  `ArrayGep` would be its first real measurement.
- **The candidate cap.** `parse_decimal_seq` stops at 784 candidates for one
  store (the cap is 256, set from the class's tables; no AY measurement
  of a select or update that large was made).
- **Robustness exclusions.** The probe's ground truth does not model the
  `movsd` table (`F64Table` is left out) or the O1+ forms above (21 mutants
  "GT n/a"); two correct mutants (`IndexedStoreInLoop` with a stride that
  writes past the slot while the returned element is unchanged) are
  refuted, as the claim requires.
- **Not pushed.** The branch is local, as slice 16's was before its
  landing; nothing was pushed to `main`.
- **Decision-record numbering.** OD-183 and OD-184 are above main's maximum
  (OD-181) and slice 16's OD-182; OD-58, OD-145, OD-146 and OD-155 are
  duplicates on main itself.

## Reproducers (in tree)

- `fails-before/mutate.py`, `fails-before/run_mutants.sh`: the 13 rule
  mutants and their runner.
- `robustness/x86_source_bound_body_slice17_robust_tests.rs` (place it in
  `crates/trust-cg-verify/src/` and add its `#[path]` module to
  `x86_source_bound_body_tests.rs`; LOCAL ONLY) and `robustness/table.py`:
  the mutation probe with its concrete LIR and x86 interpreters, and its
  table.
- `census/run_probe.sh`: the slice-16 report's probe
  (`../2026-10-14-darwin-x86-64-slice16-parts/probe/x86_body_probe.rs`,
  built LOCAL ONLY in `crates/trust-cg-verify/examples/`) over a `core`
  dump, restricted to the class.
- `census/measure_s17.py`: the probe run classified per function against a
  control run, with the offline certification when given.
- `census/select_arms.py`: the select and update chains of a query
  directory, with their arm counts.
- `census/replay_dir.py`: offline replay of a query directory on AY build
  12713 with Clean, each query within the live 30 s budget.
- `census/qualify.sh`: one tool-gated test per process on the
  qualification pair.
- `census/dump_core_ir.sh`: a fresh `core` trust-ir dump from a census
  bridge, stopped once the main CGU's module is written (a solver run: the
  bridge proves the per-item modules before the main CGU with AY and Clean).
- `census/payloads.py`: the PAYLOADS.md table.
