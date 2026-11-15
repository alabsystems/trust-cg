# Darwin x86-64 `library/core` census — slice 15 (the value, call and observable residue), 2026-10-06

Slice 15 of the x86-64 source-bound whole-body theorem
(`crates/trust-cg-verify/src/x86_source_bound_body.rs`) closes the
value, call and observable refusals that a real proof can close: float
constants and the sign-bit operations `Fneg`/`Fabs` (ruling OD-112),
registers of mixed width, a `bool` parameter forwarded as a `bool`
argument (ruling OD-113, with a selector change), loads and stores through
an address that may derive from an escaped slot (ruling OD-114), and an
`I128` in the stack argument areas. A body with no observable stays
refused (ruling OD-115). This record holds the measurement that chose the
scope, where each meaning comes from, the host qualification, the controls
and their fails-before evidence, the mutation robustness probe and the
census rows. Host and toolchains as in the
[slice-13 census](../2026-10-05-darwin-x86-64-census-slice13/README.md):
native stage-1 `trustc 1.99.0-dev (d7f143f3b 2026-09-21)` through the
x86-stage1-ay12713 overlay (AY 0.27.0 build 12713, `b1b0b9de0`, with Clean
5f09e36c; the lane's qualification AY since the
[requalification](../2026-10-05-darwin-x86-64-ay12713-requalification/README.md),
ruling OD-85), bridges built on this host against the bridge overlay
(`targo --unverified build --release --locked`, no proof claim about the
build), `-Ztrust-verify=off`, O0, `-Cpanic=abort`, one CGU, proofs required
(the bridge default), `x86-body-trace` and `x86-body-dump`. Nothing here is
a completion claim. Payloads are out of tree; [PAYLOADS.md](PAYLOADS.md)
lists each with its SHA-256, and this README states the numbers they
carry.

| Row | Bridge built from | AY | Bridge sha256 | Failed roots | Wall |
| --- | --- | --- | --- | ---: | ---: |
| `core-x86_64-darwin-O0-proof-slice13-ay12713` (the class measurement; the slice-13 record's row) | the slice-13 branch, `90608b684` | 12713 | `01fa4c3a…` | 493 | 6253 s |
| `core-x86_64-darwin-O0-proof-main-cf98` (baseline) | `main` `cf982f936` | 12713 | `16c09ce3…` | 499 | 8866 s |
| `core-x86_64-darwin-O0-proof-slice15-cf98` | this branch at `6770368eb` (`main` `cf982f936` merged) | 12713 | `ebf1e17e…` | 466 | 9831 s |

**33 roots promoted, 0 newly failing, 0 named mismatches, 0 bound bodies
refuted**: 29 in the slice-15 classes, and 4 the baseline run's replay
noise (see Census delta). Every failed root of the three runs is
`[TCG-PROOF-465]`, and none recorded a resource-budget refusal. Both new
bridges were built on this host with `~/tcg-scratch/build_bridge.sh`
against the bridge overlay (`main` from a `git archive` of `cf982f936`,
the branch in its worktree) and hosted by the root overlay's `trustc`
(`census/census_s15.sh`). Each ran beside other agents' builds and this
branch's gates (the baseline beside the slice-15 bridge build, the slice-15
row beside the codegen and verify gates, load 10 to 20 on 4 cores), so
wall time is a trend, and a body whose replay sits near the 30 s
deadline may certify in one run and not in the other.

## The class, measured first

On the slice-13 census row (`census-s13-12713`, 493 failed roots, every
one `[TCG-PROOF-465]`), each failed root's named function's last body
trace (`census/roots_full.py`; every failed root names a distinct
function, so functions = roots). The value, call and observable refusals
the coordinator assigned to this slice, read from the traces themselves:

| First refusal | Roots | Slice 15 |
| --- | ---: | --- |
| `Fconst` (`F32` 0.0 ×2, `F32::MIN_POSITIVE`, `F32` +∞; `F64` 0.0 ×2, `F64::MIN_POSITIVE`, an `F64` NaN) | 8 | admitted (OD-112) |
| `Fneg` 2, `Fabs` 2 | 4 | admitted (OD-112) |
| `FcvtFromUint` 2, `FcvtFromInt` 1, `Fmul` 2, `Fdiv` 2 | 7 | outside: rounding (OD-73) |
| a machine `MovRR` of mixed widths (`mov edx, r64` 5, `mov r64, r32` 1; the 3-byte aggregate eightbyte) | 6 | admitted |
| a `B1` argument passed by a function that takes a `B1` parameter | 12 | admitted (OD-113, with the selector's entry `movzx`) |
| a `Load` (14) or a `bool` `Store` (1) through an address that may derive from an escaped slot (slice 7's retention rule) | 15 | admitted (OD-114) |
| an `I128` parameter (4: `carrying_mul`, `carrying_mul_add` ×3) or argument (1: `div_rem_1e16`) past the argument registers | 5 | admitted |
| no observable (no result, call or incoming-memory access) | 14 | stays refused (OD-115) |
| an aggregate parameter (3) or argument (1) over 16 bytes (MEMORY class) | 4 | outside: a by-value aggregate in memory is a copy in the caller's frame, which no slice models |
| an `Iadd` of a private address by a non-constant amount | 6 | outside: a symbolic offset into a slot (an array index) needs a symbolic slot model |
| more than 64 stack slots | 3 | outside: a size bound |
| a `Bitcast` into another carrier, an `I128` shift by a variable amount, `I128` atomic loads 2, an `AtomicRmw`, a join leaving different bytes where one holds an address 2 | 7 | outside (slices 2, 11 and 13 refuse them by name) |

The assignment named the derived-address class "`Load` of a non-scalar
or `I128` piece" and the machine rows "`MovRRN`" (the digit-normalized
`MovRR32` of the refusal's list of admitted rows); the traces name an
address that may derive from an escaped slot and a `MovRR` of mixed widths,
and the scope follows the traces. **Scope: 50 roots
first refused in an admitted class** (by roots over proof risk: every
admitted meaning is an exact bit-vector statement of trust-ir's own
definition, and the derived-access rule reuses slice 7's call congruence).
A first refusal is not the only one: a function may stop at a later
refusal (a loop, the size bounds), which the census row measures.

**The no-observable class stays refused.** Its 14 roots are three empty
`drop_in_place` instances, `ptr::metadata::<()>`, the `Waker` and
`LocalWaker` vtable no-ops, seven `Clone::clone` of zero-sized types and
`Extend<()>::extend_one`: private-slot traffic and copies only.
The suggested ABI-preservation observable (callee-saved registers and RSP
restored, no store outside the frame) is already enforced, by name, by the
trusted walk before any theorem exists (`PreservedWrite`, the slot-bounds
mismatch, an incoming store being an observable access). Stated in the
theorem, each conjunct is an identity on both sides, which the structural
non-vacuity check rejects and which a replayed proof would prove without
saying anything about the rows it would credit; crediting them would rest
on the walk alone, a proof exception (OD-115).

**Floating-point arithmetic stays outside.** `Fmul`, `Fdiv` and the
integer-to-float conversions round; their IEEE meaning needs `QF_FP`,
which AY's strict certification rejects on the qualification host
(OD-73). `Fneg`, `Fabs` and constants do not round and are exact bit
operations, which is why they are admitted.

## Semantics: where each meaning comes from

LIR meanings are trust-ir's (`trust_ir::interpret`, pin `137e2b55`) and
`trust_cg_lower`'s documented opcodes; machine meanings are the Intel
SDM's; the System V placement is the psABI's (§3.2.3).

- **Float constants** (OD-112). trust-ir's `float_bits_from_f64`
  (`interpret.rs`): `(value as f32).to_bits()` at `F32` (one
  round-to-nearest narrowing of the stored `f64`) and `value.to_bits()` at
  `F64`. The owner's `float_constant_bits` computes exactly that; an `F32`
  NaN constant is refused by name, because Rust leaves the payload of an
  `as`-narrowed NaN unspecified. The selector puts the constant's 4 or 8
  bytes in the function's constant pool and loads them with `movss`/`movsd
  xmm, [rip + entry]`, which writes those bytes and zeroes the rest of the
  register (Intel SDM, the memory form). The walk admits a constant-pool
  entry only as the operand of such a load of exactly its size, and reads
  the entry's bytes from the machine function (`const_pool_entries`).
- **`Fneg` and `Fabs`** (OD-112). trust-ir's `eval_float_unop`: `-operand`
  and `operand.abs()` on the host float, which IEEE 754 §5.5.1 defines as
  `negate` and `abs`: the sign bit flipped or cleared, every other bit
  kept, NaN payloads included, no rounding and no exception (trust-ir
  states its `F16` arm as exactly those bit operations). The owner states
  them as `x xor sign` and `x and not sign` (`FloatSignOp`), and
  `the_float_sign_and_constant_meanings_are_trust_irs` checks both, and the
  constant rule, against the pinned interpreter on zeros, subnormals,
  normals, infinities and quiet and signalling NaNs of both widths. The
  selector loads the sign mask (`0x80000000`, `0x8000000000000000`) or its
  complement from the constant pool and applies the three-operand `pxor`
  or `andps`/`andpd`, which are bitwise over the whole register (the walk
  models the low 64 bits; register allocation's two-address fixup later
  copies the source into the destination with a full 128-bit `movdqa`,
  after the pre-RA stream this theorem judges).
- **Registers of mixed width.** The encoder emits a register-register
  `mov` or ALU row with REX.W unless every register is 32-bit
  (`encode_alu_rr`), so `mov edx, r64` writes all of RDX from all of the
  source and `mov r64, r32` reads all of the 32-bit virtual register's
  physical register, whose bits above 31 the allocator does not keep. The
  walk therefore defines the low 32 bits of such a row as the operation of
  the operands' low 32 bits (exact for `mov`, `add`, `sub`, `imul`, `and`,
  `or`, `xor`, whose low half depends only on the operands' low halves)
  and the bits above as a free input: the theorem must hold whatever they
  are. The rows come from the selector's assembly of a 3-byte aggregate's
  eightbyte (`mov r64, r32` at a parameter, `mov edx, r64; or edx, r64` at
  an argument), whose observed bytes are the low 24 bits.
- **A forwarded `bool`** (OD-113). The theorem observes a `B1` argument as
  the clean 32-bit bool (EAX bits 0..31 = 0 or 1) under every caller view,
  the width the backend passes a `bool` at and an LLVM callee relies on
  (`fn(b: bool) -> u32 { b as u32 }` is `movl %edi, %eax`). A psABI caller
  defines only bits 0..7 of a `bool` argument register, so the selector
  now defines a System V `bool` register parameter as `movzx r32, r/m8`
  of the register's low byte (it copied the 32-bit register before), and
  the theorem holds under both caller views.
- **Accesses through a derived address** (OD-114). The trust-ir memory
  model gives a load the bytes at its address and a store writes them; an
  address that may derive from an escaped slot (a call result, bytes a
  call left or an incoming load read after an escape, and what is computed
  from them) may point into that slot or into incoming memory. The
  theorem makes such an access an event of the world trace (address,
  width, a store's value; a load's one shared result input) that also
  observes every escaped slot's bytes at that point, and a store leaves
  every escaped byte as a fresh input `t{site}s{slot}o{off}` on both
  sides. Both sides reach the access with equal incoming memory and equal
  escaped bytes (induction over the trace), which is all the memory such
  an address can reach, so equal inputs give an equal result and an equal
  next state: the Ackermann congruence, as for a call.
- **An `I128` on the stack.** psABI §3.2.3: an `__int128` is two INTEGER
  eightbytes; with fewer than two registers left the whole argument goes
  to the argument area, 16-byte aligned there, and a later INTEGER argument
  still takes a register left over. The parameter is `e_stack{d + 8} ++
  e_stack{d}` with `d` the 16-aligned displacement past `[rbp + 16]`; the
  argument is observed as its two halves at `[rsp + d]` and `[rsp + d + 8]`
  when the call runs. `the_verify_owned_i128_stack_placement_agrees_with_the_selector`
  sweeps the verify-owned placement against the selector's formal-argument
  bindings and call rows.

## What is admitted, and what is trusted

Admitted (each with its fixture shapes, of 22 in `SLICE_FIFTEEN`):

- `Fconst` of `F32` and `F64` (an `F32` NaN refused by name), `Fneg` and
  `Fabs` of both widths, through the constant-pool `movss`/`movsd` load
  of exactly the entry's size and the three-operand `pxor`/`andps`/`andpd`
  (`ConstF32`, `ConstF64`, `ConstF64Nan`, `ConstF32Inf`, `ConstStored`,
  `NegF32`, `NegF64`, `AbsF32`, `AbsF64`, `NegAbsBits`).
- A `MovRR` or a three-address (or tied) `add`/`sub`/`imul`/`and`/`or`/`xor`
  of mixed 32- and 64-bit registers, defining the low 32 bits
  (`ThreeBytes`: `fn(x: [u8; 3]) -> [u8; 3] { g3(x) }`, whose eightbytes the
  selector moves through 32- and 64-bit registers).
- A `B1` argument in a function with a `B1` parameter (`ForwardBool`,
  `ForwardBoolMixed`, `ForwardBoolReturn`, the last walked under both
  caller views).
- A load or store through an address that may derive from an escaped slot
  (`DerivedLoad`, `DerivedLoadReturned`, `DerivedStore`,
  `DerivedLoadOffset`).
- An `I128` parameter or argument past the integer registers
  (`StackParamI128`, `StackParamI128ThenScalar`, `StackArgI128`,
  `StackArgI128Aligned`).

Trusted for slice 15, in addition to what slices 1 to 13 trust:

- the constant-pool entry is emitted read-only, with its bytes, at the
  address the RIP-relative load resolves to (the encoder's and linker's,
  as for a symbol);
- the encoder's REX.W rule for rows of mixed widths (the walk's free input
  above bit 31 makes the theorem independent of what those bits hold, so
  only "the low 32 bits are the operation's" is relied on, which both
  encodings satisfy);
- the derived-access congruence: an address that may derive from an
  escaped slot reaches only incoming memory and the escaped slots (the
  provenance rule behind slice 7's retention rule: a slot that has not
  escaped has an address nothing outside the function holds);
- the verify-owned `I128` stack placement (swept against the selector);
- that every caller of a function taking a `bool` follows one of the two
  conventions the views state (psABI or clean 32-bit), as slice 11 already
  trusts.

## Qualification

`host_qualification_replays_the_slice_fifteen_body_theorems` replays the
22 fixture shapes (`f32`/`f64` constants, an `f64` NaN, `f32` infinity, a
stored `-0.0`; `-x` and `x.abs()` at both widths and `(-x).abs()`; a
`[u8; 3]` passed through a callee; a `bool` forwarded alone, beside a
`u64`, and to a callee whose `bool` result is returned; a load through a
pointer a callee left in a local, through the pointer a callee returned
after a local escaped to it, a store through it, and a vtable-like load at
an offset; `u128` parameters and arguments on the stack, aligned and after
a scalar) and 14 wrong lowerings. On AY 0.27.0 build 12713 with Clean
5f09e36c every fixture replays Verified (each in at most
1.5 s, beside a census) and every wrong lowering returns a counterexample
(payload `qualification.log`): another constant, another NaN payload, a
sign mask of another bit, `xor` for `and` and `and` for `xor`, `(-x).abs()`
without the `abs`, a 3-byte argument missing its third byte, the `bool`
register forwarded raw (alone and beside a `u64`), the slot written behind
a derived load, a value kept in a register across a derived store, another
offset of a derived load, the swapped eightbytes of an `I128` stack
parameter and the swapped halves of an `I128` stack argument.
`KNOWN_UNCERTIFIED_SLICE_FIFTEEN` is empty, and the verifier-credit test
credits every bound row of every fixture Formal with the replayed theorem.

## Controls and fails-before

The solver-free library gate row `x86_source_bound_body::tests::slice15::`
(14 tests, golden digest `slice15_snapshots.smt2`) passes. Earlier tests
that encoded the old boundary now state the new one: a `bool`
parameter's entry row is the selector's `movzx` (the golden snapshots of
slices 1, 3's memory family, 5, 6, 7, 9 and 11 change exactly there, and
every changed theorem keeps its recorded outcome: each slice's host
qualification passes on build 12713 except slice 9's, whose `StoreJoin`,
an unchanged query, ran out the deadline beside a census, see Gates); a
mixed-width `add` returning a 64-bit sum is refuted and a mixed-width
truncating copy builds a theorem that holds (both were outside); slice 7's and slice 8's
retention controls now check that exactly the derived accesses observe the
escaped slots and that their theorems hold (and slice 8's sweep of 45
admitted aggregate types through a call builds 45 theorems that hold,
where the 3 with a 3-byte eightbyte stopped at a mixed-width row);
the controls that stood for "outside" with an `Fneg` or an `I128` on the
stack now use a square root, a `bool` and a ninth `f64` there, which stay
outside.

**Rule mutants** (`fails-before/mutate.py`, `run_mutants.sh`; one build,
`TCG_S15_MUTANT` selects the rule; payloads `mutant_logs/`): every mutant
fails at least one control; the unmutated build passes all 14. (The golden
snapshot test also fails under every mutant that changes a fixture
theorem's text; the table names the semantic control.)

| Mutant | Rule disabled | Failing (of 14) | Among them |
| --- | --- | ---: | --- |
| `neg-as-abs` | `Fneg` flips the sign bit (the source meaning) | 5 | `the_float_sign_and_constant_meanings_are_trust_irs` |
| `f32-nan-constant` | an `F32` NaN constant is refused by name | 2 | `constant_pool_reads_and_float_operations_are_admitted_exactly` |
| `const-pool-any-size` | a constant-pool load reads exactly its entry's size | 1 | `constant_pool_reads_and_float_operations_are_admitted_exactly` |
| `const-pool-any-row` | only `movss`/`movsd` may name a constant-pool entry | 1 | `constant_pool_reads_and_float_operations_are_admitted_exactly` |
| `pxor-as-and` | `pxor` is an exclusive or (the machine meaning) | 5 | `every_slice_fifteen_refutation_is_refuted_on_samples` (`AbsF64/xor-for-and`), `slice_fifteen_theorems_hold_on_samples` |
| `mixed-copy-zero-extends` | a mixed-width copy defines only its low 32 bits | 2 | `a_mixed_width_copy_defines_only_its_low_32_bits` |
| `mixed-alu-full-width` | a mixed-width ALU row defines only its low 32 bits | 2 | `a_mixed_width_alu_row_defines_only_its_low_32_bits` |
| `bool-arg-byte` | a `B1` argument is observed as the clean 32-bit bool | 2 | `every_slice_fifteen_refutation_is_refuted_on_samples` (`ForwardBool*/raw-forward`) |
| `derived-load-unobserved` | a derived load observes the escaped slots | 2 | `derived_accesses_observe_the_escaped_slots`, `every_slice_fifteen_refutation_is_refuted_on_samples` (`DerivedLoadReturned/slot-written-before-load`) |
| `derived-store-keeps` | a derived store redefines the escaped slots' bytes | 2 | `derived_accesses_observe_the_escaped_slots` |
| `derived-escape-unchecked` | at a derived access the machine's escaped slots are the source's | 1 | `derived_accesses_observe_the_escaped_slots` |
| `i128-stack-unaligned` | an `I128` on the stack is 16-byte aligned | 1 | `the_verify_owned_i128_stack_placement_agrees_with_the_selector` |
| `i128-stack-swapped` | an `I128` stack parameter is high eightbyte over low | 6 | `the_verify_owned_i128_stack_placement_agrees_with_the_selector`, `slice_fifteen_theorems_hold_on_samples` |
| `selector-bool-copy` | (the selector) a `bool` register parameter is `movzx` of its low byte | 7 | `a_forwarded_bool_is_the_clean_32_bit_bool_under_every_caller_view`, `slice_fifteen_theorems_hold_on_samples`; and the lowering library's `test_lower_formal_arguments_sysv_bool_register_is_movzx_of_the_low_byte` (payload `mutant_logs/mutants_lower.txt`) |

The first run (payload `mutant_logs/mutants_first.txt`, before the ALU
control existed) left `mixed-alu-full-width` failing only the golden
snapshot: the earlier mixed-width controls of the first slices
(`wrong_width_or_extension_is_refused`, whose mixed `add` returns through
a mixed copy) refute through the copy, which hid the ALU rule
(`mutant_logs/mutants_base.txt`). The new control
`a_mixed_width_alu_row_defines_only_its_low_32_bits` (an `add r64, r64,
r32` of a zero-extended 32-bit register, refuted) fails under it
(`mutant_logs/mutants_alu.txt`), and the table above is the rerun with it.

**Mutation robustness** ([robustness/README.md](robustness/README.md)):
1341 mutants of the 24 distinct O0-O3 streams of the 22 fixtures, judged
against an independent concrete interpreter (AY build 12713 and Clean
5f09e36c). 969 are wrong by ground truth: 144 make no claim, 408 are named
mismatches and 417 are refuted by the sampler and AY; none is credited or
replays Valid. Every theorem AY refutes the sampler refutes too (467 of
467). The 222 credited streams (24 originals, 198 mutants) are all correct
by ground truth. 150 correct mutants are not credited, each fail-closed by
rule (65 no claim, 35 named mismatches, 50 refuted: 45 of them the
mixed-width rule keeping only the low 32 bits where the encoder's REX.W row
moves all 64, 4 the derived access observing escaped bytes no read
reaches, 1 the probe's concrete callee being the identity). Building the
probe found only defects of its own ground truth.

**Optimized fixtures.** The real x86 optimizer's O1, O2 and O3 output of
every fixture: every theorem the owner builds holds on samples and none is
a mismatch (`optimized_slice_fifteen_fixtures_are_judged_without_false_mismatches`).

## End to end (`crates/trust-cg-codegen/tests/x86_source_bound_body.rs`)

The end-to-end module gains six slice-15 functions (`float_const`,
`float_neg`, `float_abs`, `bool_forward`, `derived_load`,
`wide_stack_param`); the proof-required compile must promote with every
one Formal, on Darwin and Linux. On AY build 12713
(`X86_BODY_E2E_REPLAY_IDENTITY`) the module's other four tests pass (no replay refuses the compile by name, an
out-of-lane body keeps its sampled refusal, an uncertified body is judged
by its theorem alone, Win64 is named), and so does `must_refuse_corpus`.
The promotion test itself failed twice beside a census (payloads
`e2e.log`, `e2e_rerun.log`): the Darwin compile is refused at slice 9's
`dag_stores`, whose body theorem did not replay within the deadline (the
shape of the `StoreJoin` fixture, five conditional stores; see Gates).
With slice 9's three functions left out of the module (a local diagnostic
edit, never committed) the same test passes: the proof-required compile
promotes on both triples with every listed function Formal and its
theorem exported, the six slice-15 functions among them (payload
`e2e_without_slice9.log`).

## Census delta

`census/census_compare.py` against the baseline (payload `compare/`):

- **29 promoted roots** name a function the baseline refused in a
  slice-15 class that is now bound and certified: a forwarded `bool` 12,
  a derived access 5, `Fneg`/`Fabs` 4, a float constant 4, an `I128` on
  the stack 3, a mixed-width row 1.
- **4 promoted roots are replay noise** of the baseline run: bound on both
  sides, uncertified in the baseline run and certified here
  (`EscapeIterInner::printable`, `fmt::num::format_into`, an
  `Option<SocketAddrV6>` `from_residual` and `Parser::read_socket_addr`).
  All four certify on the slice-13 row too; they are among the six roots
  by which the baseline row (499) exceeds the slice-13 row (493), each
  "bound, replays Valid" there and "bound, no independently checked
  proof" in the baseline run (payload `compare_main_vs_s13/`). No
  function lost certification between the baseline and this row.
- **No root newly fails**, no mismatch is named and no bound body is
  refuted.

Where the 50 functions of the slice-15 classes went (payload
`compare/slice15_transitions.tsv`):

| Class | Functions | Bound, certified | Bound, not certified | Refused |
| --- | ---: | ---: | ---: | --- |
| a forwarded `bool` | 12 | 12 | 0 | |
| a derived access | 15 | 5 | 2 | 8: more than 512 machine rows 3, the machine-function refusal (a constant pool beyond a float load's, jump tables, EH, guard obligations or an outgoing call area) 3, a join leaving different values in a slot where one is an address 2 |
| a float constant | 8 | 4 | 2 | 2: an `Fcmp` |
| `Fneg`/`Fabs` | 4 | 4 | 0 | |
| an `I128` on the stack | 5 | 3 | 1 | 1: a `Udiv` |
| a mixed-width row | 6 | 1 | 4 | 1: machine blocks not one to one with the LIR's |
| **total** | **50** | **29** | **9** | **12** |

The 14 no-observable roots stay refused (OD-115), as do the other classes
outside the scope.

**The 9 that do not certify are AY's certification class and the host's
load**, replayed offline with the requalification's simulation of the
production protocol (`replay/production_replay.py` of that record: the
resident `ay --incremental` first, 30 s, then the fresh strict solve and
Clean; payloads `uncert_replay_12713.tsv`, `.log`): 8 distinct texts,
none satisfiable. 4 functions (3 texts: `char::escape_debug` and its
closure, `CharEscapeDebugContinue::call`, `Wtf8`'s `write_str_escaped`
closure) certify offline in 9-10 s, so they missed the deadline beside the
gates; `parse_inf_nan::<f64>` is a proof AY cannot render (`incomplete
proof-unrenderable`) and `parse_inf_nan::<f32>` a strict self-check
rejection (`incomplete proof-trusted`); the two `bignum` `bit_length`
methods and `CarryingMulAdd::carrying_mul_add` for `u128` run out the
resident route's 30 s deadline.

## Gates

On the merged tree (`main` `cf982f936` merged at `6770368eb`; the gates
ran on it and on `096882679`, which adds one control), through the
x86-stage1-ay12713 overlay (`targo --unverified`, no proof claim about
the build), AY build 12713 and Clean 5f09e36c, on a host shared with two
censuses and other agents' builds:

| Gate | Result |
| --- | --- |
| every workspace library and test target type-checked (`check --workspace --lib --tests --keep-going`) | only the three known kernel-JIT fixture refusals (`e2e_defeq_cache`, `e2e_lazy_delta`, `e2e_phase_completion`; payload `check_merged.log`) |
| the same after merging `main` `9df706eb5` (at `ce1276ad9`, with the rulings renumbered past `main`'s OD-101 to OD-107) | the three kernel-JIT refusals, and `main`'s own x86-host break: `ay_bridge_compact_tests.rs` imports `sha2::{Digest, Sha256}` for an AArch64-macOS-only test, an unused import under `-D warnings` on this host (payload `check_merged2.log`). Gating the import to that target fixes it; the verify crate then checks clean (payload `check_verify_after_fix.log`) and the slice-15 row and qualification pass again (payload `qualification_merged.log`) |
| verify library, serially: `x86_source_bound_body`, `x86_source_bound_envelope`, `diag::` (every slice's qualification and credit test, the matrix, the negative memo) | 267 passed, 3 failed, 11 ignored (payload `verify_body_serial.log`). `negative_memo::any_key_component_change_misses` passes alone (payload `rerun_slice9_memo.log`). Slice 9's qualification and credit tests fail on `StoreJoin`, whose canonical theorem ran out the deadline (41 s) beside a census, in this run and again alone; its query is byte-identical to `main`'s (the `StoreJoin` section of `slice9_snapshots.smt2`, SHA-256 `351c1780…` on both), and the requalification records it at 34.2 s of AY plus Clean, "credit near the budget therefore depends on load". Its credit test passes in the rerun |
| `x86_source_bound_body::tests::slice15` (the gate row and the qualification), serially, with AY and Clean | 16 passed, 1 ignored (payload `qualification.log`) |
| codegen `x86_source_bound_body` end to end and `must_refuse_corpus` | see End to end; 5 passed |
| IR, lowering and optimizer libraries | 538, 1994 and 4226 passed (2 ignored) |
| codegen library, without replayer controls in the environment | 4629 passed, 1 ignored (payload `libs_codegen.log`; a first run with `TCG_X86_BODY_QUALIFY_AY` and `TCG_EXTERNAL_CLEAN_CHECKER` set, whose log the rerun replaced, failed 64 admission tests by name, `UnkeyedAmbientCompilerControlsDuringAdmission`, which is why the host's gate script runs this library without them) |
| CLI `must_refuse_corpus` | 1 passed |
| `scripts/test_soundness_check.sh` (the new `slice15::` row) | 100 passed |
| `scripts/tests/test_export_x86_qualification_matrix.py` | 10 passed (eleven snapshot families) |
| `bash scripts/check_fmt.sh`, `python3 scripts/check_documentation.py --check` | OK; OK |
| `scripts/check_tippy.sh` | not run: the lint tool is unavailable on this host (the only `tippy` is the managed package 6808's, which stops before linting every package, and the stage-1 build has none) |

## Open findings

- **No miscompile was found** in the selector's output for a Rust caller:
  every fixture's theorem certifies, every robustness mutant AY refutes is
  wrong by the independent interpreter, and no original stream is wrong.
- **A `bool` forwarded from a psABI caller** (fixed here, OD-113): the
  selector copied a System V `bool` register parameter's 32 bits at entry,
  so a function forwarding it passed on whatever a caller left in bits
  8..31, which the psABI allows a caller to leave and the backend's own
  callee contract (a clean 32-bit bool, which an LLVM callee relies on)
  does not. LLVM, clang and this backend extend a `bool` argument to 32
  bits, so no Rust or C program built by them reaches it; a minimal psABI
  caller (hand-written assembly) could. The selector now zero-extends the
  low byte, and the C11 mutants of the robustness probe are the old
  lowering, refuted.
- **`main` `9df706eb5` does not build its verify library tests on an
  x86-64 host**: `ay_bridge_compact_tests.rs` imports `sha2::{Digest,
  Sha256}` at module level for a test gated to AArch64 macOS, an unused
  import under `-D warnings` elsewhere. This branch gates the import to
  the same target (the x86-64 host build breakage class: code validated on
  AArch64 only).
- **The no-observable class stays refused** (OD-115), and floating-point
  arithmetic stays outside (OD-73).

## Reproducers (in tree)

- `census/census_s15.sh` (the census command), `census/census_compare.py`
  (promoted, newly failing, mismatches, refuted bodies, transitions),
  `census/roots_full.py` and `census/roots_by_class.py` (the class
  measurement), `census/dump_class.sh`, `census/summarize.py` and
  `census/sig_compare.py` (the offline body profile through the
  [slice-9 record's probe](../2026-10-02-darwin-x86-64-census-slice9/probe/x86_body_probe.rs)),
  `census/payloads.py` (the [PAYLOADS.md](PAYLOADS.md) rows).
- `fails-before/`: `qualify.sh`, `mutate.py`, `run_mutants.sh`.
- `robustness/`: the mutation probe and its README.
