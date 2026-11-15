# Darwin x86-64 `library/core` census — slice 7 (calls through memory), 2026-10-01

Slice 7 of the x86-64 source-bound whole-body theorem
(`crates/trust-cg-verify/src/x86_source_bound_body.rs`): a direct call may
receive a private stack slot's address, as the hidden return buffer of an
`sret` callee or as an ordinary out-parameter. This record holds the census
row, the host qualification, the controls and their fails-before evidence,
and the cross-backend matrices. Host and toolchains as in the
[slice-6 census](../2026-09-30-darwin-x86-64-census-slice6/README.md): native
stage-1 `trustc 1.99.0-dev (d7f143f3b 2026-09-21)`, bridge built on this host
against the stage-1 `stage0-sysroot` (`targo --unverified build --release
--locked`), `-Ztrust-verify=off`, O0, `-Cpanic=abort`, one CGU, proofs
required (the bridge default), `-Ztrust-ir-cg-args=x86-body-trace`,
`--timeout 14400`. Replay tools: the toolchain AY the bridge build records
(`ay 0.27.0+build.10530`, sha256 `9a149c35…`) and the default checker
discovery. Nothing here is a completion claim. Payloads (root lists,
provenance, outcome tables, logs) are out of tree; [PAYLOADS.md](PAYLOADS.md)
lists each with its size and SHA-256, and this README states the numbers
they carry.

| Row | Bridge built from | Bridge sha256 | Failed roots | Distinct reasons | Wall |
| --- | --- | --- | ---: | ---: | ---: |
| [`core-x86_64-darwin-O0-proof-336a49f14`](../2026-09-27-darwin-x86-64-census/README.md) (baseline) | `main` `336a49f14` | `05a601b6…` | 1817 | 1 | 3093 s |
| `core-x86_64-darwin-O0-proof-slice7` | slice-7 branch `01b43cc0e` (base `65e3818dd`) | `1ff7bf40…` | 1634 | 1 | 7711 s |

## What was measured

- **Trees.** The baseline is the census of record on `main` `336a49f14`
  (`runs/main-336a.dylib`, sha256
  `05a601b609a128ba3cc920fb41da2b81f0413ac89513ff25de9b871bfe215234`; its
  per-function trace is that run's `stderr.log`). The slice-7 bridge
  (`runs/s7.dylib`, sha256
  `1ff7bf401bb77c7d27f65c965c2a4909aab5cd631ac656eba938ba9facf53dd5`) was
  built from this branch at `01b43cc0e`: `65e3818dd` (this branch's base,
  `origin/main` when the work started), the slice-7 owner and tests, and
  `eaa5d9ca8` cherry-picked unchanged. `main` did not build the bridge at
  `65e3818dd` (`error[E0004]: non-exhaustive patterns:
  PipelineError::StackLimit { .. } and
  PipelineError::StackLimitNotProofQualified { .. } not covered`, the U10
  merge `23b378270`); `eaa5d9ca8` is `main`'s own fix (it classifies the two
  variants in the bridge's diagnostic map and changes nothing else). Between
  `336a49f14` and `65e3818dd` `main` merged AArch64 work (U10 stack limit,
  pair/scalar memory refutation lanes, L03-P9 target features) and two
  O1+ optimizer fixes; the class transitions below attribute every change of
  this row to slice 7 (no function changed class for another reason, and no
  function that replayed Valid on the baseline fails to now). The changes
  after `01b43cc0e` change no behaviour of the owner: formatting, a slice
  `fill` for the equivalent loop (a lint), documentation, a `Copy` for a
  `clone` and one more control in the tests; the mutants and the gate row
  were re-run on the final tree with the same results.
- **Memory and host.** The census started with 527797 free pages; no
  `[TCG-COMPILE-DRIVER]` resource-budget refusal occurred. The host was
  shared (other agents' builds, and this branch's `targo tippy` run for part
  of the time; load 3.5-6.6).
- **Wall time** was 7711 s against the baseline's 3093 s (single runs on a
  shared host: a trend). The new solves are 334 newly bound bodies, 151 of
  which do not certify; each uncertified body is judged twice (the batched
  compile and its per-function fallback, the second answered by the
  negative memo: 363 memo hits in this run), and the bodies are larger than
  the ones that certify (newly bound uncertified: median 131 bound rows).

## Result

| Row | Failed roots | `[TCG-PROOF-465]` | Promoted | Newly failing | Emitted objects |
| --- | ---: | ---: | ---: | ---: | ---: |
| baseline `336a49f14` | 1817 | 1817 | — | — | 1627 |
| slice 7 `01b43cc0e` | 1634 | 1634 | 183 | 0 | 1810 |

1634 failed roots against the baseline's 1817, every one `[TCG-PROOF-465]`
(the sorted root list, payload `failed_roots.jsonl`, sha256
`58f23ed9961ec49d16c65f6e3333ecd776af6451fd1e8fb8d0bc52e0305be087`).

- **183** roots newly promote (payload `promoted.txt`, sha256
  `349855b79bc886f598fb4902634ff904da8072c7b330f9173272b4f2f01d0ce5`): 131
  whose function the baseline refused for a private slot's address escaping
  into a call, 52 for an sret-arg callee.
- **0** roots newly fail (`newly_failing.txt` is empty), no
  `[TCG-SOURCE-BOUND-X86-MISMATCH]` is named, and every function that
  replayed Valid on the baseline replays Valid here.

## Body trace

Per function (3446 traced on both sides; a function's class is its bound
verdict if it has one, else its last refusal; payload
`body_trace_classes.tsv`, sha256 `d5298082…`):

| Class | Baseline | Slice 7 |
| --- | ---: | ---: |
| bound, replays Valid | 1568 | 1751 |
| bound, no independently checked proof | 245 | 396 |
| an sret-arg callee (frame metadata) | 423 | — |
| a private slot's address escaping into a call | 185 | — |
| a non-scalar parameter | 235 | 281 |
| a non-scalar result | 227 | 234 |
| control flow: more than sixteen blocks | 102 | 167 |
| control flow: a path of more than 256 instructions | 33 | 78 |
| control flow: a loop | 40 | 49 |
| a call result with no scalar type | 49 | 62 |
| a private slot's address escaping into a store | 24 | 32 |
| an inconsistent sidecar type hint | 0 | 27 |
| more than six register parameters | 4 | 22 |
| an incoming access through an escape-derived address (slice 7) | — | 6 |
| a non-scalar load (integer / float) | 10 / 2 | 18 / 6 |
| more than 64 slots or a slot over 4096 bytes | 0 | 3 |
| more than 256 machine rows | 1 | 4 |

Where the baseline's two slice-7 refusals went:

| Baseline refusal | Valid | Bound, not certified | > 16 blocks | Non-scalar parameter | Long path | > 6 parameters | Type hint | Other |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| an sret-arg callee (423) | 52 | 131 | 65 | 46 | 45 | 18 | 12 | 54 |
| a slot escaping into a call (185) | 131 | 20 | — | — | — | — | 15 | 19 |

("Other" for the sret functions: 11 a call result with no scalar type, 9
loops, 7 non-scalar results, 6 non-scalar loads, 4 a slot address stored, 4
float loads, 3 more than 256 machine rows, 3 too many or too large slots, 2
an access through an escape-derived address, 5 in four other causes; for the
escape functions: 4 an access through an escape-derived address, 4 a slot
address stored, 11 in six other causes.)

**The 151 newly bound bodies that do not certify.** Their outcome is the
baseline's kind: AY's strict certification rejecting its own proof
(`(:reason-unknown (incomplete self-check-rejected))`,
`proof_gate_class=SOUNDNESS`) or an incomplete certificate
(`unproved_steps=1`), and a few attempts reached AY's 30 s budget; none is
a counterexample (outcome lines in this run: 736 self-check rejections, 53
incomplete certificates and 5 timeouts, the negative memo answering 2
later occurrences of a timed-out key; against 436, 54 and 0 on the
baseline). Their rows stay Unverified; the encoding is not reshaped per
function.

Offline (`probe/x86_body_probe.rs --census` over the census's own O0
modules, dumped with `-Ztrust-ir-cg-args=no-proof-certs
dump-trust-ir=DIR`, 447 s): the owner binds exactly the 2147 functions the
census bound (1751 + 396), and writes the theorem of 150 of the 151 (one
name collides at the 200-character file-name cut). Replayed with
`replay_dir.py` (the slice-6 report's: the toolchain AY with
`--strict-proofs --proof-format alethe`, then `clean cert verify-external`
with Clean 5f09e36c):

| Replay | Verified | AY self-check rejected | Incomplete certificate | Other |
| --- | ---: | ---: | ---: | ---: |
| two at a time, load 4-6 (`replay_uncertified.tsv`) | 9 | 134 | 6 | 1 unknown |
| one at a time, load 3-5 (`replay_uncertified_serial.tsv`) | 13 | 126 | 10 | 1 unknown |

None is refuted. The outcome is not a function of the query bytes alone:
the smallest rejected query, `Formatter::debug_struct` (4.6 kB, 47 bound
rows), was rejected in the two-at-a-time run (`c !! MODEL-UNCONFIRMED
[UNCONFIRMED/withheld]`, then the self-check rejection) and certified alone
(9.1 s), as in the 2026-09-30 AY report.
The call-defined bytes' spelling is not the cause: respelling every
aligned 8-byte run of call-defined bytes as one 64-bit free input (where
every use of those bytes is such a run, 77 of the 150 queries;
`word_respell.py`, evidence only, never a credit route) leaves all 77
rejected (`replay_words.tsv`). By size the newly bound bodies certify like
the baseline's (`size_rates.py`; Valid / bound per bound-row bucket):

| Bound rows | Baseline | Newly bound |
| --- | ---: | ---: |
| < 50 | 1096 / 1127 | 115 / 117 |
| 50-99 | 413 / 521 | 43 / 77 |
| 100-149 | 34 / 116 | 16 / 82 |
| >= 150 | 25 / 49 | 9 / 58 |

so the lower overall rate (183 of 334 against 1568 of 1813) is mostly the
larger bodies that calls through memory bring in (the sret callers are
`core`'s bigger functions).

**The 27 inconsistent type hints.** A new first refusal for functions the
two slice-7 rules used to stop earlier, and a correct one: each passes a
small aggregate BY VALUE (rustc's `Copy` aggregates such as `[I8; 3]`
`EscapeDebugExtArgs` or a `(&dyn Error)` `[I64; 2]` pair), which LIR
represents by its slot's address and types by the sidecar hint as the
aggregate; the selector passes its bytes in registers, not the address. The
owner types a slot's address as the `I64` pointer, so the hint disagrees and
the body is refused: a by-value aggregate is never taken for a
private-address argument. (Read from the offline probe of the census's
modules; a unit control, `other_uses_of_an_escaped_address_stay_outside_the_domain`,
pins it.)

## Remaining blockers

The 1634 failed roots by their function's body-trace class: 396 bound and
not certified (above), 281 a non-scalar parameter, 234 a non-scalar
result, 167 more than sixteen blocks, 78 a path over 256 instructions, 47 a
loop, 32 a slot's address stored, 30/22/21 `CheckedUadd`/`CheckedUmul`/
`CheckedUsub`, 27 an inconsistent type hint, 22 more than six parameters,
21 an indirect call, 18 a non-scalar load, 16 `GuardBoundsCheck`, 15
`CtPop`, 14 no observable, 14 `Bnot`, and 179 other causes.

## The model (what the theorem states about a call through memory)

A slot whose address a call receives ESCAPES to that call and every later
call on the path. The slice-3 call model (an uninterpreted function of the
world and the arguments, stated Ackermann-reduced: both sides read one free
input per call site) is extended with the slot's memory, exactly:

- **Inputs.** A call's observable inputs are its scalar arguments and the
  contents, at the call, of every slot that escaped to it or earlier: a
  callee may read any byte of a slot whose address it receives (pointer
  arithmetic within the allocation is defined, and LIR states no read-only
  promise for a `&T`), and may retain the address for a later callee. Each
  slot is observed in 8-byte chunks from offset 0; a chunk that is exactly
  one store's bytes is that value, any other the concatenation of its bytes;
  a chunk both sides spell alike (initial bytes neither wrote, or the bytes
  an earlier call left) states nothing and is not stated.
- **Outputs.** Besides its scalar result, the call leaves every byte of every
  escaped slot as it chooses: byte `y` of slot `x` after call site `c` is the
  free input `d{c}s{x}o{y}` on both sides. A Valid theorem means, by
  induction over the calls, that each call meets equal arguments, equal
  escaped bytes and an equal world, so it leaves equal bytes and an equal
  result — the UF congruence, with no assumption about which bytes a callee
  writes (an LLVM callee may write every byte of an `sret` buffer or of
  `*out`, padding included, or leave any of them).
- **The address.** A frame address is no SMT term: the walk checks that the
  machine's argument register holds exactly the paired slot and offset.
  Another slot or offset, or a private address where the source passes a
  value, is `X86BodyMismatch::CallStackAddress`; a value the walk does not
  track as a private address makes no claim.
- **Retention.** Once a slot escaped, a call's result, an incoming load's
  bytes and a call-defined slot byte may be an address derived from it, and
  so may anything computed from one; an incoming load or store through such
  an address is outside the domain (it could reach the slot behind the byte
  model). Every other incoming address existed before the slot's address
  left the function and stays disjoint from it (slice 4's premise).
- **`sret` callees.** A callee in `Function::sret_arg_callees` takes its
  buffer as argument 0; the selector places it in RDI (the first integer
  argument, as System V requires) and the call must have no result, so RAX
  is clobbered like any other caller-saved register (a caller that read the
  buffer address back from RAX would be named an undefined read; the
  selector never does).

What the real bridge emits was read from its LIR (`probe/x86_body_probe.rs`
over `fails-before/probe_callee.rs`, dumped with `dump-trust-ir`): an sret
call is `StackAddr` of a slot sized for the result, `Call [slot, args...]`
with no result and the callee in `sret_arg_callees`, then field loads
through `Copy`/`Iadd` chains (the selector: `lea v, [slot]; mov rdi, v; mov
rsi, x; call`, then `mov r, [v + 0]`); a `&mut local` is a store into a
slot, the slot's address as the argument, then a reload (the bridge gives
each borrow of the same local its own slot).

## Qualification (`fails-before/qualify.sh`)

`host_qualification_replays_the_slice_seven_body_theorems` on AY 0.27.0
build 10530 (`d14080122`, sha256 `9a149c35…`) with Clean 5f09e36c
(`~/clean-checker/bin/clean`, sha256 `949365b6…`): all 15 fixture theorems
are `Verified` through the real builder (fresh replays, 174 ms to 3391 ms
each), and AY refutes all 6 wrong lowerings with a counterexample (the
reload moved before the call, the stored value kept across the call, the
slot read before a later call, another field of the buffer, other contents
at the call, an `Option`'s tag read before the call). The recorded gap list
`KNOWN_UNCERTIFIED_SLICE_SEVEN` is empty.
`verifier_credits_every_bound_slice_seven_row_with_the_replayed_body_theorem`:
every covered row of every fixture is Formal under the body theorem, each
function is promotable and exports one payload per covered row, and each
refutation fails every covered row. The e2e proof-required AOT test
(`crates/trust-cg-codegen/tests/x86_source_bound_body.rs`, renamed
`slice_one_to_seven_functions_promote_with_replayed_body_theorems`) promotes
four slice-7 bodies (an external sret callee's buffer, a `&mut` and a `&`
out-parameter, an `Option<u64>` out-parameter with its tag branched on) on
x86_64-apple-darwin and x86_64-unknown-linux-gnu; `must_refuse_corpus`
passes.

## Controls and fails-before

The solver-free library gate row `x86_source_bound_body::tests::slice7::`
(22 tests; `fails-before/gate_row.sh` is the gate's exact command and
parser) passes: `pass: rc=0; 22 captured passes; 0 failed; 0 ignored; 0
runtime SKIPs; 4683 filtered; 1 suites; 0 incomplete suites`. Before this
branch the filter selected no test.

**Walk-rule mutants** (`fails-before/mutate.py`, `run_mutants.sh`; one build,
`TCG_S7_MUTANT` selects the rule; each disables one rule on BOTH sides, so a
correct fixture can still hold and only the control the rule exists for
notices): every mutant fails at least one control (payload `mutants.txt`).

| Mutant | Rule disabled | Failing tests (of 22) | Among them |
| --- | --- | ---: | --- |
| `no-redefine` | a call leaves the escaped bytes as they were | 13 | `the_old_contents_after_the_call_are_refuted`, `reading_the_slot_before_the_call_is_refuted`, `a_slot_value_kept_across_a_later_call_is_refuted` |
| `no-observe` | a call observes no escaped slot's contents | 8 | `different_slot_contents_at_the_call_are_refuted`, `a_cast_slot_address_passed_to_a_call_is_admitted` |
| `no-retention` | a call reads and redefines only the slots passed to it | 4 | `a_slot_value_kept_across_a_later_call_is_refuted` |
| `no-frame-check` | a machine argument may pass any private address | 1 | `a_wrong_slot_or_offset_argument_is_a_named_mismatch` |
| `no-taint` | an incoming access through an escape-derived address is admitted | 1 | `accesses_through_addresses_that_may_derive_from_an_escaped_slot_are_outside_the_domain` |

**The real bridge before and after** (`fails-before/probe_callee.rs`, built
by `probe_run.sh`): through the `main` `336a49f14` bridge
(`runs/main-336a.dylib`) every slice-7 probe function is refused — `sum3`,
`first3`, `mid`, `fwd3` and `branch_sret` with `requires no EH, stack
protector or sret callee metadata: has an sret-arg callee`, `out_param`,
`twice_param` and `read_ref` with `uses a private stack address as a value
(the slot's address escapes)`; through the slice-7 bridge all eight replay
Valid (payloads `probe_trace_main336a.txt`, `probe_trace_s7.txt`).

**One slice-3 test changed meaning, not strength.**
`calls_outside_the_slice_three_domain_are_unsupported` held "a slot address
passed to a callee" outside the domain; that use is slice 7's domain. Its
case now passes the address AND returns it (still outside, still asserted
Unsupported), and the passing form is asserted admitted, with a theorem
that holds, in `slice7::a_cast_slot_address_passed_to_a_call_is_admitted`.

**Optimized fixtures.** The real x86 optimizer's O1, O2 and O3 output of the
15 fixtures: 14 build a theorem that holds on samples at each level (frame
slot forwarding, CSE and copy propagation keep every reload after its call),
one (`SretBranch`, a `bt` row) makes no claim, none is a mismatch.

## Cross-backend matrices (`cross-backend/`)

- **Proof-required, LLVM callees** (`s7_credited_native.py`): a `dep` crate
  compiled by LLVM holds the callees (`make3` and `triple` return 24-byte
  values through a buffer, `pair_opt` an `Option<(u64, u64)>`, `mixed` a
  `(u64, u32, bool)`; `bump`, `peek`, `fill` take `&mut u64`, `&u64`, `&mut
  Option<u64>`), so every callee is an LLVM-compiled one; the `callee` crate
  holds the fourteen callers, built by LLVM or by trust-cg with proofs
  required containing exactly the functions a first traced compile credits;
  the bin by LLVM or trust-cg. At O0 all fourteen are credited
  (`replay=Valid`), the proof-required rlib promotes, and all four cells
  print the oracle's 1400 lines (payload `credited_O0.txt`). At O1 eleven, at
  O2 and O3 ten are credited (the rest make no claim: a `bt` row, a merged
  block), and the four cells agree at each level (`credited_O123.txt`).
- **`m145_xback.py --test cross-backend/s7_xback.rs`** (the repo's matrix
  tool on the same fourteen callers and their callees in one crate,
  `no-proof-certs`, each row folding 100 results to an exit code): 112 cells
  at O0 and O2, all equal to the LLVM oracle (`m145_O0_O2.txt`).

## Reproducers (in tree)

- `census/census_s7.sh`: the census command (`postpush_census.sh`'s, on the
  built bridge); `census/census_compare.py`: promoted / newly failing lists
  and the body-trace classes; `census/dump_core.sh`: the O0 trust-ir dump;
  `census/probe_fn.sh`, `census/typehint_check.py`: the type-hint
  diagnosis; `census/replay_dir.py`, `census/word_respell.py`,
  `census/size_rates.py`: the offline replays and the respelling
  experiment; `census/payloads.py`: the identities in
  [PAYLOADS.md](PAYLOADS.md).
- `probe/x86_body_probe.rs`: the LIR / machine / verdict probe and its
  `--census` mode.
- `fails-before/`: `qualify.sh` (the tool-gated tests on the stage-1
  toolchain), `gate_row.sh` (the gate row and its parser), `mutate.py` and
  `run_mutants.sh` (the walk-rule mutants), `probe_callee.rs` and
  `probe_run.sh` (the probe crate through either bridge).
- `cross-backend/`: `s7_credited_native.py` (proof-required, LLVM callees),
  `s7_xback.rs` (rows for `m145_xback.py`) and `oracle.py` (their LLVM
  exit codes).

## Open findings

1. **`main` did not build the bridge at this branch's base.** `65e3818dd`'s
   `crates/rustc-codegen-trust-cg` fails with `error[E0004]` (U10's two new
   `PipelineError` variants are unclassified in the bridge's exhaustive
   diagnostic map); `main` fixed it in `eaa5d9ca8`, cherry-picked here
   unchanged. The root workspace's checks never compile that crate.
2. **AY's strict certification is the slice's credit limit.** 151 of the
   334 newly bound bodies did not certify in the census (above), and the
   offline replays show the outcome is not a property of the query bytes
   alone (the smallest rejected query, `Formatter::debug_struct`, certified
   when replayed by itself), while 126 of 150 are rejected even one at a
   time. The respelling experiment rules out the call-defined bytes'
   spelling; by size they certify like the baseline's bodies. A larger AY
   budget or a fix of AY's strict self-check is the route, not a different
   encoding per function.
3. **Not covered by the theorem: the slot's size and alignment against the
   callee's pointee.** LIR states neither; the slot table's size and
   alignment are the adapter's, and the frame layout that honours them is
   TV-4/TV-5's subject, as for every slot. (The x86-64 frame layout aligns a
   fixed slot's offset relative to the 16-byte-aligned frame base, so it
   honours alignments up to 16; the bridge refuses an over-aligned local,
   `memory_slot_lane_ty`, so no fixed slot asks for more. A slot passed to a
   callee that relies on `align 32` would be the frame's defect, not this
   theorem's; none reaches it today.)
4. **A caller that read the `sret` buffer back from RAX** (which System V
   lets it do) would be named an undefined read: the model gives the call no
   result. The selector never does so today.
