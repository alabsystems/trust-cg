# XD-01 on Linux x86-64: route B, landed with the three blocking fixes (2026-09-24)

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Two rival implementations of XD-01 — making x86-64 JIT proof promotion succeed on
a formal-capable host — were built independently and judged by a third agent that
re-measured both. Route B (`frontier/xd01b`) won every measured axis, but the
judgement was that **neither route was honest as it stood**: in both, the whole
measured win was carried by the one class whose `Formal` credit it had not
earned — the register COPY family, whose three schemas granted `Formal` without
ever checking the replayed source OPERATION.

This round lands route B plus the three blocking fixes, and then the one step the
judgement listed as optional. **The fixes REDUCE the number of passing tests**,
because they refuse the schemas that produced most of route B's win. That reduced
number is recorded here as the answer; the count was not recovered by loosening
anything.

Host: `x86_64-unknown-linux-gnu`, 24 cores, 61 GiB, GCC 15.2.0. Root workspace
built with the pinned stock Rust 1.97.1 (`rust-toolchain.toml`; the project's own
pin overrides this machine's Trust default toolchain). Every build and test ran
under the memory guard (`CARGO_BUILD_JOBS=3`, one of three flock slots,
`MemoryMax=16G`); other agents were building throughout, and the verify crate's
solver tests are load-flaky on a loaded host.

This is a regression and refusal measurement. It is not a proof claim, and it
does not establish compiler completion or release readiness.

## What the three fixes were

**FIX 1 — `bind_copy` checked no source operation at all.** Every other family in
`x86_source_operand_binding` checks the replayed opcode by EQUALITY before
consulting the emission, because the reconstruction reads its source operation off
the EMITTED opcode and a wrong selection would otherwise self-attest. The three
copy schemas skipped that and bound OPERANDS only, and TV-2 cannot cover for them:
`x86_emitted_op_class` answers `None` for `CopyGpr`/`CopyXmm`, so a move passes the
op-class cross-check beside any source instruction whatever. Measured, not
supposed — a `MovRR32` stamped from an `Isub`, with the `Isub`'s own recorded
operands, published:

```
RECONSTRUCTED x86_64 Copy_32 -> MovRR32 (real-operand) [source-bound: result-defining-copy]
```

Route A's dispatch discipline is ported: source opcode first, arity against the
opcode's own shape, and a per-source-opcode permitted-form table that also fixes
the width. `ResultDefiningCopy` now requires a replayed `Opcode::Copy` of arity
1/1 with both ends bound and distinct; `BoundSourceOperandCopy` and
`BoundResultOperandCopy` return `None`.

**FIX 2 — the normative list, corrected.** The module's "ALL of" list claimed
source-operation equality for every family while the copy family had none, and the
per-family section credited "TV-2's op-class check that a copy can implement the
claimed source at all" — vacuous for the one family whose entire credit rested on
it. `docs/linux-x86-64-completion.md` is reconciled: the paragraph added in
`91a45385f` was written before the memory/GEP schemas existed and stated the
general case as the whole case, while the table added in `1da93ca7e` recorded the
disp-0 subset binding.

**FIX 3** — (a) the deep-override cert-cache test gains the
`formal_authority_available()` early return its four siblings have, and its
assertion goes back to fail-closed; (b) the `BinaryAluImmediate` schema is
dropped — it compared the emitted `Imm` against the immediate SELECTION ITSELF
recorded, which cannot disagree with it; (c) the operand table stores
`Option<u32>` bits instead of a deep-cloned `Type`.

## Files

* `floor-route-b-prefix/` — the eight floor targets on route B as judged
  (`1da93ca7e`), before the fixes.
* `floor-postfix/` — the same eight after the fixes and the return-ABI binder.
* `lib/` — `cargo test -p trust-cg-codegen --lib` before and after.
* `gates/` — the named gates that must keep passing, and the binder unit tests.
* `solver-evidence/` — the observed `[source-bound: …]` schemas and solver answers.

## The step the judgement listed as optional, and why it is landed

With the three fixes alone the floor drops from 74 passing to **63** — the whole
+11 was the unearned copy credit, and 18 `trust-cg-codegen --lib` tests went with
it (`floor-fixes-only/`, `lib/codegen-lib-fixes-only.log`). That is the honest
number for "route B with the copy credit withdrawn and nothing put back", and it
is retained rather than hidden.

The judgement also named the right next step: bind the RETURN ABI end from the
replayed signature using the convention logic in
`derived_formal_argument_register`, and leave the outgoing-ARGUMENT half refused.
That is landed here as `X86OperandBindingSchema::ReturnAbiRegisterCopy`:
`X86ReturnAbiBindings` records which return index each return move materializes,
and `derived_scalar_return_register` re-derives the result register from the
DECLARED `returns` and the shared `trust_cg_ir::x86_64_regs` return file, refusing
anything that is not a single scalar register slot. It buys a refutation the
`X == X` obligation never could: **the right value moved into the wrong result
register is refused.**

An outgoing CALL ARGUMENT and a CALL RESULT stay refused, because their registers
follow the CALLEE's declared parameter and return types, which this function's
replayed signature does not contain. **That refusal is visible in the
measurement**, not just asserted: the three floor tests route B passes and this
round does not are exactly
`call_placeholder_binds_raw_target_name_even_at_the_same_host_address`,
`recovered_exact_and_ordinary_direct_calls_do_not_share_a_caller_verdict` and
`x86_64_host_jit_block_counts_preserve_late_call_fixup` — all three about a CALL.

## The honest delta, per target

Measured against the RETAINED origin-era round-3 floor at
`../2026-09-22-linux-x86-64-upstream-round3/floor/`, as instructed, not against a
"before" run of this branch. Route A's report was falsified for exactly that
reason.

| target | retained baseline | route B as judged | + 3 fixes | **landed** |
| --- | ---: | ---: | ---: | ---: |
| `jit_cert_cache_identity_x86_64` | 1p/4f | 4p/1f | 1p/4f | **3p/2f** |
| `jit_sysv_x86_64_spill_replay` | 2p/2f | 2p/2f | 2p/2f | **2p/2f** |
| `jit_validation_modes_x86_64` | 2p/5f | 7p/0f | 2p/5f | **7p/0f** |
| `jit_x86_64_aggregate_abi_fail_closed` | 4p/33f | 4p/33f | 4p/33f | **4p/33f** |
| `jit_x86_64_profile_modes` | 3p/5f | 6p/2f | 3p/5f | **5p/3f** |
| `x86_64_constant_pool` | 1p/1f | 1p/1f | 1p/1f | **1p/1f** |
| `x86_64_sysv_ay_abi` | 3p/1f | 3p/1f | 3p/1f | **3p/1f** |
| `x86_64_target_features` | 49p/1f | 47p/3f | 47p/3f | **47p/3f** |
| **total passing** | **65** | **74** | **63** | **72** |

`cargo test -p trust-cg-codegen --lib`: **4164 passed, 2 failed** — the two known
pre-existing AArch64-shaped failures
(`test_aarch64_parallel_and_serial_multi_function_byte_identical`,
`compile_service_refuses_variadic_definition_with_shared_diagnostic`). Identical
to route B; the 18 extra failures the three fixes caused are all recovered by the
return-ABI binder.

### The one caveat that makes a naive +7 wrong

`x86_64_target_features` reads 47p/3f here and 49p/1f in the retained baseline,
and **none of that 2-test difference is XD-01's**. The two extra failures are
`Select scalar condition must be Bool, got Vector(Bool, 2)` and a closed-vector
diagnostic string — vector-shape lowering, in a file and a code region no commit
in this work touches. The retained baseline was measured on merge `d4ceec6b4`,
which is **not an ancestor of this branch's base** (`bae05a7c2`); the two
lineages differ by 461 commits, so a per-target delta against it mixes XD-01's
effect with that lineage difference.

Excluding `x86_64_target_features`, the landed delta is **+9** (16 -> 25
passing). Overall it is **+7** (65 -> 72): +9 earned, -2 inherited. The same
arithmetic reconciles the judgement's "+11" for route B, which is route B's
excluding-`target_features` figure (16 -> 27); route B's overall figure against
the retained baseline is **+9** (65 -> 74), and the 2-test gap between the two
numbers is this same inherited vector-shape regression. Route B is 2 ahead of the
landed tree, both for the CALL reason above.

`x86_uncertified_execution_requires_unchecked_env_optin` carries a related
correction: commit `91a45385f` widened its accepted citations and attributed the
widening to the copies being discharged. MEASURED here, that attribution was
wrong — the opcode inventory refuses that module first with the copies credited
and refused alike, so the third citation is earned independently and the comment
now says so.

## Per-class solver evidence OBSERVED on this host

`TCG_TRACE_STATISTICAL=1` prints one residual row per sampled instruction and a
bound row's certificate carries `[source-bound: <schema>]`. Running each target
twice — once normally, once with `TCG_REFINE_SOLVER=0 TCG_NO_VERDICT_DB=1` so
every bound obligation takes its documented fallback — separates "the binding did
not fire" from "the binding fired and the solver declined".
`solver-evidence/*.nosolver.log` is the forced run, `*.trace.log` the normal one.

| schema | rows BOUND over the 8 targets | still statistical with the solver on | observed verdict |
| --- | ---: | ---: | --- |
| `binary-alu` | 241 | 0 | reaches `Formal` |
| `fp-binary` | 112 | 112 | **solver declines** |
| `scalar-load-at-bound-address` | 74 | 74 | **solver declines** |
| `return-abi-register-copy` | 49 | 0 | reaches `Formal` |
| `formal-argument-register-copy` | 43 | 0 | reaches `Formal` |
| `field-address` | 22 | 0 | reaches `Formal` |
| `scalar-store-at-bound-address` | 16 | 0 | reaches `Formal` |
| `element-address` | 2 | 0 | reaches `Formal` |
| `result-defining-copy` | **0** | — | **no observed answer** |
| `unary-alu` | **0** | — | **no observed answer** |
| `extend` | **0** | — | **no observed answer** |

The solver's own words, from `TCG_SOLVE_TRACE=1`:
`Unknown("(:reason-unknown (incomplete self-check-rejected))")` (11),
`Unknown("(:reason-unknown (incomplete proof-trusted))")` (2), and
`Unknown("incomplete AY proof certificate: …")`. `live_formal_outcome` maps
`Unknown` to nothing, so those rows fall back to sampling. That is the gate
working.

**The three zero rows are stated rather than glossed.** `result-defining-copy` is
the ONE copy schema that survived FIX 1, and it binds on **zero** rows across all
eight targets: it has no observed solver answer on this host and this report
claims none for it. Every copy credit these targets earn comes from the two ABI
binders. `unary-alu` and `extend` likewise bind nothing here — an `i8 -> i32` zext
carries an 8-bit verifier input and is genuinely `Exhaustive`, so it never needed
a binding to be promotable.

Two rows CORRECT the table committed in `1da93ca7e`: bound scalar STORES do reach
`Formal` (it said the solver limited stores too), and its single
"register copies" row hid which of three schemas was working (it was the ABI
binders, never `result-defining-copy`).

## What is unchanged, with counts

| gate | result |
| --- | ---: |
| `trust-cg-verify` binder unit tests + the two e2e copy controls | 46 passed, 0 failed |
| `reconstruction_x86` | 142 passed, 0 failed |
| `x86_encoding_gate` | 22 passed, 0 failed |
| `coverage_gate_tests` (classification) | 51 passed, 0 failed |
| `proof_evidence::` honesty tests | 18 passed, 0 failed |
| `verdict_db::` route-live pins | 31 passed, 0 failed |
| pinned promotion-gate tests in `compiler.rs` | 3 passed, 0 failed |
| `trust-cg-lower --lib` | 1906 passed, 0 failed |

`reconstructed_identity_cannot_formally_self_attest_wrong_source_opcode` passes.
`udiv_portable_theorem_cannot_formally_self_attest_sdiv_source` FAILS, alone and
in company, on `portable_cert_verified_obligation` — the committed portable
certificate's replay needs an authorized checker identity this host does not
supply, and the same run's solver trace shows
`incomplete AY proof certificate` / `self-check-rejected`. It is **confirmed
pre-existing**: `../2026-09-21-linux-x86-64-integrated/README.md` records it
failing in the retained 2026-09-20 `lib-synthesis` shard, and neither route B nor
this round changes anything in `canary_cert.rs` or `verdict_db.rs` beyond doc
comments. `gates/udiv-alone.log`.

## Route A: what was taken and what was not

Per the judgement, `frontier/xd01a` is NOT merged. Its
`x86_source_bound_inst.rs` module and tests, its hard-coded `degenerate: false`,
and its `step0_merged_two_function_module_compiles_to_one_object` rewrite are all
absent here. What was taken, **by hand and as a discipline rather than as code**,
is its source-opcode-first dispatch: `bind_class`'s ordering, its per-source-opcode
permitted-form table, and its `Copy` arity check.

Route A's `ay_bridge.rs` `prepare_source_bound`/`verify_fresh_source_bound`
deduplication was judged a genuine orthogonal improvement, but it is entangled
with an unsound arm. **It is not extracted here** — this round touches no
`ay_bridge.rs`. Re-extracting it as its own clean commit remains open.
