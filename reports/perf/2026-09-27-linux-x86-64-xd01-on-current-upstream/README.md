# XD-01 re-measured on CURRENT upstream, Linux x86-64 (2026-09-27)

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

`frontier/xd01b` was built on `bae05a7c2`. Upstream advanced 308 commits past
that base, 47 of them in the five proof-path files this branch touches, and one
of those 47 — `8d4e83b54`, "withdraw: a registry name lookup and a sampled
discharge are not proof credit (E0.2, E0.5)" — changes what XD-01 measures.
This report replaces the numbers in
[`../2026-09-24-linux-x86-64-xd01/README.md`](../2026-09-24-linux-x86-64-xd01/README.md),
which stand as the record for their own revision and base and are NOT edited.

Host: `x86_64-unknown-linux-gnu`, 24 cores, 61 GiB. Root workspace built with
the pinned stock Rust 1.97.1 from `rust-toolchain.toml`; the project's own pin
overrides this machine's aterm Trust default toolchain. Every build and test ran
under the memory guard (`CARGO_BUILD_JOBS=3`, one of three flock slots,
`MemoryMax=16G`); other agents were building throughout.

Upstream baseline: `origin/main` at `0ebd84edc`, measured on THIS host in a
throwaway detached worktree, not taken from any earlier report. Merged tree:
`frontier/xd01b` after `merge origin/main`. Both suites: each floor target alone,
`--test-threads=1`.

Two further upstream tips arrived during the work and are merged on top
(`ba27f8da6` and its six, then `7ab5f81d1`). Both rounds are entirely inside
`crates/rustc-codegen-trust-cg/` — a separate workspace on the custom `trust`
toolchain — plus their reports and the generated `INVENTORY.md` /
`docs/diagnostics.md`. No root-workspace file, so the measurement below stands for
the branch tip: the eight floor targets and `trust-cg-codegen --lib` link nothing
those commits change. Upstream pushes about thirty times a day and the fetch is
shared between this host's worktrees, so whoever pushes should re-check the tip.

This is a regression and refusal measurement. It is not a proof claim, and it
does not establish compiler completion or release readiness.

## THE HEADLINE, stated first because it is not the earlier one

**XD-01's measured effect on proof promotion against current upstream is ZERO.**
The binding still computes, still refuses what it refused, and still refutes a
wrong selection — all of that is unchanged and asserted. What is gone is the
credit: upstream deleted the only lane by which a freshly reconstructed
obligation could be discharged `Formal` in this process, and XD-01's `Formal`
verdicts went with it.

The floor moves by exactly one test, and that one test is a stale-assertion
repair, not a binding credit.

## Floor: the eight targets, upstream vs merged

| target | upstream `0ebd84edc` | merged | retained 2026-09-24 record |
| --- | ---: | ---: | ---: |
| `jit_cert_cache_identity_x86_64` | 5p/0f | **5p/0f** | 3p/2f |
| `jit_sysv_x86_64_spill_replay` | 2p/2f | **2p/2f** | 2p/2f |
| `jit_validation_modes_x86_64` | 4p/3f | **5p/2f** | 7p/0f |
| `jit_x86_64_aggregate_abi_fail_closed` | 4p/33f | **4p/33f** | 4p/33f |
| `jit_x86_64_profile_modes` | 3p/5f | **3p/5f** | 5p/3f |
| `x86_64_constant_pool` | 1p/1f | **1p/1f** | 1p/1f |
| `x86_64_sysv_ay_abi` | 3p/1f | **3p/1f** | 3p/1f |
| `x86_64_target_features` | 47p/3f | **47p/3f** | 47p/3f |
| **total passing of 117** | **69** | **70** | 72 |

`floor-upstream/` and `floor-merged/` are the raw runs. `floor-merged-committed/`
and `lib/codegen-lib-merged-committed.log` are the SAME eight targets and the
same `--lib` suite re-run on the COMMITTED tree after the two controls were
repaired and the docs corrected, so the numbers above apply to what would be
pushed and not only to the intermediate state: per-test outcomes and the `--lib`
failing set are identical.

**The one difference is `x86_uncertified_execution_requires_unchecked_env_optin`,
and it is NOT an operand-binding credit.** It fails on upstream because the
refusal it demands moved: the module is deliberately built to leave a
`MovdqaRR` uncovered, and the gate that fires first now says
`emitted opcode inventory found 1 uncovered non-pseudo opcode(s)`, which matches
neither `UNCERTIFIED` nor `promotion`. This branch adds that third citation to
the test's ENUMERATION of accepted fail-closed refusals; a new and unexpected
reason still fails, and the `expect_err` is untouched. The test's own comment
records the measurement that the ordering holds with the ABI copies credited and
refused alike — so the repair is independent of any binding strength.

### The four tests XD-01 used to win and no longer does

Against the 2026-09-24 base these four passed; on the merged tree they fail:

* `jit_validation_modes_x86_64::x86_always_verify_never_serves_from_cache`
* `jit_validation_modes_x86_64::x86_cached_verified_certifies_every_published_function`
* `jit_x86_64_profile_modes::x86_64_host_jit_accepts_block_counts_profile_hooks`
* `jit_x86_64_profile_modes::x86_64_host_jit_accepts_call_counts_profile_hooks`

**None of the four is a regression this merge introduced.** All four fail on
pristine upstream, with a refusal string BYTE-IDENTICAL to the merged tree's.
For the block-counts one, both trees print:

```
non_verified proof entry opcode_inventory_instruction_0 in linear would publish a
JIT function without required evidence: emitted opcode inventory found 1 uncovered
non-pseudo opcode(s) across 1 distinct opcode(s) [x86_64::MovRR]; first in
linear[4] is x86_64::MovRR (no complete evidence: statistical sampling is not
proof credit: `RECONSTRUCTED x86_64 Copy_64 -> MovRR (real-operand)` found no
counterexample in 100000 sampled inputs)
```

The blocking row is an unbound `Copy_64 -> MovRR`, which XD-01 refuses ON
PURPOSE — it is the shape FIX 1 withdrew and the outgoing-ABI end the branch
declines to credit, because the destination register follows the callee's
declared types. On the 2026-09-24 base that row was a credited
`Verified { strength: Statistical }`, so it never blocked the inventory gate and
the function promoted on sampling. Upstream withdrew that credit. The row is now
`Unverified`, the gate refuses, and no binding this branch owns can reach it.

## Why the credit is gone, precisely

Upstream's `8d4e83b54` deleted `lowering_proof::try_formal_on_miss` and
`try_formal_on_miss_with`, the arm `discharge_registry_obligation` took on a
tier-0 MISS. That arm ran one live checked solve on the obligation in front of
it. XD-01 routed a BOUND reconstruction's instance obligation through exactly
that function, and that miss arm is where its `Formal` came from: a freshly
reconstructed `Copy_32 -> MovRR32` or `Iadd_64 -> AddRR` has no committed
portable DRAT certificate and no tier-0 row, so the two lanes upstream KEPT both
miss.

Upstream's reason for the deletion was measured and is not disputed here: on the
registry lane that route made 148 attempts with zero successes and re-solved the
same queries 40x/28x/17x. It was deleted with registry credit because it existed
to lift registry credit. The consequence for the bound lane is a side effect of
that deletion, not a judgement about the binding.

What survives is the correct shape of the answer: upstream kept a live checked
lane for obligations that ARE source-bound —
`verdict_db::live_frame_discharge_with_request` and
`live_bound_alu_discharge_with_request`, reached through
`FunctionDischargeContext::frame`/`alu`, and now gated on AY BINARY IDENTITY
(`ay_identity`, the SHA-256 of the admitted bytes). Neither is reachable from
`x86_64_function_verifier.rs`: both take a `SourceBoundFrame`/`SourceBoundAlu`,
which only the AArch64 `MachFunction` verifier constructs. So there is no
upstream x86-64 equivalent of the operand binding, and nothing was chosen
between — but there is also no lane left for it to feed.

**Giving the x86-64 bound reconstruction its own live checked lane is the work
this measurement identifies, and it is deliberately NOT done in this merge.** It
is a design act with soundness weight (which AY identity admits the verdict,
what per-key budget, what refusal on inconclusive), it must use upstream's
identity admission rather than the deleted `live_formal_solve_config`, and
inventing it inside a merge resolution would be granting a proof strength on the
strength of a merge rather than of evidence.

## What the binding still does, and how that is now asserted

The binder is alive on the merged tree and its answers are unchanged. 44 unit
tests in `x86_source_operand_binding` pass (`gates/binder-tests.log`), and the
two end-to-end controls in `x86_64_function_verifier` both hold
(`gates/x86-verifier-tests.log`).

Those two controls had to be REPAIRED, and the repair is a narrowing of what
they observe, not of what they require:

* they used to read the schema off the published certificate's
  `[source-bound: …]` token, which appears only on a CREDITED row. With no lane
  to credit a bound reconstruction, the certificate can no longer witness the
  binding at all.
* both now assert AT THE BINDER, over the same four inputs the verifier pre-pass
  hands it — the emitted instruction, its TV-1 stamp, the replayed source
  instruction at that stamp, and the operand correspondences ISel recorded.
  `x86_faithful_copy_earns_the_result_defining_copy_schema` asserts
  `Some(ResultDefiningCopy)`; `x86_mov_stamped_from_an_isub_earns_no_source_binding`
  now asserts `None` there as well as the absent certificate token, so it can no
  longer pass vacuously through a harness that never reaches the binder.
* the positive control ALSO pins the row's uncredited status on this host, the
  way upstream's own E0.2 tests pin their refusals: the day a lane credits a
  bound reconstruction, that assertion fails and is re-examined rather than
  quietly changing meaning.

`reconstruction_x86` is 142 passed / 0 failed on BOTH trees
(`gates/reconstruction-x86.log`, `gates/reconstruction-x86-upstream.log`), so the
reconstruction teeth — a wrong ISel opcode or wrong operand wiring REFUTES — are
intact.

## The per-class solver-evidence table cannot be reproduced, and why

The 2026-09-24 table (241 `binary-alu` rows bound, 112 `fp-binary`, 74
`scalar-load-at-bound-address`, and so on) was produced with
`TCG_TRACE_STATISTICAL=1`. **Upstream's `8d4e83b54` deleted that diagnostic**, in
both `proof_certificates_from_x86_64_report` and its sibling: it existed to print
the statistically-CREDITED rows, and after the withdrawal there are none. Running
the eight targets on the merged tree with `TCG_TRACE_STATISTICAL=1` and
`TCG_SOLVE_TRACE=1`, in both the normal and the forced-fallback configuration,
yields ZERO `TCG_STATISTICAL` lines and ZERO `TCG_SOLVE_TRACE` lines
(`diagnostic-gone/`). No `[source-bound: …]` token is published anywhere, which
is the same fact as the headline: nothing is credited.

So the earlier table is retained as the record for its own revision and is not
restated as current. Re-establishing an equivalent census on this tree needs a
diagnostic that reports BOUND rows rather than credited ones, which does not
exist yet.

## Suites, upstream vs merged

| suite | upstream `0ebd84edc` | merged |
| --- | ---: | ---: |
| `cargo test -p trust-cg-codegen --lib` | 4291 passed / 20 failed | **4291 / 20** |
| `cargo test -p trust-cg-verify --lib` | 4366 passed / 18 failed | **4413 / 17** |
| `cargo test -p trust-cg-verify --test reconstruction_x86` | 142 / 0 | **142 / 0** |

`trust-cg-codegen --lib`: the failing SET is byte-identical, 20 tests, mostly the
`compile_service::` install-gate class plus the two long-known
`test_aarch64_parallel_and_serial_multi_function_byte_identical` and
`compile_service_refuses_variadic_definition_with_shared_diagnostic`. Upstream's
own stronger assertions hold under the binding with no environment forcing:
`x86_verifying_jit_certification_rejects_sampled_function_on_any_host`,
`merged_object_promotion_rejects_uncredited_evidence` and
`step0_merged_two_function_module_compiles_to_one_object` all pass, which is why
`compiler.rs` and `module_merge.rs` resolved to upstream verbatim.

`trust-cg-verify --lib`: +47 passing and the merged failing set is a strict
SUBSET of upstream's. The one difference is
`ay_bridge::subprocess_tests::resident_io_waiter_is_refused_only_when_the_holder_overruns_its_own_budget`,
a timing-budget test in the load-flaky solver group; it failed on the upstream
run and passed on the merged one on a differently loaded host, and nothing in
this branch touches `ay_bridge.rs`.
`x86_64_function_verifier::reconstruction_teeth_audit::report_which_credited_opcodes_have_no_address_teeth`
fails on BOTH trees with the identical assertion (`left: 51, right: 37`) over the
identical toothless set — pre-existing upstream, unaffected here.

## Gates

| gate | result |
| --- | ---: |
| `scripts/check_fmt.sh` | OK |
| `python3 scripts/check_documentation.py --check` | current |
| `x86_source_operand_binding` unit tests | 44 passed, 0 failed |
| `x86_64_function_verifier` tests | 55 passed, 1 failed (pre-existing upstream) |
| `reconstruction_x86` | 142 passed, 0 failed |
