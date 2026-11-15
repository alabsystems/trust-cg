# Linux x86-64, round 5 (2026-09-28): the split cascade, a ratcheted Clean row, and three host inputs that were forging results

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Host: `x86_64-unknown-linux-gnu`, Ryzen 9 9900X3D, 24 cores, 61 GiB, kernel
7.0.0-34-generic. Root workspace built with the pinned stock Rust 1.97.1
(`rust-toolchain.toml`); bridge built with the tree-built stage2 `trustc`
(`$HOME/trust/build/x86_64-unknown-linux-gnu/stage2/bin/trustc`).

This is a regression, refusal and host-qualification measurement in the explicit
unverified frontend lane. It is not a proof claim, and it does not establish
compiler completion or release readiness.

## What landed

| Commit | What it changed |
| --- | --- |
| `a03876ecf` | the greedy split-generation bound (`split_depth_cap`, LLVM's RS_Split2 rule), plus two merges of upstream (271 commits) |
| `bb712d228` | `clean_fixture_host_lowering` promoted to a ratcheted floor row, 68 -> 69 targets |

### The bound

`GreedyAllocator::apply_split` re-enqueued BOTH halves of a split at
`Stage::New`, so a split PRODUCT was itself eligible for unbounded splitting.
`build_env` in `clean_lazy_delta.gate.trust.tir` performed 159 813 splits,
spilled 157 852 of the 160 589 resulting pieces, and cost 331s of a 343s module
compile. Bounded to generation 1: seven Clean fixtures 125x-1117x faster, machine
code **9.2x-11.1x SMALLER** on every one, and the whole
`clean_fixture_host_lowering` target 1844s -> ~54s.

The deterministic number is the code size; the wall-clock ratios sit at the top
of this host's variance envelope and should be read as "two to three orders of
magnitude", not as four significant figures.

### A false claim this round retracted

The bound's first commit message asserted the bound was a measured NO-OP outside
the Clean corpus. **That was false, and its measurement was broken**: the A/B loop
exported `TCG_RA_SPLIT_UNBOUNDED=` (empty) on the bounded side while
`split_depth_cap` tested `var_os(..).is_some()`, so both arms ran the UNBOUNDED
path and agreed by construction. Re-run with the variable genuinely unset, across
every `e2e_x86_64_*` suite in the crate (34 suites, 489 greedy allocations, 57 of
which split), three suites and eight distinct functions differ — and every one
differs in the bound's favour:

| suite | function | bounded (insts/spills/splits) | unbounded |
| --- | --- | ---: | ---: |
| callee_saved | `tcg_cs_stress` | 17 / 1 / 1 | 20 / 2 / 4 |
| callee_saved | `tcg_cs_two_exit` | 27 / 2 / 1 | 32 / 2 / 6 |
| callee_saved | `tcg_cs_two_exit` | 33 / 1 / 1 | 36 / 2 / 4 |
| fp_across_call | `_f32_across_call` | 26 / 1 / 1 | 28 / 2 / 3 |
| fp_across_call | `_fp_one_call` | 26 / 1 / 1 | 28 / 2 / 3 |
| fp_across_call | `_fp_int_io` | 30 / 2 / 1 | 36 / 4 / 7 |
| fp_across_call | `_fp_two_calls` | 30 / 2 / 1 | 36 / 4 / 7 |
| triple_oracle | `_deep_select_chain` | **77 / 6 / 4** | **117 / 26 / 44** |

Retained as `split-ab-bounded.txt` / `split-ab-unbounded.txt`. All three suites
pass in BOTH modes (9/9, 4/4, 9/9), one of them a cross-backend oracle, so this is
a code-quality difference and not a correctness one. The empty-value footgun is
fixed behind a pure `unbounded_override_is_set` with a regression test that names
this defect. Wall-clock EXECUTION of the changed bodies is still unmeasured.

## Linux x86-64 regression floor

`scripts/check_linux_x86_64.py --trust-driver <stage2>/bin/trustc --require-clean`,
run twice: once on `bb712d228` and again on `b26d09b79` after the objdump format
gate landed.

| Measurement | Targets | Pass | Fail |
| --- | ---: | ---: | ---: |
| 2026-09-28, `bb712d228`, correct host toolchain | 69 | 55 | 14 |
| 2026-09-28, `b26d09b79`, after the objdump format gate | **69** | **56** | **13** |

The retained `floor-report.json` and `floor-run.log` are the SECOND run, on
`b26d09b79`.

`clean_fixture_host_lowering` passes as a row: 5 of 5 tests, 62.7s, all 38
fixtures deciding at O0 AND O1 with refusal class map `{}`. It had been held out
because its wall clock was unbounded and its undecided set DRIFTED between runs;
that had one cause, the split cascade, and with the cascade bounded the target
measures 54.28s / 54.47s / 54.28s over three consecutive debug runs — a 0.4%
spread, ~390 MiB peak RSS, 34x under the runner's default timeout.

### The failures, and why they are nearly all one thing

* **XD-01, the credit withdrawal (12).** `e2e_x86_64_dispatcher`,
  `e2e_x86_64_module_batch_fnptr`, `e2e_x86_64_module_batch_globals`,
  `jit_integration_x86_64`, `jit_sysv_x86_64_spill_replay`,
  `jit_validation_modes_x86_64`, `jit_x86_64_aggregate_abi_fail_closed`,
  `jit_x86_64_profile_modes`, `x86_64_constant_pool`, `x86_64_sysv_ay_abi`,
  `x86_64_target_features` and `rustc-codegen-trust-cg/m143_x86_vectorize_trace`.
  An earlier revision of this report listed m143 separately as a
  `[TCG-MIR-UNSUPPORTED]` capability gap. That was wrong: its log carries 18
  `TCG-PROOF-465` and 16 "statistical sampling is not proof credit", and
  `TCG-MIR-UNSUPPORTED` is the AGGREGATE those roll up into — the bridge refuses
  the module because its required functions could not be promoted, not because
  their MIR is a shape the backend cannot lower. Same blocker as the other
  eleven.
* **`guard_kernel_gate_x86_linkrun` (1).** Explicitly SKIPs an AArch64 macOS
  mirror leg, which a Linux x86-64 host cannot supply. Structurally unavailable
  here rather than a defect, so it is a candidate for `DECIDED_ABSENT` under a
  named decision id — but adding a row there REDUCES what the floor requires, so
  it was not taken here. Ruled 2026-10-02 (OD-46 in the
  decision record): the row stays required.
* **`e2e_x86_64_callee_saved` — FIXED.** It failed on an explicit transcript SKIP
  (a vacuous pass the runner correctly refused) because the disassembler probe was
  gated on the objdump VENDOR. It is now gated on the object FORMAT, asked of
  binutils via `objdump --info`, and the row passes with the (E2)
  INDEPENDENT-DECODE controls actually running.

So twelve of the thirteen remaining failures are the single blocker described
below, and the thirteenth is a cross-host mirror.

## Three host inputs that were forging results

None of these is a compiler defect, and each presented as one. All three come from
this machine's PATH and umask.

1. **`cc` is `zig cc`.** `~/.local/bin/cc` -> `ay-zig-cc` -> `zig cc` (reporting
   as clang 21.1.0), and `~/.local/bin` precedes `/usr/bin`. That single fact
   produced three unrelated-looking failures:
   * the bundled DRAT checker built as
     `5dbbe753…` (134 624 B) instead of the manifest-qualified
     `6bd14b38…` (55 424 B, GCC), so every portable certificate declined
     fail-closed and `clean_fixture_host_lowering` reported **12 of 38** lowered
     with 26 `UNRECORDED CLASS` refusals instead of 38/38, plus a failing
     `guard_carrier_canary_memo_end_to_end_rejects_drifted_condition`;
   * `e2e_x86_64_differential` (`i128_shl`, `i128_ashr`), `e2e_x86_64_i128_div`
     and `e2e_x86_64_mixed_width_shift` failed with BOTH binaries at exit 134 —
     zig cc traps the shift UB the C reference relies on. With GCC: 17/17, 4/4,
     7/7;
   * the bridge dylib could not link at all: `error: unsupported linker arg:
     --exclude-libs`.

   `CC=/usr/bin/gcc` alone is NOT enough — it fixes the checker while the LINKER
   still comes from PATH `cc`, which is how the bridge lane still failed after
   `CC` was set. `PATH=/usr/bin:$PATH CC=/usr/bin/gcc` fixes all three and
   reproduces the qualified checker hash exactly. The vendored `drat-trim.c` is
   unchanged at `d834b649…`, so this is C-toolchain identity, not tampering.
   `docs/portable-checker-host-qualification.md` recorded this condition and its
   remedy on 2026-09-27; this report adds no documentation because that section is
   already correct.

2. **AY never started, because of a directory mode.** `~/.cache/trust-cg` was
   0775 (this host's umask is 0002) and trust-cg "creates each cache directory
   0700 whatever the umask, but never changes one that already exists". So AY was
   ADMITTED and then not materialized:
   `[TCG-AY-IDENTITY-UNMATERIALIZED] ... has mode 0775: others may rename entries
   in it, so no AY is started beneath it`. `chmod -R go-w ~/.cache/trust-cg
   ~/.cache/trust-cg-cegis` fixes it, and `no AY is admitted in this process`
   disappears. It changed NO test outcome — see the blocker — but it removes a
   real one.

3. **A GNU-only `objdump`** turned every (E2) independent decode into a skip,
   because the probe asked the objdump's VENDOR rather than whether it can read the
   format in hand. FIXED in `b26d09b79`: the probe now takes an `ObjFormat` and
   asks binutils itself through `objdump --info`, which on this host lists
   `elf64-x86-64` and `pe-x86-64` and NO Mach-O. `e2e_x86_64_callee_saved` goes
   from a floor FAIL on a vacuous pass to 10 of 10 with zero skips and 29
   `[E2 ...]` decode lines across both of its formats. Unlike the other two this
   one was a trust-cg defect, not a host input — it is listed here because the same
   host property exposed it.

## The blocker for the performance clause, stated precisely

There is **no x86-64 Linux row in `ratchet/ledger.jsonl`**. Its 7 `x86_64` rows
are all a MacBookPro (newest 2026-08-20, `runtime_geomean_vs_llvm_o3` 1.302) and
the newest row overall is aarch64 (2026-08-30, 0.871). `benchmarks/beat-llvm`
cannot produce one on this host in the default lane, and the reason is not the
harness and not the host:

Since `8d4e83b54` (2026-09-17, "withdraw: a registry name lookup and a sampled
discharge are not proof credit"), `STATISTICAL_EVIDENCE_IS_NOT_CREDIT` and
`REGISTRY_NAME_LOOKUP_IS_NOT_CREDIT` are unconditional constants — there is no
policy switch. The x86 lowering has no operand-exact evidence for its most basic
opcodes, so a bridge compile of a trivial program fails closed:

```
[TCG-PROOF-465] proof promotion rejected for target X86_64: ... in
_RINvNtCsk5fCgHVYj7v_3std2rt10lang_startuE...: emitted opcode inventory found 16
uncovered non-pseudo opcode(s) across 5 distinct opcode(s)
[x86_64::MovRR, x86_64::MovRR32, x86_64::Lea, x86_64::MovMR, x86_64::LeaRip];
first ... is x86_64::MovRR (no complete evidence: statistical sampling is not
proof credit: `RECONSTRUCTED x86_64 Copy_64 -> MovRR (real-operand)` found no
counterexample in 100000 sampled inputs)
error: [TCG-MIR-UNSUPPORTED] cannot compile required function with unsupported MIR
```

Measured after the AY fix, so this is not solver availability: the obligations are
not merely undischarged, they are not BUILT. `x86_64_constant_pool` and
`jit_sysv_x86_64_spill_replay` are unchanged by it. A `--bridge-cg-arg` knob would
put the run in a "diagnostic lane" that `benchmarks/beat-llvm/contract` does not
accept as evidence, so it is not a route to a ledger row.

### Why "routed to AY" is not the fix, and what is

The operand-exact route already EXISTS and is already wired.
`x86_source_operand_binding.rs` (TV-1 EXTENDED) builds the
`ExactSourceOperandBinding` witness, and
`discharge_reconstructed_obligation_with_exact_source_binding` is called from
`x86_64_function_verifier.rs:6922`. It reaches `Formal` through exactly two lanes,
both of which REPLAY A COMMITTED ARTIFACT against this obligation's content: an
exact portable DRAT certificate (`verdict_db::portable_cert_verified_obligation`)
or a tier-0 candidate revalidated by a live checked solver
(`verdict_db::tier0_lookup_obligation`). Its own comment states the rule that
makes a live solve useless here: it "spends no solve on a miss". So making AY
available does not and cannot grant credit for an obligation that has no committed
artifact — measured, not assumed: `x86_64_constant_pool` and
`jit_sysv_x86_64_spill_replay` are unchanged after the AY fix.

The committed artifacts do not cover these opcodes. `verdict_db/tier0.vdb`'s seeds
are five program-independent canaries (the popcnt SWAR width-32 canary and four
guard-carrier expansion canaries at widths 32/64), and while
`regen_verdict_db` DOES enumerate "the x86 + aarch64 CANONICAL (parametric)
reconstruction obligations" (verdict_db.rs:1116), tier-0 holds the CANONICAL form
while the lookup routes the INSTANCE — the discharge deliberately refuses to
credit an instance from a parametric generalization, because "crediting the
instance from a free-immediate generalization would need a substitution argument
the binding does not supply".

And minting them cannot be done from this workspace as configured. AY admission
records the SHA-256 of `<sysroot>/bin/ay` for the compiler that BUILT the crate,
and admits a candidate only when its bytes equal that digest, with "none falls
back". The root workspace is built with stock Rust 1.97.1 per
`rust-toolchain.toml`, whose sysroot ships no `ay`, so every root-workspace tool
reports `[TCG-AY-IDENTITY-UNRECORDED]` and `AY_SOLVER_PATH` cannot help — there is
no recorded digest for an override to match. Verified: `regen_verdict_db` refuses
for exactly that reason, with and without `AY_SOLVER_PATH` set to a byte copy.
The bridge is different only because the process IS a `trustc` driver, so the
"toolchain HOSTING this process" route applies and AY is admitted there
(`toolchain-pinned-ay`).

**So the critical path, shared by the proof clause and the performance clause,
is:** build `trust-cg-verify` with a Trust toolchain that ships `bin/ay` so an AY
identity is recorded, mint instance-keyed evidence (tier-0 rows or portable DRAT
certificates) for the opcodes a minimal binary needs — `MovRR`, `MovRR32`, `Lea`,
`LeaRip`, `MovRM`, `MovMR`, `Movzx` — and commit it as the proof-authority change
it is. That unblocks the 11 XD-01 floor targets and the first x86-64 Linux
performance measurement together. Step one crossed the boundary
`rust-toolchain.toml` drew; since the owner directive of 2026-09-28 the root
pins `channel = "trust"`, so that boundary is gone.

## What this does not measure

No `library/core` census this round, no runtime or RSS number for any target, no
Trust-verified compilation of trust-cg itself, and no execution measurement of the
eight functions whose code the split bound changed.
