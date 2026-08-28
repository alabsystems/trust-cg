# Local soundness gate

`scripts/soundness_check.sh` aggregates trust-cg tests with checks from sibling
Clean and AY repositories. It is a local evidence gate: it helps reproduce a
particular cross-repository validation state, but it is not hosted CI and it is
not an end-to-end proof of the compiler.

The script fails closed when a configured check is missing, vacuous, errors, or
returns a nonzero status. Known RED opcode-evidence rows are pinned data inside
the passing coverage inventory; an unknown/unclassified RED row fails that test.

## Run it

From the trust-cg repository root:

```sh
export PATH="$HOME/.cargo/bin:$PATH"
scripts/soundness_check.sh
```

Exit status `0` means every configured gate passed. Status `1` means at least
one gate failed or could not run; status `2` reports invalid command-line use.

Useful modes:

```sh
scripts/soundness_check.sh --list    # print the configured gates
scripts/soundness_check.sh --pinned  # require live HEADs to match the lock
scripts/soundness_check.sh --help
```

By default the script derives the trust-cg root from its own location and uses
`$HOME/clean` and `$HOME/ay`. Override them when using isolated worktrees:

```sh
CLEAN_DIR=/path/to/clean AY_DIR=/path/to/ay scripts/soundness_check.sh
```

The root workspace pins Rust 1.97.1 in `rust-toolchain.toml`. The gate verifies
that version and rebuilds `$CLEAN_DIR/target/release/clean` from the selected
Clean checkout with its locked dependencies before checking proof files.
Each Cargo test, Clean build/check, and Lake build runs in a separate process
group with a 7,200-second default limit. Set the positive
`SOUNDNESS_COMMAND_TIMEOUT_SECONDS` environment variable to use another
per-command bound. Timeout or interruption fails the gate and terminates the
whole process group, including descendants that remain in that group.

## Configured checks

The trust-cg portion runs these `trust-cg-verify` integration-test targets:

| Target | Evidence checked |
| --- | --- |
| `soundness_manifest` | Every registered fail-closed invariant has a live enforcing test, including all nine differential bridge IDs. |
| `coverage_gate_tests` | Accepted/deferred opcode inventory: AArch64 156/248 with 92 explicitly deferred RED rows; x86-64 167/196 with 29; RISC-V 14/17 with 3; and WebAssembly 111/113 with 2 — the two INTEGER scalar-constant rows closed when an INDEPENDENT spec-derived signed-LEB decoder replaced the self-equality that had made them uncreditable, and `f32.const` (0x43) / `f64.const` (0x44) entered the mirror as the two named RED rows, because their immediates are raw IEEE-754 payloads rather than LEB128 and that decoder does not reach them. A high ratio on THIS gate is not a claim that the wasm lane is verified: the P3 value-domain gate still carries its 4 named deferrals, relooper bisimulation is deferred, and host-memory obligations belong to the host per the ownership map. The test passes with exactly these named classifications and fails on unknown drift. The ratios report accepted evidence obligations for inventoried emitted value/effect opcodes, not correctness-proof or end-to-end compiler-proof percentages. A default `Statistical(N)` Valid result is regression evidence, not a formal proof. |
| `meta_theorems` | Property-level executable invariants. |
| `mutation_catalog` | Mutation-harness invariants. |
| `proof_gate_strict` | Non-degeneracy and fail-closed proof-gate behavior. |
| `fsym_real_function_corpus` | Bounded symbolic preflight on the maintained real-function corpus. |
| `wasm_encoding_gate` | WebAssembly encoding/indexing evidence over the bytes the live backend really emits: the module index spaces (the shift imported functions impose, export targets, the element segment's `funcidx == table-index` identity, the little-endian static data image, section order), an INDEPENDENT spec-derived signed-LEB128 decoder applied to every captured `i32.const`/`i64.const` immediate at canonical length, and `TargetInfo` conformance for `wasm32`. Every obligation is a byte-level statement plus a mutation that must refute it. The tally is pinned exactly and reported in three parts, never as a headline: **210 proven / 0 refuted / 108 not-applicable**, plus 7 named RED deferrals. The not-applicable count is load-bearing: every row here quantifies over a set of constructs, and a row whose set is empty for a module (no calls, no globals, no branch, no memory access, no import) reports NOT-APPLICABLE rather than banking that module's silence as credit — which is why a `() -> i32 { ret -1 }` module earns 8 rows here and not 18. One module, the full-surface island, makes every row of both families applicable at once, so no row is merely stated. It does NOT establish that the lowering chose the right value, the right call target, or the right control flow — a wrong constant encodes and decodes perfectly. Neither does it catch a forgotten import shift from a single module: that partition is true by the decoder's construction, so the obligation is carried by a TWO-COMPILE differential (the same trust-ir lowered closed and as an island) whose refutation of the exact silent miscompile is asserted, together with the single-module family's measured blindness to it. `f32.const`/`f64.const` immediates are raw IEEE-754 payloads this decoder does not reach; they are the two RED rows of the opcode inventory above. |
| `wasm_cfg_structural_gate` | The per-compile CFG structural invariant on the relooper's output, checked against a control-flow-diverse corpus compiled by the live backend, and RUN ON EVERY EVIDENCE-CARRYING COMPILE (`wasm::compile_module_with_evidence[_and_policy]` calls it on the bytes it just emitted; a refuted verdict fails the compile, an inconclusive one is filed uncredited in the evidence's `not_run` list, and a holding one is filed in `ran` and moves nothing else — that compile's verdict stays `MissingEvidence` and its route stays `NotRun`): every `br`/`br_if`/`br_table` depth names a LIVE label, branch operand types and counts follow the spec's polymorphic-stack rule, every `br_table` arm and its default take the same types, join heights and operand types are checked at every `end`/`else`, and the bracket structure is well formed. This is a NECESSARY CONDITION on the structuring, NOT a proof that the structured program computes what the trust-ir CFG computes: relooper BISIMULATION is a named RED deferral, and two blind-spot mutants — a branch retargeted to another live same-arity label, and a `block` opener rewritten as a `loop` — are shipped and asserted NOT to be caught, so the gap is measured rather than claimed away. Also silent on block-parameter (phi) resolution and on code the spec proves unreachable. |
| `wasm_abi_proofs_gate` | The WebAssembly shadow-stack frame refinement and the call/table ABI discipline, over a corpus of REAL emitted module bytes (frozen fixtures re-compiled and required to match byte-for-byte, plus live modules outside the corpus). Reconstructed SMT obligations pin the frame arithmetic (frame size, slot offsets, slot disjointness, the prologue's publish-into-the-global-it-read, the epilogue's restore of the caller's stack pointer on a normal return); decidable structural checks pin the index spaces, direct-call targets, argument and result discipline, function-pointer constants, the element segment, `call_indirect`'s table immediate, and the imported stack base's immutability. Byte-mutation guards are its teeth. It does NOT establish the five HOST obligations named in `crates/trust-cg-codegen/src/wasm/OWNERSHIP.md` (host-memory aliasing under Policy I, stack-reserve sufficiency, stack-pointer restoration on a trap or host throw, stack-base alignment, argument-window validity), the engine's `call_indirect` runtime type check, imported-function behaviour, whole-body operand-stack typing, or call-site correspondence across a reordered CFG — the last of which ships as a declared blind guard. |
| `bdefs_differential_bridge` | AArch64 integer bridge. |
| `bdefs_differential_bridge_x86` | x86-64 bridge. |
| `bdefs_differential_bridge_riscv` | RISC-V bridge. |
| `bdefs_differential_bridge_x86_packed` | x86 SSE packed bridge. |
| `bdefs_differential_bridge_x86_fp` | x86 SSE floating-point bridge. |
| `bdefs_differential_bridge_neon` | AArch64 NEON bridge. |
| `bdefs_differential_bridge_riscv_fp` | RISC-V floating-point bridge. |
| `bdefs_differential_bridge_neon_fp` | AArch64 NEON floating-point bridge. |
| `fp_bitmodel_bridge` | AArch64 floating-point bit-model/silicon bridge. |

A Cargo target passes only if `cargo test` exits successfully, emits a
`test result: ok.` line, and runs at least one test.

The Clean portion checks the maintained B-definition and LRAT-checker proof
files with `clean check`:

```text
aarch64_isa  aarch64_isa_chip  aarch64_fp  aarch64_fp_arith
aarch64_fp_cvt  aarch64_fp_divsqrt  aarch64_fp16  reducible_word
lrat_checker  lrat_checker_word  lrat_checker_tree
```

It also runs `cargo test -p clean-kernel --test micro_diversity_gate`. The AY
revision is recorded for provenance; this script does not invoke AY directly.

Finally, the trust-cg checkout runs `lake build` in `formal/lean`, requires the
classified-gap and explicit-axiom counts to remain exactly 17 and 4, and runs
the `trust-cg-codegen` `lean_encode_golden_binding` integration test. That test
binds the Lean encoder's shared golden vectors to the production Rust encoder.

The separate external-solver database floor may classify obligations as
timeout/unknown. `scripts/check_proof_gate.sh` prints the verified/pending split
and requires zero counterexamples, zero errors, and no statistical fallback.
Pending obligations are not described as proofs.

Two wasm offline-oracle gates run the backend's differential harnesses as
first-class checks: the `wasm_difftest` example (interpreter-vs-compiled-wasm
over its corpus, replayed under node) and the bounded `wasm_cfg_fuzz` relooper
fuzz. A missing node is a loud SKIP counted in the summary, never a silent
pass; any divergence or vacuous (0-case) run fails the gate.

Two further gates run the shipped ISLANDS' three-way differential
(`wasm_island_differential.mjs`): the generator emits its trust-cg wasm, its
rustc/LLVM twin SOURCE and interpreter-checked expectations, and the runner
then COMPILES the twin for wasm32, instantiates both modules and replays
every expectation against both. A generator run alone never compiles or runs
the twin, so without this gate the islands' "differential-experimental" label
would be a deployment intention rather than repository evidence. The vt
islands need an aterm tables dump (`ISLAND_VT_TABLES=<tables.json>`, schema
`aterm.vt-islands.tables` v1); absent, that one gate SKIPs loudly. A missing
`rustc` likewise SKIPs rather than passing.

All four are differential evidence, not proofs — the wasm lane's per-op
refinement obligations remain the `wasm_formal` suite's territory.

## Revision lock

`soundness_revs.lock` records the audited trust-cg source commit, the Clean
commit used by the executable proof checks, and the AY dependency-source
context. The script does not invoke AY, so the AY entry is not a solver-result
or fixture-generation attestation. Normal mode warns when a live checkout has
drifted. `--pinned` makes drift a hard failure and also requires all three
worktrees to be clean.

The trust-cg entry uses a two-commit attestation model to avoid an impossible
self-reference. After a green run at source commit `C0`, update mode records
`C0`; the lock is then committed alone as `C1`. Pinned mode accepts `C1` only
when it is a single-parent child of `C0` and `soundness_revs.lock` is the sole
changed file. Any additional source or follow-up commit is drift.

That relationship describes the development release input. Publication maps
dependency identities and creates a new, root public snapshot commit, so the
embedded development lock is provenance rather than a claim that the public
commit is `C1`. A fresh public snapshot is validated by the anonymous clone
gate. To create a new executable public pin, run `--update` against clean public
Clean/AY checkouts at the exact mapped lock revisions and commit only the
resulting lock in a public fork; the same `C0`/`C1` rule then applies there.

To record a new green state:

```sh
scripts/soundness_check.sh --update
```

Update mode first requires all three candidate worktrees to be clean. It then
requires one exact TrustIR and Clean revision across the root, standalone rustc
backend, and fuzz `Cargo.lock` files, one exact AY revision across the two locks
whose graphs enable AY, and the Clean/AY checkout heads to equal those resolved
revisions. `scripts/soundness_check.sh --validate-dependency-locks` runs this
toolchain-free lock check by itself. Update mode then runs the full configured
gate, rechecks that the commits and contents did not change during the run, and
rewrites only the three revision entries if every check passes. Review and commit
`soundness_revs.lock` as the sole changed file. This prevents a commit ID from
attesting unrelated uncommitted bytes or a different dependency source.

## Optional pre-push hook

The repository includes `hooks/pre-push`. Install it per clone with:

```sh
scripts/install-hooks.sh
```

Once installed, it runs the soundness script when a push updates `main`, and a
failure blocks that push. It requires the pushed SHA to be the clean checked-out
HEAD and invokes pinned mode. Feature-branch pushes are not gated. Git hooks
are local and optional, so an unconfigured clone has no automatic enforcement;
release reviewers must verify the recorded gate result independently.
