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
| `coverage_gate_tests` | Accepted/deferred opcode inventory: AArch64 155/248 with 93 explicitly deferred RED rows; x86-64 163/192 with 29; RISC-V 14/17 with 3; and WebAssembly 109/111 with 2. The test passes with exactly these named classifications and fails on unknown drift. The ratios report accepted evidence obligations for inventoried emitted value/effect opcodes, not correctness-proof or end-to-end compiler-proof percentages. A default `Statistical(N)` Valid result is regression evidence, not a formal proof. |
| `meta_theorems` | Property-level executable invariants. |
| `mutation_catalog` | Mutation-harness invariants. |
| `proof_gate_strict` | Non-degeneracy and fail-closed proof-gate behavior. |
| `fsym_real_function_corpus` | Bounded symbolic preflight on the maintained real-function corpus. |
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
requires the Clean and AY checkout heads to equal the unique exact revisions in
the candidate `Cargo.lock`, runs the full configured gate, rechecks that the
commits and contents did not change during the run, and rewrites only the three
revision entries if every check passes. Review and commit
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
