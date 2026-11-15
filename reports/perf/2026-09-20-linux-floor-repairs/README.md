# Repairs from the complete Linux regression inventory — 2026-09-20

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The [complete 125-family run](../2026-09-20-linux-required-floor/README.md)
finished with 120 passing families and five failures on `86857ff3d`.
The repairs address three implementation/fixture failures, one wrong-result
conversion and one harness environment mistake. **553 targeted Rust tests pass**
on the final candidate; the complete inventory is scheduled for a new clean
commit and is not claimed to pass by this record.

## Changes and independent checks

- Saturating f64-to-u128 returned the wrong result at exactly `2^128` on this
  Linux host. The old lowering assumed the runtime helper already saturated.
  The retained original object and C runner reproduce the failure. Signed and
  unsigned f16/f32/f64-to-i128/u128 lowering now computes explicit bounds and
  NaN conditions, passes a finite in-range value to the raw helper, then selects
  zero or the appropriate destination bound for exceptional inputs. The native
  regression covers f32/f64 at O0–O3, fixed boundaries and 1,024 sampled bit
  patterns per width and level. GNU linker wrappers abort on any out-of-domain
  raw helper argument. Adjacent f16/i128 conversion suites also pass. This is
  native numerical and runtime-call evidence, not formal conversion authority.
- Canonical TrustIR forbids `InsertField` on an enum discriminant, including
  a niche-encoded enum. The adapter still emitted that invalid operation and
  the native corpus used it. The obsolete helper is removed; typed refusal
  agrees with the canonical validator for every codec shape. The positive
  corpus selects and stores complete variants instead, retaining all twenty
  functions and all 882 native checks at each of O0–O3. Exact compiler refusals
  are checked on both ELF and Mach-O targets. Darwin native execution is not
  claimed; only its two host-neutral refusal tests ran.
- An identity function can allocate to NOP/RET alone. Omitting its frame loses
  the current non-vacuous source-bound JIT certificate. Return-only bodies with
  a value result now retain the checked frame envelope. All seven proof-policy
  tests pass, including identity execution at all four levels, twelve Formal
  frame rows, 32 native calls and the original unproved-call refusal. The
  existing arithmetic and emitted-layout frame tests remain passing. No verifier
  rule, certificate-strength requirement or raw RET credit is weakened.
- The stack-protector fixture uses `add_function_proof`, the current explicit
  name for its function annotation. All 21 runtime/link tests pass with the
  original stack-protector checks intact.
- The first census supplied `TRUST_CG_LLVM_BIN` to every test. Sealed Core
  admission correctly rejects that unknown ambient compiler control. Removing
  that harness override, while keeping the installed LLVM readers on PATH,
  restores all eleven Core planning tests. A separate clean-environment run
  confirms that the identity JIT failure persists independently of this mistake.

The first repair qualification passed the native enum checks but failed a new
negative assertion that expected display text from a helper returning Debug
text. The assertion now checks the exact `EnumTagWriteUnsupported` result; the
failed attempt and its test source are retained. The final targeted run has
zero failed or ignored tests; its explicitly filtered unit and Darwin refusal
runs are recorded as such. Formatting passes.

## Scope and reproduction

The eight-file candidate patch, file hashes, parent revision, complete commands,
selected environment, dependency/tool records, test executable identities,
resource plans and guard receipts are retained. The original complete-run
archive identifies all tools and pinned dependencies. Native saturation objects,
drivers and executables are retained with stored and decoded hashes. Jobs ran
serially under an anchored 16 GiB process-group RSS ceiling, zero memory grace,
two Cargo build jobs and one test thread. Source and HEAD stayed fixed during
the final qualification.

This record does not update the installed compiler, qualify the private Trust
backend or establish full Linux acceptance. Those steps have separate records.
The frontend remains an explicit development lane; all L01–L14 requirements
remain OPEN. No performance or self-hosting result is claimed.

```sh
cargo test --locked -p trust-cg-codegen --test e2e_aarch64_fptosi_sat_i128 -- --nocapture --test-threads=1
cargo test --locked -p trust-cg-codegen --test e2e_aarch64_niche_enum_linux -- --nocapture --test-threads=1
cargo test --locked -p trust-cg-codegen --test jit_fail_closed_proof_policy -- --nocapture --test-threads=1
python3 scripts/check_evidence_archive.py reports/perf/2026-09-20-linux-floor-repairs
```
