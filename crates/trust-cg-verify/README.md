# trust-cg-verify

`trust-cg-verify` constructs and checks verification obligations used by the
Trust Codegen pipeline. It is a research-preview verification backend, not a
claim that every lowering rule, optimization, encoder, or emitted binary has a
completed proof.

## Evidence lanes

The crate keeps evidence strength explicit:

| Lane | Scope | Meaning |
| --- | --- | --- |
| Exhaustive evaluator | Small bounded obligations, normally widths up to 8 bits subject to the input-count limit. | Every point in the represented bounded domain was checked. |
| Statistical evaluator | Wider obligations, normally 32 and 64 bits. | Edge cases and deterministic pseudorandom samples matched. This is regression evidence, not a proof over all inputs. |
| External SMT solver | Supported obligations serialized through `ay_bridge` to AY. | A live `Verified` requires AY's exact UNSAT proof to be independently accepted by Clean. Bare solver UNSAT, timeout, unknown, error, and counterexample are not proofs. |

The encoding and bridge still determine which obligation was represented.
Independent checking does not prove that the source semantics were modeled
correctly. Portable committed canaries have a separate, exact-query-bound
DRAT replay path; they do not require a locally installed AY.

trust-cg intentionally exposes no native-AY Cargo feature. Solver-backed checks
use the canonical external AY binary so Trust-CG keeps a one-way tool boundary
instead of introducing an AY <-> Trust-CG Cargo cycle.

## Running the checks

Run the default evaluator-focused package tests:

```sh
targo --unverified test --locked -p trust-cg-verify
```

Run the opt-in slow evaluator sweep of the full proof database:

```sh
targo --unverified test --locked -p trust-cg-verify \
  --features slow-full-database --test full_proof_suite
```

With the build toolchain's AY — admitted by the SHA-256 of its bytes recorded at
build time (see `src/ay_identity.rs`) — and
aterm's capable Clean package, run the short fail-closed SMT smoke:

```sh
scripts/check_proof_gate.sh \
  --test representative_arithmetic_is_formally_verified
```

Run the much slower full-database SMT floor:

```sh
scripts/check_proof_gate.sh \
  --test full_database_is_formally_verified
```

The full-database floor requires zero counterexamples/errors and forbids a
statistical fallback. Solver timeouts and `unknown` results remain explicit
pending obligations. Only the five explicitly audited capacity-pending names
in `tests/proof_gate_strict.rs` are allowed; any new pending name fails the
floor. Its verified/pending split never relabels pending work as proved.

Set `TRUST_CG_AY_TIMEOUT_MS=<milliseconds>` to change the default AY/Clean
per-subprocess budget (30 seconds unless overridden); `0` means unlimited.
`AYConfig::with_timeout` sets the authority caller's policy explicitly. Cache
replay, solving, proof checking and optional minting have separate budgets;
staging and executable hashing are outside the timer. This is not a whole-query
deadline. Solver availability never permits a statistical downgrade.

## The independent Alethe checker (required to promote UNSAT)

An AY `unsat` is a solver verdict, not a proof. Before it becomes `Verified`,
the Alethe proof AY emits is re-checked by an **independent** checker — Carcara,
invoked as `clean cert verify-external <cert.json> --verbose`. Without a usable
checker, UNSAT stays `Unknown`; a timed-out probe or replay yields `Timeout`.
AY identification is separate from checker availability: a broken Clean
package is not reported as a missing AY executable.

AY is the sole SMT solver. The Trust toolchain ships AY and Clean as one
sealed pair, and both come from the toolchain that owns the code (the compiler
hosting the process, otherwise the one that built this crate): AY exclusively
(`src/ay_identity.rs`), Clean first, because a checker must read the proofs of
the AY it is paired with. aterm's managed Clean package is the fallback when
that toolchain ships no capable checker. Normal use requires neither sibling
source checkouts nor a separate checker installation. Clean must ship with
`carcara-verify` enabled. Inspect the package with `aterm pkg doctor` and
`aterm pkg which clean`.
[LIMITATIONS.md](../../LIMITATIONS.md) records what happens when no candidate
checker is usable.

For toolchain development only, `$TCG_EXTERNAL_CLEAN_CHECKER` explicitly
selects a checker. `$TCG_CLEAN_CHECKER` is a legacy alias, used only when the
canonical variable is unset. Overrides are authoritative and never fall back.
Without one, discovery tries the owning toolchain's `bin/clean`, then aterm's
managed package paths, never arbitrary PATH commands or sibling builds. A
default candidate that fails the probe is skipped with a one-line notice when
the other one is capable; the DEGRADED banner means no checker is usable. No
alternate SMT solver is a fallback.

A known-good propositional refutation checks capability before proof admission.
Stable capability defects receive a package-repair diagnostic; transient probe
timeouts and I/O failures remain retryable. `clean_checker_path` is only a
cached scheduling hint. `clean_checker_path_and_identity` binds current checker
bytes, and replay checks that identity before and after complete output capture.

The machine-local Alethe store rechecks exact query, producer, certificate and
checker bindings before granting a replay hit. Its two writers use owned
same-directory staging and no-clobber publication. Minting is synchronous,
optional and checked before publication; it is not an unchecked verdict cache.

## Coverage boundaries

`ProofDatabase` contains obligations across arithmetic, flags, comparisons,
branches, memory, peepholes, register allocation, vector operations, object
handling, and other targeted families. Registration is not the same as a
proof: inspect each result's strength and status.

The first whole-function translation-validation slice supports a deliberately
small subset:

- one entry block on each side, ending in `Return`;
- scalar integer types `B1`, `I8`, `I16`, `I32`, and `I64`;
- pure SSA operations including integer constants, copies, basic arithmetic,
  comparisons, and bitwise operations.

Branches, loops, calls, memory, floating point, aggregates, vectors,
division/remainder, shifts, casts, bitfields, multi-result operations, and other
unsupported shapes fail closed with `Unknown` on this slice.

## Proof artifacts

The CLI's `--emit-proofs=<DIR>` path can write SMT-LIB obligations, structured
certificate records, lowering reports, and function-level sidecars for
supported compilations. A serialized record is not automatically an
independently checked certificate. Unsigned exports identify their
authority, and missing or unsupported evidence causes proof-required paths to
fail closed.

`LoweringCertificate::to_trust_proof_cert_json()` exports the current JSON
transport. Its status and signature fields must be interpreted literally; an
unsigned transport does not establish a signed chain of trust.

See the repository [`README`](../../README.md),
[`LIMITATIONS`](../../LIMITATIONS.md), and
[`SOUNDNESS_CHECK`](../../SOUNDNESS_CHECK.md) for the release-wide trust
boundary and cross-repository gates.
