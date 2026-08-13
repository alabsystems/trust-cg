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
| External SMT solver | Supported obligations serialized through `ay_bridge` to an AY binary. | `Verified` means AY reported the negated represented obligation unsatisfiable. Timeout, unknown, error, and counterexample are not proofs. |

The encoding, solver, and bridge are part of the trusted computing base for an
SMT verdict. Independent replay exists only on named certificate paths.

v0.1.0 intentionally exposes no native-AY Cargo feature. Solver-backed checks
use the canonical external AY binary so Trust-CG keeps a one-way tool boundary
instead of introducing an AY <-> Trust-CG Cargo cycle.

## Running the checks

Run the default evaluator-focused package tests:

```sh
cargo test --locked -p trust-cg-verify
```

Run the opt-in slow evaluator sweep of the full proof database:

```sh
cargo test --locked -p trust-cg-verify \
  --features slow-full-database --test full_proof_suite
```

With `ay` on `PATH`, run the short fail-closed SMT smoke:

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
pending obligations; the test prints the verified and pending counts and does
not relabel pending work as proved.

Set `TRUST_CG_AY_TIMEOUT_MS=<milliseconds>` to raise the external solver budget;
`0` means no timeout. Solver availability never causes the strict gate to
downgrade silently to statistical evaluation.

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
independently checked certificate. Unsigned v0.1.0 exports identify their
authority, and missing or unsupported evidence causes proof-required paths to
fail closed.

`LoweringCertificate::to_trust_proof_cert_json()` exports the current JSON
transport. Its status and signature fields must be interpreted literally; an
unsigned transport does not establish a signed chain of trust.

See the repository [`README`](../../README.md),
[`LIMITATIONS`](../../LIMITATIONS.md), and
[`SOUNDNESS_CHECK`](../../SOUNDNESS_CHECK.md) for the release-wide trust
boundary and cross-repository gates.
