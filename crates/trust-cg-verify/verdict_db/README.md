# Tier-0 committed candidate DB (PROOF-3)

`tier0.vdb` is a repo-committed, content-addressed database of **candidate
queries previously observed as unsat** for fixed, program-independent proof
obligations. It includes target-lowering, reconstruction, and per-process
canary queries and is embedded into `trust-cg-verify` at build time. A match is
an optimization hint only:
the current process must re-run the solver and observe `unsat` before the
obligation can be credited as Formal.

## Key schema

Every candidate is addressed by this v2 content key:

```
key = SHA-256( "tcg-proof-cache-v2\0"
             ‖ lowercase-hex SHA-256 of the solver binary's BYTES
             ‖ "\0"
             ‖ the exact SMT2 query bytes )
```

The key is re-derived from the query at lookup time. This detects accidental
corruption and correlates exact bytes, but it does not authenticate writable
data. The former `AYResultCache` and machine-local `.verdict` cache were
removed because forged JSON or a file containing `unsat` could establish
proof authority without revalidation.

## Trust story — read this before trusting a hit

**A tier-0 hit is not a proof.** A row records that a solver returned `unsat`
on exact SMT2 bytes during regeneration, but the consumer treats it as
untrusted input. Consequently:

- The consuming process re-executes the solver on every candidate hit and
  credits Formal only after a live `unsat`. That result may then be memoized
  in process memory, never on disk.
- **Self-disable:** tier-0 refuses to serve (falls back to live discharge)
  unless the resolved solver binary's bytes-hash EQUALS the manifest's
  `solver-sha256`. A new, rebuilt, or foreign `ay` — including one carrying
  an ay soundness fix — invalidates every shipped verdict rather than
  trusting stale ones.
- **Verified-only rows:** the format has no verdict column; a row's existence
  means `unsat`. Timeout / CounterExample / Unknown / Error are never
  persisted in any tier (a timeout is a scheduling fact, not a proof fact).
- **Fail-closed corruption policy:** malformed data disables the tier; a
  well-formed forged row still cannot mint `Verified` because live
  revalidation is mandatory.
- Independently checked LRAT certificates can eventually replace live
  revalidation for certified rows; an unchecked recorded verdict cannot.

## Canary CERT-SKIP tier (`canary_certs/`)

The sanctioned replacement above is live for eight fixed obligations:
popcnt SWAR at width 32, Shl/Shr/Sar reconstruction at widths 32 and 64, and
x86 integer equality at width 32. Their files under `canary_certs/` are
repo-committed, build-embedded `tcg-lrat-cert-v2` certificates (see
`lrat_cert.rs`) carrying the obligation's bit-blasted CNF plus a trimmed DRAT
refutation. On a per-compile hit the
vendored, independent `drat-trim` re-checks the refutation **in this process,
now** (~1-2 s, deterministic — no solver search, no deadline) before the
verdict is credited. The recorded verdict itself is never trusted:

- the key (`verdict_cache_key_v2`) binds the solver binary's bytes-hash and
  the exact SMT2 bytes derived in-process from the live model, so a regressed
  model or a new/rebuilt/foreign solver misses and re-proves LIVE;
- the cert's recorded `solver_identity` must additionally equal the resolved
  solver's bytes-hash (self-disable, as tier-0);
- the combinatorial (SAT-search) half of the verdict is independently
  re-established on every consume; the residual trusted link is the regen-time
  bit-blast by the byte-identical solver — a strict subset of the live run's
  trusted surface;
- any miss / mismatch / tamper / check-failure falls through to the live
  solver discharge (fail-closed; the 30 s deadline semantics there are
  unchanged).

Unlike the removed `.verdict` disk cache this artifact is not machine-local
writable data: it is committed and embedded at build time, the same trust
class as the compiler's own source — and even then it must pass the
independent checker on every consume.

Regenerate with `cargo run --release -p trust-cg-verify --bin
regen_canary_certs` (quiet machine; requires the real `ay`), then rebuild and
commit. Opt out per-run with `TCG_CANARY_NO_CACHE=1` (this tier only) or
`TCG_NO_PROOF_CACHE=1` (all reuse).

## Regenerating

```
cd crates/trust-cg-verify
cargo run --release --bin regen_verdict_db
```

Requires the real `ay` solver (the canonical Trust-toolchain `ay`, or
`AY_SOLVER_PATH`). The tool arms an in-process recorder, re-proves every seed
obligation with a LIVE solver run (the process memo is bypassed while
recording), and rewrites `tier0.vdb` deterministically (sorted, deduped) —
re-running it with an unchanged solver and unchanged obligations is
diff-clean. It refuses to write anything if any seed fails to discharge
`Verified`. Set `TCG_VERDICT_DB_PROVENANCE="<commit/context>"` to record a
provenance line. After regenerating, rebuild (the file is embedded via
`include_str!`) and commit the new `tier0.vdb`; re-verification is re-running
the tool and checking `git diff` is clean.

Note: the SMT2 bytes embed the default solver timeout, so a non-default
`TRUST_CG_AY_TIMEOUT_MS` at compile time changes the query bytes and simply
misses tier-0 (live discharge, never wrong).

## Opting out

- `TCG_NO_VERDICT_DB=1` — disable tier-0 only.
- `TCG_NO_PROOF_CACHE=1` — disable tier-0 and process-local live-result reuse.
