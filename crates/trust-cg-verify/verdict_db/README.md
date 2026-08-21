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

## Portable canary CERT-SKIP tier (`canary_certs/`)

The sanctioned replacement above is live for sixteen fixed obligations:
popcnt SWAR at width 32, Shl/Shr/Sar reconstruction at widths 32 and 64,
x86 integer equality at width 32, and Bounds/ShiftRange/NullIfZero/DivZero
guard carriers at widths 32 and 64. Their files are repo-committed,
build-embedded `tcg-lrat-cert-v3` certificates carrying the exact SMT2, its
bit-blasted CNF, and a trimmed DRAT refutation. `manifest.v1` binds the exact
filename set to each complete file SHA-256, domain-separated exact-query
SHA-256, per-artifact producer AY SHA-256, and authorized drat-trim checker
SHA-256. On a per-compile hit the
vendored, independent `drat-trim` re-checks the refutation **in this process,
now** (~1-2 s, deterministic — no solver search, no deadline) before the first
credit for that exact query/certificate/checker tuple. Later hits in the same
process reuse only that positive, content-keyed replay result. The recorded
verdict itself is never trusted:

- the portable lookup key binds the exact SMT2 bytes derived in-process from
  the live model and is independent of any locally installed AY; a regressed
  model misses and falls through to the live lane;
- the producer AY hash remains immutable provenance inside the v3 artifact,
  not a consumer prerequisite or checker authority;
- the exact `drat-trim` executable is hashed before and after replay, and the
  replay memo binds query + complete cert bytes + checker bytes;
- the combinatorial (SAT-search) half of the verdict is independently
  re-established before its first per-process credit; the residual trusted link
  is the regen-time bit-blast by the manifest-recorded producer bytes — a
  strict subset of the live run's trusted surface;
- any miss / mismatch / tamper / check-failure falls through to the live
  solver discharge (fail-closed; the 30 s deadline semantics there are
  unchanged).

Unlike the removed `.verdict` disk cache this artifact is not machine-local
writable data: it is committed and embedded at build time, the same trust
class as the compiler's own source — and even then it must pass the
independent checker before its first content-keyed credit in each process.

Regenerate all sixteen transactionally with `cargo run --release -p
trust-cg-verify --bin regen_canary_certs` (quiet machine; requires the real
AY producer). An existing proof payload is upgraded only when its historical
producer plus exact current query reproduce its bound key and the current
checker replays it; missing or stale entries are freshly produced. Set
`TCG_CANARY_REGEN_ALL=1` to force fresh production of all sixteen. Certificate
files publish first and the manifest last, so an interrupted update disables
rather than partially authorizes the tier. Opt out per-run with
`TCG_CANARY_NO_CACHE=1` (this tier only) or
`TCG_NO_PROOF_CACHE=1` (all reuse).

Regeneration note (2026-08-19): exact AY A0 source
`9ff68fe0cc8a0145c8101682123211a7b5992771` (isolated release binary SHA-256
`3cc63abbb41f183d2e97e0842ef2a625a120124da73f483f5164e62a97a4e2d6`)
conservatively answered `unknown` for the popcount query after its embedded
30-second timeout. It nevertheless published a genuine PID-bound bit-blasted
CNF (1,420 variables, 4,807 clauses). That abstention is not evidence and is
never promoted by itself: A0's second, DIMACS-mode run produced the DRAT over
those exact exported CNF bytes, and the independent checker accepted it. All
sixteen current artifacts were freshly generated by that exact A0 binary; the
previous eight were rejected for reuse because their old producer-bound keys
did not match the current exact queries. The manifest records A0 only as
untrusted production provenance. Every artifact requires exact query/file
binding and independent `drat-trim` replay; runtime acceptance grants the
producer no checker authority.

The machine-local Alethe store uses an independent external Clean/Carcara C0
checker selected by `TCG_EXTERNAL_CLEAN_CHECKER` (legacy alias:
`TCG_CLEAN_CHECKER`). Its executable SHA-256 is recorded in schema v2 certs
and checked before and after every replay. This external checker role is
separate from the Cargo-pinned C1 `clean-kernel` dependency.

"Portable" here means portable across AY absence. The committed manifest
authorizes one exact vendored `drat-trim` executable identity; another platform
or compiler build is a cache miss until its checker bytes are explicitly
reviewed, authorized, and used to replay the full set.

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
