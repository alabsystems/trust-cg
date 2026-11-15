# Tier-0 committed candidate DB (PROOF-3)

`tier0.vdb` is a repo-committed, content-addressed database of **candidate
queries previously observed as unsat** for fixed, program-independent proof
obligations. It includes target-lowering, reconstruction, and per-process
canary queries and is embedded into `trust-cg-verify` at build time. A match is
an optimization hint only:
the current process must discharge the obligation through AY and independently
check its exact proof before the live result can be credited as Formal.

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

- The consuming process re-executes AY on a candidate hit and credits Formal
  only after independently checking its exact UNSAT proof. That result may be memoized
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

The sanctioned replacement above is live for 33 fixed obligations. They cover
popcnt SWAR; Shl/Shr/Sar reconstruction; AArch64 UDIV; x86 integer equality;
Bounds/ShiftRange/NullIfZero/DivZero guard carriers; AArch64 frame layout,
Mach-O relocation, MOVZ/MOVK, LDP, byte-roundtrip, and checked-overflow proofs.
Their files are repo-committed, build-embedded `tcg-lrat-cert-v3` certificates
carrying the exact SMT2, its bit-blasted CNF, and a trimmed DRAT refutation.
`manifest.v1` (historical filename; its strict schema is now
`tcg-canary-cert-manifest-v2`) binds the exact filename set to each complete
file SHA-256, domain-separated exact-query SHA-256, per-artifact producer AY
SHA-256, and reviewed checker authorizations. New authorizations require both
the bundled checker's compile-time Cargo target triple and exact executable
SHA-256. The one pre-existing unqualified checker hash is explicitly retained
as a legacy exception; its unrecorded original host is not inferred.
On a per-compile hit the vendored,
independent `drat-trim` re-checks the selected refutation **in this process,
now** (deterministic — no solver search or deadline) before the first credit for
that exact query/certificate/checker tuple. Later hits in the same process reuse
that content-keyed replay result. The recorded verdict itself is never trusted:

- the portable lookup key binds the exact SMT2 bytes derived in-process from
  the live model and is independent of any locally installed AY; a regressed
  model misses and falls through to the live lane;
- the producer AY hash remains immutable provenance inside the v3 artifact,
  not a consumer prerequisite or checker authority;
- the exact `drat-trim` executable is hashed before and after replay, and the
  replay memo binds query + complete cert bytes + checker bytes, with the owned
  authority additionally binding target, manifest, path and captured environment;
- the combinatorial (SAT-search) half of the verdict is independently
  re-established before its first per-process credit; the residual trusted link
  is the regen-time bit-blast by the manifest-recorded producer bytes — a
  strict subset of the live run's trusted surface;
- any miss, or any mismatch / tamper / check-failure in the selected artifact,
  falls through to the live solver discharge (fail-closed; the 30 s deadline
  semantics there are unchanged). Unselected bodies are checked when selected;
  full-set regeneration/audit checks every body.

Unlike the removed `.verdict` disk cache this artifact is not machine-local
writable data: it is committed and embedded at build time, the same trust
class as the compiler's own source — and even then it must pass the
independent checker before its first content-keyed credit in each process.

Regenerate all 33 transactionally with `targo --unverified run --release -p
trust-cg-verify --bin regen_canary_certs` (quiet machine; requires the real
AY producer). An existing proof payload is upgraded only when its historical
producer plus exact current query reproduce its bound key and the current
checker replays it; missing or stale entries are freshly produced. Set
`TCG_CANARY_REGEN_ALL=1` to force fresh production of all 33. Certificate files
publish first and the manifest last, so new bytes cannot be authorized before
the manifest commit. During an interrupted mixed update, only selected entries
whose complete digest and bindings still match can authorize; full-set
regeneration/audit rejects the mixed set. Opt out per-run with
`TCG_CANARY_NO_CACHE=1` (this tier only) or
`TCG_NO_PROOF_CACHE=1` (all reuse).

Regeneration preserves earlier checker qualifications only when every complete
certificate/file/query/producer entry is unchanged. A changed corpus drops those
prior qualifications and records the checker that actually replays the new set.
New checker/host entries still require review before their manifest is committed.

Regeneration note (2026-08-19): exact AY A0 source
`9ff68fe0cc8a0145c8101682123211a7b5992771` (isolated release binary SHA-256
`3cc63abbb41f183d2e97e0842ef2a625a120124da73f483f5164e62a97a4e2d6`)
conservatively answered `unknown` for the popcount query after its embedded
30-second timeout. It nevertheless published a genuine PID-bound bit-blasted
CNF (1,420 variables, 4,807 clauses). That abstention is not evidence and is
never promoted by itself: A0's second, DIMACS-mode run produced the DRAT over
those exact exported CNF bytes, and the independent checker accepted it. The
original sixteen artifacts were freshly generated by that exact A0 binary; the
previous eight were rejected for reuse because their old producer-bound keys
did not match the current exact queries. The current 33-entry manifest records
producer identity per artifact, only as untrusted production provenance. Every
artifact requires exact query/file binding and independent `drat-trim` replay;
runtime acceptance grants the producer no checker authority.

The machine-local Alethe store uses the Clean/Carcara C0 checker of the Trust
toolchain that owns the code, else aterm's managed one.
Toolchain developers may explicitly override it with `TCG_EXTERNAL_CLEAN_CHECKER`
(legacy alias: `TCG_CLEAN_CHECKER`); normal use needs no separate checker install.
Its executable SHA-256 is recorded in schema v2 certs
and checked before and after every replay. This external checker role is
separate from the Cargo-pinned C1 `clean-kernel` dependency. Clean probes/replay
and optional AY minting use the configured per-subprocess budget, with zero
unlimited. A timeout cannot establish a replay hit. Both writers use owned
staging files and preserve any already-published certificate.

"Portable" here means portable across AY absence. The committed manifest
authorizes one exact vendored `drat-trim` executable identity; another platform
or compiler build is a cache miss until its checker bytes are explicitly
reviewed, authorized, and used to replay the full set. That identity is the
SHA-256 of the executable `crates/trust-cg-drat-trim/build.rs` compiles from
the vendored source, so it is a function of that build's INPUTS: the C
compiler, `SDKROOT`, and — on macOS — the deployment target clang stamps into
`LC_BUILD_VERSION`. `build.rs` pins the deployment target
(`APPLE_DEPLOYMENT_TARGET`) because `cc` would otherwise infer it from the
host's DEFAULT SDK version, which a CommandLineTools update moves (measured
2026-09-20: 26.5 -> 27.0 re-keyed the checker with nothing in this repository
changed, and every portable certificate was silently declined). That pin and
the manifest's Apple `host-checker` rows are a bound set: moving the pin re-keys
every Apple row, and a row minted on a tree without the pin is stale once the
pin reaches it (both Apple rows were, after the 2026-09-21 merge; re-qualified
2026-09-27 and 2026-09-29 per `docs/portable-checker-host-qualification.md`). A different compiler or SDK still re-keys the checker: the portable
set then misses fail-closed, `canary_cert` prints the actual and authorized
identities once per process together with the fix, and
`committed_set_binds_the_exact_runtime_checker_bytes` goes red. Re-authorize
with `regen_canary_certs` below (payloads whose exact query is unchanged are
replayed, not re-proved, so this changes only the manifest line).

It is not a wildcard for other
platforms or compiler builds. The Linux qualification and explicit legacy
boundary are recorded in
portable checker host qualification.
Wrong-host entries, unknown hashes, malformed schemas, and changed checker bytes
cannot borrow another qualified entry. The legacy exception retains only its
one exact pre-existing hash, not a general unqualified authorization mechanism.

## Regenerating

```
cd crates/trust-cg-verify
targo --unverified run --release --bin regen_verdict_db
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

## Bound-memory form certificates (`bound_memory_certs/`)

Owner ruling (2026-09-29): an AArch64 bound-memory row — a pair `LDP`/`STP`
or a scalar `LDR`/`STR` — is credited only by a formal proof, never by
sampling (`bound_memory_authority`). The proofs are the form theorems of
`aarch64_pair_memory_forms` (21 forms) and `aarch64_scalar_memory_proofs`
(64 attributable forms; the literal load is never attributed). Equal-width
store forms of the two register banks are one formula, so the 85 forms are
72 exact queries, and the set carries one certificate per query. A
certificate proves a FORM; a row is credited through it only when the row's
own in-process refutation check ran and held (the pair lane's concrete-word
obligation; the instruction-derived obligation of a general-purpose scalar
form; or, since L04-P1, the exact word-bound memory-effect decomposition of an
`H`/`S`/`D`/`Q` scalar form) and the word that check judged decodes to the
certified form. Every attributable form now has such a check.

The set follows the canary conventions above — schema-v3 `tcg-lrat-cert-v3`
certificates (exact SMT2, bit-blasted CNF, trimmed DRAT), a
`tcg-canary-cert-manifest-v2` `manifest.v1` binding each file to its complete
SHA-256, exact-query SHA-256 and producer AY SHA-256, reviewed
`(target, checker SHA-256)` authorizations, exact-query lookup, independent
`drat-trim` replay before the first credit in each process, and the same kill
switches — with three deliberate differences:

- **A separate manifest.** Regenerating the canary manifest over a changed
  corpus drops every checker qualification it carries for hosts this machine
  cannot replay on. This set's manifest records the checkers that replayed
  all 72 of its bodies: `aarch64-apple-darwin`
  `0f634db2aed73a915aa0c0f76258d84801385b15416ee608219df01af6962d20` (the
  canary set's legacy identity) and `aarch64-unknown-linux-gnu`
  `2aeaf98d78db430ebe805b6457d2d6016b1b18aa9ede74234eea0a1f3f1b8722`
  (1eb6928aa). The canary set's other host-qualified checkers
  (`aarch64-apple-darwin 6933827a…`, `x86_64-apple-darwin`,
  `x86_64-unknown-linux-gnu`) are not authorized here: another host's checker
  credits no bound-memory row until it replays the complete set and is
  reviewed into the manifest (`regen_bound_memory_certs` run on that host
  replays every payload with its checker and, the corpus being unchanged,
  keeps the existing authorization and adds that host's). On an unqualified
  host every bound-memory row misses fail closed with `a checker-identity
  miss, not a proof gap`, and exactly one test is red,
  `bound_memory_set_binds_the_exact_runtime_checker_bytes`, naming the
  host's identity and that command. Every test that observes bound-memory
  credit asks `bound_memory_authority::bound_memory_checker_qualification`
  which outcome to expect and asserts the fail-closed one there (measured by
  running the suites with this manifest's checker line replaced; see the
  2026-09-29 report).
- **Bodies on disk, compressed.** The 72 certificates are ~409 MB of text
  (the largest, `pairmem_ldp_offset_fpr_w16`, 44.8 MB). They are committed
  zstd-compressed (`<file>.lratcert.zst`, ~54 MB) and are not embedded: only
  the manifest is. A consumer reads and decompresses only the body its exact
  query selects, and uses it only after its complete-file SHA-256 (of the
  DECOMPRESSED text) equals the embedded manifest's. A binary run away from
  its source tree finds no body and credits nothing.
- **Replay only under proof promotion.** Only the compiler's
  `SourceBoundReplay` policy (`VerificationConfig::for_proof_promotion`)
  replays these certificates; an evaluation-only walk credits no bound row.
  Replay costs one checker run per form per process (0.6 s to 24 s per form,
  measured under load average ~100).

Regenerate with
`scripts/trust_cargo.sh run --release -p trust-cg-verify --bin
regen_bound_memory_certs` (`--only <substring> <out-dir>` stages a subset out
of tree; `TCG_BOUND_MEMORY_REGEN_ALL=1` forces fresh AY production). A query
AY cannot refute into a checker-accepted DRAT proof gets no file, and its rows
stay unverified. Commit every `.lratcert.zst` and `manifest.v1`.

## Atomic form certificates (`atomic_memory_certs/`)

The 46 single-instruction AArch64 atomic opcodes (`LDAR{,B,H}`, `STLR{,B,H}`,
`CAS*`, `SWP*`, `LD<op>*`; ledger `X-OPCODES-P2`) are memory rows of the same
kind and take the same Formal-only rule (`bound_memory_authority`, atomic
family). Their proofs are the 48 form theorems of `aarch64_atomic_forms`
(12 operations x 4 access widths; the ordering bits do not change the value
semantics, so the four orderings of an operation share its form): the
returned old value at every register byte and the memory left at every query
address, over a chain-of-points memory, against the machine-IR intent. A row
is credited through a certificate only when its word-bound decomposition
(`aarch64_atomic_effect`) held exactly in process and the word decodes to the
certified form.

The set follows the bound-memory conventions above (compressed bodies on
disk, embedded manifest, replay only under proof promotion) with its own
`manifest.v1`, for the reason the bound-memory set is not part of the canary
set: adding 48 entries to the bound-memory corpus would have dropped its
`aarch64-unknown-linux-gnu` and legacy Darwin qualifications. This manifest
authorizes only `aarch64-apple-darwin`
`f075353bccb02de692091e97cc35493266f6119a9b7546bff95dde0ecc52a226`, the
checker that replayed all 48 bodies; on any other host every atomic row misses
fail closed and `atomic_memory_set_binds_the_exact_runtime_checker_bytes` is
red until that host replays the set. Producer: the Trust 9192 package's AY
0.26.0 build 9624 (`40e852cc…ac7a8`); 48 of 48 queries certified in 24 s (3
jobs), 7.1 MB committed.

Regenerate (or qualify another host) with `scripts/trust_cargo.sh run
--release -p trust-cg-verify --bin regen_bound_memory_certs -- --set atomic`.

## NEON structure form certificates (`neon_memory_certs/`)

The two NEON one-register immediate post-index rows (`NeonLd1Post`,
`NeonSt1Post`: `LD1`/`ST1 {Vt.<T>}, [Xn|SP], #<bytes>`; ledger `L04-P1`) are
memory rows of the same kind and take the same Formal-only rule
(`bound_memory_authority`, NEON structure family). Their proofs are the 14
form theorems of `aarch64_neon_structure_forms` (load/store x the seven
arrangements the encoder accepts: `8B`, `16B`, `4H`, `8H`, `2S`, `4S`, `2D`):
the element loop of the encoded fields against the operands' `LDR`/`STR
Dt|Qt` intent, at every register byte (loads, including the zeroed upper half
of a 64-bit transfer) or every query address (stores), and the written-back
base. A row is credited through a certificate only when its word-bound
memory-effect decomposition (`aarch64_memory_effect`, L04-P6) held exactly in
process and the word decodes to the certified form.

The set has its own `manifest.v1` for the reason the atomic set does: adding
14 entries to the bound-memory corpus would have dropped that manifest's
`aarch64-unknown-linux-gnu` and legacy Darwin qualifications. This manifest
authorizes only `aarch64-apple-darwin`
`f075353bccb02de692091e97cc35493266f6119a9b7546bff95dde0ecc52a226`, the
checker that replayed all 14 bodies; on any other host every `LD1`/`ST1` row
misses fail closed and `neon_memory_set_binds_the_exact_runtime_checker_bytes`
is red until that host replays the set. Producer: the Trust 9192 package's AY
0.26.0 build 9624 (`40e852cc…ac7a8`); 14 of 14 queries certified in 34 s (3
jobs, load average 63; 71.6 G instructions retired, 2.29 GB peak RSS), 5.4 MB
committed.

Regenerate (or qualify another host) with `scripts/trust_cargo.sh run
--release -p trust-cg-verify --bin regen_bound_memory_certs -- --set neon`.
