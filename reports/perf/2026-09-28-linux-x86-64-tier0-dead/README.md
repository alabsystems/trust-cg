# The committed tier-0 verdict DB cannot be consulted on this host, which is why the reconstructed route never credits (2026-09-28)

`crates/trust-cg-verify/verdict_db/tier0.vdb` is 6.3 MB of committed evidence,
8606 lines, and it holds rows named EXACTLY what the `core` census refuses on:

```
entry 201 RECONSTRUCTED x86_64 Copy_64 -> MovRR (real-operand)
entry 201 RECONSTRUCTED x86_64 Copy_64 -> MovRR32 (real-operand)
```

The census refusal text is `RECONSTRUCTED x86_64 Copy_64 -> MovRR (real-operand)`
found no counterexample in 100000 sampled inputs — the same obligation, by name.
So the evidence exists and is not consulted. This is why.

## Tier-0 rows are keyed to the SOLVER IDENTITY that wrote them

`verdict_db.rs` builds the in-memory index by hashing the DB's OWN header
identity with each row's query:

```rust
.map(|e| verdict_cache_key_v2(&parsed.solver_identity, &e.smt2))
```

and `ay_bridge.rs` defines that key as

```rust
hasher.update(b"tcg-proof-cache-v2\0");
hasher.update(solver_identity_hex.as_bytes());
hasher.update(b"\0");
hasher.update(smt2.as_bytes());
```

while the per-compile lookup (`tier0_candidate_verified`) computes the key from
the LIVE solver: `solver_identity_hash(solver_path)`.

The committed DB's header reads

```
solver-sha256: 6d6a8b6c7531420e8e3277f22fcdf0c9b5e656731b201b5e6e413df714aaf842
solver-version: build.version=0.11.0
provenance: PROOF-4 (registry) + PROOF-5 (parametric reconstruction) regen, ay 0.11.0
```

so every stored key is `H(ay-0.11.0-hash, query)`, and every lookup on this host
is `H(live-hash, query)`. They cannot match. **The DB misses on every row, for
every obligation, on any host not running that exact 0.11.0 binary** — it has been
dead weight rather than a miss-by-content.

That is the mechanism behind the 2849 sampling-route refusals: the reconstructed
route's only two paths to `Formal` are a portable DRAT certificate or a tier-0
candidate revalidated live, and `discharge_registry_obligation` "spends no solve on
a miss", so it falls straight through to the statistical sweep — which
`STATISTICAL_EVIDENCE_IS_NOT_CREDIT` has made non-credit since upstream
`8d4e83b54`.

## Regenerating it is attemptable here for the first time, and blocked at one seed

Regen needs AY ADMITTED in the regen process. The stock-built root workspace
records no toolchain AY identity (`[TCG-AY-IDENTITY-UNRECORDED]`), but the same
workspace builds under `RUSTC=<stage2>/bin/trustc` and then records one. Built that
way, `regen_verdict_db` admits the solver and re-proves 1865 registry obligations
(the rebuild must FOLLOW installing the solver, or it refuses with
`[TCG-AY-IDENTITY-MISMATCH]` naming both digests).

It fails at a SEED:

```
pass[x86-popcnt-expand]: popcount SWAR expansion matches spec on x86_64 (i32):
fail-closed: solver unknown ((:reason-unknown (incomplete self-check-rejected)))
```

and the tool writes nothing unless every seed discharges `Verified`. The
exemption mechanism does not apply: `exemptions.txt` is for REGISTRY obligations
the solver did not discharge (167 were auto-exempted in this run), while the five
canary seeds are mandatory by design — they are what proves the solver works.

NOT a regression from today's bump. Extracting that seed's query out of the
committed DB and running it under both solvers gives the same verdict:

| solver | popcnt SWAR (i32) seed |
| --- | --- |
| ay 0.26.0+build.9624 | `unknown`, `unsupported hole rule` |
| ay 0.27.0+build.11385 | `unknown`, `unsupported hole rule` |

## And a fresh DB would not be enough on its own

The 7 roots that block every beat-llvm program need **17 distinct opcodes**
covered. tier-0's x86-64 reconstructed surface is 29 rows covering 18 opcodes, and
the overlap is only **6 of the 17**:

| needed by the 7 roots | in tier-0 |
| --- | --- |
| MovRR, MovRR32, AddRR, XorRR, SubRR, Movzx | **yes** |
| MovMR, MovRM, Lea, LeaRip, Jcc | no |
| ShrRI, ShlRI, ImulRRI, CmpRI, AddRI, Mul | no (it has the RR forms: ShrRR, ShlRR, ImulRR) |

So the enumerated reconstruction surface covers register-register ALU and the
extensions, and excludes the IMMEDIATE forms, the memory forms, `Lea`/`LeaRip` and
`Jcc`. Widening `enumerate_reconstruct_regen_obligations` is what would close that,
and what gets committed as evidence is an authority decision.

## The complete chain to whole-program compilation, with every link named

1. **tier-0 is unusable** — keyed to a solver identity absent from this host.
   Regeneration is the fix and is now attemptable.
2. **Regeneration is blocked by one AY capability**: a checkable Alethe proof for
   the popcnt SWAR expansion. Same family as `MulU32`/`MulI16` — bit-blasted
   arithmetic AY decides but cannot express as a derivation, exporting
   `Trust`/`Hole`, which strict certification refuses and an independent checker
   cannot replay.
3. **Even regenerated, tier-0 covers 6 of the 17 opcodes** the blocking roots
   need. Closing the rest means widening the enumerated reconstruction surface, or
4. **the source-bound body domain** — which is gated on BOTH the source and machine
   sides (each carries its own `stack_slots.is_empty()` refusal), so it needs
   machine-side frame modelling, not a condition deleted.

Every link is now identified, measured where measurable, and attributed. (1) is a
defect. (2) is solver work. (3) and (4) are evidence-authority and theorem work.

## Provenance

`ay 0.27.0+build.11385` and Clean `e75141b7b` installed; bridge rebuilt against
them; stage2 `trustc 1.99.0-dev (3a3e781fe 2026-09-14)`; Trust repo `ceb94fe99`;
`PATH=/usr/bin:$PATH CC=/usr/bin/gcc`. The tier-0 reading is from the committed
file and the two source sites quoted above; the seed comparison ran both solver
binaries on the query extracted from that file.
