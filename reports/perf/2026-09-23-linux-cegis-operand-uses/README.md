# AArch64 CEGIS: operand-0 reads and non-degenerate obligations — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These records gate `f8c60b01d597f74cc444b537535367f706cd1405`
("verify(cegis): count operand-0 reads and build obligations from the
windows") on the Linux AArch64 host. Its parent is `69ce55479`, the linear
walk-facts index on top of the solver-budget fix `debabccd9`. The CEGIS pass
is opt-in (`--cegis-superopt=<SECS>`), but it ships.

## What was wrong

**Wrong code.** The Layer B (`Movz` + `AddRR`) and Layer C (`Movz`/`Movn`
+ `Movk`* + `AndRR`) matchers splice the constant's materializer out when
the rewritten instruction is its only reader. `count_vreg_uses`, the indexed
walk facts and cache replay counted reads as "every operand after operand
0". A store, compare, conditional branch, tied `Movk` or any of the other
119 opcodes whose operand 0 the shared role model reads therefore went
uncounted. The constant looked single-use, and the rewrite deleted a
definition that was still read.

Exact read counting exposes a dual defect. The def maps of Layers A and B
and the Layer C scan also took operand 0 as the only definition, and the
Layer C scan compared register classes exactly. A write to the constant's
register at operand 1 (`LdpRI`, `LdpPostIndex`, LSE, the LL/SC pseudos: 62
opcode/operand rows), or under another class of the same id, was invisible
to them. Only the old over-count of those operands as reads had kept that
latent.

Layer B also admitted any `imm16`. A `Movz #5000` feeding an `AddRR` became
an `AddRI #5000` that the encoder rejects, which failed the compile.

**Proof vacuity.** Layer B discharged `y + k == y + k` and Layer C
`x & m == x & m`, both built from the matcher's own constant, so no matcher
bug could be refuted.

## The fix

Reads and definitions now come from the shared operand-role model
(`trust_cg_opt::effects::aarch64_for_each_use_position` and
`aarch64_for_each_def_position`). That covers the arena read counts, the
indexed facts, the Layer A/B reaching-definition maps and the Layer C
materializer scan. Any modeled definition of the id, under any class,
forgets the constant. Layer C discounts the chain's own tied `Movk` reads.
Cache replay re-runs the search's matchers on the current body and splices
only the window they admit, of the recorded length. The recorded body is
still replayed as recorded, as `cegis_stats_trace` pins for #492. Layer B
admits only immediates that `ADD #imm12` encodes. `CEGIS_SEARCH_SEMANTICS_REVISION`
is now 3: revision 2 entries in the host-shared cache can hold the
wrong-code rewrites, so they must never replay.

Every layer's obligation now comes from one window interpreter,
`crates/trust-cg-verify/src/cegis_pass_obligation.rs`:

- the **original side** runs the materializer from its encoded `imm16`/`hw`
  fields, then the `MulRR`/`AddRR`/`AndRR`;
- the **replacement side** encodes the immediate as `trust-cg-codegen` does
  (`imm12`, `sh = 0`; `N:immr:imms`), then decodes it (`ZeroExtend(imm12)`;
  the Arm ARM `DecodeBitMasks`, written independently of the encoder's
  search);
- the observed register is the consumer's destination.

An unencodable replacement or an `X == X` pair builds no obligation. The
encoder mirrors equal the real encoder's words for every logical immediate
(1,302 at 32 bits, 5,334 at 64 bits) and across the `imm12` boundary.

## Pre-fix native evidence

`prefix-native-mask-readers.log.gz` runs the new native row on the fixed
source with only `cegis_pass.rs` restored from `69ce55479`, using a fresh
CEGIS cache. At O2 the constant folder turns `(0x55555555 << 32) |
0x55555555` into `Movz #0x5555` plus three `Movk`s. That mask is ANDed, and
also stored (`cegis_mask_store`) or compared at operand 0
(`cegis_mask_compare`). The C driver calls each function with `x2`–`x7` set
to a poison value. The reference build (CEGIS off) passes. The revision 2
CEGIS build emitted:

```text
cegis_mask_store:   and x0, x0, #0x5555555555555555
                    str x2, [x1]            // x2 never written
cegis_mask_compare: and x3, x0, #0x5555555555555555
                    cmp x2, x1              // x2 never written
```

The driver saw these mismatches, among others:

```text
cegis_mask_store(0) = 0, stored 0xbadc0ffee0ddf00d; want 0, stored 0x5555555555555555
cegis_mask_compare(0xffffffffffffffff, 0x5555555555555555) = 0xffffffffffffffff; want 0x5555555555555555
cegis_mask_compare(0x123456789abcdef, 0x5555555555555555) = 0x123456789abcdef; want 0x101454501014545
```

Before the poison was added, an earlier draft passed by accident: the
preceding call had left the mask in `x2`.

`prefix-native-wide-add.log.gz` shows the unencodable `AddRI` under the same
setup:

```text
Pipeline(Encoding("... invalid operand at index 2 for AddRI: add/sub immediate 5000 out of range [0, 4095] in function cegis_wide_add ..."))
```

At `f8c60b01d` both rows pass against the oracle
(`codegen-e2e-cegis-run*.log.gz`). The CEGIS object still differs from the
reference, because the control function `cegis_mask_only` is fused, so CEGIS
demonstrably ran.

Unit-level controls replace only `for_each_vreg_read` or `for_each_vreg_def`
with the revision 2 model. With revision 2 reads, 5 regression tests fail
(`control-legacy-reads.log.gz`). With revision 2 definitions, 2 fail
(`control-legacy-defs.log.gz`), including the 62-row later-definition test.

## Obligations, certificates and the mutation control

`obligation-certificates.log.gz` runs the solver-backed obligation tests
with `TCG_NO_PROOF_CACHE=1` under `strace -f -e trace=execve`; the trace is
`obligation-execve.log.gz`. A representative Layer B obligation (32-bit,
`Movz #7`):

```text
source: (bvadd v0 (bvshl ((_ zero_extend 16) (_ bv7 16)) (_ bv0 32)))
target: (bvadd v0 ((_ zero_extend 20) (_ bv7 12)))
```

and Layer C (32-bit, `Movz #0x5555; Movk #0x5555, lsl 16`):

```text
source: (bvand v0 (bvor (bvand (bvshl ((_ zero_extend 16) (_ bv21845 16)) (_ bv0 32)) (_ bv65535 32))
                        (bvshl ((_ zero_extend 16) (_ bv21845 16)) (_ bv16 32))))
target: (bvand v0 (_ bv1431655765 32))
```

**Verdicts.**
- *Payload obligations.* All 9 returned `Equivalent`: Layer A at 32 and 64
  bits, Layer B for `#7` and `#0xFFF` at both widths, Layer C for a
  `Movz`+`Movk` mask, a `Movz`+`Movk`×3 mask and a `Movn` mask. None is
  structurally `X == X`.
- *Legacy obligations.* The 3 revision 2 obligations also returned
  `Equivalent`: B and C are degenerate `X == X`, and A is `x*0 == 0`.
  Neither side reads the replacement.
- *Certificate replay.* The trace records 12 `ay -smt2 … --strict-proofs
  --proof … --proof-format alethe` queries (24 execs: each query is exec'd
  twice). Each is followed by a `clean cert verify-external`. With the 2
  `clean` runs before the first query (the checker's control probe), that
  makes 14 `clean` runs: one fresh AY UNSAT per `Equivalent` above, each
  accepted by Clean.
- *Mutation control.* All 20 corrupted replacements the interpreter can
  model were refuted by AY with no concrete seeds (`NotEquivalent`,
  `found_by_concrete: false`), through the resident `ay --incremental`
  server. They cover:
  - a wrong immediate: `AddRI` `#7`→`#6`, `#0xFFF`→`#0xFFE`; a `Movz #1`
    Layer A result; an `AndRI` mask rotated one bit;
  - a wrong register: the replacement reads the removed constant register;
  - a wrong operation: `AddRI`↔`AndRI`.

  Each model distinguishes the two sides. The 3 `AndRI`→`AddRI` swaps of a
  logical-immediate mask have no `imm12` encoding and are rejected before
  any query.

The same controls run through the whole pass in `cegis_layer_a`,
`cegis_layer_b` and `cegis_payload`. There each corrupted rewrite ends
`Complete { committed: false }` with `rejected == 1` and no errors. The
concrete phase rejects it first.

## Gates

All ran at `f8c60b01d` with a clean tree:
`PATH=<prefix>/bin:$HOME/.cargo/bin:$PATH`, `cargo --locked --offline -j 8`,
stock Rust 1.97.1, AY 0.27.0 and Clean 0.9.0 from
`~/.local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23`.

| Gate | Result |
| --- | --- |
| `cargo test -p trust-cg-verify --lib cegis` | `test result: ok. 92 passed; 0 failed; 0 ignored; 0 measured; 4111 filtered out` |
| `cargo test -p trust-cg-verify --lib cache` | `test result: ok. 26 passed; 0 failed; 0 ignored; 0 measured; 4177 filtered out` |
| `--test cegis_cache_codec` | `test result: ok. 21 passed; 0 failed` |
| `--test cegis_layer_a` | `test result: ok. 3 passed; 0 failed` |
| `--test cegis_layer_b` | `test result: ok. 6 passed; 0 failed` |
| `--test cegis_pass` | `test result: ok. 5 passed; 0 failed` |
| `--test cegis_payload` | `test result: ok. 11 passed; 0 failed` |
| `--test cegis_shared_cache` | `test result: ok. 6 passed; 0 failed` |
| `--test cegis_stats_trace` | `test result: ok. 7 passed; 0 failed` |
| `cargo test -p trust-cg-codegen --test e2e_cegis_superopt` run 1 (cold `TRUST_CG_CEGIS_CACHE`) | `test result: ok. 9 passed; 0 failed` |
| run 2 (same cache, replay) | `test result: ok. 9 passed; 0 failed` |
| run 3 (same cache, replay) | `test result: ok. 9 passed; 0 failed` |
| `cargo test -p trust-cg-codegen --lib` | `test result: ok. 4104 passed; 0 failed; 1 ignored` |
| `cargo test -p trust-cg-cli --bin trust-cg` | `test result: ok. 29 passed; 0 failed` |
| `bash scripts/check_fmt.sh` | `check_fmt: OK` |
| `python3 scripts/check_documentation.py --write`, then `--check` | no drift after `--write`; `--check` current |
| `python3 scripts/generate_diagnostics_inventory.py --check` | current |

## Residuals

- **Outside the proof.** Two facts rest on structural checks rather than the
  proof: that the removed materializer is the reaching definition, and that
  nothing else reads it. They come from the shared role model over the whole
  arena, and are checked against the allocator partition for every opcode,
  but they are not proven. So does the window interpreter's semantics for
  its eight opcodes, which no independent decoder checks. The
  `aarch64_value_decode_proofs` decoder models neither logical immediates
  nor move-wide.
- **Cache replay.** Replay applies the recorded replacement body without
  re-proving it. The cache key binds the function body and revision; a
  tampered entry could substitute a different body. That is by design
  (#492). *Closed at `a99183cff`: see "Cache integrity" below.*
- **Orphan copies.** Arena reads by instructions no block schedules still
  count. Orphaned block-parameter copies therefore keep the natural O2 Layer
  B shape (and the 32-bit Layer C shape) from ever being a candidate.
  Before and after the fix, this is conservative and costs rewrites. No
  natural trust-ir shape reached the Layer B wrong code; its rows are unit
  and pass-level.
- **x86-64 pass.** `TCG_CEGIS_X86` still discharges `op(x, k) == op(x, k)`,
  as `LIMITATIONS.md` now states.

## Retained files

- `records/verify-lib-cegis.log.gz`, `records/verify-lib-cache.log.gz`,
  `records/verify-cegis-integration.log.gz`
- `records/codegen-e2e-cegis-run1.log.gz`, `…-run2…`, `…-run3…`
- `records/codegen-lib.log.gz`, `records/cli-bin.log.gz`
- `records/check-fmt.log.gz`, `records/docs-write.log.gz`,
  `records/docs-check.log.gz`, `records/diagnostics-check.log.gz`
- `records/obligation-certificates.log.gz`, `records/obligation-execve.log.gz`
- `records/prefix-native-mask-readers.log.gz`,
  `records/prefix-native-wide-add.log.gz`
- `records/control-legacy-reads.log.gz`, `records/control-legacy-defs.log.gz`

## Cache integrity — 2026-09-23

The records in `records/cache-integrity/` gate
`a99183cff13e14be0035a56720687bdf934f0946` ("verify(cegis): replay only the
body the matcher rebuilds; require a private cache root") on the same host.
Its parent is `e022aae6e`, this archive's first commit. It closes the
**Cache replay** residual above.

### What was wrong

**Wrong code.** A CEGIS cache hit applied each recorded replacement body as
recorded. Replay already re-ran the search's matcher on the current body to
find the window it splices, but it discarded the replacement the matcher
built. Entries carry no MAC, and the codec checks only their format. The
cache wrote them under the process umask: `0775` directories and `0664`
files on this host (umask `002`). Without `HOME` and `XDG_CACHE_HOME` the
root is `/tmp/.trust-cg-cegis-cache`, which every user of the host shares.

`tamper-before.log` runs the native row
`cegis_native_operand_zero_readers_keep_the_materialized_mask` at
`e022aae6e` with a clean tree and a fresh `TRUST_CG_CEGIS_CACHE`. It then
overwrites the 8 bytes at offset 88 of entry `026a893175409706874208139e0e1223`
(the `cegis_mask_only` rewrite, `AndRI #0x5555555555555555`) with
`0x3333333333333333`, which is still a logical immediate, so the entry still
decodes. The rerun links the tampered body:

```text
cegis_mask_only(0xffffffffffffffff) = 0x3333333333333333; want 0x5555555555555555
cegis_mask_only(0x5555555555555555) = 0x1111111111111111; want 0x5555555555555555
cegis_mask_only(0xaaaaaaaaaaaaaaaa) = 0x2222222222222222; want 0
cegis_mask_only(0x123456789abcdef) = 0x123012301230123; want 0x101454501014545
MISMATCH
```

The entry kept the tampered bytes.

### The fix

- **Replay applies only the matcher's own body.** `apply_cached_rewrite`
  keeps the replacement the matcher rebuilds. It applies the rewrite only if
  that body's cache projection equals the recorded blob: the opcode, every
  register id and class, and every immediate. The check runs before any
  splice, and the rebuilt body is what gets written. Any other entry is
  stale. The partial replay is rolled back, the function is searched again,
  and a complete search rewrites the entry. Production no longer decodes a
  blob into an instruction. New counters: `cache_stale` and
  `repeated_schedule_skips`.
- **The cache root must be private.** A root is used only if the directory it
  resolves to (canonicalized, and used by that path afterwards) is owned by
  the current user and is not group- or world-writable. Otherwise the
  process warns once (`refusing untrusted shared cache root`) and uses an
  in-memory cache. `FileCache` creates directories `0700` and entries `0600`
  through an `O_EXCL` staging file; the lock and probe files are `0600` too.
  `default_arc()` resolves the root path on the calling thread but opens the
  root on first use, so a compile without CEGIS neither creates it nor
  warns.
- **Repeated schedules are skipped.** A function whose block schedule lists
  an instruction id twice is not looked up, searched or written. Every layer
  rewrites in place in the shared arena, so a rewrite also changed the other
  copy, whose window was never checked.
- **No revision bump.** `CEGIS_SEARCH_SEMANTICS_REVISION` stays 3 and
  `CegisCacheEntry::VERSION` stays 7. The search records the same entries.
  An honest entry is exactly the body the matcher rebuilds, so it still
  replays. A skipped function never reads its entry. The tampered entry
  above has the same key before and after the fix.

### What #492 protected

The v4 entry format (#492) made an entry a self-describing rewrite plan:
each proven rewrite records its layer, the window it consumes and its
serialized replacement body. A hit replays that plan without CEGIS and
counts a cache hit and exactly the rewrites it applied. The failure it
followed, #491, was a hit that skipped the recorded mutation and credited
phantom counts. The old test showed that the body came from the blob by
tampering the `Movz` immediate (0 to 123) and requiring the tampered body to
be applied. That assertion demanded wrong code.
`cache_entry_records_and_replays_serialized_replacement_body_issue_492` now
keeps the intent: a valid recorded body replays byte for byte on a
solver-free hit (`cache_hits` 1, `solver_calls` 0), and the hot function
equals the cold one. `cache_entry_tampered_twin_is_refused_as_stale_issue_492`
tampers the same immediate. It requires `cache_hits` 0, `cache_stale` 1, a
fresh search, the correct `Movz #0`, and a rewritten entry.

### Evidence

- `tamper-after.log` repeats the reproducer at `a99183cff` with a clean
  tree. The same entry at the same offset is patched. The rerun passes
  against the C oracle, and the entry holds `0x5555555555555555` again. The
  new root is `0700`, its shard directories are `0700` and its entries
  `0600`.
- `e2e_cegis_superopt::cegis_native_tampered_cache_entry_is_refused_and_refreshed`
  does the same in-process against its own private root. It requires the
  rerun object to be byte-identical to the honest one, the C oracle to pass,
  and the entry to be refreshed.
- `control-replay-as-recorded.log` applies `control-replay-as-recorded.diff`
  to `a99183cff` (one dirty path). The diff restores replay-as-recorded and
  changes nothing else. All four tamper rows fail: the two `replay_tests`
  rows, the #492 tampered twin and the native row. The honest #492 row, the
  apply-the-body row and the schedule rows still pass.
- `replay_tests` (unit): the matcher's body replays byte for byte, with the
  replaced instruction's source location, for Layers A, B and C. 23 tampered
  bodies are refused with the function untouched: a wrong immediate,
  destination, source, register class or opcode, an extra or a missing
  operand, and an unknown opcode. A pass-level tampered Layer C entry is
  stale, searched again and rewritten, and the honest entry then replays
  with no verifier call. Repeated-schedule detection covers one block,
  across blocks and a block listed twice. A repeated `AddRR` is skipped with
  no cache lookup, search or put, while a direct search would rewrite both
  copies.
- `cegis_cache_io` (unit) covers `0700`/`0600` creation of the root, shard,
  entry and lock. Group- and world-writable roots are refused: `0770`,
  `0775`, `0777`, `1777`, `0720` and `0702`. So is a root with another owner
  (simulated uid, and `/`). The shared temp fallback is refused, including
  `/tmp` itself and a planted `1777` copy. A symlinked root is judged, and
  used, by its target. The deferred backend does not touch the root before
  first use. `trust-cg-opt` covers private creation and the exclusive
  staging file (`opt-cache.log`).
- `codegen-e2e-default-root.log` runs the native row with no
  `TRUST_CG_CEGIS_CACHE` or `XDG_CACHE_HOME`. This host's existing
  `~/.cache/trust-cg-cegis` was created `0775` by earlier builds, and the run
  refuses it with the warning line. The row still passes on the in-memory
  cache. The root is judged before the write probe, so a refused root is
  never written. The directory itself is shared with other builds on this
  host, so its timestamps are not evidence either way.

### Gates

All ran at `a99183cff` with a clean tree and the same toolchain and prefix
as above.

| Gate | Result |
| --- | --- |
| `cargo test -p trust-cg-verify --lib cegis` | `test result: ok. 103 passed; 0 failed; 0 ignored; 0 measured; 4111 filtered out` |
| `cargo test -p trust-cg-verify --lib cache` | `test result: ok. 32 passed; 0 failed; 0 ignored; 0 measured; 4182 filtered out` |
| `--test cegis_cache_codec` | `test result: ok. 21 passed; 0 failed` |
| `--test cegis_layer_a` | `test result: ok. 3 passed; 0 failed` |
| `--test cegis_layer_b` | `test result: ok. 6 passed; 0 failed` |
| `--test cegis_pass` | `test result: ok. 5 passed; 0 failed` |
| `--test cegis_payload` | `test result: ok. 11 passed; 0 failed` |
| `--test cegis_shared_cache` | `test result: ok. 6 passed; 0 failed` |
| `--test cegis_stats_trace` | `test result: ok. 8 passed; 0 failed` |
| `cargo test -p trust-cg-opt --lib --test cache_backends cache` | lib `test result: ok. 37 passed; 0 failed; 0 ignored; 0 measured; 3495 filtered out`; `cache_backends` `test result: ok. 4 passed; 0 failed; 0 ignored; 0 measured; 2 filtered out` (the four `FileCache` rows) |
| `cargo test -p trust-cg-codegen --test e2e_cegis_superopt` run 1 (fresh `TRUST_CG_CEGIS_CACHE`) | `test result: ok. 10 passed; 0 failed` |
| run 2 (same cache, replay) | `test result: ok. 10 passed; 0 failed` |
| run 3 (same cache, replay) | `test result: ok. 10 passed; 0 failed` |
| native row with the host's default root (`codegen-e2e-default-root`) | `test result: ok. 1 passed; 0 failed`; root refused |
| tamper reproducer at `e022aae6e` (`tamper-before`) | populate `test result: ok. 1 passed`; rerun `test result: FAILED. 0 passed; 1 failed` (`MISMATCH`) |
| tamper reproducer at `a99183cff` (`tamper-after`) | populate `test result: ok. 1 passed`; rerun `test result: ok. 1 passed`; entry rewritten |
| `cargo test -p trust-cg-codegen --lib` | `test result: ok. 4104 passed; 0 failed; 1 ignored` |
| `cargo test -p trust-cg-cli --bin trust-cg` | `test result: ok. 29 passed; 0 failed` |
| `bash scripts/check_fmt.sh` | `check_fmt: OK` |
| `python3 scripts/check_documentation.py --write`, then `--check` | no drift after `--write` (`tree-after-gates` is empty); `--check` current |
| `python3 scripts/generate_diagnostics_inventory.py --check` | current |

### Residuals

- **Integrity, not authenticity.** The cache is integrity-checked against
  the matcher, not signed. Replay does not re-run the solver, so a writer of
  the root can still make the pass apply a matcher candidate without its
  proof, or drop rewrites and lose optimization. The private-root rule
  limits who that writer can be.
- **Existing roots.** A root an earlier build created `0775` is refused until
  its owner runs `chmod 700`. On this host that includes
  `~/.cache/trust-cg-cegis`, so CEGIS compiles here use an in-memory cache
  until then.
- **Path checks.** The root's ancestors are not checked. A user who can write
  a non-sticky parent directory could replace the root after the check.
  Windows gets no ownership or mode check.

### Retained files

- `records/cache-integrity/tamper-before.log.gz`,
  `records/cache-integrity/tamper-after.log.gz`
- `records/cache-integrity/control-replay-as-recorded.diff`,
  `records/cache-integrity/control-replay-as-recorded.log.gz`
- `records/cache-integrity/verify-lib-cegis.log.gz`, `…/verify-lib-cache.log.gz`,
  `…/verify-cegis-integration.log.gz`, `…/opt-cache.log.gz`
- `records/cache-integrity/codegen-e2e-cegis-run1.log.gz`, `…-run2…`, `…-run3…`,
  `…/cache-modes.log.gz`, `…/codegen-e2e-default-root.log.gz`
- `records/cache-integrity/codegen-lib.log.gz`, `…/cli-bin.log.gz`
- `records/cache-integrity/check-fmt.log.gz`, `…/docs-write.log.gz`,
  `…/docs-check.log.gz`, `…/diagnostics-check.log.gz`,
  `…/tree-after-gates.log.gz`
