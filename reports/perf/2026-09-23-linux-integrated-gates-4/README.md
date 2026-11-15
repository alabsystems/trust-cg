# Integrated Linux gates before the fifth main push — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `ece600993390fbe4dcd5710ade5515033160485b`,
which is origin/main `ba9e57cd7` plus four merged branches, each reviewed
adversarially, repaired and then independently re-verified:

- TLS-model link controls (L02-P9): classified `tls-model-mismatch` and
  `tls-symbol-type-mismatch` linker diagnostics. The pre-link refusal of
  local-exec TLS inputs to a shared link now covers every GNU ld 2.42
  spelling of a driver-owned option. A link with a local-exec input is staged
  and its output read back.
- Native NEON LD1/ST1 post-index execution through `neon_fmap`
  (X-OPCODES-P11), a new floor target.
- Native TrustIR ARC operations against a C counting runtime (L05-P3), a new
  floor target.
- A kernel page-protection witness in the installed JIT binding
  (L11-P6). The follow-up commit `5385d88e2` orders `/proc/self/maps` rows
  against the running maximum end.

## Linux regression floor

`scripts/check_linux_aarch64.py` passed all **147 required target families
and 864 Rust tests** (previously 145 and 839). Source fingerprint
`7790bc2e2dfef696adfa64dc9949ff288e197d48961662eaa5e8dee2d3dc2a52` was
identical before and after the run. The run took 581 seconds of target wall
time (07:50:45Z to 08:00:32Z), with a highest sampled resident set of
173 MiB. All four controls were on, and the AY/Clean and dependency
identities did not change. The new or changed targets passed:

| Target | Tests |
| --- | ---: |
| `e2e_aarch64_arc_ops_linux` | 6/6 |
| `neon_ld1_st1_post_execution` | 4/4 |
| `jit_wx_refusal` | 10/10 |
| `link_options` | 14/14 |
| `e2e_aarch64_elf_tlsie` | 11/11 |
| `e2e_aarch64_link_runtime` | 21/21 |
| `trust_ir_construct_inventory` | 15/15 |

An earlier floor run at `722e7611f` also passed 147/147. That source
predated the witness ordering fix and the second L02-P9 repair. It is not
archived.

## Library suites

On the same checkout, `cargo test -p trust-cg-codegen -p trust-cg-lower --lib`
passed:

- codegen: 4,089 passed and 1 ignored (the pre-existing
  `raw_machir_request_cache_real_exhaustive_campaign`);
- lower: 1,879 passed.

`cargo test -p trust-cg-cli --bins` passed 29/29.

## Not run

The bridge lane was not run. The rustc backend links `trust-cg-codegen` and
`trust-cg-lower`, but none of the changes is on its object-emission path.
They are in the JIT compile service and page witness, the CLI link driver,
comment edits in `trust-cg-lower/src/adapter.rs`, and test targets. The last
bridge run is the one in
[the fourth push's gate record](../2026-09-23-linux-integrated-gates-3/README.md).

## Known L02-P9 boundary at this source

An independent check of the second L02-P9 repair confirmed its claims and
found no regressions. It also found two routes that still let trust-cg
write a local-exec shared library whose user reads the wrong thread-local:

- **Response file in a typed value:** a typed `--rpath` or `--soname` value
  beginning with `@` is expanded by `cc` as a response file.
- **Unscanned object inputs:** local-exec objects that reach the link other
  than as positional inputs are never examined (inside a `-Wl` group, as
  `-l:<file>`, as archive members, through a linker script, or as shared
  libraries).

A third repair is in progress. The documents at this source describe the
checked inputs less precisely than that. L02-P9 stays PARTIAL.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.

```sh
PKG=$HOME/.local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23
PATH="$PKG/bin:$HOME/.cargo/bin:$PATH" env -u RUSTFLAGS -u CARGO_TARGET_DIR -u RUSTC -u RUSTC_WRAPPER \
  python3 -B scripts/check_linux_aarch64.py --require-clean --max-rss-gib 16 \
    --require-offline-deps --require-proof-tools --jobs 2 --out /path/outside/source/run8
cargo test --locked --offline -p trust-cg-codegen -p trust-cg-lower --lib
cargo test --locked --offline -p trust-cg-cli --bins
python3 scripts/check_evidence_archive.py reports/perf/2026-09-23-linux-integrated-gates-4
```

`records/run8/` holds the complete floor output; `records/lib-i5.log.gz` and
`records/cli-bin-i5.log.gz` hold the library transcripts.
