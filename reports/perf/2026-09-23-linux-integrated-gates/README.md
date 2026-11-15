# Integrated Linux gates before the second main push — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Two maintained lanes ran on clean source
`b591ce6e908f2933e4fec255fd68ab9fab957123`: origin/main `568a20631` with three
merged branches. They are the ELF relocated TLS templates and Linux globals twin
(L05-P10, L03-P6), linked-image byte binding in the arithmetic AOT runner
(L11-P3), and the trust-cg-lower library clippy cleanup. These are the gate
runs for pushing that content to remote main.

## Linux regression floor

`scripts/check_linux_aarch64.py` passed: **145/145 required target families and 824 Rust tests**, with
source fingerprint `d7f69fed3109bfc50c12f21f445954b142a3daa928b72f7cbe48fad17f7718ee` identical before and
after, from 2026-09-23T01:16:06Z to 01:25:08Z (525 seconds of target wall time, highest sampled
resident set 210 MiB against the 16 GiB ceiling). All four controls were on. The AY/Clean identities
were pinned through the package prefix and identical before and after. The new
`e2e_aarch64_globals_linux` passed 15/15; `e2e_aarch64_elf_link` passed 11/11 with its former TLS-template
refusal pin now a positive control; `e2e_aarch64_elf_tlsie` 8/8 and `e2e_aarch64_elf_relocation_model`
19/19 also passed. The pre-warm build ran `cargo test --no-run` for exactly these targets at the same commit.

```sh
PKG=$HOME/.local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23
PATH="$PKG/bin:$HOME/.cargo/bin:$PATH" env -u RUSTFLAGS -u CARGO_TARGET_DIR -u RUSTC -u RUSTC_WRAPPER \
  python3 -B scripts/check_linux_aarch64.py --require-clean --max-rss-gib 16 \
    --require-offline-deps --require-proof-tools --jobs 2 --out /path/outside/source/run4
```

## Arithmetic AOT matrix with linked-image binding

`scripts/check_aarch64_aot_arithmetic.py` (report schema v2) passed at the same
source. It ran 48/48 cases and 6,912/6,912 native calls. All 48 linked images
were bound to their certified objects and all 144 linked-image negatives were
refused. It accepted 9/9 original certificates and rejected 27/27 corruptions,
from 2026-09-23T01:14:57Z to 01:15:52Z. The CLI was a release build of this
source in the integration worktree, SHA-256
`f4dec51f5f0f1c7321d3ef46a8b0bcba7a8297c9452802542e5b35028f9b4958`. AY
`ec2bf181…` and Clean `8d819378…` came through explicit overrides. The
runner cannot itself prove the CLI's source (owner decision OD-13); the build
log is retained as `records/aot/release-cli-build.log`.

```sh
AY_SOLVER_PATH=$PKG/store/ay/current/bin/ay TCG_EXTERNAL_CLEAN_CHECKER=$PKG/store/clean/current/bin/clean \
  python3 -B scripts/check_aarch64_aot_arithmetic.py --trust-cg <release trust-cg> \
    --require-clean --max-rss-gib 16 --out /path/outside/source/aot2
python3 scripts/check_evidence_archive.py reports/perf/2026-09-23-linux-integrated-gates
```

## Not covered by these runs

The codegen library unit test
`test_aarch64_parallel_and_serial_multi_function_byte_identical` fails on
origin/main and on this source. Its multiply leaves have no frame proof owner
since the pair-memory credit was withdrawn. No gate runs it. The follow-up
commit that rebuilds the test on admitted affine leaves is a library-test-only
change and is not part of this floor's source; it was run separately and
passes with the pinned proof tools. Workspace-wide clippy with path
dependencies stays red: trust-cg-opt has 169 lints and trust-cg-lower's test
targets have 10.

This is regression evidence. It is not complete Linux qualification, proof
or Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.

`records/floor/` holds the complete floor output. `records/aot/` holds the
AOT report, runner log and CLI build log; the per-case objects are not copied
again.
