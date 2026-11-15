# Integrated Linux gates before the third main push — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Three lanes ran on clean source `8d380377aaa35f686ab74252e77a28ee46f37e66`.
That commit is origin/main `3058c0de4` plus two merged branches. The first adds
whole-module AArch64 DWARF parameters and variables with gdb correspondence
(L03-P4). The second adds the Linux ELF `thread_local` bridge twin
(L06-P4, L03-P7).

## Linux regression floor

`scripts/check_linux_aarch64.py` passed all **145 required target families
and 827 Rust tests**. Source fingerprint
`703d4c655a02e0d2257ada62c48236caa40ad7561babc67079cc4c4647e2aef0` was
identical before and after. The run lasted from 2026-09-23T03:42:06Z to
03:51:09Z: 534 seconds of target wall time, highest sampled resident set 177 MiB.
All four controls were on, including `--require-proof-tools` with AY/Clean
identities unchanged. `aarch64_elf_dwarf` passed 12/12 and
`e2e_aarch64_elf_debugger_linux` passed 2/2 with its module gdb leg.

## Codegen library suite

`cargo test -p trust-cg-codegen --lib` passed on the same checkout: 4,063
passed, 0 failed, 1 ignored (the pre-existing
`raw_machir_request_cache_real_exhaustive_campaign`). No maintained gate runs
this suite, so it is recorded here; the transcript is `records/codegen-lib.log`.

## Bridge lane

`scripts/check_linux_aarch64_bridge.py` rebuilt the private backend from this
source with the sealed Trust `a62ae50d` package. The backend SHA-256 is
`b5d43f1b36075532a584491041308ba76413d3059751055ede5dc8451e4da79b`. The
runner now requires two targets:

- **`tls_thread_local_linux` passes 2/2** on this backend: the new Linux
  thread-local twin.
- **`aarch64_c_fnabi_aggregate_linux` fails** at the known
  `aliased_f32_read` O0 `[TCG-PROOF-465]` refusal (L06-P1), unchanged from
  the [2026-09-22 checkpoint](../2026-09-22-linux-bridge-checkpoint/README.md).

The lane verdict is FAIL for that reason only. `records/bridge/` holds its
report and logs; the backend snapshot is hash-identified, not archived.

```sh
PKG=$HOME/.local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23
PATH="$PKG/bin:$HOME/.cargo/bin:$PATH" python3 -B scripts/check_linux_aarch64.py --require-clean \
  --max-rss-gib 16 --require-offline-deps --require-proof-tools --jobs 2 --out /path/outside/source/run5
PATH="$HOME/toolchains/trust-a62ae50d/bin:$PKG/bin:$HOME/.cargo/bin:$PATH" \
  python3 -B scripts/check_linux_aarch64_bridge.py --require-proof-tools --out /path/outside/source/bridge4 \
  --target-dir /path/outside/source/cache --jobs 4 --timeout-seconds 7200
python3 scripts/check_evidence_archive.py reports/perf/2026-09-23-linux-integrated-gates-2
```

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.
