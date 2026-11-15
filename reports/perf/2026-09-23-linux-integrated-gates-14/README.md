# Integrated Linux gates before the fifteenth main push — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `9db72db82242143cacdd8b59b45238889b53039c`.
That source is origin/main `31f0fa52f` plus the L02-P10 closure-residual
branch. The owner had moved origin/main in two commits:
- `b61b4b291` moved trust-ir to `4f09dab8` and lowered its WS3.20
  constructs;
- `31f0fa52f` fixed a test.

The branch was reviewed adversarially and repaired, and every round was
checked by an independent verifier.

## What the branch adds

**The GOT-addressing window check covers every link input.** The
linked-image check in `link_driver::run_link` now collects every psABI
GOT-addressing relocation from every positional and traced AArch64 ELF
input. That includes `-Wl` operands, `-l:`, archive members, linker-script
inputs and grouped inputs. There are 17 kinds, pinned against the aaelf64
table, each checked against its own window:
- page forms: ±4 GiB;
- load-literal and ADR forms: ±1 MiB;
- `GOTPCREL32`: ±2 GiB.

It also refuses images that are out of reach and hold linker-written
GOT-addressing code: PLT and IPLT stubs, and the TLS-descriptor trampoline.
A defined IFUNC counts as a page-window use, so an IPLT hidden by a linker
script is refused. GNU ld 2.42 silently truncates most of these. Every
earlier verifier reproducer is now refused, and its near twin links and
runs.

**Text-offset ceiling controls.** The imm21 jump-table limit is triggered
by a real compile. The u32 block, instruction, jump-table and LSDA
ceilings are exercised through a unit-level synthetic layout.

## Linux regression floor

`scripts/check_linux_aarch64.py` passed all **154 required target families
and 960 Rust tests**. Among them, `link_options` passed 26/26,
`e2e_aarch64_link_runtime` 32/32 and `trust_ir_construct_inventory` 15/15;
the last runs under the new trust-ir pin.

The source fingerprint
`59c2484dbd7a8349e6cd09138fb0473974fa1bdcadc0f0a628e67ff2dfd1228c` was
identical before and after the run. The run took 730 seconds of target
wall time (22:10:40Z to 22:23:04Z), and the highest sampled resident set
was 339 MiB. All four controls were on, and the AY/Clean and dependency
identities did not change.

## Library, CLI and extra suites

- **Library:** codegen 4,133 passed and 1 ignored (the pre-existing
  `raw_machir_request_cache_real_exhaustive_campaign`); lower 1,889 passed.
- **CLI:** bin 30, `link_options` 26, `output_paths` 8 and
  `trust_ir_binary_container` 4 passed. The container fixtures were
  re-vendored by the owner's pin move.
- **trust-cg-verify:** the CEGIS and proof-suite targets passed.
- **Race targets:** both passed at 16 threads.

## Bridge lane

`scripts/check_linux_aarch64_bridge.py --require-proof-tools` rebuilt the
private backend from this source, including the new trust-ir pin. Its
SHA-256 is
`03a39ad25b68b44b569fea2b63553d0d7ca567e73acbded82e5148c8b05b34e3`.

- `tls_thread_local_linux` passes 2/2.
- `aarch64_c_fnabi_aggregate_linux` fails only at the known
  `aliased_f32_read` O0 `[TCG-PROOF-465]` refusal (L06-P1).

## Known finding at this source (fix in progress)

`R_AARCH64_LD64_GOTPAGE_LO15` is exempted from the check as a "GOT-base
form". The stated reason is that the linker places both the GOT base and
the slot and rejects out-of-range values. That holds for GNU ld 2.42 and
gold 2.42. LLD 22.1.6 instead truncates silently with the default layout:
a shared library or PIE linked through `cc -fuse-ld=lld` is installed and
reads the wrong slot. A fix that checks this form's window is in progress.
L02-P10 stays PARTIAL.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.
