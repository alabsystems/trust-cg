# Linux ELF thread-local bridge lane — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The maintained `scripts/check_linux_aarch64_bridge.py` gate ran on clean
source `7b9ee3683786ec0e3730c32225a064cd800eb740` (origin/main `3058c0de4`
plus the commit that adds
[`tls_thread_local_linux`](../../../crates/rustc-codegen-trust-cg/tests/tls_thread_local_linux.rs)
and makes it the runner's second required target) with the sealed Trust
`a62ae50d` package and `--require-proof-tools`. The runner verdict is **FAIL**,
from the ABI target alone:

| Required target | Verdict | libtest |
| --- | --- | --- |
| `tls_thread_local_linux` | **pass** | `test result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 50.28s` |
| `aarch64_c_fnabi_aggregate_linux` | fail (pre-existing, L06-P1) | `test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out; finished in 67.31s` |

The ABI target fails where the
[2026-09-22 checkpoint](../2026-09-22-linux-bridge-checkpoint/README.md)
recorded: `aliased_f32_read` at O0 is refused with `[TCG-PROOF-465]`
(`StpPreIndex`/`StpRI`/`LdpRI`/`LdpPostIndex` without bound proof). The runner
runs both targets against the same backend snapshot whatever the other's
verdict and records `target_status` per target, so the TLS result below is a
complete, independently classified run, not a partial one.

## What the TLS target established

The `#[thread_local] pub static mut X: i32 = 0xABCD` crate and the two-thread
C driver are byte-identical to the Darwin fixture's. Each lane compiles the
crate as a `staticlib` for `aarch64-unknown-linux-gnu` with
`-Ccodegen-units=1 -Cpanic=abort --emit=obj`, selects objects by defined
symbol with `readelf -sW` and links them with `cc -pthread`.

- **CG, O0–O3 (backend via `-Zcodegen-backend=<snapshot>` and
  `-Ztrust-ir-cg-args=no-proof-certs`).** Three objects per level. `tls.X.rcgu.o`
  defines `X` as a 4-byte `TLS GLOBAL` symbol in `.tdata` (flags `WAT`); the only
  function there is the dead `X.tls.anchor`. The accessor object
  `tls.tls.<hash>-cgu.0.rcgu.o` defines `read_x` and `bump_x` (`FUNC`), imports
  `X` as `UND TLS`, reads `tpidr_el0`, and carries exactly three initial-exec
  pairs `R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21` /
  `R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC` against `X` and no other TLS
  relocation. The allocator shim defines none of `X`/`read_x`/`bump_x` and is
  not linked. Every executable is a PIE with a `PT_TLS` segment and printed
  `43981 43982 44181 43982` with exit 0 in 5/5 runs. No aborting stubs were
  needed (the O0 overflow checks are inline `brk #1`).
- **LLVM twin, O0–O3.** One object defining all three items with the TLSDESC
  relocations; the same output and exit 0 in 5/5 runs per level. O0 needed three
  aborting stubs for undefined panic helpers, none of which was reached.
- **Shared-storage control.** The same crate without `#[thread_local]` defines
  `X` as `OBJECT`; with the identical driver both compilers exit 3 at every
  level with `43981 43982 44182 44182`, so the driver detects non-thread-local
  storage.
- **Refusal control.** With `#[link_section = ".custom"]` added, the bridge
  exits 1 with `[TCG-MIR-UNSUPPORTED]` and one row each for `static X`,
  `bump_x` and `read_x` carrying `thread-local static with explicit
  #[link_section = ".custom"] is not supported (default TLV-section emission
  only)`. Only `tlsneg.allocator_shim.rcgu.o` remains, and it defines none of
  the items. LLVM compiles the same source and places the `STT_TLS` `X` in
  `.custom`. This is a named fail-closed refusal, not support.
- **Without the knob** (`records/extra/no-knob-O1.log`, the same snapshot at
  O1): the definition object is emitted, but both accessors are refused with
  `[TCG-PROOF-465]` (`StpPreIndex` and `LdpPostIndex` have no proof mapping).
  The TLS lane therefore has no certificate-backed path at this revision.

The marker `TCG_BRIDGE_TLS_EXECUTION` in `records/runner/tls-native.log` carries
all eight lanes, eight shared-storage controls and four refusal controls; the
runner verified each against its floors.

The observed model is what the fixture asserts. It agrees with the codegen
path: AArch64 ELF object emission uses `ObjectAccessModel::elf` of the
configured relocation model (`crates/trust-cg-codegen/src/compiler.rs:14426`),
the bridge never changes the default `RelocationModel::Static`, `Static` maps
to `TlsDialect::ElfExecutable` (`crates/trust-cg-lower/src/adapter.rs:1363`),
and that dialect gives an initializer-less thread-local import initial-exec
(`adapter.rs:12823`, `global_is_thread_local_import` at `adapter.rs:21267`).
Local-exec access to a definition is not exercised: the definer contains no
access.

## Identities and controls

- Host `aarch64-unknown-linux-gnu`, Ubuntu 24.04.4 LTS, kernel
  `6.17.0-1026-nvidia`, glibc 2.39, GNU `cc` 13.3.0, GNU binutils 2.42
  (`ld`, `readelf`, `objdump`).
- `trustc -vV`: `rustc 1.99.0-dev (a62ae50d8 2026-09-16) (trustc 0.1.0)`,
  commit `a62ae50d8bd2b990650db2cf0dd25019c67c6ed8`, LLVM 22.1.2
  (`records/tls-artifacts/rustc.log`). `trustc`/`targo` came from
  `~/toolchains/trust-a62ae50d/bin`, first on PATH, with `RUSTC` pinned to that
  `trustc`.
- Backend: a fresh locked release build of the committed source (51 s against a
  warm run-local cache; dependencies fresh), snapshotted read-only in the report
  directory and passed to the test by path and SHA-256
  `5baaca65fd0d7b275be381d7d12656e62e69c13a2d7d56d44478ac898f3388cf`, identical
  before and after each target. Cargo's test build then replaced the mutable
  cache library (`2cd87bdb…`); that copy was not tested, as the runner records.
- AY `ec2bf181c384bff0453487b47781fb6d40b959a72c1236bdc760ccc1feee4830` and
  Clean `8d819378eb80696a6a753980bb1722de676f283c4219887f769ac70868f0fff8`
  resolved through the `aterm-packaged` route, unchanged across the run. No
  compile log in this run carries the `INDEPENDENT PROOF CHECKER UNUSABLE`
  banner. With `no-proof-certs` the TLS objects carry no certificate either
  way.
- Source fingerprint `1c9e900d…`, clean and identical after the build, the test
  build and the tests. Controls: `--require-proof-tools`, `--jobs 8`,
  `--timeout-seconds 2400`, run-local `XDG_CACHE_HOME`; every
  `TCG_*`/`RUSTC*`/`RUSTFLAGS` ambient override absent.

## Trusted base and evidence boundary

This is native testing evidence for the bridge's ELF thread-local lane only.
The toolchain is unqualified (owner decision OD-01 is pending). The frontend
ran with `-Ztrust-verify=off`, the backend was built by `targo --unverified`,
and the backend ran with `no-proof-certs`, so nothing here is a proof or
certificate claim. The `.tdata` symbol rows and the TLSIE relocation pairs are
unproven object-side facts checked by GNU `readelf`/`objdump`. GNU `cc`/`ld`,
the glibc TLS runtime and the kernel are trusted for linking, `PT_TLS` setup
and per-thread block allocation. Only the static relocation model is covered:
no shared-object, `dlopen`, general-dynamic or local-dynamic lane, and no
pointer-bearing or over-aligned template (both refused by name).

Ledger rows L06-P4 and L03-P7 stay open; this is their TLS sub-lane. The
unwind lane (`[TCG-EH-A64-BATCH]` at
`crates/rustc-codegen-trust-cg/src/lib.rs:1686-1699`), multi-function unwind
tables, and the drop/heap, static-data and coroutine fixtures remain
Darwin-only. L06-P1 (the ABI target's proof refusal) is unchanged. No existing
gate, assertion, floor or denominator was weakened.

## Records

- `records/runner/`: `report.json`, `build.log`, `test-build.log`,
  `native.log` (ABI target), `tls-native.log` (TLS target) and the console log.
  The backend snapshot is identified by hash, not archived.
- `records/tls-artifacts/`: the TLS fixture's complete text output: sources,
  driver, per-lane compile/link/run logs, `readelf -sW/-SW/-rW` dumps of every
  object, accessor disassembly, program headers, refusal logs and the tiny
  per-compile witness files. Objects and executables are excluded;
  `records/binaries.sha256` lists their SHA-256 and the snapshot's.
- `records/extra/no-knob-O1.log`: the certificate-requiring compile above.
- `runner-source/`: the runner and the fixture at the recorded commit.

```sh
python3 scripts/check_evidence_archive.py reports/perf/2026-09-23-linux-bridge-tls
PATH="$HOME/toolchains/trust-a62ae50d/bin:$PKG/bin:$HOME/.cargo/bin:$PATH" \
  python3 scripts/check_linux_aarch64_bridge.py --require-proof-tools --out /path/outside/source \
    --target-dir /path/outside/source/cache --jobs 8 --timeout-seconds 2400
```
