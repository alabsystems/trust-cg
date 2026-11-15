# TLS-model link controls (L02-P9) on Linux AArch64 — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This run qualifies the TLS-model-mismatch control that ledger gap L02-P9 was
missing. It runs on clean source `fca6bf082e6e20629e578ff73e934b13d3f77905`
(tree `9263931b6c604f4863af54d8f613a5395b3e6182`). `git status --porcelain
--untracked-files=all` was empty before and after the qualifying run, and
again after the mutation leg restored its file. `records/results.json`
records the provenance.

The change adds two classified linker diagnostic kinds to
[`link_driver.rs`](../../../crates/trust-cg-codegen/src/link_driver.rs):

- `tls-model-mismatch` for a local-exec relocation (`R_AARCH64_TLSLE_*`) that
  lld refuses in a `-shared` link (`relocation R_AARCH64_TLSLE_* against
  <symbol> cannot be used with -shared`), or that GNU ld refuses against an
  undefined symbol (`TLS relocation R_AARCH64_TLSLE_* against undefined
  symbol `<symbol>'`);
- `tls-symbol-type-mismatch` for GNU ld's four TLS/non-TLS clash forms
  (`<symbol>: TLS definition|reference in a.o ... mismatches non-TLS
  definition|reference in b.o ...`).

It also adds a refusal that runs before the linker. `run_link` reads every
AArch64 ELF relocatable input of a shared-object link and refuses any
`R_AARCH64_TLSLE_*` relocation by name (`[TCG-LINK-TLS-MODEL]`,
`LinkError::InputRefused`). The reason is the finding below: the host's
default linker does not refuse this case.

L02-P9 stays **PARTIAL**. A separate adversarial audit decides closure.

## Finding: GNU ld 2.42 silently links local-exec TLS into a shared object

`records/direct/cg/tls_lib.o.gz` is the `static`-model object for
`records/inputs/tls_lib.tmbc` (the test's `tls_counter_module(false)`). Its
text is in `records/direct/cg-cat-tls_lib.trust_ir.txt.gz`. It defines the
thread-local `tcg_cli_tls` (40), and `tcg_cli_tls_bump` adds 2 to it and
returns the result. The object addresses it with
`R_AARCH64_TLSLE_ADD_TPREL_HI12`/`_LO12_NC` (`cg-objdump-dr-tls_lib.o`).

- `cc -shared tls_lib.o` with GNU ld 2.42 exits 0 with no diagnostic
  (`gnu-cc-shared-static-object`). The library has no dynamic TLS
  relocation and no `DF_STATIC_TLS` flag (`gnu-readelf-rW-…`,
  `gnu-readelf-dW-…`). The TPREL pair was resolved at link time to
  `add x0, x0, #0x10`, the first slot after the 16-byte TCB
  (`gnu-objdump-d-libtcgtls_bfd.so`). That offset belongs to the
  executable's TLS block.
- `tls_user.tmbc` (`tls_user_module()`) defines its own thread-local
  `tcg_cli_main_tls` (1000). Its `main` returns `tcg_cli_tls_bump() +
  tcg_cli_main_tls - 1000`: 42 when the two thread-locals are distinct.
  Linked against the GNU ld library, the program exits **236**
  (`run-user_bfd`). The library read and bumped the executable's thread-local
  (1000 + 2 = 1002, then 1002 + 1002 - 1000 = 1004 ≡ 236). This is silent
  wrong code, not a link failure.
- lld (`cc -fuse-ld=lld`, LLD 22.1.6) refuses the same object:
  `rust-lld: error: relocation R_AARCH64_TLSLE_ADD_TPREL_HI12 against
  tcg_cli_tls cannot be used with -shared` (`lld-cc-shared-static-object`).
- gcc objects behave the same way. `cc -shared` of a gcc
  `-ftls-model=local-exec` definition links under GNU ld
  (`gnu-le-defined-shared`, exit 0), and lld refuses it
  (`lld-le-defined-shared`). A local-exec reference to an undefined
  thread-local is refused by both: GNU ld says `TLS relocation … against
  undefined symbol` (`gnu-le-undefined-shared`), and lld gives its
  `cannot be used with -shared` message (`lld-le-undefined-shared`).

Before this change, `trust-cg -shared` linked such a module through `cc`
(GNU ld on this host) with no diagnostic. The refusal therefore comes from
trust-cg's object check, not from the linker.

## Native controls through the CLI (records/direct)

- `cli-shared-static`, `cli-shared-pie`: `trust-cg -shared` with the
  `static` and `pie` models prints exactly one
  ``trust-cg: error[link:tls-model-mismatch] `tcg_cli_tls`
  (R_AARCH64_TLSLE_ADD_TPREL_HI12): [TCG-LINK-TLS-MODEL] …`` line and
  `trust-cg: error: link inputs refused before the linker ran`, exits 1,
  runs no linker (no `ld` output), and writes no library
  (`cli-shared-outputs-absent`).
- Positive twins: `cli-executable-static`/`run-prog` link the same module
  with `main` as an executable, which exits 42. `cli-shared-pic` links it
  `-shared` under `--relocation-model pic`, with one `R_AARCH64_TLSDESC`
  dynamic relocation against `tcg_cli_tls` (`pic-readelf-rW-libtcgtls.so`).
  `cli-user-against-pic-library`/`run-user_pic` link the thread-local user
  against that library through `-L`/`-l`/`--rpath`, and it exits 42.
- `cli-clash-plain-reader`: one input defines `tcg_cli_tls` as a
  thread-local and the other (`tls_reader_plain.tmbc`) reads it as an
  ordinary global. GNU ld fails with `tcg_cli_tls: TLS definition in
  …/input_0.o section .tdata mismatches non-TLS reference in …/input_1.o`,
  and the CLI adds ``error[link:tls-symbol-type-mismatch] `tcg_cli_tls` ``.
  Its twin (`tls_reader_thread.tmbc`, a thread-local import) links and exits
  42 (`cli-thread-reader`, `run-reader`).

The `.tmbc` inputs were written by the committed test builders through a
temporary test (`records/inputs/dump-probe-modules.patch`). It was applied,
run and reverted before the qualifying run, and the tree was clean when the
run started. Their SHA-256 values are in `results.json` (`inputs`).

## Test targets and gates (records/logs)

| target / gate | result |
| --- | --- |
| `trust-cg-codegen --lib` (whole library suite) | `test result: ok. 4072 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out` |
| `trust-cg-codegen --lib link_driver` | `test result: ok. 17 passed; 0 failed; 0 ignored; 0 measured; 4056 filtered out` |
| `trust-cg-cli --test link_options` | `test result: ok. 10 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `trust-cg-cli --bin trust-cg` | `test result: ok. 29 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `trust-cg-codegen --test e2e_aarch64_elf_tlsie` | `test result: ok. 9 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `trust-cg-codegen --test e2e_aarch64_link_runtime` | `test result: ok. 21 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `cargo check -p trust-cg-codegen` / `--features verify` / `-p trust-cg-lower -p trust-cg-cli` | exit 0, no warnings |
| `scripts/check_fmt.sh` | OK |
| gate script tests (Linux, Darwin, Linux bridge) | `Ran 94 tests`, `OK (skipped=1)` |
| `native_test_host_matrix.py --check`, `check_documentation.py --check`, `generate_diagnostics_inventory.py --check` | exit 0 |

The ignored library test is the existing explicit real-tool
`raw_machir_request_cache_real_exhaustive_campaign`. The base had 4,069
passing library tests. The three new ones are
`classifies_tls_model_and_symbol_type_mismatches`,
`near_miss_tls_messages_stay_unclassified` and
`local_exec_tls_in_a_shared_link_is_refused_before_the_linker_runs`. They
pin, in order:

- the classifier on complete captured stderr: lld on the trust-cg object
  and on a gcc section anchor, GNU ld on a gcc object and on the trust-cg
  local-exec import, and GNU ld's four clash forms;
- twelve near misses, which stay `unclassified`: initial-exec,
  general-dynamic and misspelled relocation names, `can be used`,
  `-static`, an empty symbol, a defined symbol, an unquoted symbol,
  `matches`, TLS/TLS and non-TLS/non-TLS. A truncated TPREL stays
  `relocation-out-of-range`;
- the object check on writer-built objects. A local-exec object in a
  shared link is refused before a nonexistent driver would be spawned. An
  executable link is not refused, and neither is an initial-exec object,
  a linker script or a missing file.

The new native tests are `linux_tls::local_exec_tls_in_a_shared_object_is_refused_by_name`
and `linux_tls::thread_local_symbol_type_clash_is_classified` in
`link_options`, and `native::local_exec_tls_in_a_shared_link_is_refused_by_name`
in `e2e_aarch64_elf_tlsie`. The last one links a trust-cg local-exec import
`-shared` with the host `cc`, using the driver's own argument vector, and
requires GNU ld's refusal to classify as exactly
`(TlsModelMismatch, tls_probe_var, R_AARCH64_TLSLE_ADD_TPREL_HI12)`. It
requires `run_link` to refuse that object and a local-exec definition before
the linker runs. It also requires initial-exec objects, imported and
defined, to link `-shared` through `run_link` into `ET_DYN` outputs. Every
existing classification test is unchanged.

## Mutation leg (records/mutation)

`disable-guard.patch` removes the refusal from `run_link`. Under it, the
`linux_tls` CLI tests fail. `local_exec_tls_in_a_shared_object_is_refused_by_name`
panics at its first assertion because the `static` `-shared` link succeeds
through GNU ld. The e2e shared-link control also fails, because `run_link`
reaches the linker and returns `Failed` with GNU ld's classified diagnostic
instead of `InputRefused`. The script restored the file, and the tree was
clean afterwards (`results.json`: `restored_clean: true`).

## Host and tools

The host runs Linux `6.17.0-1026-nvidia` on NVIDIA Grace (CPU part `0xd87`)
with glibc 2.39 (`Ubuntu GLIBC 2.39-0ubuntu8.7`). `cc` is Ubuntu gcc 13.3.0,
and `/usr/bin/ld` resolves to `aarch64-linux-gnu-ld.bfd`, GNU ld 2.42
(SHA-256 `1e4d3369…`). GNU readelf and objdump are 2.42. The lld probes put
`~/.local/bin` first on PATH for `cc -fuse-ld=lld`. Its `ld.lld` resolves to
the rustup stable toolchain's `gcc-ld/ld.lld`, which reports LLD 22.1.6
(SHA-256 `61ec0509…`), so its messages are prefixed `rust-lld:`. Rust is
stock 1.97.1 through rustup. `results.json` (`tools`) has every path and
hash, and the SHA-256 of the `trust-cg` binary the probes ran.

## Boundaries

- This is execution and linker-output evidence on one host, not proof.
  The 236 result shows one wrong-code outcome under this glibc's TLS
  layout. It is not a general characterization of GNU ld.
- The object check covers only inputs passed to `run_link` that parse as
  AArch64 ELF64 relocatable objects. It does not examine archive members,
  shared libraries, linker scripts or unparseable files. A link made
  outside the driver, for example `cc -shared` on a `trust-cg -c` object,
  is not checked. That is exactly how the 236 program above was built.
- The classifier matches only the AArch64 relocation names and sentence
  shapes captured here. x86-64 and RISC-V TPREL relocations are not
  matched. lld's TLS/non-TLS clash message is not matched either: on these
  gcc objects, LLD 22.1.6 crashed with SIGTRAP on a TLS definition paired
  with a non-TLS reference (`lld-clash-tdef-nref`) and linked a non-TLS
  definition paired with a TLS reference without any diagnostic
  (`lld-clash-ndef-tref`, exit 0).
- The CLI's native controls use `static`, `pie` and `pic` objects from
  small fixtures. They are not a census of TLS shapes.

## Reproduce

`harnesses/qualify-tls-model-20260923.py WORKTREE RUN` needs
`RUN/inputs/*.tmbc` from the dump patch. It runs every gate and probe and
writes `RUN/records`. `harnesses/mutation-tls-model-20260923.py WORKTREE RUN`
runs the mutation leg, and `harnesses/archive-tls-model-20260923.py RUN DEST`
writes this archive and `inventory.json`. Logs, probe records, objects and
inputs are stored as `*.gz`. Linked binaries are not stored; their
`readelf`/`objdump` records are.
