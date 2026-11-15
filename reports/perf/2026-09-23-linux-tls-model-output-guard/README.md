# TLS-model output guard (L02-P9 repair) on Linux AArch64, 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This run qualifies the repair of the L02-P9 TLS-model link controls after
their first adversarial review. The first version is
[2026-09-23-linux-tls-model-link-controls](../2026-09-23-linux-tls-model-link-controls/README.md)
on `fca6bf082`. The repair ran on clean source
`cd54805b0775fd7c6b2d3e0a340b62497e37b714` (tree
`93c848768c9d89ff2f3c6e7f416efbba7674f01f`). `git status --porcelain
--untracked-files=all` was empty before and after the qualifying run, and
again after the mutation legs restored their file. `records/results.json`
records the provenance.

L02-P9 stays **PARTIAL**. A separate adversarial audit decides closure.

An independent verifier later found two escapes in this repair. The
[second repair](#second-repair-2026-09-23) section below records the fix and
its run (`records/repair-2`). Its source is `9f8f4def9`. The first repair's
records are unchanged.

A later verification confirmed the second repair and found one more escape
(a response file in a forwarded value) and several statements to correct.
The [third repair](#third-repair-2026-09-23) section records that fix and its
run (`records/repair-3`). Its source is `502fab20f`. The earlier records are
unchanged.

## What the review found

1. **Bypass through the driver.** `local_exec_tls_refusals` ran only when the
   request's output kind was `SharedLibrary`. The driver-owned `-Wl`
   spellings were `-shared` and `-Bshareable`, not `--shared` and
   `--Bshareable`. GNU ld 2.42 accepts both double-dash forms. So
   `trust-cg -Wl,--shared -o libB.so tls_lib.tmbc` wrote an `ET_DYN` library
   whose `tcg_cli_tls_bump` addressed `tpidr_el0 + 0x10`, the executable's
   first TLS slot. A user executable with its own thread-local then exited
   236 instead of 42.
2. **Misnamed executable-side mismatch.** An executable's local-exec
   reference to a thread-local that a shared library defines was classified
   `relocation-out-of-range` (GNU ld's truncation form) or
   `non-pic-relocation` (lld). The `TlsModelMismatch` doc comment implied
   that it covered this case.

## The repair (crates/trust-cg-codegen/src/link_driver.rs)

- `--shared` and `--Bshareable` are driver-owned `-Wl` spellings, which
  `parse_wl_group` refuses in favour of `--shared`.
- Listing spellings is not enough. The host's GNU ld accepts any
  unambiguous abbreviation of a long option with one or two dashes: `-shar`,
  `--shar`, `-Bshar` and `--Bshare` all wrote shared objects
  (`records/direct/cli-wl-sh*`, `cli-wl-bshar*`). So `run_link` now also
  derives the check from what the linker wrote. After every successful link
  with an AArch64 ELF input that carries an `R_AARCH64_TLSLE_*` relocation,
  it reads the output's ELF header and, for `ET_DYN`, its `DT_FLAGS_1`. It
  accepts only `ET_EXEC`, `ET_DYN` with `DF_1_PIE`, or `ET_REL`. Any other
  output, including an unreadable one, is removed and refused with
  `LinkError::OutputRefused`, one `error[link:tls-model-mismatch]` per
  object and symbol, and `[TCG-LINK-TLS-MODEL]`. The CLI prints those lines,
  then `the linked output <path> was refused and removed`.
- The classifier maps GNU ld's `relocation truncated to fit:
  R_AARCH64_TLSLE_* against symbol `<s>' defined in <section> section in
  <file>` to `tls-model-mismatch` when `<file>`'s last component is
  `<name>.so` or `<name>.so.<digits>[.<digits>...]`. It does the same for
  lld's `relocation R_AARCH64_TLSLE_* cannot be used against symbol '<s>';
  recompile with -fPIC`. The truncation against an object-defined
  thread-local stays `relocation-out-of-range`, as does any non-TLSLE
  relocation.

## Direct probes (records/direct)

All probes use the static-model thread-local module `tls_lib.tmbc` retained by
the first run (same SHA-256; `results.json` `inputs`) and the binary built
from the clean source (`trust_cg_binary_sha256`).

| probe | result |
| --- | --- |
| `cli-wl-shared-2dash`, `cli-wl-bshareable-2dash` (the review's bypass), `cli-wl-shared-1dash`, `cli-wl-bshareable-1dash` | exit 1: ``-Wl,--shared: `--shared` is controlled by the trust-cg option `--shared` `` and the same for the other spellings; no linker runs |
| `cli-wl-shar-2dash`, `cli-wl-shar-1dash`, `cli-wl-bshare-2dash`, `cli-wl-bshar-1dash` | exit 1: GNU ld writes a shared object, and the CLI prints exactly one ``error[link:tls-model-mismatch] `tcg_cli_tls` (R_AARCH64_TLSLE_ADD_TPREL_HI12): [TCG-LINK-TLS-MODEL] … which is an ELF shared object (ET_DYN without DF_1_PIE)`` and `the linked output … was refused and removed` |
| `cli-refused-outputs-absent` | none of the eight refused libraries exist |
| `cli-pic-wl-shar` → `cli-user-against-pic-library` → `run-user_pic` | the `pic` model links through `-Wl,--shar` (`DYN (Shared object file)`, one `R_AARCH64_TLSDESC` against `tcg_cli_tls`), and the user with its own thread-local exits **42** |
| `cli-executable-{pie,no_pie,static}` → `run-prog_*` | the local-exec module links as `DYN (Position-Independent Executable file)` with `FLAGS_1 NOW PIE`, as `EXEC`, and as a static `EXEC`; each exits **42** |
| `outside-cc-wl-shar` → `run-user_outside` | boundary: `cc -Wl,--shar` on the `trust-cg -c` object outside the driver links (exit 0; `add x0, x0, #0x10`), and the user exits **236**. Links made outside trust-cg are not checked |
| `gnu-exe-no-tls-segment` | GNU ld, executable without its own TLS segment: `TLS relocation R_AARCH64_TLSLE_ADD_TPREL_HI12 against undefined symbol `ext_tls'` (already `tls-model-mismatch`) |
| `gnu-exe3-tdata`, `gnu-exe4-tbss`, `gnu-exe3-versioned-soname` | GNU ld, executable with its own TLS segment: `relocation truncated to fit: R_AARCH64_TLSLE_ADD_TPREL_HI12 against symbol … defined in .tdata/.tbss section in ./libdef.so` (and `./libdef.so.1`) |
| `lld-exe3-tdata`, `lld-exe4-tbss` | LLD 22.1.6: `relocation R_AARCH64_TLSLE_ADD_TPREL_HI12 cannot be used against symbol 'ext_tls'; recompile with -fPIC` and the `LO12_NC` twin |

The complete stderr of the last five rows is pinned verbatim in the unit test
`classifies_executable_local_exec_against_a_shared_library_thread_local`.

## Test targets and gates (records/logs)

| target / gate | result |
| --- | --- |
| `trust-cg-codegen --lib` (whole library suite) | `test result: ok. 4075 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out` |
| `trust-cg-codegen --lib link_driver` | `test result: ok. 20 passed; 0 failed; 0 ignored; 0 measured; 4056 filtered out` |
| `trust-cg-cli --test link_options` | `test result: ok. 11 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `trust-cg-cli --bin trust-cg` | `test result: ok. 29 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `trust-cg-codegen --test e2e_aarch64_elf_tlsie` | `test result: ok. 11 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `trust-cg-codegen --test e2e_aarch64_link_runtime` | `test result: ok. 21 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `cargo check -p trust-cg-codegen` / `--features verify` / `-p trust-cg-lower -p trust-cg-cli`, `cargo build -p trust-cg-cli` | exit 0 |
| `scripts/check_fmt.sh` | OK |
| gate script tests (Linux, Darwin, Linux bridge) | `Ran 94 tests`, `OK (skipped=1)` |
| `native_test_host_matrix.py --check`, `check_documentation.py --check`, `generate_diagnostics_inventory.py --check` | exit 0 |

New tests, relative to the first run (4072 → 4075 library tests, 10 → 11
`link_options`, 9 → 11 `e2e_aarch64_elf_tlsie`):

- `link_driver` unit tests:
  - `classifies_executable_local_exec_against_a_shared_library_thread_local`
    checks the five captured stderr blocks. Each gives exactly one
    `(TlsModelMismatch, symbol)`, and each names
    `R_AARCH64_TLSLE_ADD_TPREL_HI12`. Ten near misses keep their old kind.
    For `relocation-out-of-range` these are an `.o` file, `.so.o`, `.so.1a`,
    a bare `.so`, a non-TLS relocation, and an initial-exec relocation. For
    `non-pic-relocation` they are an lld non-TLS relocation, an lld
    initial-exec relocation, and an empty symbol. One without `recompile
    with -fPIC` stays `unclassified`.
  - `linked_output_kind_is_read_from_the_image` checks `ET_REL`, `ET_EXEC`
    and PIE. It checks four unconfirmed `ET_DYN` shapes, a truncated dynamic
    segment, and hostile header offsets (no panic). It checks that a
    big-endian image, a non-ELF image, `ET_CORE` and a truncated header are
    errors.
  - `local_exec_tls_in_a_shared_output_is_refused_after_the_link` uses a
    scripted driver that writes a prepared image. A shared image and a
    non-image output are refused and removed. `ET_EXEC`, PIE and `ET_REL`
    outputs pass unchanged, and an initial-exec-only input is not
    refused.
  - `wl_groups_refuse_driver_owned_and_malformed_arguments` gains
    `--shared`, `-Bshareable`, `--Bshareable` and `--gc-sections,--shared`.
- `link_options`
  `linux_tls::wl_shared_spellings_cannot_make_a_local_exec_library` is the
  CLI control from the table above, with its `pic` twin that runs (42).
- `e2e_aarch64_elf_tlsie`:
  - `native::local_exec_tls_against_a_shared_library_thread_local_is_named`
    covers a trust-cg local-exec import of `tls_probe_var`, which only
    `libtlsprobe.so` defines. Through `run_link` and GNU ld, it fails as
    exactly one `(TlsModelMismatch, tls_probe_var,
    R_AARCH64_TLSLE_ADD_TPREL_HI12)`. That holds in the undefined-symbol
    form (no TLS segment in the executable) and in the truncation form
    against the library's `.tdata` (with one), and each sentence is required
    verbatim. The initial-exec twin links against the same library and
    exits 42.
  - `native::local_exec_tls_in_a_linker_steered_shared_object_is_refused`
    has `run_link` refuse and remove the output for `--shar`, `-shar`,
    `--Bshare` and `-Bshar` on a local-exec definition. Through the same
    spellings, the initial-exec twin links into a shared object
    (`ElfLinkedKind::SharedObject`). The local-exec definition links and
    exits 42 as a PIE, a non-PIE and a static executable.

Every earlier test and assertion is unchanged.

## Mutation legs (records/mutation)

Each leg mutates `link_driver.rs`, runs its tests and restores the file.

- `output-check.patch` disables the post-link refusal. The CLI control
  panics on `--shar`, because the link succeeds. The e2e steered control
  gets `Ok(LinkSuccess)` for `--shar` instead of `OutputRefused`, and the
  scripted-driver unit test does too. All three fail.
- `driver-owned.patch` removes the two new driver-owned spellings. The
  `wl_groups` unit test fails because `--shared` parses. The CLI control
  fails because `-Wl,--shared` reaches the linker. Even then, the output
  check refuses and removes the library, so the two parts overlap as
  defence in depth.
- `both.patch` applies both mutations. It rebuilds `trust-cg` and replays
  the review's reproduction. `trust-cg -Wl,--shared -o libtcgb.so
  tls_lib.tmbc` exits 0 with a `DYN (Shared object file)`. Its
  `tcg_cli_tls_bump` addresses `tpidr_el0 + 0x10`, and `userB` exits
  **236**.

Afterwards the file was restored, `trust-cg` was rebuilt, its SHA-256 matched
the qualifying binary again, and the tree was clean (`results.json`:
`every_test_leg_failed`, `both_reproduces_236` and `restored_clean` are all
`true`).

## Host and tools

The host runs Linux `6.17.0-1026-nvidia` on NVIDIA Grace (CPU part `0xd87`)
with glibc 2.39. `cc` is Ubuntu gcc 13.3.0, and `/usr/bin/ld` is GNU ld 2.42
(`aarch64-linux-gnu-ld.bfd`). readelf and objdump are GNU 2.42. The lld
probes put `~/.local/bin` first on PATH. Its `ld.lld` resolves to the rustup
stable toolchain's `gcc-ld/ld.lld`, LLD 22.1.6, whose messages are prefixed
`rust-lld:`. Rust is stock 1.97.1. `results.json` (`tools`) has every path
and hash.

## Boundaries

- This is execution and linker-output evidence on one host, not proof.
- The object checks cover only inputs passed to `run_link` that parse as
  AArch64 ELF64 relocatable objects. Archive members, shared-library and
  linker-script inputs and unparseable files are not examined, so a
  local-exec relocation that reaches the link only through them is not
  checked.
- The output check reads only the written file's ELF header and dynamic
  section. It trusts `DF_1_PIE` to mark a position-independent executable,
  which GNU ld 2.42 and LLD 22.1.6 set on every PIE here, static-pie
  included. An executable `ET_DYN` from a linker that omits the flag would be
  refused, which fails closed. `ET_REL` output (`-r`) is accepted because it
  keeps the relocations for a later link, and that later link is outside
  this check unless it also runs through the driver.
- A link made outside trust-cg is not checked (`run-user_outside`, 236).
- The classifier matches only the captured GNU ld and LLD sentence shapes
  and AArch64 relocation names. For GNU ld's truncation form, it relies on
  the library's file name (`*.so`, `*.so.<digits>`). A library named
  otherwise stays `relocation-out-of-range`. x86-64 and RISC-V TPREL
  relocations are not matched.

## Reproduce

`harnesses/qualify-tls-output-guard-20260923.py WORKTREE RUN` needs
`RUN/inputs/*.tmbc`, which are the gunzipped `records/inputs`. It runs every
gate and probe and writes `RUN/records`.
`harnesses/mutation-tls-output-guard-20260923.py WORKTREE RUN` runs the
mutation legs. `harnesses/archive-tls-output-guard-20260923.py RUN DEST`
writes this archive and `inventory.json`. Logs, probe records, objects and
inputs are stored as `*.gz`. Linked binaries are not stored; their
`readelf`/`objdump` records are.

## Second repair (2026-09-23)

An independent verifier reproduced two escapes on the `cd54805b0` tip build.
It used `target/debug/trust-cg` and `records/inputs`.

1. **Output redirection escaped the check.** GNU ld parses with
   `getopt_long_only`, so it accepts any unambiguous prefix of a long option
   with one or two dashes. `-Wl,--outp=<path>` and the joined short form
   `-Wl,-o<path>` both passed `parse_wl_group`, which matched exact names,
   and both redirected the output. With an existing executable at the `-o`
   path, `trust-cg -Wl,-shar,--outp=libtcgb.so -o preexist tls_lib.tmbc`
   exited 0 and wrote a local-exec shared object. A user linked against it
   exited 236 instead of 42. With a fresh `-o` path, trust-cg reported that
   a never-existing file was "refused and could not be removed" and left the
   real library in place.
2. **The check could delete a file the linker did not write.** `trust-cg
   -Wl,--version -o keep2.txt tls_prog.tmbc` made ld print its version and
   exit 0 without writing. trust-cg then read `keep2.txt`, printed a false
   `error[link:tls-model-mismatch]` naming it, and deleted it.

The repair ran on clean source `9f8f4def93f1bec0ba6f5f391ac89ca378de97f1`
(tree `1bbeeaf1597d53df883f8fe7565a3b20230032cc`). `git status --porcelain
--untracked-files=all` was empty before and after the run, after
`check_documentation.py --write`, and after the mutation legs restored their
file. `records/repair-2/results.json` records provenance, tools, input
hashes and every gate and probe. The `trust-cg` binary SHA-256 was
`9108ec77e2a1df4d13c9b456d9aa953a4caa27b18ffa712bab857ae3089f2696`.

### The repair (crates/trust-cg-codegen/src/link_driver.rs)

- **Driver-owned options are read the way GNU ld reads them.**
  `parse_wl_group` now takes the target. On every non-Darwin target it
  refuses each piece that the host's GNU ld 2.42 reads as a driver-owned
  option:
  - one or two dashes and every prefix of `output`, `shared`, `Bshareable`,
    `pie`, `pic-executable`, `no-pie`, `static`, `nostdlib`, `soname`,
    `rpath` and `just-symbols` (the long name of `-R`), with or without
    `=<value>`;
  - the joined short forms `-o<value>`, `-h<value>` and `-R<value>`;
  - a bare `-G`, which GNU ld rewrites to `--shared` when no number follows.

  `LinkRequest::refusals` re-validates every group, so a request built
  without the parser is refused the same way before anything runs. ld64
  matches names exactly. A Darwin link therefore keeps its exact-name
  refusals and its own `-order_file` and `-headerpad_max_install_names`.
- **The read-back acts only on a file this link wrote.** A link with a
  local-exec AArch64 ELF input now links into a fresh directory next to the
  output, which the driver creates (`mkdir`, mode 0700,
  `.tcg-link-<pid>-<n>-<ns>`). The image there keeps the output's file name.
  An `ET_EXEC`, PIE or `ET_REL` image is moved onto the output by one
  `rename`. A refused image is removed with the directory
  (`LinkError::OutputRefused`, which now also names the staged path). A
  successful link that wrote nothing there is refused with
  `LinkError::OutputMissing` (`[TCG-LINK-NO-OUTPUT]`). A staging or install
  failure is `LinkError::OutputStaging`. None of these reads, removes or
  replaces a file already at the output. Links without a local-exec input
  write the output directly, as before.

### How the host linkers read each spelling (records/repair-2/direct/ld)

`harnesses/ld-option-reading-20260923.py` passes every prefix of the eleven
owned long names straight to `ld`. It uses one and two dashes, and for
value-taking options both a separate value and `=VALUE`, 222 spellings in
all. Each option has a setup that makes its effect observable: the
redirected file, `ET_DYN` with or without `DF_1_PIE`, `ET_EXEC` after
`-pie`, `cannot find -lprobe` under `-Bstatic`, `cannot find -lc` under
`-nostdlib`, `DT_SONAME` or `DT_RUNPATH`. The eleven controls without a
spelling show no effect. Of the 222 spellings, 141 act as the owned option
and 60 are ld errors (ambiguous or unrecognised). The other 21 exit 0
without the owned effect:

- `-ou`, `-out`, `--ou` and `--out` (all forms) select `--out-implib` and
  write an `ET_REL` import library beside the executable. They are refused
  because they abbreviate `--output`.
- `-outp=`, `-outpu=` and `-output=` write the executable as `utp=…`,
  `utpu=…` and `utput=…`. That is `-o<value>`, so these are refused.

The files written for those output prefixes are in
`direct/ld/ld-output-prefix-reading.txt`
(`harnesses/ld-output-prefix-reading-20260923.py`). It is a supplementary
record, run after the qualifying run, and it reads only the host's ld.
- `-s`, `-n` and `-p` are short options (`--strip-all`, `--nmagic`, an
  undocumented `-p`) and stay admissible.
- `--n`, `--no` and `--no-` select `--no-omagic`: after `-N`, the `LOAD`
  segment goes from `RWE` to `R E`, as with `--no-omagic`. They are refused
  because they abbreviate `--no-pie`/`--nostdlib`.

The same harness runs the joined forms and the neighbours through
`cc … -Wl,<group>`, as trust-cg does:

| spelling | host GNU ld 2.42 | parser |
| --- | --- | --- |
| `-G` | `ET_DYN` without `DF_1_PIE` (shared) | refused (`--shared`) |
| `-G,8` / `--gpsize=8` | PIE (small-data size) | refused / accepted |
| `-oredir.elf`, `--outp=redir.elf` | writes `redir.elf` | refused (`-o`) |
| `-outp=redir.elf`, `-omagic`, `-oformat=elf64-littleaarch64` | writes `utp=redir.elf`, `magic`, `format=elf64-littleaarch64` | refused (`-o`) |
| `-orphan-handling=place` | `--orphan-handling` (writes `out.elf`) | refused (over-refusal; `--orphan-handling=place` accepted) |
| `-hlibtcgprobe.so.7` | `DT_SONAME libtcgprobe.so.7` | refused (`--soname`) |
| `-hash-style=gnu` | `--hash-style` | refused (over-refusal; `--hash-style=gnu` accepted) |
| `-R/tcg/joined-rpath` | `DT_RUNPATH /tcg/joined-rpath` | refused (`--rpath`) |
| `-sh`, `--pic-exec` | shared object; PIE despite `-no-pie` | refused (`--shared`, `--pie`) |
| `-s`, `-S`, `-O1`, `-z,now`, `-L.,-lprobe`, `-rpath-link,.`, `--rpath-link=.`, `--gc-sections`, `--as-needed`, `--oformat=elf64-littleaarch64`, `--hash-style=gnu`, `--orphan-handling=place` | link, PIE | accepted |
| `--omagic`, `-n` | link fails: `cannot find -lgcc_s` (both disable shared libraries) | accepted |
| `-r` | `-r and -pie may not be used together` | accepted |
| `-Bstatic,-lprobe` | `cannot find -lprobe` (only `libprobe.so` exists) | accepted |
| `--version` | prints the version, exit 0, writes nothing | accepted; the staged check refuses it (below) |
| `-sofoo`, `-nhfoo` (grouped short options) | `Error: unable to disambiguate` | accepted; ld refuses them |

LLD 22.1.6 (`~/.local/bin` first on PATH) reads `-oredir.elf`,
`-hlibtcgprobe.so.9` and `-R/tcg/lld-rpath` as the joined short forms.
It rejects `--outp=redir.elf` and `-sh` as unknown arguments.

### Direct probes (records/repair-2/direct)

The probes run in `cg`, with `preexist` a copy of `/bin/true`. The
`state-*` records list the directory, hidden entries included, and hash the
files at each step.

| probe | result |
| --- | --- |
| `cli-redirect-{shar-outp,outp,o-joined,outp-1dash}-{preexist,fresh}` | exit 1 before anything runs, for example ``-Wl,-shar,--outp=libtcgb.so: `-shar` is controlled by the trust-cg option `--shared`: …``. `state-1-after-redirects` is the same as `state-0-before`: `preexist` keeps its hash, and neither `fresh` nor `libtcgb.so` nor `utp=libtcgb.so` exists |
| `cli-version-keep2` | exit 1: `[TCG-LINK-NO-OUTPUT] the linker exited successfully but wrote nothing at ./.tcg-link-…/keep2.txt … keep2.txt was not touched`. `keep2.txt` keeps its hash, and no staging directory remains (`state-3`) |
| `cli-version-keep2-pic` | twin without a local-exec input: exit 0, `keep2.txt` unchanged (`state-4`). The unchecked path is unchanged |
| `cli-shim-shared-static` | a `cc` shim first on PATH runs the host `cc -shared "$@"`. Exit 1 with exactly one ``error[link:tls-model-mismatch] `tcg_cli_tls` (R_AARCH64_TLSLE_ADD_TPREL_HI12)`` (`… which is an ELF shared object (ET_DYN without DF_1_PIE)`) and `the linked output for libtcgshim.so was refused and not installed; the linker's image was removed`. The existing `libtcgshim.so` keeps its hash (`state-6`) |
| `cli-shim-shared-pic` → `cli-user-against-shim-library` → `run-user_shim` | the pic library links through the shim (`DYN`), and the user with its own thread-local exits **42** |
| `cli-pic-shared` → `cli-user-against-pic-library` → `run-user_pic` | typed `-shared` pic library; user exits **42** |
| `cli-executable-fresh` → `run-prog`; `cli-executable-replaces-keep2` → `run-keep2` | the staged local-exec executable links fresh (`DYN`, PIE) and in place of the existing `keep2.txt`; each exits **42** |

### Test targets and gates (records/repair-2/logs)

| target / gate | result |
| --- | --- |
| `trust-cg-codegen --lib` (whole library suite) | `test result: ok. 4076 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out` |
| `trust-cg-codegen --lib link_driver` | `test result: ok. 21 passed; 0 failed; 0 ignored; 0 measured; 4056 filtered out` |
| `trust-cg-cli --test link_options` | `test result: ok. 14 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `trust-cg-cli --bin trust-cg` | `test result: ok. 29 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `trust-cg-codegen --test e2e_aarch64_elf_tlsie` | `test result: ok. 11 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `trust-cg-codegen --test e2e_aarch64_link_runtime` | `test result: ok. 21 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `cargo check -p trust-cg-codegen` / `--features verify` / `-p trust-cg-lower -p trust-cg-cli`, `cargo build -p trust-cg-cli` | exit 0 |
| `scripts/check_fmt.sh` | OK |
| gate script tests (Linux, Darwin, Linux bridge) | `Ran 94 tests`, `OK (skipped=1)` |
| `native_test_host_matrix.py --check`, `check_documentation.py --write` (no change) then `--check`, `generate_diagnostics_inventory.py --check` | exit 0 |

New and changed tests, relative to the first repair (4075 → 4076 library
tests, 11 → 14 `link_options`, 11 `e2e_aarch64_elf_tlsie`):

- `link_driver` unit tests:
  - `wl_groups_refuse_driver_owned_and_malformed_arguments` pins 74 refused
    Linux spellings with the owning option. For each one, a request built
    without the parser is refused identically. It also pins 27 accepted
    Linux groups, 4 Darwin-only groups that Linux refuses, and 5 exact
    Darwin refusals.
  - `local_exec_tls_in_a_shared_output_is_refused_after_the_link` (scripted
    driver) now also covers an existing output kept through refusal and
    through an unreadable image, and a driver that exits 0 without writing
    (`OutputMissing`, `[TCG-LINK-NO-OUTPUT]`, output kept). It covers
    `ET_EXEC`, PIE and `ET_REL` installed over the file, and it checks that
    no staging directory is left.
  - `a_checked_link_that_cannot_stage_or_install_is_refused` is new. A
    missing parent directory and an output that is a directory are each
    refused as `OutputStaging`, and the directory's content is kept.
- `link_options` `linux_tls`:
  - `wl_output_redirection_is_refused_by_name` (new).
  - `a_link_that_writes_no_output_leaves_the_output_file_alone` (new, with
    the pic and staged-executable twins).
  - `a_shared_object_the_driver_writes_for_an_executable_is_refused` (new,
    cc shim, pic twin runs 42).
  - `wl_shared_spellings_cannot_make_a_local_exec_library` now expects every
    `--shared` spelling, `-sh` and `-G` included, to be refused before
    anything runs under both `static` and `pic`. Its pic twin links through
    the typed `-shared`. The abbreviations it used to send to the linker are
    now refused by name.
- `e2e_aarch64_elf_tlsie`
  `native::local_exec_tls_in_a_linker_steered_shared_object_is_refused`
  refuses ten `--shared` spellings in the parser and in `run_link` on an
  unparsed request. It refuses a `cc -shared` wrapper's local-exec library
  at the staging path while the existing output keeps its bytes, and it
  refuses `--version` as `OutputMissing`. The initial-exec twin is installed
  as a shared object, and the PIE, non-PIE and static executables still
  return 42.

### Mutation legs (records/repair-2/mutation)

`harnesses/mutation-tls-output-guard-2-20260923.py` applies each mutation,
runs its tests, rebuilds `trust-cg` and replays, then restores the file. A
test leg counts only when the mutant compiled and its log has a `test
result: FAILED.` line. The first attempt's `unstaged` mutant did not compile
under the workspace's `-D warnings` (an unused parameter). It was discarded
and the harness rerun, and only the rerun is archived.

- `gnu-model.patch` stops applying the GNU ld reading, leaving exact names
  only. `unit_wl_groups`, `cli_redirection`, `cli_shared_spellings` and
  `e2e_steered` fail. Replay: `trust-cg -Wl,-shar,--outp=libtcgb.so -o
  preexist tls_lib.tmbc` now reaches ld, which writes `libtcgb.so`. The
  staged check sees no image and refuses with `[TCG-LINK-NO-OUTPUT]`, and
  `preexist` keeps its hash. But the library is left at the other path
  (`DYN`, `tcg_cli_tls_bump` adds `#0x10` to `tpidr_el0`), and `userB`
  linked against it exits **236**. The parser is what stops a redirection;
  staging can only report it.
- `unstaged.patch` points the checked link at the requested output instead
  of the staging path. `cli_no_output`, `cli_shim`, `unit_scripted_driver`
  and `e2e_steered` fail. Replay: `-Wl,--version -o keep2.txt` prints the
  reviewed false ``error[link:tls-model-mismatch] … keep2.txt, which is not
  a confirmed executable``. The shim link overwrites the existing
  `libtcgshim.so` with the refused `DYN` library (hash `a372…` → `d041…`).
- `output-check.patch` installs the staged image without the check.
  `cli_shim`, `unit_scripted_driver` and `e2e_steered` fail. Replay: the
  shim link exits 0 with a local-exec `DYN` library (`add x0, x0, #0x10`),
  and `userS` exits **236**.

After the legs, the file was restored and `trust-cg` was rebuilt. Its
SHA-256 matched the qualifying binary, and the tree was clean
(`mutation/results.json`: `every_test_leg_failed`, all three `replays`,
`restored_binary_matches_qualifying` and `restored_clean` are `true`).

### Boundaries and residuals

- This is execution and linker-output evidence on one host, not proof.
- The option model is the host's GNU ld 2.42. It relies on 2.42 refusing a
  grouped short option that takes a value (`-sofoo`: `unable to
  disambiguate`). A GNU ld that accepts such grouping, as plain
  `getopt` does, is not modelled. Prefixes are
  refused whether 2.42 reads them as the owned option, as another option or
  as an error. That keeps them refused under a later ld with fewer
  look-alike options.
- These are over-refusals. `-G <number>`, which only sets the small-data
  size, is refused (`--gpsize=<number>` is accepted). So are the one-dash
  spellings of unrelated options that begin with `o` or `h`
  (`-orphan-handling=…`, `-hash-style=…`); their two-dash spellings are
  accepted. A value piece that looks like an owned option is refused even
  when the option before it would consume it.
- The checks examine only AArch64 ELF64 relocatable inputs passed to
  `run_link` and the staged image's ELF header and `DT_FLAGS_1`. They do not
  examine archive members, shared-library or linker-script inputs, a file a
  linker writes at a path other than the staged one, or links made outside
  trust-cg.
- Only links with a local-exec input are staged. The arm64 Darwin
  code-signature check still reads and, on refusal, removes the output path
  itself, so the same "file the linker did not write" question is open
  there. It was not changed, and it cannot be run on this host.

### Reproduce

Run `harnesses/qualify-tls-output-guard-2-20260923.py WORKTREE RUN` with
`RUN/inputs/*.tmbc` (the gunzipped `records/inputs`) and
`RUN/ld-option-reading-20260923.py`
(`harnesses/ld-output-prefix-reading-20260923.py RUN/records/direct/ld`
adds the supplementary record). Run
`harnesses/mutation-tls-output-guard-2-20260923.py WORKTREE RUN` after it.
`harnesses/archive-tls-output-guard-2-20260923.py RUN DEST` writes
`records/repair-2` and regenerates `inventory.json`, checking that every
earlier entry is unchanged. Probe working directories and linked binaries
are not stored; their states, `readelf` and `objdump` records are.

## Third repair (2026-09-23)

An independent verifier confirmed the second repair and its edge cases
(staging, concurrency, mode bits and the GNU ld spelling model), and found
one more escape and several statements to correct. The repair ran on clean
source `502fab20fbbf0f088298cec8a5ede9eee038c1e4` (tree
`55876d8b1e1376a55564344492ae71add774ad00`). `git status --porcelain
--untracked-files=all` was empty before and after the run, after
`check_documentation.py --write`, and after the mutation leg restored its
file. The `trust-cg` binary SHA-256 was
`221a0d3c9020d20b82d6a25b7866bfb69ccbe0098bef896914a344abdcfe436c`.
`records/repair-3/results.json` records provenance, tools, input hashes and
every gate and probe.

### The escape (D1): a response file in a forwarded value

gcc, collect2 and GNU ld expand an argument `@<file>` into the arguments the
file contains. A typed value trust-cg forwards to the driver could be such a
file, and nothing in it passes `parse_wl_group`. The verifier reproduced,
on the second-repair tip:

- `printf -- '/x --shared -o libevil.so\n' > resp; cp /bin/true preexist;
  trust-cg --rpath @resp -o preexist tls_lib.tmbc` — refused with
  `[TCG-LINK-NO-OUTPUT]`, `preexist` untouched, but GNU ld wrote a local-exec
  `libevil.so` (`add x0, x0, #0x10` off `tpidr_el0`) and a user linked
  against it exited 236;
- `--shared --soname @resp` with `resp` holding `libq.so.1 le.o` linked a
  local-exec object into a library, exit 0;
- an unstaged `-o @resp` (`resp` holding `libredir.so -shared`) had gcc
  expand it.

`LinkRequest::refusals` now refuses, before anything runs, every forwarded
value that begins with `@`: the output path, each input path, each `-L`
directory and `-l` name, the soname and each run-time search path
(`[TCG-LINK-RESPONSE-FILE]`). A path is accepted spelled `./@...`; that is
the chosen design, over rewriting the path. On Darwin a run-time search path
or install name that begins with a dyld path token (`@loader_path`,
`@executable_path`, `@rpath`) stays accepted; whether ld64 expands those as
response files was not checked (no Darwin host). `-Wl` pieces are already
refused by `parse_wl_group`.

### The corrections (D2 and minor)

- **Scan scope.** Only positional AArch64 ELF64 relocatable inputs are
  scanned before the link, and the staged read-back runs only when one of
  them carries `R_AARCH64_TLSLE_*`. A local-exec object that reaches the
  linker any other way is not examined: named inside a `-Wl` group
  (`-Wl,le.o`), as a `-l:<file>` library (`-L . -l :le.o`), as an archive
  member, through a linker script's `INPUT()`, or inside a shared-library
  input. README.md, LIMITATIONS.md, docs/linux-aarch64-completion.md, the
  `adapter.rs` `ElfLocalExec` comment, the CHANGELOG L02-P9 bullet and the
  ledger note now state this, and the false comment in
  `link_options.rs` ("No -Wl spelling makes a local-exec library through the
  CLI") now names the spellings it means.
- **`-Bstatic`.** The docs called `-Bstatic` a name that "only begins like an
  owned one". Corrected: GNU ld reads `-Bstatic`, `-dn`, `-non_shared` and
  `-static` as one option. `-Wl,-static` is refused as the typed `--static`.
  The other three are accepted deliberately as the positional
  library-search switch (`-Wl,-Bstatic ... -Wl,-Bdynamic`), and the unit
  test now pins `-dn` and `-non_shared` as accepted.
- **Second-repair ledger wording.** The second-repair count said "21 of 222
  prefix spellings select another option"; three of those (`-outp=`,
  `-outpu=`, `-output=`) are `-o` itself writing to `utp=...`. The archive
  README already states this; the third-repair ledger sentence uses the
  README's wording.
- **Staging limits.** LIMITATIONS now records that a staged link killed
  (for example by SIGTERM) after the linker wrote its image can leave a
  mode-0700 `.tcg-link-<pid>-...` directory holding an unchecked image, and
  that a staged link replaces a symlink at the output path (the linker
  writes the image, not through the link, as the host's GNU ld and LLD do).

### Direct probes (records/repair-3/direct)

The probes run in `cg`. `preexist` is a copy of `/bin/true`; `@inp` and
`@src` are copies of `tls_prog.tmbc`; `resp`, `resp2`, `resp3` hold the
review's redirections; `le.o` is `trust-cg -c` of the static-model
`tls_lib.tmbc`. The `state-*` records list the directory and hash the
retained files.

| probe | result |
| --- | --- |
| `cli-response-file-{rpath,soname,output,input,libpath,libname}` | exit 1 before anything runs, for example ``--rpath: [TCG-LINK-RESPONSE-FILE] the run-time search path `@resp` begins with `@` … spell the path as `./@...` ``. `state-1-after-response-files` equals `state-0-before`: `preexist` and every `resp*`, `le.o`, `@inp` keep their hash, and no `libevil.so` or other output exists |
| `cli-dot-at` → `run-dot-at` | `trust-cg -o ./@out ./@src` links and `@out` exits **42** (the `./@` spelling reaches the driver as a path) |
| `cli-route-wl` → `run-user_wl` | `trust-cg --shared --relocation-model pic -o libtcgwl.so -Wl,le.o tls_reader_thread.tmbc` exits 0; a user with its own thread-local, linked against it, exits **236** — the documented unexamined route |
| `cli-route-lcolon` → `run-user_lcolon` | the same through `-L . -l :le.o`; user exits **236** |

The `-Wl,le.o` and `-l:le.o` rows are the boundary, not a defect: the
local-exec object arrives other than as a positional input, so it is never
scanned and the link is not staged. `link_options`
`unexamined_link_routes_are_the_documented_boundary` pins both, so a future
fix that examines them is visible.

### Test targets and gates (records/repair-3/logs)

| target / gate | result |
| --- | --- |
| `trust-cg-codegen --lib` (whole library suite) | `test result: ok. 4077 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out` |
| `trust-cg-codegen --lib link_driver` | `test result: ok. 22 passed; 0 failed; 0 ignored; 0 measured; 4056 filtered out` |
| `trust-cg-cli --test link_options` | `test result: ok. 16 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `trust-cg-cli --bin trust-cg` | `test result: ok. 29 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `trust-cg-codegen --test e2e_aarch64_elf_tlsie` | `test result: ok. 11 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `trust-cg-codegen --test e2e_aarch64_link_runtime` | `test result: ok. 21 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out` |
| `cargo check -p trust-cg-codegen` / `--features verify` / `-p trust-cg-lower -p trust-cg-cli`, `cargo build -p trust-cg-cli` | exit 0 |
| `scripts/check_fmt.sh` | OK |
| gate script tests (Linux, Darwin, Linux bridge) | `Ran 94 tests`, `OK (skipped=1)` |
| `native_test_host_matrix.py --check`, `check_documentation.py --write` (no change) then `--check`, `generate_diagnostics_inventory.py --check` | exit 0 |

New tests, relative to the second repair (4076 → 4077 library tests, 21 → 22
`link_driver`, 14 → 16 `link_options`):

- `link_driver` `forwarded_values_beginning_with_at_are_refused_as_response_files`
  refuses each of the six forwarded values on Linux and Darwin (before a
  nonexistent driver is spawned), accepts `./@` spellings and an `@` after
  the first character, and accepts the dyld path tokens on Darwin only.
- `wl_groups_refuse_driver_owned_and_malformed_arguments` now also accepts
  `-dn,-lprobe,-dy` and `-non_shared`.
- `link_options`
  `linux_tls::response_files_in_forwarded_values_are_refused_by_name`
  replays the verifier's `--rpath`, `--soname` and `-o` commands and adds an
  input path and `-L`/`-l` values; each is refused with no file written
  anywhere and the existing files byte-identical, and the `./@` twin runs 42.
- `link_options`
  `linux_tls::unexamined_link_routes_are_the_documented_boundary` pins the
  `-Wl,le.o` and `-l :le.o` routes (user exits 236).

### Mutation leg (records/repair-3/mutation)

`response-file.patch` keeps `response_file_refusals` called but discards its
result, so the mutant compiles under `-D warnings` while the `@` refusal is
disabled. `unit_response_file` and `cli_response_file` fail with real `test
result: FAILED.` lines. Replay: `trust-cg --rpath @resp -o preexist
tls_lib.tmbc` now reaches gcc, which expands `resp` and has GNU ld write a
local-exec `libevil.so` (`add x0, x0, #0x10`); `preexist` keeps its hash
(the redirection went elsewhere), and `userE` linked against `libevil.so`
exits **236**. After the leg the file was restored, `trust-cg` was rebuilt,
its SHA-256 matched the qualifying binary, and the tree was clean
(`mutation/results.json`: `test_leg_failed`, both `replay` flags,
`restored_binary_matches_qualifying` and `restored_clean` are `true`).

### Boundaries and residuals

- This is execution and linker-output evidence on one host, not proof.
- The `@` refusal covers only the values trust-cg forwards. It assumes gcc,
  collect2 and GNU ld expand `@<file>` (they do on this host). Whether ld64
  expands the Darwin dyld path tokens is unchecked.
- The over-refusals from the second repair still hold.
- The scan still covers only positional AArch64 ELF64 relocatable inputs and
  the staged image. The `-Wl`, `-l:`, archive-member, linker-script and
  shared-library routes are documented as unexamined and pinned as such;
  they are not fixed here.
- A staged link killed mid-write can leave its 0700 staging directory. The
  arm64 Darwin code-signature check still reads and removes the output path
  itself, and was not changed.

### Reproduce

`harnesses/qualify-tls-output-guard-3-20260923.py WORKTREE RUN` needs
`RUN/inputs/*.tmbc` (the gunzipped `records/inputs`, plus
`tls_reader_thread.tmbc` for the route probes). Run
`harnesses/mutation-tls-output-guard-3-20260923.py WORKTREE RUN` after it.
`harnesses/archive-tls-output-guard-3-20260923.py RUN DEST` writes
`records/repair-3` and regenerates `inventory.json`, checking that every
earlier entry is unchanged.
