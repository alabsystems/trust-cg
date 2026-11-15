# L02-P10: closure record — 2026-10-15

This is the durable closure record that task LA-05 in
docs/completion-progress.md owes for
closure-ledger gap L02-P10 (Linux AArch64 link-time relocation limits). The
closure ledger marks
the gap `CLOSED e8130d958` under ruling LD-74 of the
decision record. The record binds the
closing re-check's three gate targets to the commands, source and executable
identities of an independent re-run at `e8130d958` on the Linux AArch64 host.
It follows the
durable evidence policy.

It is execution and object evidence from one host, compiled in Trust's
explicit unverified lane (`targo --unverified`; targo printed "this run
emits no proof claim"). It is not a proof. It does not
close the L02 acceptance row, which stays OPEN against the full
Linux AArch64 contract.

## The claim and its boundary

**Gap text** (ledger): "Target relocation limits delegated entirely to the
linker; no range-extension, LDST lo12 forms or overflow controls". Closing it
needs "documented/modeled limits per kind, a large-object or
synthetic-distance control that triggers linker overflow, and either
range-extension support or a typed refusal". The thirteenth closure audit
(`baf1a4dee`) found every gap-text criterion met. Its blocking findings were
a fail-open in the link driver and a red floor target.

**The closing rule, LD-74** (TAKEN 2026-10-15): a row is CLOSED when

1. a closure audit's auditor and every skeptic but one say CLOSE under the
   explicit closing standard (stated fail-closed refusals, trust boundaries
   and out-of-scope items do not block);
2. the remaining skeptic's blocking findings are repaired on one branch and
   an independent verifier confirms the repair; and
3. a closure re-check that takes the blocking skeptic's lens says CLOSE on
   the repaired head.

"A finding that is wrong code or a fail-open is never waived this way: it
must be repaired and re-checked. Reversible: reopen the row by a dated note
when a later audit or user finds an in-scope defect."

**How L02-P10 met it.** The ledger note and LD-74's "Applied" line give
this history:

- **Thirteenth audit at `baf1a4dee`: unanimous KEEP_PARTIAL.** Two findings
  blocked. The first was a fail-open: code that LLD compiled from bitcode
  the driver could not read skipped the GOT-window check. The second was a
  red floor: `link_options` failed 24 of 68. The repairs are LD-58, LD-59,
  LD-60 and LD-64, and they landed in `8cc4ab677`.
- **Fourteenth audit at `8cc4ab677`.** All three reviewers reported one
  finding: an input named like LLD's compiled object hid that object. LD-69
  repaired it, and the repair landed through `1b83ce066`.
- **Fifteenth audit at `b3070867f`.** The auditor and the soundness skeptic
  said CLOSE. The false-refusal skeptic blocked on one finding, rated low.
  It was fail-closed: a false refusal of a fat object linked with
  `--lto-partitions=N>1` and no `--fat-lto-objects`. That finding was
  repaired in `5726a440a`, the correction to LD-69 dated 2026-10-15. The
  verifier CONFIRMED the repair, and a closure re-check with that skeptic's
  lens said CLOSE. The repair was merged as `e8130d958`. LD-69's correction
  also records a second low finding, from skeptic 1: a refusal named an
  object compiled from an uncounted fat object after the counted bitcode
  input alone. The same repair fixed it; the verdict was unchanged.

The blocking finding of the fifteenth audit was neither wrong code nor a
fail-open, so LD-74's exclusion does not apply.

**What CLOSED does not claim.** The rulings and LIMITATIONS keep these
conservative refusals, unmeasured cases and trust boundaries, quoted by LD
number:

- **LD-07** (thread-local templates, segment permissions, LLVM bitcode):
  - the thread-local template rule applies to the whole image;
  - an image without a section header table that has a `PT_TLS` with
    memory is refused, even in the linkers' own layouts (a correct
    `-z nosectionheader` TLS link included);
  - an execute-only segment is refused, because trust-cg's jump tables lie
    in `.text`;
  - a `PT_TLS` that begins with other bytes is refused for LLD and gold too;
  - where trust-cg's `.eh_frame` lies is over-approximated through both
    LLD (the whole output section, where it holds other input) and gold
    (its merged `** eh_frame` data).
- **LD-58:** where the objects LLD compiled are not read (another linker's,
  an LLD whose `--version` was not measured, anything LLD did not write to
  the stage in full), every check that needs them refuses the image as
  `[TCG-LINK-LTO-OBJECTS-UNREAD]` (`unclassified`, conservative).
- **LD-60:** uses found in a fat object's own code are an
  over-approximation: they "can refuse a link, never admit one".
- **LD-64 and LD-69, "Not covered":**
  - a C driver can still run another linker altogether;
  - an LLVM plugin for gold or GNU ld was not measured;
  - a file replaced between the link and the driver's read of it is not
    detected.
- **LD-69:**
  - through an LLD whose `--version` was not measured, a link that loads an
    AArch64 fat object is refused wherever a check needs the compiled code;
  - every LLD 22.1.6 link that loads a fat object is linked twice.
- **LD-69, as corrected by the fifteenth audit.** These stay refused as
  unread:
  - an empty file beside a non-empty one;
  - a counted bitcode input whose link left only empty files;
  - a non-empty file that is not an AArch64 relocatable object.

  Also from that correction:
  - a task's file left out is refused (fail-closed; no measured LLD wrote
    such a set);
  - the separate two-dash `--plugin-opt lto-partitions=<N>` spelling was not
    measured;
  - "Not covered: an LLD other than 22.1.6, as before. A link LLD could
    make that compiles bitcode, links an ELF image, and writes only empty
    files was not found." Reading only empty files as "compiled nothing"
    rests on that measurement.
- **The ledger note's standing scope:**
  - static glibc links with a linker script or `-z muldefs` are refused
    deliberately, even when they would run;
  - not examined: registration through `dlsym` or through a library reached
    only as another library's `DT_NEEDED`, LSDA contents, range-extension
    and erratum veneers, non-Linux links, and links outside the driver;
  - dynamic C-runtime rebinding and identity-trusted driver files are trust
    boundaries;
  - LLD's TLS/non-TLS clash belongs to L03-P6, and gold's non-PIC local
    binding to L02-P2.
- **LIMITATIONS** (the verifier note dated 2026-10-15): the executable-stack
  refusals read only the `-Wl` groups the driver is given. A C driver that
  appends `-z execstack` itself still gets an executable stack installed.
- **LIMITATIONS, the second conservative thread-local refusal:** a `PT_TLS`
  whose file part reaches past the file part of its `PT_LOAD` is refused,
  even where a page mapping happens to hold the template's bytes.
- **Measured linkers only:** the rules were measured against GNU ld 2.42,
  gold 2.42, LLD 22.1.6 and glibc 2.39 on one host.

This list is a selection, not the whole: the L02-P10 link-driver sections of
LIMITATIONS state further conservative refusals, each beside the rule it
belongs to.

## What this record re-ran, and what it carries as reported

The closing re-check reported these results:

- `link_options` 71/71 (trust-cg-cli);
- `e2e_aarch64_link_runtime` 35/35;
- `link_driver` 136/136;
- every audit reproducer refused or read;
- ordinary links through GNU ld, gold and LLD installed.

This record re-ran the three test targets at `e8130d958` and nothing else.
It did not re-run these, and carries them as LD-69's fifteenth-audit
correction and LIMITATIONS report them:

- the audits' standalone reproducers (`repro/repro.out`,
  `repro/decoy14.out`);
- skeptic 2's 185-link sweep harness;
- the 240 + 108 LLD measurement links;
- the five mutants of the fifteenth repair.

The sources and logs of the thirteenth to fifteenth audits' harnesses are
not in the tree, unlike the twelfth audit's
([2026-10-03 record](../2026-10-03-linux-l02p10-audit12/README.md)). To that
extent those citations rest on host-local captures. The durable evidence
policy says of such a citation that it "points at unarchived evidence, and
every row that depends on it stays open to that extent".

The committed form of each of those audits' findings is a native row of
`link_options`. Each row passed here:

| Audit | Native row |
| --- | --- |
| Thirteenth | `linux_got_page::got_base_code_lld_compiles_from_bitcode_is_read_on_every_lto_route` |
| Fourteenth | `linux_got_page::compiled_code_lld_wrote_is_read_whatever_the_inputs_are_named` |
| Fifteenth | `linux_got_page::lld_links_that_compile_nothing_are_installed_under_lto_partitions` |

Each row makes the installed, read and refused links that its doc comment
lists. The thirteenth's and fifteenth's rows link through the driver with
LLD only (directly, or through C drivers that run LLD); the fourteenth's
also links through GNU ld and gold.

## Commands

The commands ran in a fresh, detached worktree. They used no
`TCG_LLD_DIR` and needed no fetch, because `--offline` resolved every
dependency. Each step ran under the machine's `build-slot` gate, which set
`CARGO_BUILD_JOBS`. The paths are the original capture locations: local
provenance, not portable evidence.

```sh
git -C $HOME/trust-cg worktree add --detach /home/ayates/trust-cg-wt/la05rec e8130d958
export PATH="/home/ayates/toolchains/trust-ae9c2c1d/bin:$HOME/.local/lib/trust-cg/ae9c2c1d-tools/bin:$HOME/.cargo/bin:$PATH"
export CARGO_TARGET_DIR=/home/ayates/trust-cg-wt/la05rec-target
export TCG_REQUIRE_LLD=1 TCG_REQUIRE_GOLD=1
cd /home/ayates/trust-cg-wt/la05rec

# Build (2026-10-15T23:13:19Z to 23:28:14Z; both exit 0).
bash scripts/trust_cargo.sh test --locked --offline -p trust-cg-cli --test link_options --no-run
bash scripts/trust_cargo.sh test --locked --offline -p trust-cg-codegen --test e2e_aarch64_link_runtime --lib --no-run

# Run (2026-10-15T23:28:28Z to 23:30:35Z; each exit 0).
bash scripts/trust_cargo.sh test --locked --offline -p trust-cg-cli --test link_options -- --nocapture
bash scripts/trust_cargo.sh test --locked --offline -p trust-cg-codegen --test e2e_aarch64_link_runtime -- --nocapture
bash scripts/trust_cargo.sh test --locked --offline -p trust-cg-codegen --lib -- link_driver:: --nocapture
```

`scripts/trust_cargo.sh` removes `TCG_REQUIRE_LLD` and `TCG_REQUIRE_GOLD`
from targo's environment and hands them to the test executables through a
Cargo target runner. With either variable set, a missing linker fails its
test instead of printing `SKIP:`.

## Results

The denominators are fixed: each is every test the target compiles on
`aarch64-unknown-linux-gnu`.

| Target (owner) | Passed | Failed | Ignored | Filtered out | `SKIP` lines | Re-check |
| --- | --- | --- | --- | --- | --- | --- |
| `link_options` (`trust-cg-cli`, `tests/link_options.rs`) | **71** | 0 | 0 | 0 | 0 | 71/71 |
| `e2e_aarch64_link_runtime` (`trust-cg-codegen`, `tests/`) | **35** | 0 | 0 | 0 | 0 | 35/35 |
| `link_driver` (`trust-cg-codegen` lib unit tests, filter `link_driver::`) | **136** | 0 | 0 | 4,730 | 0 | 136/136 |

Each count equals the re-check's. No `SKIP` line appeared in any log, so
every LLD and gold leg ran. libtest reported the runs finishing in 83.12 s,
8.13 s and 26.08 s.

- **`link_options`:** 71 is the floor minimum that `e8130d958` pins in
  `scripts/check_linux_aarch64.py` (`("trust-cg-cli", "link_options"): 71`).
  The source has 73 `#[test]` functions; the other 2 are
  `#[cfg(target_os = "macos")]`.
- **`e2e_aarch64_link_runtime`:** the source has 38 `#[test]` functions; the
  other 3 are in the macOS-only `darwin_native` module.
- **`link_driver`:** 135 rows are in `link_driver::tests`, including the new
  `compiled_nothing_is_only_empty_files_one_per_task`. The other row is
  `link_driver::linked_image_evidence::tests::run_link_removes_a_stale_record_before_the_driver_runs`.

The `e2e_aarch64_link_runtime` log shows the linkers' own overflow refusals
through each linker. Examples are `rust-lld: error: ... relocation
R_AARCH64_ADR_GOT_PAGE out of range` and `/usr/bin/ld.gold: error: TLS
variable referred by reloc 541 is too far from TP`, beside the driver's
named refusals (`[TCG-LINK-EH-FRAME-UNPROVEN]`,
`[TCG-LINK-TLS-TEMPLATE]`).

The results for earlier commits are as reported in LD-69, not re-measured
here. At `b3070867f` (the fourteenth repair) they were `link_driver` 135/135,
`link_options` 70/70 and `e2e_aarch64_link_runtime` 35/35. The fifteenth
repair added one unit row and one native row.

## Identities

The source tree is the same as current `origin/main` (`6097041be`) apart
from documentation. `git diff --stat e8130d958 6097041be` touches only
`LIMITATIONS.md`, `docs/aarch64-completion-audit-2026-09-17.md`,
`docs/completion-progress.md`, `docs/decision-record.md` and one report
README.

| Item | Identity |
| --- | --- |
| Source commit | `e8130d958525368d8951ded3bf3ecd36937efb91`, which merges repair `5726a440a3cb8c8517905611cc3e23f7a3bde8b8` into `b8079089fc9541468118e37e38f62369fee5ad35`; worktree clean |
| `Cargo.lock` | sha256 `187fd25bafda41f89b1b278117fb8f6a49332d4a260044164c21ca5a850bbbda` |
| `rust-toolchain.toml` | `channel = "trust"`; sha256 `67044c89c6c085fd7c29f5f13331ad1e9b4bf732df917f1df3960079141790e0` |
| trust-ir | `dc2b80739ea947557a34b59a10f6c8510e690de7` (`trust-ir` 0.14.0; 5 lock packages); in both crates' graphs (`targo tree`) |
| Clean | `92bcc897908b248154ace880a6c518a3d9c09634` (`clean-kernel` 0.9.0; 9 lock packages); in both crates' graphs |
| AY crates | `Cargo.lock` pins 38 `ay*` packages at `8e7b3fe6bdea88c07e1e7f82913f82d70ab1d3ee` (0.27.0). None is in the normal, build or dev graph of `trust-cg-cli` or `trust-cg-codegen`; they enter only through `trust-cg-regalloc`'s optional `ay-regalloc` feature |
| AY executable (recorded) | `trust-cg-verify`'s build script recorded the build compiler's sysroot `bin/ay`: sha256 `81efc9f3bc4058062a64de75b4dd9827217a7b5f7b315f257b757bff818de0c5`, commit `657ce1821183b2076bb994167f830bde5d8e0509`, version 0.27.0, increment 10454, no overlay. The first `ay` on the run's `PATH` is that sysroot file; the next, `~/.local/lib/trust-cg/ae9c2c1d-tools/bin/ay` (→ `store/ay/ae9c2c1d/bin/ay`), has the same bytes |
| Compiler (`trustc -vV`) | `rustc 1.99.0-dev (ae9c2c1da 2026-09-21) (trustc 0.1.0)`, `commit-hash: ae9c2c1daa0fc80afbfd380e493f5581ac714acb`, `host: aarch64-unknown-linux-gnu`, `trust: 0.1.0`, `LLVM version: 22.1.2` |
| `trustc` | `/home/ayates/toolchains/trust-ae9c2c1d/bin/trustc` (a hard link of `bin/rustc`): sha256 `b2d4fa4bb1ce8106539d7c2967f1eb3f3f613293b8c905de586fbb4f5ffa4212` |
| Compiler driver | `lib/librustc_driver-3d85360a91bba93f.so`: sha256 `1e9c5dded395234c61bed09a99a70e25f5898d8332782ce1c95a673a01b39050`, which matches the package `PROVENANCE` (`BUILD-STAMPED-CLEAN`, sealed 2026-09-24) |
| `targo` | `targo 1.99.0-dev (ae9c2c1da 2026-09-21) (targo 0.1.0)`; sha256 `4d877f14d86c786a1c077d5423f14304493d56ecf058447d6d8244cbb8a446ba` |
| Toolchain lane | `scripts/trust_toolchain.py --purpose workspace`: `selection: path`, `lane: unverified`, sysroot `/home/ayates/toolchains/trust-ae9c2c1d` (also the target directory's `.rustc_info.json` sysroot) |
| GNU ld | `/usr/bin/ld` → `/usr/bin/aarch64-linux-gnu-ld.bfd`: `GNU ld (GNU Binutils for Ubuntu) 2.42`; sha256 `1e4d3369b76845fa8e099b83513bf28f6f722e046f9b2cde1378c9e27f96d19c` |
| gold | `/usr/bin/ld.gold` → `/usr/bin/aarch64-linux-gnu-ld.gold`: `GNU gold (GNU Binutils for Ubuntu 2.42) 1.16`; sha256 `91be8ad8ab23070ae4d55989793e457d507370cb3537338b403f6f5e8229b6d9` |
| LLD | `~/.local/bin/ld.lld` → the stock Rust 1.97.1 package's `gcc-ld/ld.lld` wrapper (sha256 `61ec0509c9d489c606b27c5658ead32d86200c83fc342800e72492fc6385fe7b`). The wrapper runs `rust-lld` (sha256 `533dffee7995258d3de4f995b0c926f18a5245a0aef09896901deee6ef144eb7`): `LLD 22.1.6 (/checkout/src/llvm-project/llvm dcc3606807c989700e0ac1cac18c31741bcd40d9) (compatible with GNU linkers)`. `rust-lld` links `libLLVM.so.22.1-rust-1.97.1-stable` (sha256 `639f2d6b7e64b21decab15bb2851e62be84fac37d08fc2d921886ce72fd1e458`) |
| `cc` | `/usr/bin/cc` → `/usr/bin/aarch64-linux-gnu-gcc-13`: `cc (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0`; sha256 `a20520ee21543f243d40636a9181a142c45ecd989de31ab86b99a8ea5ada870d` |
| Other tools the tests run | Binutils 2.42 (`2.42-4ubuntu2.10`), each `/usr/bin/<tool>` → `/usr/bin/aarch64-linux-gnu-<tool>`: `as` `1ffda50efb6d91b6b05ef933aced099595c36577594c0296c91161f2d13db374`, `ar` `f4583a612510e038dbc1ae8afb5eae5f0445c435bdd7c4c28e78acc7e757d2b1`, `objcopy` `1216ee3b084501a5132643fef4bba7221186f4b7dc99cd46e2bf9e3e7d37c344`, `readelf` `6bca2bbd23b072db9e9a19ae0e65cf7b7c15c08a3c2cf01dd56453e1ac9340b1`, `nm` `338d018c73ef394539da2566405a1f2f50a808e3c15ef72e9b48dd2f0b0d262f`, `objdump` `f2e917a5d118ebf5679b24740e20d30338308e7f3f0630527c469de452d5a250`; `c++` → `/usr/bin/aarch64-linux-gnu-g++-13` (13.3.0) `fc02363794280f404c6ca6f5da1c8fe469be902e9de140d35d8573bb3393f53b`. GCC's own subprograms and the C runtime objects are identified by package only (`gcc-13` `13.3.0-6ubuntu2~24.04.1`, `libc6-dev` `2.39-0ubuntu8.7`) |
| Host | Linux 6.17.0-1026-nvidia aarch64, Ubuntu 24.04.4 LTS, glibc 2.39 (`2.39-0ubuntu8.7`), 4 KiB pages, 20 CPUs |

Notes on the identities:

- **Which linker each leg used.** The tests find LLD in `TCG_LLD_DIR`
  (unset here), then `~/.local/bin`, then `PATH`. gold is `ld.gold` on
  `PATH`. GNU ld is `cc`'s default: `cc -print-prog-name=ld` gives `ld`,
  which resolves on `PATH`. The logs name `rust-lld` and `/usr/bin/ld.gold`
  in the linkers' own error lines.
- **Where the LLD comes from.** The Trust package ships no `rust-lld`: its
  `lib/rustlib/aarch64-unknown-linux-gnu/bin` has none. So the LLD under
  measurement is the stock Rust package's. It is the linker under test, not
  a compiler of trust-cg. Its version string is the `LLD 22.1.6` that
  LD-58 to LD-69 were measured against. No `STOCK EXCEPTION` marker names
  it where the tests look it up (`lld_dir` in `link_options.rs`,
  `linker_drivers` in `e2e_aarch64_link_runtime.rs`); this record changes
  nothing there.
- **Whether AY ran.** The test sources name no solver. That these tests did
  not run AY is inferred from that, not measured.

**Built test executables** (sha256, not archived; the durable evidence
policy identifies executables by hash):

| Executable | sha256 |
| --- | --- |
| `link_options-521a1064a3808c11` | `8aebb30bab8af975ce4297749baf62dbe0f48d904d32b2f962f3363bc8b27311` |
| `trust-cg` CLI (`CARGO_BIN_EXE_trust-cg`) | `70305f217acbee44dea01ae610d5b726d933357355a7aae879ae12f971affc2d` |
| `e2e_aarch64_link_runtime-ce3aedd7e956cca3` | `80b599db50de5b392a3d6058cb074eafaadeca8222e1c92511a785fbc090c481` |
| `trust_cg_codegen-489f6918048e47b0` (lib unit tests) | `b5eadda9bb1c837bd837653be3611fb4fcb15d70bf8c15253a26d4b5bf36181a` |

## Evidence record

```text
Task ID / kind / platform: LA-05 / Closure / Linux AArch64 (aarch64-unknown-linux-gnu)
Parent ledger gaps and acceptance row: L02-P10; acceptance row L02 (stays OPEN)
Input candidate and implementation commit: e8130d958 (merge of repair 5726a440a into b8079089f);
  the repair chain 8cc4ab677 (LD-58..LD-60, LD-64), 1b83ce066 (LD-69), 5726a440a (LD-69 correction)
Compiler, sysroot, dependency pins and backend hash: Trust ae9c2c1da (trustc 0.1.0, LLVM 22.1.2),
  sysroot /home/ayates/toolchains/trust-ae9c2c1d, trustc sha256 b2d4fa4b..., librustc_driver
  sha256 1e9c5dde..., targo sha256 4d877f14...; unverified lane. trust-ir dc2b80739ea9,
  Clean 92bcc897908b, AY crates 8e7b3fe6bdea (not in these graphs), recorded bin/ay 81efc9f3...
  (commit 657ce1821183). Backend: trust-cg CLI sha256 70305f21..., test executables in the
  table above
Required host, prerequisites and dependent task IDs: native Linux AArch64 with GNU ld 2.42,
  gold 2.42 (binutils 2.42), LLD 22.1.6, GCC 13.3, glibc 2.39; TCG_REQUIRE_LLD=1
  TCG_REQUIRE_GOLD=1; no dependent task
Smallest failing input / expected behavior: the fifteenth audit's blocking finding, a fat object
  linked through LLD with --lto-partitions=N>1 and no --fat-lto-objects, was refused as
  [TCG-LINK-LTO-OBJECTS-UNREAD] at b3070867f; expected: installed, running the object's own code
  (native row lld_links_that_compile_nothing_are_installed_under_lto_partitions)
Completion condition: LD-74 (1) audit CLOSE but one skeptic, (2) that skeptic's blocking finding
  repaired and verifier-confirmed, (3) closure re-check CLOSE; this record binds (3)'s gate targets
Exact commands and fixed denominator: see Commands; link_options 71, e2e_aarch64_link_runtime 35,
  link_driver 136 (every test each target compiles on this host)
Before / after matches, refusals, failures, skips and timeouts: before (b3070867f, as reported in
  LD-69): link_driver 135/135, link_options 70/70, e2e 35/35. After (e8130d958, re-run here):
  71/71, 35/35, 136/136; 0 failed, 0 ignored, 0 SKIP lines, no timeout
Negative or mutation control: the native rows' refused links (decoys, unread compiled objects,
  linker-overflow controls) passed here; LD-69's five fifteenth-repair mutants, each caught,
  are cited, not re-run
Evidence location and evidence class: this README (committed); logs host-local under
  /home/ayates/trust-cg-wt/la05rec-logs/ (local provenance only). Execution and object evidence
  on one host, unverified compilation lane; not proof, not an acceptance record
Remaining limitations and next smallest task: the conservative refusals and trust boundaries
  above; the 13th-15th audits' reproducer and sweep sources are host-local, not committed.
  Next: archive those sources beside a report if they are recovered; the L02 acceptance row
  needs its own complete review
Task status / ledger status / acceptance status: DONE / L02-P10 CLOSED e8130d958 (LD-74) /
  L02 OPEN
```

## Local provenance (not committed)

These files are under `/home/ayates/trust-cg-wt/la05rec-logs/`. They are
original capture locations, not portable evidence.

| File | Contents |
| --- | --- |
| `run.sh` | The step script |
| `driver-build.log`, `driver-test.log` | Step times and exit codes |
| `build-cli.log`, `build-codegen.log` | The build steps |
| `link_options.log` | sha256 `015a81b241b2a13256b1640b8c317d2eed0f4b15bfbd6df7d32cfd4610f9ab78` |
| `e2e_aarch64_link_runtime.log` | sha256 `8b246b81bb9594b75bcac3c0b9fe1626dcaf34f13330b5596462e66aa5b16c4d` |
| `link_driver.log` | sha256 `d67a13e1d67155e4cb737f0581812ae6edb335f851e4ee2e80752e4b6bb7af01` |
| `tree-cli.txt`, `tree-codegen.txt` | `targo tree` output |
