# AArch64 ELF BTI/PAC link refusal on Linux — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

> Superseded in part by the review-repair run
> [`2026-09-23-linux-bti-pac-refusal-2`](../2026-09-23-linux-bti-pac-refusal-2/README.md).
> In this run the test's `force-bti` warning matcher kept any stderr line
> containing `force-bti`, and its scratch directory name contained that text.
> It was therefore not pinned to the linker's message. The refusal messages of
> `c6b1d2483` also gave a rationale that is false for `-z pac-plt` under GNU
> ld and for `-z bti-report`. The records below are unchanged.

This run covers the BTI/PAC part of ledger gap C-01. It ran on clean source
`c6b1d248375c7a1abd77e58d59d545a3916b129e` (tree
`28199e8c5bab67997cd8749052fc724da9f47797`, empty
`git status --porcelain --untracked-files=all` before and after) on the
Linux AArch64 GNU host. Recording wrappers stood in front of `cc`, `readelf`
and `getconf` for the native target. Every target passed:

- `e2e_aarch64_elf_stack_zero_fill` (`--show-output --test-threads=1`, wrapped):
  `test result: ok. 9 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out`
- `trust-cg-codegen --lib link_driver`:
  `test result: ok. 14 passed; 0 failed; 0 ignored; 0 measured; 4052 filtered out`
- `trust-cg-cli --test link_options`:
  `test result: ok. 8 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out`
- `trust-cg-cli --bin trust-cg invalid_link_options_are_refused_by_name`:
  `test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 28 filtered out`
- `trust-cg-codegen --lib` (the whole library suite):
  `test result: ok. 4065 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out`.
  The ignored test is the pre-existing explicit real-tool
  `raw_machir_request_cache_real_exhaustive_campaign`. The base `be25d1ba6`
  passed 4,063; this change adds the two link-driver tests.

trust-cg emits no BTI landing pads, no PAC instructions and no
`GNU_PROPERTY_AARCH64_FEATURE_1_AND` note. The link driver's `-Wl` parser
now refuses `-z force-bti`, `-z pac-plt` and `-z bti-report[=<mode>]` with
`[TCG-LINK-BTI-PAC]`, on every target and in the `-z,<keyword>` and
`-z<keyword>` spellings. C-01 stays **PARTIAL**.

## Host

`records/results.json` (`host`) holds the identities: Linux
`6.17.0-1026-nvidia` on NVIDIA Grace. Its `/proc/cpuinfo` Features line
includes `bti`, `paca` and `pacg`. The host has glibc 2.39
(`Ubuntu GLIBC 2.39-0ubuntu8.7`), GNU ld 2.42 (`/usr/bin/ld` ->
`aarch64-linux-gnu-ld.bfd`, SHA-256 `1e4d3369…`) and GNU readelf 2.42. `cc`
is Ubuntu gcc 13.3.0. rustc and cargo are 1.97.1. `records/tools.json`
gives the path and SHA-256 of each wrapped tool; each wrapper re-checked
that hash before and after every call.

## What the run shows

- **The refusal.** `wl_groups_refuse_bti_and_pac_hardening_with_a_named_code`
  covers `-z,force-bti`, `-zforce-bti`, `-z,pac-plt`, `-zpac-plt`,
  `-z,bti-report`, `-zbti-report`, `-z,bti-report=error`,
  `-zbti-report=warning` and `-z,bti-report=none`, and the keyword before or
  after admissible options. Each refusal starts with
  `[TCG-LINK-BTI-PAC] `-z <keyword>` is refused:`, names the missing landing
  pads and property note, and carries the `-Wl,` flag as spelled. A `-z`
  split from its keyword into a later group is refused first by the existing
  same-group rule. `force-bti=0` as a `--defsym` value is forwarded. The CLI
  unit test refuses `-Wl,-z,force-bti`, `-Wl,-zpac-plt` and (for a Darwin
  target) `-Wl,-z,bti-report=error`. `link_options` runs the `trust-cg`
  binary with three spellings, and each is refused before the input is read.
- **The unchanged stack contract.**
  `bti_pac_refusal_leaves_the_noexecstack_contract_unchanged` checks three
  things. The three execstack spellings are still refused with the old
  message and without the new code. A `-z,noexecstack` group is forwarded.
  Linux executable and shared links still emit `-Wl,-z,noexecstack` before
  the objects, and a Darwin link has no `-z` option.
- **No property note in any route object.** GNU `readelf -n -W` lists no
  `NT_GNU_PROPERTY_TYPE_0` in the 48 route objects: 12 emitter routes at
  O0–O3, 13 distinct byte images because several routes do not depend on
  the level. The predicate is the same one the host-neutral route test
  applies. On a gcc `-mbranch-protection=standard` object it reports
  `NT_GNU_PROPERTY_TYPE_0 … AArch64 feature: BTI, PAC`. Fourteen readelf
  listings show a property note: that control object (read twice), the three
  harness objects, the harness control image and the eight forced outputs.
  None is a CG object (`records/results.json`, `calls`).
- **A forced BTI link claims what the CG code lacks.** At O0–O3 a CG
  function object (`long cg_bti_bump(long)`, `x + 1`) linked with
  `cc -shared -Wl,-z,force-bti` succeeds. GNU ld names the object in its
  warning: `<path>/cg-O<n>.o: warning: BTI turned on by -z force-bti when all
  inputs do not have BTI in NOTE section.` The output carries
  `AArch64 feature: BTI`, while the default `-shared` link carries no property
  note. `records/direct/` repeats this outside the test from the retained
  `cg-O2.o`. The object has no notes. The forced `libbti.so` has
  `GNU_PROPERTY`, `NT_GNU_PROPERTY_TYPE_0 … AArch64 feature: BTI` and
  `GNU_STACK … RW`. There ld also warns about the host's `crti.o` and `crtn.o`.
- **Execution.** The harness is a startfile-free executable. Its entry is
  `BTI JC` (`hint #38`), and its C code, built with
  `-mbranch-protection=standard`, starts every function with a landing pad.
  It prints `indirect call`, calls `cg_bti_bump` through a volatile pointer
  (`BLR`) and prints `returned 42`. Linked normally with the CG object it
  printed both lines and exited 0 at O0–O3 (asserted). With a BTI-marked C
  callee under `-z force-bti` the link warned about nothing and the image ran
  (asserted), so the harness itself survives BTI enforcement here.
  `/proc/cpuinfo` lists `bti`, so the CG image linked with `-z force-bti` was
  run. Its outcome is recorded, not asserted: at every level it exited with
  SIGILL (status 132) after printing only `indirect call`. That is the
  indirect call into the CG function, which has no landing pad. O1–O3 give
  byte-identical objects and images for this function, so the four records
  cover two distinct images.
- **Host startfiles (record).** An ordinary `main` built with branch
  protection and linked with `-Wl,-z,force-bti` also draws the warning for
  the host's `Scrt1.o`, `crti.o` and `crtn.o`. It died with SIGILL before
  `main` printed. So a forced BTI link of any executable fails on this host.
  The startfile-free harness exists to make the CG fault attributable.
- **Stack controls, unchanged.** Every non-TLS route and the O0–O3 zero-fill
  libraries linked without `-z noexecstack` have `PT_GNU_STACK` RW. The O0–O3
  dlopen loader passes, and the `-z execstack` control is RWE.
- **glibc 2.41 (not exercised).** The test now dlopens the RWE control and
  requires failure (exit 2) when `getconf GNU_LIBC_VERSION` is 2.41 or
  later. On this glibc 2.39 host it loaded (`exit status: 0`), which is
  recorded, not asserted. The 2.41 assertion has never run. No newer-glibc
  host or container was available. `sudo` needs a password, and the user
  is not in the `docker` group, so `/var/run/docker.sock` refuses the
  connection.

## Negative controls

- The in-test controls above: the BTI/PAC object that the note predicate
  must flag, the RWE `-z execstack` library, and the BTI-marked harness
  callee that must run under enforcement.
- Development-time mutation (transcript not retained). With the refusal
  disabled (`.filter(|_| false)` on the keyword match),
  `wl_groups_refuse_bti_and_pac_hardening_with_a_named_code` failed and the
  other 13 link-driver tests passed. The source was restored before commit.

## Records

- `records/results.json`: source and host identities, each command, exit
  status and `test result:` line, and the tests' `record:`/`glibc`/`host
  linker` lines. It also has a per-call summary (tool, arguments, exit,
  `force-bti` warning lines, whether a readelf listing shows a property
  note) and the direct-listing summary.
- `records/logs/*.log.gz`: complete stdout/stderr of the five runs.
- `records/calls.tar.gz`: all 149 wrapped calls (104 `readelf`, 44 `cc`,
  1 `getconf`) with request, result, stdout and stderr.
- `records/blobs.tar.gz`: content snapshots (≤ 1 MiB) of every file the
  calls named under the two BTI/PAC tests' scratch directories: the route
  objects, CG objects, harness sources and objects, and the linked images.
- `records/direct/`: the retained `cg-O2.o` (as `cg-O2.o.gz`, because the
  repository ignores `*.o`; the inventory records its decoded hash) and
  gzip-compressed listings of
  `readelf -n`/`-S` of it and of `cc -shared` with and without
  `-Wl,-z,force-bti`, with `readelf -lW`/`-n` of both outputs.
- `harnesses/`: the qualify, capture-wrapper and archive scripts that
  produced this directory. `source/`: the tested `link_driver.rs` and test
  file.
- Recorded paths under `/tmp/claude-1000/…` are the original capture
  locations on the host and are not themselves evidence.

## Boundary

This is object and execution evidence on one host, not a proof. The
refusal applies to `-Wl` groups through the `trust-cg` link driver, whose
only caller is the CLI. A user's own `cc` link and rustc-driven bridge links
do not pass through it and can still force BTI. Other feature-forcing
keywords, such as `-z gcs=always` or x86-64 `-z force-ibt`/`-z shstk`, are
not refused. trust-cg has no BTI/PAC code-generation policy, so CG code runs
unprotected. The SIGILL outcome depends on this loader and kernel guarding
the BTI-marked mapping. The x86-64 and RISC-V ELF emitters still lack
`.note.GNU-stack`, and the glibc 2.41 dlopen control needs a newer-glibc
host.
