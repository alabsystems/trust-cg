# AArch64 ELF BTI/PAC link refusal, review repair, on Linux — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This run follows up the review of the first C-01 BTI/PAC run
([`2026-09-23-linux-bti-pac-refusal`](../2026-09-23-linux-bti-pac-refusal/README.md),
source `c6b1d2483`). The review found three problems:

- The refusal rationale ("the image would claim hardening its trust-cg code
  lacks") was false for `-z pac-plt` under GNU ld and for `-z bti-report`.
- The docs said GNU ld warns only about the CG object.
- The test's `force-bti` warning matcher kept any stderr line containing
  `force-bti`, and the test's own scratch directory name contained that
  text.

This run is on clean source `f14f5b0eb964091e2a58d72f531ed345c1f09c8a` (tree
`c5725744c6b03d311fe6e6b1e65787f25897bd92`). `git status --porcelain
--untracked-files=all` was empty before and after the run. The run used the
Linux AArch64 GNU host, with recording wrappers in front of `cc`, `readelf`
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
  The ignored test is the existing explicit real-tool
  `raw_machir_request_cache_real_exhaustive_campaign`.

The refusal keeps its scope. The link driver's `-Wl` parser refuses
`-z force-bti`, `-z pac-plt` and `-z bti-report[=<mode>]` with
`[TCG-LINK-BTI-PAC]` on every target, in the `-z,<keyword>` and
`-z<keyword>` spellings. C-01 stays **PARTIAL**.

## Host

`records/results.json` (`host`) holds the identities. The host runs Linux
`6.17.0-1026-nvidia` on NVIDIA Grace, and its `/proc/cpuinfo` lists `bti`,
`paca` and `pacg`. It has glibc 2.39 (`Ubuntu GLIBC 2.39-0ubuntu8.7`) and
GNU ld 2.42 (`/usr/bin/ld` -> `aarch64-linux-gnu-ld.bfd`, SHA-256
`1e4d3369…`). The other tools are GNU readelf 2.42, Ubuntu gcc 13.3.0 as
`cc`, gdb 15.1, and rustc and cargo 1.97.1.

The lld probes use `/home/ayates/.local/bin/ld.lld`, which resolves to the
rustup stable toolchain's `gcc-ld/ld.lld` and reports `LLD 22.1.6` (SHA-256
`61ec0509…`). It is put first on PATH only for `cc -fuse-ld=lld`, and its
diagnostics are prefixed `rust-lld:`. `records/tools.json` gives the path and
SHA-256 of each wrapped tool. Each wrapper re-checked that hash before and
after every call.

## What each refused keyword does (records/direct)

Every probe links the retained CG function object `cg-O2.o` (SHA-256
`00de99b43c10…`, stored as `cg-O2.o.gz`) with `cc -shared` and reads the
output with `readelf -n -W`/`-d -W`. `results.json` `direct_summary`
(`keyword_probes`) collects the results:

| keyword | GNU ld 2.42 | LLD 22.1.6 |
| --- | --- | --- |
| `-z force-bti` | links; warns about `crti.o`, `cg-O2.o` and `crtn.o`; output `AArch64 feature: BTI` | links; warns about the same three inputs; output `AArch64 feature: BTI` |
| `-z pac-plt` | links silently; **no** property note; `AARCH64_PAC_PLT` dynamic tag | links; warns that the three inputs lack `GNU_PROPERTY_AARCH64_FEATURE_1_PAC`; output `AArch64 feature: PAC` and `AARCH64_PAC_PLT` |
| `-z bti-report=error` | `warning: -z bti-report=error ignored`; no property note | link fails: `error: … -z bti-report: file does not have GNU_PROPERTY_AARCH64_FEATURE_1_BTI property` for each input |
| `-z bti-report=warning` | `warning: -z bti-report=warning ignored`; no property note | links with the same messages as warnings; no property note |

Only `force-bti` (both linkers) and `pac-plt` (lld only) make the output
claim a property. GNU ld's `pac-plt` gives PLT stubs that authenticate the
GOT entry. A C-only `int main(void) { puts(…); }` built with plain
`cc -O2` prints and exits 0. Linked with `-Wl,-z,pac-plt`, the same program
has no property note and does have `AARCH64_PAC_PLT`, but it dies with
SIGILL (exit -4) before printing. Under gdb the fault is at
`__libc_start_main@plt+12`: `autia1716`. `bti-report` marks nothing. It is
refused only because it configures a BTI link. The refusal messages now give
these per-keyword reasons, and the link-driver unit test pins each one.

## What the run shows

- **The refusal.** `wl_groups_refuse_bti_and_pac_hardening_with_a_named_code`
  covers every spelling. Each refusal also contains its keyword's reason:
  - "GNU ld and lld mark the output BTI-compatible"
  - "lld marks the output PAC (GNU_PROPERTY_AARCH64_FEATURE_1_PAC)"
  - "it marks nothing (GNU ld ignores it; lld only reports"
  
  Each refusal also keeps the common "no BTI landing pads … no
  GNU_PROPERTY_AARCH64_FEATURE_1_AND note" tail. The CLI unit test and
  `link_options` refuse three spellings each.
- **The warning matcher is pinned to the message.** `force_bti_warnings` now
  keeps only lines containing GNU ld's `warning: BTI turned on by -z
  force-bti when all inputs do not have BTI in NOTE section` or lld's
  `-z force-bti: file does not have GNU_PROPERTY_AARCH64_FEATURE_1_BTI
  property`. The test's scratch directory is now `…-bti-link-…`. The test
  also checks the matcher itself: it must reject a linker line that names
  a CG object under a `force-bti` path and a line that mentions
  `-z force-bti` without the warning text, and it must accept both real
  messages.
  
  The harness control link (BTI-marked C callee, `-z force-bti`) must
  print nothing. At each level, the forced harness link must print only BTI
  warnings, and each one must name `cg-O<n>.o`. The per-level
  shared-link assertion now needs the BTI warning text naming
  `cg-O<n>.o`.
- **Which inputs GNU ld warns about.** The forced `-shared` link of each CG
  object warned about `crti.o`, `cg-O<n>.o` and `crtn.o` (3 warnings at
  each level; `records/results.json` `calls`). The startfile-free harness
  link warned about the CG object alone. The ordinary startfile link warned
  about `Scrt1.o`, `crti.o`, `cg-O2.o` and `crtn.o`.
- **Execution (recorded, not asserted).** Linked normally, the startfile-free
  harness returned 42 at O0–O3 (asserted). Linked with `-z force-bti`, it
  died with SIGILL (status 132) after printing only `indirect call` at every
  level. The direct gdb run of the retained forced O2 image
  (`gdb-cg-force-bti-O2`) puts the fault at `cg_bti_bump`, whose first
  instruction is `stp x29, x30, [sp, #-16]!`. That function has no landing
  pad.
  
  The ordinary forced executable (`startfile-force-bti`) died with SIGILL
  and empty stdout. gdb (`gdb-startfile-force-bti`) puts that fault at
  `_start`, which begins with `nop` in the host's unmarked `Scrt1.o`, so
  that executable never reaches `main` or the CG call. O1–O3 give
  byte-identical CG objects (`00de99b4…`) and forced images (`a5bd7796…`),
  so the four level records cover two distinct forced images.
- **No property note in any route object.** GNU `readelf -n -W` lists no
  `NT_GNU_PROPERTY_TYPE_0` in the 48 route objects (12 emitter routes at
  O0–O3). A gcc `-mbranch-protection=standard` object shows `AArch64
  feature: BTI, PAC`. There are 14 property-note listings among the 149
  wrapped calls (104 `readelf`, 44 `cc`, 1 `getconf`), and none is a CG
  object.
- **Stack controls, unchanged.** `PT_GNU_STACK` is RW without
  `-z noexecstack`, and the O0–O3 dlopen loads pass. The `-z execstack`
  control is RWE. On this glibc 2.39 host the RWE control was dlopened with
  exit 0, which is recorded. The glibc ≥ 2.41 refusal assertion has never
  run.

## Negative controls

- The in-test matcher self-check above, the BTI/PAC object that the note
  predicate must flag, the RWE `-z execstack` library, and the BTI-marked
  harness callee that must link silently and run under enforcement.
- **Broad-matcher mutation (retained,
  `records/mutation/broad-force-bti-matcher.log.gz`).** Before the code
  commit, the source had `f14f5b0eb`'s test file except for one line: the
  matcher's filter was replaced by the old `line.contains("force-bti")`.
  With that source,
  `native::linux_forced_bti_links_claim_a_property_the_cg_code_lacks`
  failed at the matcher self-check. The old matcher accepted both
  path-only lines. The source was restored, and it is byte-identical to
  the committed file. That development run was on a tree that was not yet
  committed and is not part of the clean qualifying run.

## Records

- `records/results.json`: source and host identities, each command, exit
  status and `test result:` line, and the tests' `record:`/`glibc`/`host
  linker` lines. It also has a per-call summary, in which
  `force_bti_warnings` is matched by the GNU ld or lld message text. The
  direct probe summary (`direct_summary`) holds the keyword probes, the
  C-only `pac-plt` executable and the two gdb fault locations.
- `records/logs/*.log.gz`: complete stdout/stderr of the five runs.
- `records/calls.tar.gz`, `records/blobs.tar.gz`: all 149 wrapped calls and
  content snapshots (≤ 1 MiB) of the files they named under the two BTI/PAC
  tests' scratch directories.
- `records/direct/*.txt.gz`: every direct command with its stdout, stderr
  and exit status, and the retained `cg-O2.o` (gzip-compressed, because the
  repository ignores `*.o`). The forced harness and startfile images that
  gdb ran were copied from `blobs` and are in `blobs.tar.gz`. The probe
  outputs were deleted after listing.
- `harnesses/`: the qualify, capture-wrapper and archive scripts that
  produced this directory. `source/`: the tested `link_driver.rs` and test
  file.
- Recorded paths under `/tmp/claude-1000/…` are the original capture
  locations on the host. They are not themselves evidence.

## Boundary

This is object and execution evidence on one host, not a proof. The
refusal is in the link driver's `-Wl` parser (`parse_wl_group`), and the
`trust-cg` CLI is its only caller. A library caller that fills
`LinkRequest::linker_arg_groups` directly is not re-checked. A user's own
`cc` link and rustc-driven bridge links do not pass through the driver and
can still force BTI.

Other feature-forcing keywords are not refused, such as `-z gcs=always` or
x86-64 `-z force-ibt`/`-z shstk`. trust-cg has no BTI/PAC code-generation
policy, so CG code runs unprotected. The SIGILL outcomes depend on this
loader and kernel. That the C-only `pac-plt` fault comes from an
authentication failure is inferred from the faulting instruction; the run
does not observe it directly. The x86-64 and RISC-V ELF emitters still lack
`.note.GNU-stack`, and the glibc 2.41 dlopen control needs a newer-glibc
host.
