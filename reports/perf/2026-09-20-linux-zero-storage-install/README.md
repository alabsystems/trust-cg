# Installed Linux leaf-frame repair — 2026-09-20

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The local development compiler now uses source `ad795539f8e6da83028596ee61eb15a7dfb4e6cd`. It keeps
frames for arithmetic whose existing Formal evidence owns a sixteen-byte frame,
and omits unnecessary frames for the qualified output writer and pointer leaves.
No instruction authority or verification policy was weakened.

## Installation preflight caught a regression

The first CLI candidate at `e26492c2` passed return42, select and diamond checks,
then refused the first i32 arithmetic proof export: removing the frame removed
its `SourceBoundFrame` owner, leaving only statistical instruction evidence.
That candidate was **not activated**. Its build and failed preflight are retained.

Commit `ad795539` keeps frames for AddRR, AddRI, AddRIShift12, SubRR, SubRI and
LslRI until a separately checked frameless body owner exists. The previous
Darwin/red-zone policy stays unchanged. Final source controls pass: 165 frame,
3 frame-pipeline and 87 DWARF tests, plus 979 broader pipeline tests (the latter
overlap the three frame-pipeline tests). No tests fail or are ignored.

## Qualified package

- Directory: `/home/ayates/.local/lib/trust-cg/ad795539-ay43f133d3-cleaned2a80d1`.
- CLI SHA-256: `bcce9afd1059179994efe55fbf3bc984a5b607bce8749b611c02c5c97eaab1b0`; stock Rust development build, exact
  clean source held throughout, 112.58 seconds.
- Genuine pinned Trust private backend SHA-256:
  `7209ab8b7f940106d0f97e24d279fa84a84a371f53a5eb65e083a5a6694185c0`. Its source, build tools and frozen sysroot are
  recorded separately; the sealed Trust installation itself was not modified.
- AY and Clean binaries are unchanged from the preceding installed cohort:
  AY `93fe897aea3b4ad5d2ff50c9729c8aa097bfcf36dcbf581e21c4515bbeaf400b`,
  Clean `680069f8d7185a8dbc0cc67e860d57a7df9ca4cf8bd8a4d8951346cbbf594dbc`.
- **183 preflight commands pass before switching the launcher**: O0–O3
  return42, select and diamond native controls; 48 arithmetic proof exports
  with 6,912 native arithmetic calls; and compile/link/execute of the actual
  O1 Rust writer using the packaged backend. Select and diamond each execute
  15,360 comparisons. The writer checks 257 calls, all five outputs and eleven
  surrounding arena words, eight aligned buffer placements, and callee-save/SP
  preservation.
- The rebuilt backend also repeats the complete 24-case O0/O1 matrix: 19 native
  successes and five explicit refusals. All 19 accepted objects are byte-identical
  to the first qualified repair, and their independent CFI checks still pass.

`~/.local/bin/trust-cg` now selects this package. AY and Clean links point into
the same package; previous cohorts remain available. The launcher adds the
package's tool directory to PATH and injects no proof-policy override. The
private backend is included as `librustc_codegen_trust_cg.so`; selecting it through
Trust's `-Zcodegen-backend` remains explicit. Its tested Rust frontend lane uses
`-Ztrust-verify=off`; **backend proof checks remain enabled**. This is a local
development install, not a signed release, verified frontend or verified self-host.

All heavy work was serial, with two Cargo jobs and a 16 GiB process-group RSS
limit and zero grace. The final backend/release/native/install commands use the
anchored capture API and retain authenticated monitor evidence. The baseline
unit harnesses retain their original watchdog records. No RSS breach occurred.

## Remaining work

O0 writer still refuses frame-pair/CSet proof gaps; fat-pointer casts still
refuse frame pairs; integer-to-reference casts keep their frontend rejection.
These cases emit no object. Formal frameless arithmetic body binding, general
frames/calls, reference validity and canonical-to-native memory composition
remain unfinished. **All L01–L14 remain OPEN.** No new whole-system qualification
or performance claim is inferred from this installation.

The archive retains both failed and successful installation runs, source hashes,
commands, proof exports, native objects/oracles and tool identities. Large compiler,
solver and backend binaries are identified by their hashes rather than stored in Git.

## Activated launcher and final checks

The active launcher and all installed binary/link identities were checked after
activation. Its O3 return42 proof export, system link and native run pass (four
smoke commands including version). Root formatting, documentation/inventory and
file-link checks, diagnostics refresh, whitespace checks and the complete archive
hash audit pass. The old compiler package and rejected first candidate remain
available by their explicit paths; only the qualified package is active.
