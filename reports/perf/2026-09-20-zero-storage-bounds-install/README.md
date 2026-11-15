# Installed bounds and empty-frame repairs — 2026-09-20

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The installed local development compiler now uses clean source `4b41d28fe674e8f1b9a02ffeda96c0aec21b4560`.
It includes canonical runtime bounds assertions and the audited empty-frame policy
for exact immediate bounds guards. The preceding [compiler qualification](../2026-09-20-zero-storage-bounds/README.md)
records the frame, unwind, pipeline and native controls. This installation repeats
the compiler endpoints before changing the launcher.

## Package and checks

- Package: `/home/ayates/.local/lib/trust-cg/4b41d28f-ay43f133d3-cleaned2a80d1`.
- CLI SHA-256: `4ce37184b97751d843129fba2fcc350de119c968cf3cafd779e014654996e9b6`; stock Rust build from the held clean
  source, 120.70 seconds.
- Genuine Trust private backend SHA-256:
  `fea205bbd5259d3c02dda136c7232e89be116d9fb8fd6f8900acae3b3cfdffaf`. The sealed Trust compiler itself
  is unchanged; its explicit development frontend lane remains unverified.
- AY `93fe897aea3b4ad5d2ff50c9729c8aa097bfcf36dcbf581e21c4515bbeaf400b`
  and Clean `680069f8d7185a8dbc0cc67e860d57a7df9ca4cf8bd8a4d8951346cbbf594dbc`
  are unchanged from the preceding package.
- **All 204 preflight commands pass before activation.** At O0–O3 they cover
  return42, twenty select functions, twenty diamond functions and **48 arithmetic
  proof exports / 6,912 native arithmetic calls**. Select and diamond each execute
  15,360 comparisons. Frame-bound arithmetic retains its prior Formal owner.
- The staged backend freshly compiles all **eight admitted Rust programs**:
  constant, dynamic and masked fixed-array writes and the five-word writer at
  O0/O1. Every object exactly matches its qualified counterpart. Each runs 257
  native calls, for **2,056 calls** checking sixteen arena words, eight buffer
  placements, callee-saved registers and SP. Dynamic-index cases also run eight
  combined invalid-index traps before any shared-memory modification.

`~/.local/bin/trust-cg` selects this package and adds its tool prefix to PATH.
AY/Clean links point into the same package. No proof-policy environment override
is injected, and previous packages remain available. The included backend is
selected explicitly through Trust's `-Zcodegen-backend`; the qualified Rust lane
uses `-Ztrust-verify=off`, with **backend proof enforcement enabled**.

The first installation attempt stopped after its 181st successful command because
the harness assumed the requested object filename; Rust emitted a suffixed
`.rcgu.o` file. The old package stayed active. The actual object's hash matched its
qualified counterpart. The corrected resume checked every staged tool identity,
kept the completed checks and finished the remaining 23 commands before activation.
The failed harness log, original script and intermediate record are retained.
A separate activated-launcher smoke then checks all tool identities and performs
an O3 proof export, native link and execution through `~/.local/bin/trust-cg`.

This is a local development installation, not a signed release, verified Rust
frontend or verified self-host. Four cases in the compiler's twelve-case matrix
still refuse: dominated comparisons lack CSet coverage; unwind cases retain
frame/type gaps. Broader memory, ABI, reference and whole-system proof composition
remain open. **All L01–L14 remain OPEN.** This does not rerun or inherit the full
Linux gate or establish a performance result.

The build and preflight use an anchored 16 GiB process-group RSS limit with zero
grace; builds use two Cargo jobs. Complete logs, guard records, executable/source
identities, emitted proof packets, native objects and oracles are retained. Large
compiler/solver/checker/backend binaries are recorded by hash instead of stored.
Verify the retained artifacts with:

```sh
python3 scripts/check_evidence_archive.py reports/perf/2026-09-20-zero-storage-bounds-install
```
