# Conditional output-memory diagnostics: Mac development qualification

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Source `36956c861825ae68a37e721120e464176b375eb9` (tree
`2dda7ab812bd3806c886248fbc46400be868ec75`) passes two fresh Trust **unverified**
compilations and all **33 tests**, with no failures or ignores, on ARM64/macOS.
Root and independent terminal reviews passed. This qualifies the diagnostic
checker and its exercised refusals, not production memory admission.

The implementation compares complete ordered source and allocated-machine
store streams before adding any numerical memory premise. A single arbitrary
byte observation covers public output and untouched memory; separate checks
cover restored frame registers. Production `SourceBoundFrame` still refuses
these effectful bodies. No TY-specific verifier or trusted premise is added.

## Exact scope

The four phases are an ordinary `trust-cg-verify --lib` check, a fresh library
test build, exact `source_bound_frame::` discovery and execution. Every phase
exits zero. The 33 tests comprise 16 existing frame controls, six diamond
controls, three callback-cell controls and eight new output-memory controls.
The new controls cover source/machine disagreement, store order, aliases,
widths, offsets, constants, hidden effects, ownership and numerical premises.

The actual ordinary metadata image has SHA256
`387f2ed3cce96ba6485971c271bff2c4b86e644aa5453125fa266f381ea29264`
(44,114,908 bytes); the test image has SHA256
`72c2256b365f631d710125e95361d4192bbc07cd8c876f5b55ec57e74010a3c7`
(145,792,304 bytes). Actual fresh compiler invocations, complete generated
environments, artifact messages and direct-extern identities are retained.

Both scalar and paired stores emit a 96,284-byte query with SHA256
`e7cb7c86173f17dfd2445faeaab42604ebe64f31e674f6e49803a93395a0e6c7`.
These are **two captured instances of one identical query**, not two independent
proofs. No solver was run for these new queries, and no certificate is claimed.

The authored ordinary Rust writer is not compiled by this campaign. Its
`&mut [u64; 5]` frontend path carries pointee metadata that the narrow diagnostic
currently refuses. Do not strip that metadata or treat direct LIR fixtures as
ordinary-frontend acceptance. Numerical non-wrap/alignment/frame-separation
conditions do not establish a live writable allocation or caller permission.
Encoded-byte binding, calls, provider semantics and installation ownership
also remain separate gates.

## Environment and preservation

The compiler remains the pinned September 10 Trust development lane; neither
stock Rust nor a newer atpkg compiler is substituted. Compiler features, one
build job, 7,200-second build, 60-second listing and 300-second test deadlines
remain unchanged. The existing 12 GB scheduling reservation is not a hard
memory limit or a measured peak. The only environment relocation is the new
independent `CARGO_TARGET_DIR`; runtime keeps the previously pinned AY/Clean
discovery prefix. Libtest `--show-output` retains the actual query bytes.

Before compilation, a separate copy-only step preserved the original cache.
All 10,014 copied entries match required metadata with distinct inodes; all 64
selected artifacts match exact bytes. The original cache is never released.
After qualification, all 34 recorded primary/direct-extern/checker outputs
(783,588,262 bytes), source, tools, sysroot, configuration, upstream dependencies,
proof prefix, resources, owner and historical records remain unchanged.
The 365 recorded process IDs are quiet. Two residual sampler sleeps drain
passively within the existing five-second grace; no signal was sent. This is
not a claim of complete descendant containment.

Terminal result SHA256:
`8dfa4a7cab4d08ba602b68500f3b52a93d2d68999a7010129c4e1ba6dab2a767`.
Copy result SHA256:
`122a6409a82517eb10090d6bd37093c8d3d07dff23dddf0e4f4e73f22ee42ea9`.

## Integration and next checks

Reviewed development merge `e0797b78`, subsequently integrated into main at
`3d7164b2`, preserves the source-bound arithmetic work from `c611a263` and the
peer's later documentation-only `7d42d633`. The diagnostic never constructs the
private frame or arithmetic proof owners. The peer's I32 erased-copy refinement
and its negative control remain intact.

This 33-test result belongs to **36956**, not the merged tree. Its next bounded
qualification is two fresh ordinary/test compilations and all 33 frame plus
five source-bound arithmetic unit controls. The separate
[Linux arithmetic report](../2026-09-17-source-bound-arithmetic/README.md)
retains its own source, tools, certificate and native execution scope; it is
not silently reclassified as this Mac's integrated test run. Subsequent proof
work must attempt strict solving and independent replay of the exact new query,
retaining any refusal, timeout or missing certificate.

## Retained evidence

The archive `output-memory33-evidence.tar.gz` (removed from the tree), with the per-file
byte/mode audit: 51 regular members, 34,977,432 payload
bytes; archive SHA256
`f8ca630d275d26c42a20d6c4b39f9fabef77afbe0ff018fa338ed62163682d3e`
(5,930,751 bytes). It contains all 33 qualification records, eight copy records,
four controls/history files and six exact qualified source files. No executable
payload is included; artifact identities remain in the original records.
Every archived regular member matches its original bytes and mode; there are
no links, escaping paths, duplicate members or AppleDouble entries.

The shared plan is the immutable **pre-activation** plan; enabled controller
copies and their exact recorded hashes establish the later launch. Historical
absolute workspace paths are retained as provenance, not portable install
instructions. The archive does not claim a verified compiler, complete TY
source-to-native execution, a fully checked ordinary Rust writer or any TY/TLC
performance advantage.
