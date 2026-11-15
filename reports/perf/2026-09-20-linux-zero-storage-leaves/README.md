# Linux zero-storage leaf frames — 2026-09-20

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

AArch64 Linux leaves with no stack storage can now omit an unnecessary FP/LR
frame. The actual Rust O1 five-word writer and six aggregate pointer-cast cases
now pass ordinary backend admission and execute. No verifier authority was added.

## Source and behavior

Qualified base: `0035c15062ec956aa452c8f0bebf6b3a3afe3a4e` plus the retained
source patch; staged tree `1da194484d7719e4dc3ddbcdb3d188239d325d18`.
`LeafFramePolicy::OmitZeroStorage` separates this optimization from the red-zone
flag. The legacy frame APIs retain their behavior; Linux gains no red zone.
Eligibility requires no stack slots, outgoing storage, dynamic allocation,
protector, exception metadata, calls, callee-save use or FP/SP dependency.
Only audited explicit-effect instructions are eligible. LR is permitted solely
as the ordinary return register/use. Checks include implicit effects and W aliases;
clearing call flags cannot conceal a call. Unknown/opaque operations retain a frame.
The epilogue now handles an empty saved-register list without subtraction overflow.

The [AAPCS64 frame-pointer contract](https://github.com/ARM-software/abi-aa/blob/main/aapcs64/aapcs64.rst#the-frame-pointer)
allows small LR-preserving leaf exceptions. The existing Darwin/red-zone and
framed fallback paths remain, including the old public layout API behavior.

## Qualification

- 164 frame tests, 2 AArch64 frame-pipeline tests and 87 DWARF tests pass.
- Broader pipeline selection: 978 tests pass, zero failed or ignored. This
  selection also covers other targets; it overlaps the two frame-pipeline tests.
- Genuine pinned Trust private backend build passes in 178.78 seconds. Frozen
  dylib SHA-256: `f2a45587e0a8a24bd942b71afee9dfdd7c36a819de17a5cf4f0c5e059cef2425`.
- Actual O0/O1 Rust matrix: 24 cases, 19 native compile/link/execution successes
  and 5 explicit refusals. Eighteen successful pointer-cast programs preserve
  addresses across 84 C comparisons. The O1 writer passes 257 calls, checking
  all 16 arena words per call (five outputs plus surrounding words), output
  placement at eight aligned offsets, X19–X29, D8–D15 and SP preservation.
- Independent `objdump` output for every accepted object contains no FP/LR/SP
  operations. All 19 decoded CFI records use CFA=SP+0, RA column 30, and no
  body CFA changes. The writer text is 84 bytes; object SHA-256:
  `03904fb2dc13ef8499baf93d0db092dce099e34c3d46fe682a8e26ede8edf732`.
- The same writer oracle accepts a correct assembly control and rejects seven
  controls: wrong output, preceding/following canary overwrite, GPR/FPR clobber,
  FP corruption and SP drift. The second control run retains authenticated
  monitor evidence for every command.

Heavy commands run serially with a 16 GiB process-group RSS watchdog, zero
configured grace, two Cargo jobs and one test thread. No RSS breach was observed.
The Rust frontend explicitly uses its unverified development lane; **backend
proof checks stay enabled**. The frontend's `0 obligations checked` note does
not describe the separate backend checks. This is native regression evidence,
not an end-to-end verified Rust compilation or a canonical-to-native memory theorem.

Root formatting, documentation/link/inventory checks, diagnostics refresh and
Git whitespace checks pass. The archive hash audit passes for every retained
artifact, including decoded compressed contents.

## Preserved failures and limits

The first regression attempt failed to compile a temporary test register slice;
the second caught the real empty-epilogue underflow. The third passes. The first
oracle-control run observed correct functional results but lost monitor group
identity for one short process; its audit correction denies enforced credit.
The second uses the anchored capture API and supersedes that resource result.

O0 writer still refuses `StpPreIndex`, `CSet`, and `LdpPostIndex`; the fat-pointer
cases still refuse the frame pair. Integer-to-reference casts retain their
explicit frontend rejection. These refused cases emit no object. All L01–L14
remain OPEN. The installed compiler/tool pack was not changed by this source
qualification. Full source/native composition, reference validity, general
frames/calls, verified frontend/self-hosting and whole-system closure remain work.

The inventory retains commands, source identities, logs, objects, executable
oracles and decoded unwind/code output. The large backend dylib is identified
by content hash in its build receipt rather than committed to Git.

## Installation follow-up

The [later installation qualification](../2026-09-20-linux-zero-storage-install/README.md)
caught and repaired a scalar arithmetic proof-export regression before activating
any new launcher. The final policy keeps arithmetic's required frame owner and
retains all 19 successful native cases. The first qualification above did not
include those CLI exports; its native results remain limited to its named cases.
