# Scalar callback instruction bytes and complete ELF binding

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The bounded scalar-cell checker now independently decodes actual A64 words and
binds original TrustIR/LIR call observations to immutable code and relocation
records. A separate bounded ELF reader obtains the code, caller symbol and every
text relocation directly from the complete object. No producer machine metadata
or relocation inventory supplies object identity.

The new `check_aarch64_scalar_cell_bytes` checks exact frame words, scalar
loads/stores, copy instructions, MOVZ/MOVN/MOVK and GPR-to-FPR transfers, plus
ordinary return and the narrow branch-to-next-word case. Every BL placeholder
must have exactly one zero-addend `R_AARCH64_CALL26` record at that word and the
original source callee name. Missing, duplicate, extra, shifted or foreign-kind
relocations refuse. Decoding supplies the operands and widths used by the
independent caller byte interpreter.

`check_aarch64_scalar_cell_elf` independently reads little-endian AArch64 ET_REL
objects. It binds the source caller's complete executable section and ordinary
global function symbol, checks table bounds and links, reads every text RELA,
and requires ordinary undefined global callback symbols. It checks the entire
`st_other` byte, including alternate calling-convention flags. String tables
require bounded, terminated UTF-8 names. File section overlaps, unsupported
relocation formats and oversized tables refuse. The object owner immutably
retains source, LIR, full object, code and resolved call records.

These are **diagnostic correspondence checks**, not whole-call proofs or
production admission. The caller's ABI/private-memory premises and arbitrary
public callback effects still need independent proof replay. Linked call
addresses, unwind/non-executable metadata and native execution are outside this
increment. Actual pipeline tests explicitly disable pipeline verification to
reach encoding; they supply no production bypass or new compiler admission.

## Executed qualification

The final frozen-source runs pass **85 Rust tests**: 67 source/frame tests and
18 integration tests (five new byte/ELF tests, eight pointer-copy regressions,
five signature layout regressions). None of the selected tests fail or ignore.
The maintained Linux floor now requires the new `aarch64_scalar_cell_bytes`
family, increasing its inventory from 126 to **127**. Its inventory harness
passes 31 tests with the existing one non-Linux-only conditional skip. This
increment qualifies the new family and focused regressions; it does not claim
a new complete 127-family run. The last complete floor remains 126/126 at the
previous recorded revision.

The new integration target establishes:

- All **24** actual pipeline byte streams, symbolic fixups and complete emitted
  ELF objects match the original F32/F64 caller captures at O0–O3.
- **Six GNU-assembled callers** independently exercise both scalar widths,
  argument and local-cell callers, and MOVN variants. GNU assembler identity,
  version, assembly text and full objects are retained.
- **378 replaced instruction words** and **288 changed relocation/code fields**
  refuse, covering every word in all 24 streams.
- **82 complete-object mutations** refuse, including invalid headers/section
  bounds, wrong names and symbol indices, weak or defined callbacks, alternate
  PCS/visibility, wrong caller extent, broken relocation-table links, addends,
  relocation kinds and code mutations.
- All **1,528 truncated objects** refuse. Another **2,048 deterministic byte
  mutations** return without parser panics; valid changes to unrelated bytes
  are not counted as semantic rejections.

All runs use the anchored 16 GiB process-group RSS supervisor, zero grace,
two Cargo jobs and one Rust test thread. Source fingerprints stay unchanged
within every run. There are no resource failures, cancellations or truncated
captures. Root formatting, documentation and archive checks pass. The initial
format check identified only export ordering; final tests rerun after correcting
it. Initial successful unit runs, the move to the required integration target,
and final qualification records are retained separately.

Exact raw machine code, emitted ELF objects and GNU assembly/objects are
extracted from final successful integration output with hashes in
`inventory.json`. The product checker imports neither the production encoder
nor its object parser. Decoder/relocation references are Arm's
[A64 instruction reference](https://documentation-service.arm.com/static/6245c734b059dc5ff9a8bdab)
and [ELF for AArch64](https://github.com/ARM-software/abi-aa/blob/main/aaelf64/aaelf64.rst).
No solver or installed compiler package changes are made. All L01–L14 remain
open; the [whole-call memory proof checkpoint](../2026-09-20-callback-memory-model-checkpoint/README.md)
remains unresolved.
