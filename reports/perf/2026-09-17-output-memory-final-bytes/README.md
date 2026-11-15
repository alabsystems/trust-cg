# Conditional output-memory correspondence reaches final instruction bytes

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

`check_aarch64_output_bytes` now compares a bounded LIR output writer with
the actual little-endian A64 instruction stream. Its private owner retains
immutable source and byte references together with the conditional theorem.
No allocated instruction metadata or producer hash supplies the byte meaning.

The decoder requires the complete sixteen-byte FP/LR frame envelope and RET,
decodes every body word independently of the production encoder, and compares
the entire ordered store trace before constructing any memory premise. Supported
body instructions are NOP, 64-bit register MOV, unshifted ADD immediate/register,
MOVZ/MOVN/MOVK, unsigned-offset STR64 and offset STP64. Undefined values, unsupported
widths/effects, reserved registers, malformed/trailing words, changed stores and
oversized bodies refuse. The maximum stream is 259 words, including the envelope;
the existing 256-body-instruction and 64-store limits are preserved.

Qualified index tree: `716302e089df85df8667e62c3530c3bfd3d39b68`, based on `ef2d7eaf9d9cb37730ac9f827d130328255e39ca`.
Fresh test executable SHA256: `c1fee069fdbc279cddb21e9cd5feaa2a2768c19b837411d5afe5099cb9820dfb`.
This is stock Rust 1.97.1 Linux AArch64 qualification with locked dependencies,
two build jobs, serial tests, an exclusive host resource lease and zero-grace
16 GiB child RSS supervision. Independent Clean commands use 8 GiB.

All **50 selected tests pass**: the existing 38 source-bound tests, six new
final-byte methods and all six UF traversal controls. Exact native test listings
match the executed names; there are no missing, duplicate, ignored or failed
selected tests. Unrelated tests remain explicitly filtered.

The new methods check scalar and paired stores, all **512 single-bit mutations**
of their complete instruction streams, missing/extra/reordered effects, early
returns, calls, loads, trailing bytes, the exact instruction limit, register
copies, address arithmetic, all literal halfwords and undefined MOVK input.
All 512 changed original streams refuse. Eight separate GNU assembler/objcopy
reference programs match the actual tested words exactly, including the frame,
store forms, copies, address calculations, literal construction and NOP.
Their assembly, object bytes, extracted text and tool versions are retained.

Both original byte streams reconstruct the **same 96,284-byte original query**,
SHA256 `e7cb7c86173f17dfd2445faeaab42604ebe64f31e674f6e49803a93395a0e6c7`.
Fresh frozen AY returns UNSAT; independent Clean accepts its complete certificate
and rejects all three hole/missing-conclusion/opposite-premise corruptions.
The ordinary library build, repository formatting gate and documentation checks
also pass. Exact source fingerprints remain unchanged during each campaign.

This is **conditional diagnostic correspondence**, not production memory
admission. The source-bound production frame constructor still refuses these
effectful bodies. Writable caller storage, lifetime, ownership and separation
from the private frame remain premises; numeric guards do not prove them.
TrustIR-to-LIR binding, function-to-object/link binding, production proof transport
and refinement of the Rust checker implementation are not established here.
The ordinary Rust output-buffer fixture and full Linux L01–L14 contract remain
unfinished. The installed development package remains the separately qualified
`ef2d7eaf` compiler with AY tree `43f133d3`; this source increment is not installed.

Commands, logs, source patch, tool identities, exact query and certificate
packets, all corrupted controls and independent assembler outputs are retained.
Every compressed and decoded artifact is audited against its length and SHA256.
The large test executable remains local and is identified by the hash above.
