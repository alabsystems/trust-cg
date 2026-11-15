# Linux AArch64 borrowed enums and aggregate array iteration — 2026-09-28

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Compiler-builtins now has six diagnostic failing roots, down from eight.
Borrowed fieldless enums use stable storage, and arrays of aggregates use the
existing byte-copy and pointer-layout paths required by array iteration.
The remaining compiler-builtins failures are AArch64 `fma`/`fmaf`,
`sqrt`/`sqrtf` and `rint`/`rintf` inline assembly. The complete sysroot,
proof, self-host and performance goals remain open.

## Changes

Address-taken fieldless Direct-tag enums with an admitted integer scalar type
receive scalar cells, including entry arguments borrowed only for equality.
Discriminant reads use that storage, so they observe assignments and writes
through references or raw pointers. The existing guard against reusing an
address-taken argument's entry value remains in place.

Constructing a fieldless enum in a scalar cell now emits its tag before the
store. The intermediate core build caught the missing definition in
`dragon::format_shortest`, which constructs `Ordering::Greater` and `Equal`.
An aggregate with no scalar payload or admitted tag now fails explicitly,
instead of succeeding with an undefined store operand.

Whole constants of memory-backed fieldless Direct-tag enums copy their exact
constant image. This includes unsigned 128-bit tags above `i128::MAX`, which
cannot be recovered by the previous signed-integer conversion. The scalar
image must cover the entire destination; indirect images retain the existing
constant allocation and provenance checks. This does not expand the scalar
fieldless-enum type mapper to 128 bits.

Arrays with aggregate elements now reach the shared whole-slot transmute.
It requires both memory slots, equal sizes and copies at the weaker alignment.
Thin pointers to arrays with aggregate elements use the validated memory
layout when the scalar mapping cannot represent the element. Real element
sizes and field offsets still come from rustc. Together these support
`[T; N]` to `[MaybeUninit<T>; N]` and the array iterator's borrowed storage.

## Native evidence

| Check | Result |
| --- | --- |
| Enum discriminants and borrowed storage | O0–O3 × LLVM/CG; 40,032 checks |
| Aggregate array iteration | O0–O3 × LLVM/CG; 104,448 checks |
| Baseline regression controls | Both matrices fail compilation on the prior backend |
| Compiler-builtins census | 8 → 6 roots; no new failing roots |
| Alloc census | Same 148 roots |
| Rebuilt core | 44 ELF64 AArch64 objects, 1,281 private hidden functions |
| LLVM and CG consumers of rebuilt core | 81,097 checks each |
| Existing memory-unary and linkage controls | Three tests pass |
| Mandatory machine-proof control | Existing `TCG-PROOF-465` failure remains |
| All-targets, formatting and documentation checks | Pass |

Enum cases cover signed and unsigned 8/16/32/64/128-bit tags, inferred tags,
`Ordering`, shared references, mutation through LLVM callbacks, reassignment,
raw pointer stores, aliases and loops. Literal construction cases exercise the
additional scalar-cell store repair. Array cases use lengths 1/3/7, floating
point tuples, mixed tuples and padded structs, forward and reverse iteration,
empty/partial/full consumption and exhaustion. Floating-point values include
signed zero, infinities, NaN payloads and deterministic random bit patterns;
checks compare bits rather than approximate arithmetic.

The final native matrix has **144,480** value checks. These are correctness
checks, not timing evidence. The array matrix crosses independently compiled
Rust ABI boundaries. The core consumer's C driver uses host GCC; Clang is not
installed on this host.

The first enum candidate failed optimized unsigned-128 constant assignments.
The first array fixture also reached separate existing limitations for copies
through array references and closure arguments containing floating point pairs.
Those failures and their source are retained. The final array fixture passes
arrays by value and computes its checksum directly, so it qualifies iteration
and those direct ABI boundaries, not the unsupported copy or closure paths.
The initial core build and its failed dependent-build attempts are retained;
the corrected core was followed by a fresh LLVM compiler-builtins dependency
and successful independent consumers.

## Proof scope

The isolated enum refinement probe compiles with refinement enabled: each
function's one generated `BitXor:I8` obligation is refined, with no skips.
This records existing arithmetic coverage; it is **not a proof of the new
enum storage or tag construction**. Machine-proof generation refuses:
`borrowed` has 17 uncovered instructions/13 opcode kinds, and `constructed`
has 30/18, both beginning with `StpPreIndex`. The standard mandatory control
still reports 14 instructions/12 opcode kinds, first
`aliased_f32_read[13] = StpPreIndex`. No proof gate was weakened.

All successful native/sysroot diagnostic compilations disable mandatory
machine certificates and Trust verification. Core consumers still use an
LLVM-built compiler-builtins archive. All fourteen Linux completion rows
remain open; strict compile-time and executable-runtime wins over LLVM and
Clang are unproved.

## Reproduction and identity

The frozen Trust compiler is `ae9c2c1daa0fc80afbfd380e493f5581ac714acb`,
LLVM 22.1.2, on native Linux AArch64. The final backend SHA-256 is
`9243a4d911c1c2da465edc70a443b90bcf8dd514419eb981cd4923983f90bc1d`.
The final native harness SHA-256 is
`19d416e6d2982cdedb1524772c285449790d5b16f4bba46b5b0799e1e43ef3f9`.

The evidence archive contains exact commands, source receipts, incremental
changes, frozen core/library inputs, compiler logs, native artifacts, failed
attempts and proof diagnostics. Large libraries/backends/harnesses are recorded
by hash. `assets.json` inventories each archived member; `archive.json` records
the compressed archive and independent member rehash; `inventory.json` records
stored and uncompressed identities. Verify with:

```sh
python3 scripts/check_evidence_archive.py reports/perf/2026-09-28-enum-discriminant
```

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
