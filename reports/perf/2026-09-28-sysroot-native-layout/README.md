# Linux AArch64 standard-library layouts

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The **O0 diagnostic alloc census drops from 14 failed roots to zero**. Fresh
core, compiler_builtins, and alloc libraries compile together through CG and
execute linked consumer tests. Alloc also builds at O1. **O2 and O3 still fail
at 12 roots each**; full std, mandatory machine proof, self-hosting, and
compile/runtime performance qualification remain unfinished.

## Change

The previous interception rule excluded local definitions but still modeled
upstream core iterators while compiling alloc. That mixed the bridge's custom
iterator representations with the real layouts embedded in alloc's types.
Standard-library builds named core, alloc, std, and hashbrown now withdraw
interception uniformly across type recognition, method calls, and the
assumed-dead iterator and heap stubs. Real upstream MIR and rustc layouts are
used instead. Ordinary application crates retain their existing policy, and
local definitions remain excluded everywhere.

The optimized iterator probe also exposed a missing closure case in the scalar
field memory reader. Its layout walk now descends into closure captures in the
same order as the existing flattened-field classifier. It uses rustc's field
offsets, and the existing field-count and type checks still run before loading.

## Native evidence

The permanent fixture compiles as each of core, alloc, std, and hashbrown, with
both LLVM and CG at O0 through O3. All **32 executions pass 3,194,880 checks**.
Each execution varies 256 seeds and lengths 0 through 64 and checks reversed
Unicode character iteration with a captured predicate, UTF-16 decoding with
invalid surrogates, string-length sums, array iteration from both ends,
`mem::take` of a slice iterator, and reversed chunks. The independently
LLVM-built driver computes the expected values, including a separate UTF-16
decoder. The baseline CG probe refuses all four optimization levels; the first
candidate passes O0/O1 but exposes the closure-field gap at O2/O3. The final
probe passes all four.

Fresh matching CG core, builtins, and O0 alloc libraries are linked into both
LLVM and CG no_std consumers compiled at O0 through O3. A C driver passes
**177,224 checks per execution**, **1,417,792 total**, over UTF-16 big/little
endian conversion, odd byte lengths, lossy conversion, Unicode case conversion
including contextual sigma and titlecase expansion, and partially consumed
vector and string drains. It checks drain contents, cursor state, size hints,
and that every call releases its allocations. The O1 alloc library also passes
both O0 consumers: **354,448 additional checks**. Symbol inspection verifies
that seven tested UTF-16 and case-conversion functions in each library are the
actual definitions linked into the LLVM consumer, with matching code sizes.

## Remaining optimized alloc failures

Both O2 and O3 report the same 12 roots:

- Six slice assignments using `Rvalue::Cast`, in lossy UTF-8/UTF-16 and WTF-8
  conversion paths.
- Four whole aggregate copies from non-memory sources, in lowercase,
  uppercase, titlecase, and casefold conversion.
- Two references to `Vec<u8>` in `Cow<str>` addition-assignment paths.

These are required-feature failures, not passing negative controls. The O0/O1
successes do not establish complete alloc or std support.

## Validation boundary

Seven regression tests pass **9,409,484 checks** across aggregate array
iteration, borrowed slices, closure wrappers, unsized arguments, and try-fold
including unwinding. The unsized argument admission matrix also passes its 16
compilations. Fresh core consumers pass **81,097 checks each** with LLVM and CG.
Core has 44 AArch64 objects and 1,281 hidden private functions; both builtins
builds have 11 objects and the six expected weak floating-point helpers.
The O0 alloc library has two AArch64 objects and 377 hidden private functions;
the O1 library has 24 objects and 846 hidden private functions.

The all-target check, differential formatting check, new Rust fixture formatting,
generated documentation and diagnostics checks, and `git diff --check` pass.

All compilation here uses diagnostic settings with compiler verification
disabled. Native and strict bridge coverage results do not establish mandatory
machine proof. The mandatory machine-proof probe and separate ABI proof control
remain refused at uncovered emitted AArch64 opcodes, beginning with
`StpPreIndex`.

The strict bridge probe reports 88 functions, zero unmodeled shapes, and 73
pushed scalar op-selection obligations. This records the bridge's bounded
coverage, not operand wiring, memory, control-flow, or source-to-byte proof.

## Identities

- Backend: `2da67d5286568a48e7454b16329142bd3095f16b74a9dc8e4e1d5b9382216d97`
- Harness: `e34db720b9ec35dda217b1a24c4da766b31cd0174e119fa4250337248e8c3129`
- Baseline: `reports/perf/2026-09-28-unsized-arguments`
- Investigation: `target/sysroot-native-layout-investigation`

The evidence archive contains **2,859 files**, **98,943,106 compressed bytes**,
and the **266 sealed source files**. Every member was independently rehashed;
the source hashes match the final working tree. Archive SHA-256:
`2719845395ab195e3c3ab88e021dc77cac2e3461b829511e73a1c473df44817f`.
The standard durable-evidence validator and plan citation check pass.

- Results
- Evidence archive
- Member hashes
- Archive identity
- Top-level inventory

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
