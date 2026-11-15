# Linux AArch64 optimized alloc lowering

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

**Diagnostic alloc builds now pass at O0, O1, O2, and O3.** The twelve O2/O3
unsupported roots in the previous native-layout report are cleared. Fresh CG
core, compiler_builtins, and all four alloc libraries compile together and pass
linked consumer tests. Full std, mandatory machine proof, self-hosting, and
compile/runtime performance qualification remain unfinished.

## Changes

Three MIR lowering gaps are repaired:

- A constant slice transmute stores the evaluated allocation pointer and its
  original metadata into a memory-backed wide-pointer destination. The length
  is preserved even when source and destination element sizes differ.
- A whole copy from a nested scalarized aggregate into a stack slot uses the
  existing native layout packer. It reconstructs the image using rustc field
  offsets and the established flattened-field and zero-sized-field rules.
- Borrowing a nested aggregate field that the scalarized reference path cannot
  represent gives its containing local stable storage. The existing projected
  borrow resolves that field's address in the slot, so mutations and subsequent
  whole-value moves observe the same image. Synthetic collection layouts remain
  excluded by the existing layout classifier.

The optimized failures comprised six constant slice casts in lossy conversions,
four nested iterator copies in case conversions, and two embedded Vec borrows
in Cow<str> addition assignment. The baseline fixture refuses every optimization
level; the final fixture compiles and executes at all four.

## Execution evidence

The new permanent matrix has eight LLVM/CG executions and **532,520 checks**.
It covers empty and non-ASCII constant strings, a slice transmute with different
element sizes that must retain its original length, Unicode character offsets,
and Vec mutation, reallocation, replacement, and truncation through String.
An independently LLVM-built driver computes expected results.

Fresh matching CG core and builtins are linked with each of the four CG alloc
libraries into LLVM and CG consumers at O0 through O3. All **32 executions pass
278,624 checks each, 8,915,968 total**. A C oracle checks UTF-16 endian conversion,
invalid surrogates and odd byte lengths; UTF-8 replacement; lowercase, uppercase,
titlecase and casefold; partially consumed Vec/String drains; and both Cow<str>
addition-assignment implementations over borrowed and owned operands. Every
call must release its allocations. Symbol inspection verifies thirteen tested
alloc definitions in each library are the actual functions linked into its O0
LLVM consumer, with identical code sizes.

The core library has 44 AArch64 objects; builtins has 11 objects and six weak
floating-point helpers. Alloc has 2, 24, 29, and 29 objects at O0 through O3,
respectively. All extracted objects are ELF64 little-endian AArch64 relocatables.
Fresh core consumers pass 81,097 checks each with LLVM and CG.

## Validation boundary

Eleven regression tests pass **13,116,364 checks** and the 16 unsized-argument
admission compilations. They cover aggregate stores, aggregate array iteration,
borrowed slices, closure wrappers, unsized arguments, try-fold including
unwinding, and native standard-library iterator layouts. The all-target check,
formatting, documentation, diagnostic inventory, and whitespace checks are
retained with the results.

Strict bridge probes pass at O0 and O2: 36/18 functions, 29/21 pushed refinement
obligations, zero unmodeled shapes and no skipped obligations. Mandatory machine
proof still refuses emitted AArch64 instructions, beginning with StpPreIndex;
the independent ABI proof control also fails at its existing opcode-coverage
gate. These are required-feature failures, not successful negative controls.

All library and native checks here use diagnostic code generation with compiler
verification disabled. They do not establish complete language/runtime support,
source-to-machine proof, self-hosting, or any compile/runtime speed advantage.

## Reproduction

The evidence archive retains exact commands, stdout/stderr, source snapshots,
patches, object and executable identities, native artifacts, and frozen library
sources. The compiler/toolchain and backend binaries are identified by hashes;
they are not distributed in this report. Run the archived build script in the
recorded toolchain environment, then the alloc census, fresh library builds,
consumer matrix, permanent native tests, regression controls, and proof probes.
The source receipt binds this increment to the preceding native-layout report.

## Sealed identities

Backend SHA-256: `ccd04814d350ace91560a0d003467c308c9546af9ef47a4f22b9e4473824a6fc`.

The archive contains 3957 independently rehashed files and 271 source files.
Archive SHA-256: `c4584fcda43620b5d649691815c6e73f7a7420f0765346d8006473616f53fdd0`.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
