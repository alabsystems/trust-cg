# Formatter reference cells — 2026-09-27

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Borrowing an entry aggregate's scalar field now supplies the actual field
address when the reference itself needs stack storage. Reference chains accept
that addressable terminal only when every definition is an eligible projected
borrow. Existing layout walks calculate the offset; the field stays in the
caller's storage. Other definitions and unsupported projections still refuse.

Whole-local reference and raw-pointer borrows now type the existing memory-slot
address before binding it to their result local. This prevents later pointer
casts from declaring a typed operand while receiving an untyped Alloca address.
Scalar arrays whose direct references are raw-reborrowed also get stable storage;
all direct array targets of that reference are retained. These operations change
neither the address nor pointer metadata. No proof or semantic validator changed.

Qualification binds base `7ab5f81d1d041d18f5f289a4fd0e5a61c83816e9` and seven maintained source hashes,
genuine Trust `ae9c2c1da`, and backend `20c2870ea226e062a6cad07c98c912074dfe299fb5b9ceb5497591ed399fb6e7`. These native
runs use the unverified frontend and diagnostic codegen without proof
certificates. They do not qualify verification or the installed toolchain.

- All-targets check and backend build pass; the maintained target lists exactly
  25 tests. The new test executes both corpora at LLVM/CG O0–O3.
- The original core `FromBytesWithNulError::fmt` body in an independent error
  type passes 24,576 checks of exact output and limited-writer errors.
- Expanded callbacks pass 53,248 checks of struct/enum field addresses and
  values, signed integers, float bits, booleans, Unicode characters, deeper
  reference chains, empty/payload variants, and array reference/address identity.
  Together the new maintained corpora pass 77,824 native checks.
- Twenty-two unchanged regressions pass 5,343,116 native checks, including 320
  LLVM-only checks with matching CG refusals. Existing f16-value, wide-newtype
  store, unsupported aggregate cleanup and over-aligned Drop refusals remain.
- The complete core diagnostic exits 1
  with 12 failed roots and 44
  objects. Compared with the published 13-root baseline, only the formatter
  failure disappears; no new or changed remaining failures occur.
- The unchanged mandatory proof ABI test exits 101;
  `TCG-PROOF-465` is present: True. Native success is not proof.
- Root formatting passes. Private formatting adds zero differences beyond
  59 pre-existing library blocks; all changed
  tests and fixtures pass the formatter in full.

Failed prototypes remain archived: the first stopped at the optimized formatter's
typed-pointer mismatch; the next expanded probe exposed deep-reference and
array-address refusals, and the third stopped at the raw-pointer form of the
same type mismatch. The fourth prototype passed both unchanged corpora, then
the formatted maintained source was built and tested again. Temporary tracing
was removed before that final qualification. Prototype core runs are separate
measurements; they are not counted as additional native or proof checks.

Full-core compilation, instruction proof coverage and the original conjunctive
completion gates remain open. Receipts, exact source snapshots, logs, emitted
objects and native executables are retained below; rebuildable backend/shared
archive binaries are listed by digest in `excluded.json`.
