# Linux AArch64 assertion references

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Array/slice assertions now preserve their real operands through trait-object
formatting, including nested references, pointer identity, mutation and unwind
cleanup. The native matrix passes at O0–O3 in both panic modes. **Full std,
optimized unwind core, shared-library linkage, mandatory machine proof,
self-hosting, and strict compile/runtime wins over LLVM and Clang remain open.**

## Cause and repair

The array-length query recursively peels references. A legacy borrow shortcut
used that query for `&r` when `r: &[T; N]`, retaining only a length and discarding
the pointer to the reference. That prevented the assertion runtime from
converting its operands to `dyn Debug`. The shortcut now applies only to array
values; reference values retain their addresses.

Borrowed pointer parameters and the reference chains rooted in them receive
real scalar storage. The entry argument initializes that storage, and subsequent
reads use its current value. An intermediate candidate passed formatting checks
but failed a test that replaced the pointer through a nested mutable borrow:
indexing still read the original argument. The final implementation loads the
live pointer for reborrows, unsizing, call arguments, dereferences, slice-field
reads/writes, aggregate copies and enum discriminants. A guard rejects remaining
attempts to obtain a stored pointer from stale SSA bindings. The aggregate-store
refinement receives the actual loaded base pointer used by the emitted access.
The field-store obligation starts after the pointer reload and retains the real
address arithmetic and store. This keeps its existing local proof boundary
anchored on the live runtime base. A retained counterexample records the earlier
extra-load mismatch; the final obligation discharges at O0/O2, and native tests
check both the changed field and its untouched neighbor. The pointer reload
itself is outside that local field-store proof.

Optimized array equality also transmutes an array through a reference directly
into an integer. The existing dense-aggregate transmute path now handles that
address-bearing operand. It checks equal widths and absence of padding, and
emits a load that permits byte alignment. It does not copy pointer metadata or
read beyond the aggregate image. Existing mutable trait-object copy refusals,
SSA checks, refinement checks and machine-proof gates remain active.

The later native fixtures exposed the same stale-pointer lookup in slice-bearing
structs and enum-tag/aggregate-copy consumers. Small reproductions retain the
original refusals and the final successful execution. Application panic
interception remains outside this repair; the std crate-name fixture uses the
existing sysroot boundary to retain real assertion calls.

## Native and compiler validation

The permanent fixture passes **173,056 checks in 16 executions**, comparing LLVM
and CG at O0–O3 with unwind and abort. It checks exact assertion payloads,
empty and populated arrays, nested references, dynamic formatting, trait-object
data-pointer identity, mutation through a trait object, replacement through a
nested mutable reference, slice-bearing structs, enum-tag reads, aggregate
copies, stored-reference field mutation, and destructor effects. Integer
transmute loads cover 2/4/8/16-byte images at 17 offsets. Eight additional subprocesses terminate with SIGABRT and
the expected assertion message.

Thirteen broader regression tests pass **11,253,608 checks**, 96 additional
SIGABRT cases and four expected refusals. These cover borrowed aggregates and
slices, mutable pointer coercions, dynamic tails, enum discriminants, panic
payloads, aggregate returns, scalar cells, caller locations, drop/unwind behavior
and wide owners. The final all-targets build, formatting, documentation and
diagnostic-inventory checks pass.

Core builds at O0/O1; O2/O3 retain the same **23 failing functions** each.
Their `Ipv6Addr::fmt` failure changes from an unsupported raw reborrow to the
stored-pointer guard; that optimized consumer still needs a live-pointer load.
The full CG dependency graph attempts 19 crates: eight pass, eleven fail, with the same
**103 failing functions**, unchanged diagnostics and no compiler crashes.

The isolated O0 std build reduces failing functions from **330 to 317**, removing
the assertion failure and 12 B-tree `NodeRef::ascend` instantiations, with no new
failing functions. One existing `addr2line::FrameIter::next` failure advances
from an unbound pointer to an unsupported `Option<Location>` value. No stored-
pointer guard remains in this census. This build uses the frozen LLVM dependency
artifacts to isolate std lowering; it does not establish a complete CG-built
standard library. Every final census finishes without a timeout.

Strict bridge probes pass at O0/O2: **68/56 functions**, **19/12 pushed refinement
obligations**, zero unmodeled shapes, and zero skipped obligations. Memory
refinement traces additionally record **12/11 discharged checks**, including the
stored-reference field write. Mandatory machine proof refuses uncovered emitted instructions and exception-table proof
obligations (`TCG-PROOF-465`). Diagnostic builds disable Trust frontend
verification. Development runs overlap; their timings are not performance
comparisons.

## Reproduction and identities

Final production evidence uses `build-eleventh.log`, `eleventh-backend.so`, and its
frozen `eleventh-lib.rs`. The permanent matrix and regression controls use
`test-build-fourth.log` and immutable `fourth.test`. Complete commands, logs,
MIR, native objects/executables, source snapshots, patches and artifact
identities retain the earlier failed candidates as well as the final results.
Two earlier std probes reached their 600-second limits without producing a
final root census; an empty collected list in those records is not a pass.

The frozen std source retains the same 3,044 files used by the preceding
report, and the registry inputs are also revalidated. Large backend, test and
library binaries are identified by
hash alongside their build inputs and commands. This is development evidence,
not a consolidated acceptance report reproducible from an anonymous clone.

Backend SHA-256:
`a4cc5d062d95c42e508103343eb6a3aaf8db4ccd674342c62c7a12e067ebf3b5`.

Native test executable SHA-256:
`d8be573bf4dff156eac90df1169c6730167c50232e28292749453e81171bb655`.

The evidence archive contains **102,943 files** (640542296 compressed
bytes), with every member independently rehashed. Archive SHA-256:
`c1802d70784b75c3bf823e054c838187b4cb9102cee8c649f87da8005534981c`.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
