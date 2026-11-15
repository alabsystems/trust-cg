# Linux AArch64 raw reference storage

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

References whose addresses escape through raw pointers or aggregate fields now
retain addressable storage. Reference-valued scalar cells hold the reference
pointer, and a borrow of a projected pointee computes an address from its runtime
base. Ordinary reference-return calls preserve pointer identity; the scalar
snapshot selector applies only when a borrowed binding was actually passed.
The change is scoped to admitted Linux AArch64 layouts and retains existing
mixed-snapshot and partial-copy refusals.

Production commit: `ee201313a`. Remote integration: `61dac3846` (Trust IR
`96e388531f46f387e0902bfc2a63acf6eeb15a5f`). The merged frozen backend is
`de4b234c63ef3712db96f72b6ace6e6a1c473640d3c23244a310dbf1c01653d3`.

## Results and remaining runtime failure

The permanent raw-reference fixture passes LLVM/trust-cg O0–O3 under abort and
unwind: **2,097,152 checks in 16 executions**. Its eight cases include references
stored in tuples, dynamic array indexing, local and projected aggregate borrows,
references loaded from or returned through records/calls, raw alias mutation of
a reference parameter, and a whole Range borrow. The C oracle checks pointer
identity as well as values. Together with six regression groups, both the
pre-merge and merged backends pass **19,589,120 checks in 80 executions**, plus
five named refusals. The logs record each exact backend identity.

The pre-merge backend builds core at O0 and O2 with zero failed functions:
170.76 and 355.68 seconds respectively. This removes the five compilation
failures left by the projected-aggregate milestone. These are diagnostic census
timings, not controlled performance comparisons. An isolated O2 alloc census
still refuses two roots: dynamic drop and an indirect call with cleanup edges.
Its dependencies are recorded LLVM artifacts; it is not a full trust-cg std build.

After remote integration, a fresh build of LLVM std with trust-cg O2 core
succeeds in 361.08 seconds. Dynamic consumers actually load that mixed libstd:
LLVM and trust-cg consumers each pass 81,097 character-count/UTF-8 checks;
112 caught panic cases preserve payloads and destructor counts. IPv4/IPv6 and
socket formatting passes 16,384 additional checks. Library hashes, commands,
ELF inspection and loader logs are retained locally; receipts are included here.

**A broader runtime probe fails:** `str::escape_debug().to_string()` crashes
with SIGSEGV in generated iterator/formatter code. The GDB trace reaches
`EscapeDebug::fmt`, then a private write-character helper with a corrupt pointer.
This is an open compiler correctness bug; successful core compilation and the
passing reduced fixtures do not establish that core is fully correct. The
combined formatting probe's nonzero result is retained, alongside the separate
passing network probe. This failure takes priority over extending indirect EH.

## Proof scope

Strict bridge probes accept O0/O2 on both backends: 26/22 functions, 42/32
accepted scalar obligations, 23/17 memo hits, zero skipped obligations and zero
unmodeled shapes. Address, memory, operand wiring and control-flow behavior are
not proved by those scalar results. Machine-proof-required probes still refuse
with `TCG-PROOF-465`; memory/frame evidence remains incomplete. Runtime sampling
receives no proof credit. Native and proof probes use the private AY cache;
core/stdlib diagnostic censuses retain their recorded baseline cache policy.

## Provenance and availability

The pre-merge frozen backend is
`cda3a5e78d5ca4f127700675b0e37addad96c30f5217904a84fb0e1f4bffeef8`.
Source manifests, source patch, build receipts and compiler commands identify
both builds. A wrapper naming bug overwrote the full historical pre-merge
build log; its immutable artifact, source snapshot and build receipt survive.
The successful merged build has its own preserved log. Exploratory first and
second variants were not qualified: the second exposed an incorrect address
base and a reference-return selection issue, both repaired before qualification.

These are thin evidence records. Full compiler/native artifacts and source
snapshots remain under `target/reference-raw-reborrow-investigation/` locally;
independent publication remains open. Full trust-cg std, complete machine proof,
and compile/runtime wins over LLVM and Clang remain unfinished.
