# Linux AArch64 projected reference types

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Projected borrows now carry the destination reference's Trust IR type in the
admitted scalar-leaf and sub-aggregate paths. Returning `&record.first_field`
previously returned an aggregate-typed parameter directly: its address was right,
but the checked return signature correctly rejected its type. At nonzero offsets,
field and indexed aggregate borrows could instead retain plain `Ptr` values;
converting a mutable borrow to a shared borrow then failed the cast's checked
source type. The bridge now normalizes these addresses and assigns the projected
local's thin-reference type before binding it. Layout, pointer identity and
mutability behavior are preserved; the return, cast, call and SSA gates remain.

The scalar repair is `4e8bc052a`. Remote AArch64 compile-scaling changes were
merged at `44d278597`. The aggregate extension is `1dfd6e2d2`; the subsequent
x86-only merge is `41a05beea`. Remote main subsequently updates the TrustIR pin
at `4bc57c91e`; another x86-only setting is merged at `b27031ad0`.
Generated documentation conflicts were resolved by
regenerating and checking the inventories against the combined source.

## Regression evidence

The original backend rejects the scalar reproducer at O0/O2 while LLVM executes
it correctly. The scalar-only repair still rejects mutable-to-shared aggregate
reborrows, including a runtime-indexed record at both optimization levels. The
completed repair passes those same native reproducers. Binary Trust IR and lossy
diagnostic text retain the two original type mismatches and the corrected aggregate
module; the exact probe sources and command transcripts are included.

The two permanent fixtures pass **2,162,688 checks in 32 executions**, covering
LLVM and trust-cg at O0–O3 with abort and unwind panic modes. They check reference
identity, writes through returned mutable references, first/last fields,
repr(C)/repr(Rust) records, nested arrays, indexed aggregate fields, reborrows,
branch-selected references and callback arguments. The drivers use Rust ABI
declarations and LLVM-generated code to exercise the compiled functions.

The completed repair's eight regression groups pass **13,389,824 checks in 104
fixture executions**, plus **112 expected SIGABRT outcomes**. Existing projected
aggregate, raw-reference storage, scalar-cell return, indirect-call unwind,
dynamic-drop and terminate-pad checks are included. Four expected refusals remain
for padded partial copies and disabled exception handling. These totals belong to
one frozen backend; results from different revisions are not added together.

The scalar-only pre-merge backend separately passes 12,320,768 checks in 56
executions. Its first merged rebuild passes 12,472,320 checks in 88 executions,
plus the same 112 abort outcomes. The x86-only rebuild and the subsequent TrustIR-pin rebuild each rerun both
new fixtures, passing their 2,162,688 checks in 32 executions. The final
x86-setting rebuild repeats that matrix and the strict/machine probes too.

## Libraries and unfinished work

The scalar repair compiles isolated optimized core and alloc against the recorded
dependency configuration. The first two merged AArch64 backends also build fresh mixed
libraries with **core and alloc compiled by trust-cg at O2**, and the rest of std
built by LLVM. Each mixed library passes its exact-library dynamic consumers:
21,504 network/escape-formatting checks, two sets of 81,097 UTF-8/character-count
checks, and 112 caught panics with payload/destructor checks. Compiler invocation
records, loader logs and library hashes identify what was built and executed.
The observed mixed-build durations are 73.38 and 72.26 seconds. The subsequent
TrustIR-pin rebuild also passes a fresh mixed build and the same exact-library
dynamic consumers; its build duration is retained in its receipt. These runs are
correctness qualification, not a controlled LLVM/Clang performance comparison.

The initial full-std O0 profiling probe, using the pre-repair backend, reaches its
1,800-second deadline before producing a complete root inventory. Its empty
`failed_roots` field is incomplete, not success. After the scaling merge, the
paired full-std O0 probes complete: the scalar-only repair reports **223 failed
roots**, and the aggregate extension reduces that to **213**, removing nine cast-source type failures and one branch-argument type mismatch with no new roots or changed surviving diagnostics. These
probes use the same recorded LLVM dependencies and TrustIR 96e3885; they do not
constitute a fully trust-cg-built std graph. Remaining roots include custom static
sections, unwind/intrinsic support, SIMD/alignment, SSA and register allocation.

Full trust-cg std, complete machine proof, self-hosting and strict compile/runtime
wins over LLVM and Clang remain unfinished.

## Proof and provenance

Strict MIR bridge probes pass at O0/O2. Across the two completed fixtures there
are 23 MIR functions, 6/3 refined scalar obligations, 4/2 memo hits, zero skips and
zero unmodeled shapes. These checks do not prove memory, pointer provenance,
control-flow wiring or exception tables. Machine-proof-required runs refuse with
`TCG-PROOF-465` for uncovered opcode evidence. Native execution uses diagnostic
`no-proof-certs`; the Trust frontend is explicitly run with verification off.

Frozen backend SHA256 identities:

- Scalar repair: `b48b97a3a9478a53d9c8ef19ec616fac29c1113cb2c5e82b2d7fb965ad928325`
- Scalar repair with AArch64 scaling merge: `86b322c5f6a782d70e474cb0731b5d2fa249b35edc794a9faaea89b4a9609d8b`
- Completed aggregate extension: `b7762005e1ad3a30a52ecdfbf4e54e9d5c10709b9b2c6048f71cdb798e080162`
- X86-only merge: `35600f7e77b4f439e26b6806aa95c87e74e28df489e06e2e7d856205b02a682a`

The final pin rebuild is
`54b2a31eddba05d0207f3137fb64128335767974b4ff69b966bdb049b6a286d2`.
It uses TrustIR `824174a164de10dba2053e387dfc4b1140960885`. Local Git tree
checks confirm that the core IR and conformance trees match the previous pin;
the new contract vocabulary is qualified by upstream and the rebuilt bridge
retains the same strict-pass/machine-refusal results. The complete std root
comparison above remains attributed to the earlier pin. The final x86-setting
rebuild is `ef6ecd5c809d7725e4a970948b1f7d787c6a4c76ebf90f8a215b5397f3a3df45`;
it preserves the same AArch64 lowering and TrustIR pin.

Source manifests, exact patches, harness input hashes, build receipts, commands,
compressed logs and evidence hashes accompany this report. Patch/environment
snapshots retain their exact bytes in gzip files. Native and strict probes use
the private AY cache; library probes retain their recorded baseline diagnostic
cache policy. Frozen binaries, sysroots and complete ELF inventories remain local
under `target/std-completion-investigation/`; independent binary publication is
still open.
