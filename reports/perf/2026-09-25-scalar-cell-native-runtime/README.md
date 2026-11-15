# Supply the real Rust runtime to the native C ABI harness

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The original LLVM O0 repeated-cell and loop objects call
`core::panicking::panic_nounwind_fmt` from pointer-offset precondition checks.
The harness linked their C drivers and objects without the Rust runtime, so
five required LLVM lanes failed to link. The earlier proof-enabled run stopped
before reaching those lanes, at the first CG calling-frame proof refusal.

The maintained ABI harness now builds a Rust static library with the exact
compiler selected by its existing toolchain helper. It carries the compiler's
real core/std panic-abort runtime and links with its reported native libraries,
preserving their order and duplicates. Both the scalar-cell and larger
aggregate C links use it, with the archive hash checked before each link.
The original Rust/C corpus, observations, optimization levels and debug
precondition checks are unchanged. No core/std symbol is replaced by a stub.

The support library exports one deliberate-panic control. A separate C program
disables core dumps, invokes it and must terminate by SIGABRT with the expected
panic message. The new `llvm_scalar_cell_debug_runtime_links_and_aborts_on_panic`
test additionally compiles and executes the two original f32 O0 repeated/loop
drivers (119 calls and 4,488 checks). It passes from the actual Cargo-reported
test executable. The original proof-enabled test remains a required sibling;
this scoped regression run explicitly filters it out.

## Executed results

The base is `88c5467d577aa58ae63c6ca25b8f351728b0e256`; the final two maintained
source hashes are in `scalar-cell-runtime-repair-first/results.json` inside
the corresponding archive. Qualification uses genuine immutable Trust
`ae9c2c1da`, explicit development `targo --unverified`, the matching private
compiler libraries and LLVM SDK, two jobs and a 16 GiB process-group limit.
The mandatory private bridge all-targets check, new native regression, scoped
private formatting, maintained root formatting and whitespace checks pass.
The Python bridge-runner unit suite also reports 35 passes; its retained tool
receipt is explicitly partial because the tool truncated verbose mock-gate
output. Critical compiler/native command transcripts are retained losslessly.

Three scalar-cell census rounds preserve the full twelve-family denominator
(f32/f64 read/write/local/repeated/branch-loop, u64 repeated and the projected
indirect HFA-result case), both LLVM/CG and all O0–O3 tiers:

1. The first diagnostic harness stops after a successful LLVM case and CG
   compilation because it assumes LLVM's object filename. The actual CG object
   is present under its CGU filename. This is a harness error, not a compiler
   failure; the second uses every emitted object as the maintained test does.
2. The second completes all 96 cases using the previously qualified `847fa6071`
   backend: 91 pass, and precisely the five LLVM O0 repeated/loop links fail
   with the missing core routine. All 48 CG cases pass native execution.
3. The third uses a newly built current-88 backend and the real Rust runtime:
   all 96 cases pass, with 2,992 calls and 91,528 checks. All 48 CG compilations
   also retain their complete canonical TrustIR modules. Temporary diagnostics
   only serialize those modules before the unchanged Compiler pipeline; the
   two-file patch and restoration record are preserved, and the patch is not
   part of the published implementation.

The first runtime experiment used a no-std archive with a custom abort handler
and failed to link `rust_eh_personality`. It is retained as a failed experiment.
The successful runtime uses the selected compiler's actual std/panic-abort
implementation, including its personality support and native dependencies.

A further temporary copy exercises the **entire original ABI test body** after
the repair, including the larger aggregate matrix and all named refusal
controls. Its only execution change adds explicit `no-proof-certs` to CG
compiler commands, and its structured result marker is renamed `DIAGNOSTIC`.
This run passes: 104 native executions, 12,720 calls and 243,464 checks, plus
16 typed CG refusal controls with successful LLVM object twins. These totals
combine the 96 scalar-cell cases and eight larger aggregate runs exactly once;
the projected-cell subtotal already belongs to the scalar-cell denominator.
The independent twelve-family census above is not added again.

## Evidence boundary and reproduction

These are native differential/falsification results, **not production proof
admission**. CG diagnostics explicitly disable lowering certificates, and all
frontend development compilation explicitly disables Trust verification.
The last proof-enabled ABI measurement stopped at `[TCG-PROOF-465]`; its four
paired stack-save/load forms still lack the required calling-frame authority.
No callback/loader theorem, complete Rust ABI claim, L01–L14 closure or full
compiler completion is established here. The production proof gate is not
weakened or replaced by the diagnostic test copy.

The maintained narrow regression is reproducible with the matching genuine
Trust compiler/private SDK environment:

```sh
targo --unverified check --locked --manifest-path crates/rustc-codegen-trust-cg/Cargo.toml --all-targets
targo --unverified test --locked --manifest-path crates/rustc-codegen-trust-cg/Cargo.toml --test aarch64_c_fnabi_aggregate_linux llvm_scalar_cell_debug_runtime_links_and_aborts_on_panic -- --exact --include-ignored --test-threads=1 --nocapture
```

The retained runners spell out the exact private sysroot, library paths,
compiler identities, budgets and commands used here. Runtime-only backend
bindings are supplied to the test process after compilation. `records/` keeps
all actual rounds, sources, source modules, object files, native executables,
command/guard outcomes and diagnostics in deterministic tar/gzip archives.
`assets.json` binds every contained file by hash and size and separately lists
rebuildable backend/extractor/test binaries and runtime archives identified
rather than duplicated in Git. Their sources, build commands and hashes are
retained; native linked images are archived. `manifest.json` and `inventory.json`
bind both compressed and raw archive bytes, and every tar member was independently
re-read and matched to `assets.json` before publication.
