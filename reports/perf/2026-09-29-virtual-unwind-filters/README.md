# Virtual unwind edges and empty termination filters on Linux AArch64

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Virtual trait, `Fn` and `FnMut` calls preserve their MIR cleanup edge through the existing typed indirect-call forwarding thunk. Return stores and mutable-argument reloads execute on the normal continuation. Hidden-x8 indirect returns remain refused.

The expanded test exposed a separate termination bug: a cleanup-only termination pad does not stop phase-one search. Search could reach a caller's nounwind call site and abort with a runtime unwind error before invoking `panic_cannot_unwind`. The compiler now uses an empty exception filter for its Linux AArch64 termination pads. It calls the real reason-specific panic entry on normal unwinding, while the Rust personality skips it on forced unwinding, matching LLVM.

The pinned Trust IR landing-pad carrier has no filter-list field. The compiler explicitly reserves `RUST_EH_EMPTY_FILTER = u32::MAX`, outside the positive signed LSDA index domain, as a sole non-cleanup Rust clause. Lowering and the LSDA builder reject other personalities, mixed clauses and cleanup combinations. The exact clause remains in retained LIR identity and machine EH metadata. Action -1 binds an explicit zero-byte empty list at TType base. The ELF relocation reader independently validates that binding; arbitrary negative actions and general filter lists remain refused. EH/CFI remain disclosed trusted-base components, not complete machine proofs.

The original expanded prototype incorrectly rejected LLVM's second panic hook and accepted any CG SIGABRT. It is retained as failed exploratory evidence and is not counted as qualification. The corrected v2 fixture passes LLVM but fails the old cleanup-pad CG backend at O0/O2. A separate `_Unwind_ForcedUnwind` probe also fails that old CG backend by entering a panic hook; LLVM reaches its outer stop callback after the inner destructor. Both corrected probes pass the empty-filter backend at O0/O2.

Full CG standard-library completion, self-hosting, complete machine proof, and strict compile-time/runtime superiority over LLVM and Clang remain open.


## Source identities

The repair is committed as `1c07bd5f1`; the merged compiler is built from `79e462002ce094fdb77553e90a65349460b5f20c`, incorporating remote main `c9cf81176` and its typed-load IR cohort plus x86 flag-only DCE changes. The diagnostic empty-filter backend has SHA-256 `5c28bd44f8ff74bc5deaa855062cbaa014e51fa1be4d06b9c539c8500160b518`; the merged backend is `a7dc0c2db921053f59a1530ea8e16c2a73410094703a472f1670d80756be601d`. The old cleanup-only virtual backend is `2a149f288d588fe5ee5e209afb66756f5c8ce7be4d096cd5adb503d29b56161e`. Full source manifests and patches accompany every frozen backend.

The toolchain is Trust `ae9c2c1daa0fc80afbfd380e493f5581ac714acb` on Linux AArch64. The premerge backend uses Trust IR `824174a164de10dba2053e387dfc4b1140960885`; the merged backend uses `7917c1721483b7b17136f4a6e1b8d8acef392c2f`. Independent Git-object comparison confirms identical instruction, type, constant, interpreter and conformance sources, not identity of the complete IR tree. These builds use the explicitly unverified host-compiler lane and make no claim of proving the compiler's own Rust implementation.

## Native and bridge checks

The new permanent fixture covers trait methods, a register-pair return, `Fn`, `FnMut`, mutable-reference writes, `track_caller`, a large by-value argument whose caller copy remains live, real panic payloads and destructor order. LLVM and CG run at O0–O3 under abort and unwind policies: 16 executions, 49,152 checks, 7,168 caught panics and 16 correctly identified SIGABRTs. The forced-unwind fixture adds eight executions and requires the inner destructor to run, the termination hook to stay uncalled, and unwinding to reach the outer stop callback. Four compile refusals retain hidden-x8 indirect-return and disabled-EH boundaries, with four LLVM controls.

Including the existing indirect-return, dynamic-drop and reason-specific termination controls, the premerge run passes 56 executions, 200,704 counted checks, 128 SIGABRTs and eight expected compile refusals. The forced-unwind executions are included in the execution count, while their C stop-callback assertions are not added to the numeric check counter. The merged rerun passes that same complete matrix, recorded separately in `native-merged-1-results.json`. Across the two backend revisions this is 112 executions, 401,408 counted checks, 256 SIGABRTs and sixteen expected compile refusals.

Strict bridge probes on both frozen backends pass at O0/O2: 18/15 functions, 16/13 refinements, one memo hit at each level, zero skipped and zero unmodeled shapes. The corresponding machine-proof-required probes remain refused by `TCG-PROOF-465`; this change grants no machine-proof exemption.

The premerge lowering/LSDA/ELF/module-merge selection passes 184 tests. It includes malformed filter clauses, unsupported personalities, missing/nonempty filter lists, nonterminal/other negative actions and existing typed-catch controls. The merged selection passes 702 tests: the same 184 plus 15 construct-inventory, 13 UB-map, 437 x86 selector and 53 x86 DCE tests. Every selected group executes at least one test; full commands and executable hashes are in the separate root result files.

## Standard-library progress

A fresh mixed build compiles core and alloc at O2 with the premerge CG backend and the remaining libraries, including std, with LLVM. Consumers load those exact library artifacts: both LLVM and CG UTF-8 consumers pass 81,097 checks each, formatting passes 21,504 checks, and runtime consumers catch 112 panics with matching destructor counts. This is not a whole-CG std build; the merged cohort was not used for this library run.

The completed isolated O2 std census decreases from 231 to **223 failing roots**, with eight removed, zero added and eleven changed diagnostics. All nineteen old virtual-cleanup refusals disappear. Eight roots now compile, including panic hooks, `Once::call`, process execution and backtrace helpers. Seven remaining roots reach hidden-return-buffer refusals, two reach fat `Fn` argument spreading, one reaches a closure-vtable argument ABI refusal, and one reaches the dynamic `FnOnce` refusal. Those remain real open failures.

Both std censuses use the recorded LLVM dependency artifacts and Trust IR 824174a; the before/after backend source manifests also disclose the intervening sealed-JIT integration. The after run exits 1 in 737.178 seconds without timing out. The latest separate O0 census remains 197 failures. See `std-delta-third.json` and the complete diagnostics for exact root identities. No compile-time or runtime speed superiority is inferred from these correctness runs.
