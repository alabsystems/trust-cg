# Direct global-address leaves — 2026-09-20

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Linux AArch64's existing zero-storage leaf policy now recognizes direct ADRP
page and ADD-low-offset symbol materialization with exact physical X0–X15
operands. This removes the otherwise empty stack frame from simple global-address
returns. The source allocation/reference representation is the canonical one
qualified in [the preceding repair](../2026-09-20-frontend-const-references/README.md).

The policy accepts only nonempty Symbol or ExactModuleSymbol names in the exact
operand positions. Malformed forms, other register banks, reserved scratch or
preserved registers, implicit preserved-register effects, calls, GOT/TLS loads,
stack storage and EH metadata keep the established frame. Legacy frame APIs and
Darwin red-zone behavior are unchanged. The six arithmetic opcodes whose formal
source owner requires a frame retain that frame. This adds no instruction proof,
relocation certificate, reference-validity theorem or authority override.

## Qualification

169 frame tests, 87 DWARF-CFI tests, 979 pipeline tests and six native test groups
pass: 1,241 distinct tests with no ignored tests. Three targeted frame/pipeline
checks are also run separately and are already included in the 979. The new
controls check exact accepted address shapes, zero frame/no CFI adjustment,
legacy framing and malformed register/symbol/operand/call-effect refusals.
Existing native bounds checks execute 36 valid calls and 80 invalid-index calls
across 16 O0–O3 objects; every invalid index traps before the store. The five
native global-layout groups include O0–O3 struct/packed/array/pointer readers and
the direct object-layer tuple-layout control.

The normal uninstrumented Trust backend builds. Actual O0/O1 aligned-literal,
scalar/array-reference and static-data cases compile with backend proof checking
enabled. Independent C executables check scalar values, exact float bit patterns,
Unicode, array contents, source alignment, stable allocation identity and static
relocations/mutable cells. Assembly wrappers check SP, X19–X29 and D8–D15
preservation over 7,200 calls to the eighteen address-returning functions. Independent ELF
function-body decoding requires only direct page/offset materialization,
volatile-register moves, optional padding and RET, excluding hidden stack,
callee-preserved-register and call effects. Each observed body is sixteen bytes:
ADRP, ADD, MOV and RET. Readelf additionally checks exact FDE/function extents,
CFA at SP+0, return-address column 30 and no frame-state changes.

The two unwind cases still refuse required frame proof gaps; O0 also retains
CSet. Those are required-feature failures. Generic CSet proof mapping remains
unchanged. The Trust frontend is explicitly unverified, backend proof checks
stay on, and object-bound relocation authority remains its separate obligation.
The installed package is unchanged by this source qualification. L01–L14 remain
open; this is neither a full Linux acceptance run nor a self-host/release claim.

## Evidence and reproduction

Full root/native command logs, actual ELF objects, C/assembly oracles, original
Rust inputs, binary/source identities and resource records are retained. Heavy
work ran serially under an anchored 16 GiB process-group RSS limit, zero grace,
two Cargo jobs and one test thread. Source and HEAD remained fixed within each
qualification. The backend is uninstrumented. Large tool/test/backend binaries
are identified by hash; the harnesses preserve their original machine paths.
Formatting, documentation/link/inventory and archive hash checks pass.

```sh
cargo test --locked -p trust-cg-codegen --lib frame:: -- --test-threads=1
cargo test --locked -p trust-cg-codegen --lib pipeline:: -- --test-threads=1
cargo test --locked -p trust-cg-codegen --test e2e_aarch64_global_layout -- --test-threads=1
python3 scripts/check_evidence_archive.py reports/perf/2026-09-20-global-address-leaves
```

Private frontend/native reproduction requires the exact sealed Trust toolchain
and helper identities in the retained preflight records. These results apply to
this candidate and host.
