# Original source to scalar callback machine observations

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The diagnostic checker now binds original TrustIR, retained LIR and the actual
allocated AArch64 scalar-cell caller. All 24 captured F32/F64 callers at O0–O3
match. This is **not** callback proof authority, encoded-byte binding, or native
admission. The maintained private ABI bridge still refuses the unproved frame.

`check_aarch64_scalar_cell_frame` first checks the independent original-source
contract, then the complete machine layout and caller-side byte observations.
Its result immutably borrows all three endpoints. It exposes the seven exact
48-byte frame-envelope instructions, cell width and ordered call count; it
cannot construct a `SourceBoundFrame` or a compiler proof receipt.

The machine interpreter now handles MOVZ/MOVN/MOVK and GPR-to-FPR bit transfers,
including W-register zero extension and S/D width checks. It recognizes bounded,
class-matched erased-copy NOP records left by optimization, without defining
values for them. The existing leaf frame's NOP policy remains the argument of
its unchanged instruction-ownership check. Both routes reject hidden effects,
duplicated instructions, malformed layouts and undefined subsequent uses.

## Executed qualification

- **67 source-bound frame tests pass**, including the existing leaf, diamond,
  output-memory, original-source and frame authority refusal controls.
- **13 bridge regression tests pass**: eight pointer-copy and five signature
  layout tests. Total: **80 Rust tests**, with no failed or ignored selected
  tests in the final runs.
- All **24** actual pipeline reconstructions reproduce the independently
  captured machine signature, complete instruction arena, CFG/layout, virtual
  register bound and stack slots byte-for-byte in their stable debug prefix.
  Exact capture-file and prefix hashes are retained, together with all original
  frame inputs. These came from the previously recorded genuine Trust build.
- **19 additional accepted cases** cover twelve signed-zero/subnormal/finite
  boundary literals, three MOVN/W-to-X alias variants, and four two-call
  callers where the first opaque cell result becomes the next call argument.
- **540 mutations refuse**: 408 source/ABI/call/cell/frame/layout changes,
  48 malformed or effectful erased copies and undefined-value uses, 80 constant
  setup/width/shift/address-alias changes, and four deleted second calls.
- Root formatting, documentation maintenance and durable archive checks pass.

The first targeted run matched only eight callers. Constant setup raised this
to twelve; GPR erased-copy handling raised it to twenty; the remaining four
were FPR erased copies in optimized write callers. The complete final set
matches all 24 original captured machine prefixes. Initial failures and their
source fingerprints are retained. One integration invocation requested the
nonexistent target `signature_layouts`; Cargo rejected it before testing. The
corrected `bridge_signature_layouts` invocation ran and passed all 13 tests.

All build/test commands run serially under the anchored 16 GiB process-group
RSS supervisor with zero grace, two Cargo jobs and one test thread. Source
fingerprints remain unchanged within each run. No timeout, resource breach,
cancellation or output truncation is credited as a completed check. The
harness records source/tool/dependency identities and exact commands.

## Remaining boundary

The machine interpretation assumes ABI register preservation and private-frame
noninterference across each call. It models each ordered callback cell result
as fresh bytes; it does not limit callbacks to the cell or prove their arbitrary
public effects. The [conditional memory model](../2026-09-20-callback-memory-model-checkpoint/README.md)
still has unresolved whole-call proofs. Original-module request/cache binding,
independent whole-call replay, emitted instructions and BL relocations, and
callee/ownership authority remain necessary before production admission.
No solver or installed compiler package changes occur in this increment.
All L01–L14 completion rows remain open.
