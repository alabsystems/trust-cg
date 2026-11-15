# Linux globals twin repair: native-off build and body SymbolAddr TLS refusal — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Result: **PASS** on the Linux AArch64 host (NVIDIA Grace, Ubuntu 24.04) for
clean source `ef6cc15ef89eb53e34e68176bd5bc29fe4d3f8cf` (no tracked changes;
see the two temporary edits below). This commit repairs the increment
archived in [`../2026-09-23-linux-globals`](../2026-09-23-linux-globals/README.md):

- `e2e_aarch64_globals_linux` did not compile on any host without its Linux
  GNU native legs (macOS, x86-64): three helpers and two imports used only by
  the native module were dead code under the workspace's `warnings = "deny"`.
  They now carry the native module's cfg.
- A function-body `Constant::SymbolAddr` naming a thread-local the module
  declares is refused by name in the trust-ir adapter
  (`[TCG-TLS-SYMBOL-ADDR]`). Before this it lowered to a plain
  `R_AARCH64_ADR_PREL_PG_HI21`/`ADD_ABS_LO12_NC` pair against the `STT_TLS`
  symbol (Mach-O: a page reference to the TLV descriptor).

Ledger rows L05-P10 and L03-P6 stay PARTIAL.

| Record | Result |
| --- | --- |
| `trust-cg-codegen--e2e_aarch64_globals_linux.log` (one new host-neutral row) | 15 passed, 0 failed |
| `native-off-ef6cc15ef.log` (the target with its native legs switched off) | 6 passed, 0 failed |
| `native-off-b4af65ed7.log` (the same build of the pre-repair file) | does not compile: 3 dead-code errors |
| `refusal-disabled-control.log` (the new refusal switched off) | both new tests fail, as intended |
| `trust-cg-lower--lib.log` (includes the new adapter unit test) | 1879 passed, 0 failed |
| `trust-cg-codegen--lib-unit.log` (the four unit tests of the increment) | 4 passed, 0 failed |
| `trust-cg-codegen--e2e_aarch64_elf_link.log` | 11 passed, 0 failed |
| `trust-cg-codegen--e2e_aarch64_elf_tlsie.log` | 8 passed, 0 failed |
| `trust-cg-codegen--e2e_aarch64_elf_relocation_model.log` | 19 passed, 0 failed |
| `floor-gate-script-tests.log` (Linux and Darwin floor inventories) | OK (1 host-dependent skip) |

`toolchain.txt` records the source commit and the toolchain, as in the
earlier archive. The last line of `floor-gate-script-tests.log`
(`Linux AArch64 regression floor: FAIL`) is printed by a unit test's own
fixture run, not by a floor run.

Commands (from the repository root, `PKG` the installed proof-tool package):

```sh
export PATH="$PKG/bin:$HOME/.cargo/bin:$PATH"
for t in e2e_aarch64_globals_linux e2e_aarch64_elf_link e2e_aarch64_elf_tlsie \
         e2e_aarch64_elf_relocation_model; do
  cargo test --locked --offline --color never -j 8 -p trust-cg-codegen --test "$t" \
    -- --nocapture --test-threads=1
done
cargo test --locked --offline --color never -j 8 -p trust-cg-lower --lib
# native legs off: a temporary, untracked copy of the target, deleted afterwards
T=crates/trust-cg-codegen/tests
for rev in b4af65ed7 ef6cc15ef; do
  git show "$rev:$T/e2e_aarch64_globals_linux.rs" \
    | sed 's/target_env = "gnu"/target_env = "musl"/g' > "$T/zz_offnative_globals_linux.rs"
  cargo test --locked --offline --color never -j 8 -p trust-cg-codegen \
    --test zz_offnative_globals_linux
  rm "$T/zz_offnative_globals_linux.rs"
done
python3 -B -m unittest scripts/tests/test_linux_aarch64_gate.py scripts/tests/test_darwin_aarch64_gate.py
```

The native-off build. The Darwin floor requires this target's host-neutral
rows, but this Linux host compiles its native module, so the host alone
cannot see a build failure on macOS. Replacing `target_env = "gnu"` with
`"musl"` at every cfg site (each log's first line gives the count) switches the native module off exactly as a
macOS or x86-64 host does, under the same `--deny=warnings` Cargo passes.
The pre-repair file fails (`function jit_globals_module is never used`, the
same for `body_symbol_addr` and `addend_module`); the repaired file compiles
without warnings and runs exactly the six host-neutral rows the Darwin floor
now requires. This is a type-check and a run on Linux of the code a macOS
host would compile, not a macOS run: the target has still never run on
Darwin.

The refusal control. `refusal-disabled-control.log` starts with the
temporary one-line edit (`&& false` in the adapter's check, reverted after
the run). With it, the adapter unit test fails because `tls_def` lowers, and
the e2e row fails because the `Compiler` returns an object for the Linux
static O0 module. The e2e row also compiles the same body naming the plain
data global `g_target` on every target it checks.

The object sha256 lines of the `e2e_aarch64_globals_linux` log are identical
to the earlier archive's, line for line: the new refusal changed none of the
objects that the increment's native controls link.

Boundaries. The refusal is a fail-closed control, not a feature: a body
still cannot take a thread-local's address through `SymbolAddr` (use
`GlobalAddr`, which lowers through the TLS access path). The adapter check
is target-independent, but only AArch64 triples (Linux static/PIE/PIC and
Darwin) are tested. A lower-IR `GlobalRef` or `ExternRef` handed to the
`Pipeline` API that names a thread-local object global is not refused. The
full Linux floor was not rerun for this commit. The full `trust-cg-codegen`
library suite still has the one earlier failure,
`test_aarch64_parallel_and_serial_multi_function_byte_identical`
(`ProofPromotionRejected` for `StpPreIndex`/`LdpPostIndex`), which is not
related to this change.
