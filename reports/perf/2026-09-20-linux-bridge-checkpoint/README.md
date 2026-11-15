# Current Linux private ABI bridge checkpoint — 2026-09-20

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The complete maintained `check_linux_aarch64_bridge.py` gate was run on clean
source `cc2d64164426d1b3ef55490f5e8bb6f38862e687` with the coherent Trust `a62ae50d` toolchain. Result:
**FAIL**. The fresh release backend build and complete native-test build pass;
the native target reports **0 passed, 1 failed**, without ignored or filtered
tests. The overall guarded invocation takes 667.80 seconds with no timeout,
memory breach or cancellation. This does not qualify the required ABI matrix.

The exact backend snapshot is SHA-256 `96d1dae5c80be5e4f3f932579d512c71ee6784868740b281f0af19b5070ff4da`. It is copied from the
successful current build and passed to the separately identified test executable
by path and hash. Backend/test/source identities remain checked through the run.
The frontend is explicitly unverified (`-Ztrust-verify=off`); backend proof
enforcement remains enabled. The test's aggregate/HFA/scalar-cell floors and
unsupported-boundary controls are unchanged.

The first scalar-cell fixture, `aliased_f32_read` at O0, compiles and executes
through LLVM: **17 calls and 238 checks pass**. TrustCG refuses object emission
with `TCG-PROOF-465`: `StpPreIndex`, `StpRI`, `LdpRI` and `LdpPostIndex` have no
bound proof for the calling frame. This is a compile-time proof refusal, not
a successful TrustCG execution. Later positive cells, higher optimization
levels and the full HFA corpus are not reached and receive no credit.

The failure reproduces the existing L06-P1 blocker on current source; it does
not invalidate the separate [passing root-workspace floor](../2026-09-20-linux-required-floor-repaired/README.md)
or the [installed bounded development package](../2026-09-20-floor-repair-install/README.md).
The existing diagnostic scalar-cell interpreter and off-line memory formulas
remain separate from production call-frame authority. Further work must bind
the actual source ABI/call observations, private frame and public memory effects
to independently replayed evidence before extending admission.

All gate logs and identities, the unchanged runner/test sources, guard receipts,
and every retained temporary Rust/C fixture, compiler/linker log, object and
LLVM executable are archived. The large backend/test executables are hash
identified by the gate. An additional anchored supervisor enforces 16 GiB
process-group RSS with zero memory grace; builds use two jobs and tests one
thread. The installed compiler package is unchanged.

```sh
python3 scripts/check_evidence_archive.py reports/perf/2026-09-20-linux-bridge-checkpoint
python3 scripts/check_linux_aarch64_bridge.py --out /path/outside/source --target-dir /path/to/bridge/cache --jobs 2 --timeout-seconds 7200
```

L06-P1 and all L01–L14 completion rows remain OPEN. No gate, positive case or
proof requirement was weakened to obtain this checkpoint.
