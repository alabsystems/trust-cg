#!/usr/bin/env python3
"""L04-P11 qualifying run on Linux AArch64 (2026-09-24).

Runs, from a clean checkout of this repository, every command the L04-P11
record cites and stages the logs under <out-dir>/records:

  1. the two native targets (`e2e_aarch64_switch`, `e2e_aarch64_indirect_call`)
     with `L04P11_RETAIN_DIR` pointing at <out-dir>/retained, so each test
     keeps its per-level objects and C drivers;
  2. binutils `objdump -d` and `readelf -sW` of the retained O2 objects;
  3. the library and integration targets the verifier change touches
     (`trust-cg-codegen --lib`, the five trust-cg-verify gate targets, the
     copy-binding and value-decode unit tests, the CLI binary and
     `emit_proofs_flag` tests) and, last, the complete `trust-cg-verify --lib`;
  4. the gate-script unit tests and the native test host matrix check;
  5. mutation controls: each mutation replaces exactly one source span,
     rebuilds and runs the named tests, which must FAIL (or, for the named
     equivalent mutant, must produce byte-identical objects), and the file is
     restored and checked clean before the next one.

Cargo runs with `--locked --offline -j 16`, PATH led by the pinned AY/Clean
package directory, CARGO_TARGET_DIR outside the repository and ambient
`TCG_*`/`TRUST_CG_*` variables removed. The source must be clean before and
after (`records/source.json`).

Usage: qualify-l04p11-20260924.py <out-dir> [--skip-verify-lib]
"""

from __future__ import annotations

import gzip
import hashlib
import json
import os
import platform
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(os.environ.get("L04P11_SOURCE_ROOT", "$HOME/trust-cg/.claude/worktrees/agent-a132798c1f3a4825a"))
OUT = Path(sys.argv[1]).resolve()
SKIP_VERIFY_LIB = "--skip-verify-lib" in sys.argv[2:]
PACKAGE_BIN = "/home/ayates/.local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23/bin"
TARGET_DIR = "/home/ayates/trust-cg-wt/target-l04p11"
JOBS = "16"
RECORDS = OUT / "records"
COMMANDS = RECORDS / "commands"
RETAINED = OUT / "retained"


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def environment() -> dict:
    env = {k: v for k, v in os.environ.items() if not k.startswith(("TCG_", "TRUST_CG_"))}
    env.update(
        CARGO_TARGET_DIR=TARGET_DIR,
        CARGO_PROFILE_DEV_DEBUG="0",
        CARGO_PROFILE_TEST_DEBUG="0",
        PATH=f"{PACKAGE_BIN}:/home/ayates/.cargo/bin:/home/ayates/.local/bin:"
        "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin",
    )
    return env


ENV = environment()


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(*args: str) -> str:
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True, check=True).stdout.strip()


def cargo(*args: str) -> list[str]:
    return ["cargo", "test", "--locked", "--offline", "-j", JOBS, *args]


SUMMARY_PREFIXES = (
    "test result:", "switch matrix on ", "indirect calls on ", "Ran ", "OK", "FAILED (",
    "check_fmt:", "matrix check", "native test host matrix",
)


def run(name: str, argv: list[str], *, env: dict | None = None, gz: bool = False,
        expect: str = "pass") -> tuple[int, str]:
    env = ENV if env is None else env
    started = now()
    result = subprocess.run(argv, cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    finished = now()
    data = result.stdout
    text = data.decode("utf-8", errors="replace")
    COMMANDS.mkdir(parents=True, exist_ok=True)
    log = COMMANDS / (f"{name}.log.gz" if gz else f"{name}.log")
    log.write_bytes(gzip.compress(data, mtime=0) if gz else data)
    summary = [line.strip() for line in text.splitlines() if line.strip().startswith(SUMMARY_PREFIXES)]
    outcome = "pass" if result.returncode == 0 else "fail"
    capture = {
        "name": name, "argv": argv, "cwd": str(ROOT),
        "environment": {k: env[k] for k in sorted(env) if k in (
            "PATH", "CARGO_TARGET_DIR", "CARGO_PROFILE_DEV_DEBUG", "CARGO_PROFILE_TEST_DEBUG",
            "L04P11_RETAIN_DIR")},
        "started_utc": started, "finished_utc": finished, "returncode": result.returncode,
        "log": log.name, "log_sha256": sha256(data), "log_bytes": len(data),
        "summary": summary, "expected": expect, "outcome": outcome,
        "as_expected": outcome == expect,
    }
    (COMMANDS / f"{name}.capture.json").write_text(json.dumps(capture, indent=2) + "\n")
    print(f"{name}: rc={result.returncode} expected={expect} {summary[-3:]}", flush=True)
    return result.returncode, text


def tool(name: str, version_args: list[str]) -> dict:
    resolved = shutil.which(name, path=ENV["PATH"])
    if resolved is None:
        return {"name": name, "resolved": None}
    real = os.path.realpath(resolved)
    version = subprocess.run([resolved, *version_args], capture_output=True, text=True, env=ENV)
    first = (version.stdout or version.stderr).strip().splitlines()
    return {"name": name, "resolved": resolved, "real": real,
            "sha256": sha256(Path(real).read_bytes()), "version": first[0] if first else ""}


def source_record() -> dict:
    return {"head": git("rev-parse", "HEAD"), "tree": git("rev-parse", "HEAD^{tree}"),
            "branch": git("branch", "--show-current"),
            "status_porcelain": git("status", "--porcelain", "--untracked-files=all")}


SWITCH = cargo("-p", "trust-cg-codegen", "--test", "e2e_aarch64_switch", "--", "--show-output", "--test-threads=1")
INDIRECT = cargo("-p", "trust-cg-codegen", "--test", "e2e_aarch64_indirect_call", "--", "--show-output",
                 "--test-threads=1")
# Linux floor targets that drive proof-required or verifying routes (JIT
# proof policies, source-bound JIT arithmetic, the certificate cache, the
# sealed Core planner, verifying final-layout checks).
PROOF_GRADE_FLOOR = [
    ("trust-cg-codegen", "jit_fail_closed_proof_policy"),
    ("trust-cg-codegen", "jit_source_bound_arithmetic"),
    ("trust-cg-codegen", "jit_cert_cache_identity_aarch64"),
    ("trust-cg-codegen", "core_jit_planning"),
    ("trust-cg-codegen", "jit_wx_refusal"),
    ("trust-cg-codegen", "aarch64_final_layout_crosscheck"),
    ("trust-cg-codegen", "aarch64_raw_dataflow_boundary"),
]

# (name, file, exact old text, new text, [(label, argv, expect)])
MUTATIONS = [
    (
        "m1-jump-table-bound-off-by-one",
        "crates/trust-cg-lower/src/switch.rs",
        "vec![ISelOperand::VReg(index_vreg), ISelOperand::Imm(range)],",
        "vec![ISelOperand::VReg(index_vreg), ISelOperand::Imm(range + 1)],",
        [("switch", SWITCH, "fail"), ("indirect_call", INDIRECT, "fail")],
    ),
    (
        "m2-bst-signed-lt-as-unsigned-lo",
        "crates/trust-cg-lower/src/switch.rs",
        "ISelOperand::CondCode(AArch64CC::LT),\n                ISelOperand::Block(left_block),",
        "ISelOperand::CondCode(AArch64CC::LO),\n                ISelOperand::Block(left_block),",
        [("switch", SWITCH, "fail")],
    ),
    (
        "m3-narrow-selector-not-cleaned",
        "crates/trust-cg-lower/src/isel.rs",
        "Type::I8 => AArch64Opcode::Uxtb,\n            Type::I16 => AArch64Opcode::Uxth,",
        "Type::I8 if false => AArch64Opcode::Uxtb,\n            Type::I16 if false => AArch64Opcode::Uxth,",
        [("switch", SWITCH, "fail")],
    ),
    (
        "m4-blr-clobber-set-dropped",
        "crates/trust-cg-lower/src/isel.rs",
        "ISelInst::new(AArch64Opcode::Blr, vec![fn_ptr])\n"
        "                .with_implicit_uses(implicit_uses)\n"
        "                .with_implicit_defs(call_implicit_defs()),",
        "ISelInst::new(AArch64Opcode::Blr, vec![fn_ptr])\n"
        "                .with_implicit_uses(implicit_uses)\n"
        "                .with_implicit_defs(Vec::new()),",
        [("indirect_call", INDIRECT, "identical-objects")],
    ),
    (
        "m5-indirect-stack-argument-offset",
        "crates/trust-cg-lower/src/isel.rs",
        "vec![src, ISelOperand::PReg(SP), ISelOperand::Imm(*offset)],\n"
        "                        ),\n"
        "                    );\n"
        "                }\n"
        "                ArgLocation::Indirect { ptr_reg } => {\n"
        "                    self.emit(\n"
        "                        block,\n"
        "                        ISelInst::new(AArch64Opcode::MovR, vec![ISelOperand::PReg(*ptr_reg), src])\n"
        "                            .as_call_arg_setup(),\n"
        "                    );\n"
        "                }\n"
        "                ArgLocation::RegPair(lo_preg, hi_preg) => {\n"
        "                    // i128 register pair argument for indirect call",
        "vec![src, ISelOperand::PReg(SP), ISelOperand::Imm(*offset + 8)],\n"
        "                        ),\n"
        "                    );\n"
        "                }\n"
        "                ArgLocation::Indirect { ptr_reg } => {\n"
        "                    self.emit(\n"
        "                        block,\n"
        "                        ISelInst::new(AArch64Opcode::MovR, vec![ISelOperand::PReg(*ptr_reg), src])\n"
        "                            .as_call_arg_setup(),\n"
        "                    );\n"
        "                }\n"
        "                ArgLocation::RegPair(lo_preg, hi_preg) => {\n"
        "                    // i128 register pair argument for indirect call",
        [("indirect_call", INDIRECT, "fail")],
    ),
    (
        "v1-copy-exemption-restored",
        "crates/trust-cg-verify/src/function_verifier.rs",
        "            A::Blr\n                    | A::BLR\n                    | A::Br\n                    | A::Ret",
        "            A::Blr\n                    | A::BLR\n                    | A::Br\n                    | A::MOVXrr\n"
        "                    | A::Ret",
        [
            ("verify_lib_copy_binding", cargo("-p", "trust-cg-verify", "--lib", "--",
                                              "register_copies_bind"), "fail"),
            ("coverage_gate_binding_row", cargo("-p", "trust-cg-verify", "--test", "coverage_gate_tests",
                                                "--", "aarch64_decoded_value_rows_are_credited_by_every_form"),
             "fail"),
        ],
    ),
    (
        "v2-typed-copy-width-from-operand-view",
        "crates/trust-cg-verify/src/aarch64_value_decode_proofs.rs",
        "let width = if inst.opcode == O::MOVWrr { 32 } else { 64 };",
        "let width = if let Operand::Gpr { width, .. } = dst { width } else { 64 };",
        [
            ("verify_lib_value_credit", cargo("-p", "trust-cg-verify", "--lib", "--", "register_copies_bind",
                                              "every_decoded_value_opcode"), "fail"),
            ("coverage_gate_ratio", cargo("-p", "trust-cg-verify", "--test", "coverage_gate_tests", "--",
                                          "aarch64_emittable_coverage_is_honest_under_strict"), "fail"),
        ],
    ),
    (
        "v3-copies-unbound-and-unexempted",
        "crates/trust-cg-verify/src/aarch64_value_decode_proofs.rs",
        "    AArch64Opcode::MovR,\n    AArch64Opcode::MOVWrr,\n    AArch64Opcode::MOVXrr,\n"
        "    AArch64Opcode::FmovFprFpr,\n    AArch64Opcode::FmovFprGpr,\n    AArch64Opcode::FmovGprFpr,\n"
        "    AArch64Opcode::Smull,",
        "    AArch64Opcode::Smull,",
        [("codegen_lib", cargo("-p", "trust-cg-codegen", "--lib"), "measure")]
        + [(f"floor-{target}", cargo("-p", package, "--test", target, "--", "--test-threads=1"), "measure")
           for package, target in PROOF_GRADE_FLOOR],
    ),
]


def object_hashes(directory: Path) -> dict:
    return {path.relative_to(directory).as_posix(): sha256(path.read_bytes())
            for path in sorted(directory.rglob("*.o"))}


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    RECORDS.mkdir(parents=True, exist_ok=True)
    before = source_record()
    if before["status_porcelain"]:
        print("source is dirty; refusing", file=sys.stderr)
        return 2
    (RECORDS / "host.json").write_text(json.dumps({
        "uname": platform.uname()._asdict(),
        "cpu": subprocess.run(["lscpu"], capture_output=True, text=True).stdout.splitlines()[:20],
        "glibc": subprocess.run(["ldd", "--version"], capture_output=True, text=True).stdout.splitlines()[:1],
    }, indent=2) + "\n")
    (RECORDS / "tools.json").write_text(json.dumps([
        tool("cc", ["--version"]), tool("gcc", ["--version"]), tool("ld", ["--version"]),
        tool("objdump", ["--version"]), tool("readelf", ["--version"]), tool("cargo", ["--version"]),
        tool("rustc", ["--version"]), tool("python3", ["--version"]), tool("ay", ["--version"]),
        tool("clean", ["--version"]),
    ], indent=2) + "\n")

    retain_env = dict(ENV, L04P11_RETAIN_DIR=str(RETAINED / "clean"))
    run("switch", SWITCH, env=retain_env)
    run("indirect_call", INDIRECT, env=retain_env)
    objdump = shutil.which("objdump", path=ENV["PATH"])
    readelf = shutil.which("readelf", path=ENV["PATH"])
    for label, rel in (("switch-matrix-O2", "switch_matrix/matrix_O2.o"),
                       ("indirect-call-O2", "indirect_call/fnptr_O2.o")):
        path = RETAINED / "clean" / rel
        run(f"objdump-d-{label}", [objdump, "-d", "--no-show-raw-insn", str(path)], gz=True)
        run(f"readelf-sW-{label}", [readelf, "-sW", str(path)])
    run("codegen_lib", cargo("-p", "trust-cg-codegen", "--lib"), gz=True)
    run("verify_gate_targets", cargo("-p", "trust-cg-verify", "--no-fail-fast", "--test", "coverage_gate_tests",
                                     "--test", "aarch64_value_decode_gate", "--test", "proof_gate_strict",
                                     "--test", "soundness_manifest", "--test", "meta_theorems"), gz=True)
    run("verify_lib_value_and_binding", cargo("-p", "trust-cg-verify", "--lib", "--", "aarch64_value_decode",
                                              "function_verifier::tests", "coverage_gate"), gz=True)
    run("cli", cargo("-p", "trust-cg-cli", "--no-fail-fast", "--bins", "--test", "emit_proofs_flag"), gz=True)
    run("floor_gate_script_tests", [sys.executable, "-m", "unittest", "scripts.tests.test_linux_aarch64_gate",
                                    "scripts.tests.test_darwin_aarch64_gate",
                                    "scripts.tests.test_linux_aarch64_bridge_gate",
                                    "scripts.tests.test_darwin_aarch64_bridge_gate",
                                    "scripts.tests.test_native_test_host_matrix"], gz=True)
    run("all_script_tests", [sys.executable, "-m", "unittest", "discover", "-s", "scripts/tests", "-p",
                             "test_*.py"], gz=True, expect="fail")
    run("native_test_host_matrix_check", [sys.executable, "scripts/native_test_host_matrix.py", "--check"])
    run("check_fmt", ["scripts/check_fmt.sh"])

    mutation_results = []
    for name, rel, old, new, commands in MUTATIONS:
        path = ROOT / rel
        original = path.read_text()
        if original.count(old) != 1:
            raise SystemExit(f"{name}: anchor matches {original.count(old)} times in {rel}")
        path.write_text(original.replace(old, new))
        rows = []
        try:
            for label, argv, expect in commands:
                env = ENV
                if expect == "identical-objects":
                    env = dict(ENV, L04P11_RETAIN_DIR=str(RETAINED / name))
                rc, _ = run(f"{name}--{label}", argv, env=env, gz=True,
                            expect="pass" if expect in ("identical-objects", "measure") else expect)
                row = {"label": label, "returncode": rc, "expected": expect}
                if expect == "identical-objects":
                    clean = object_hashes(RETAINED / "clean" / "indirect_call")
                    mutant = object_hashes(RETAINED / name / "indirect_call")
                    row["objects"] = sorted(mutant)
                    row["identical_to_clean"] = clean == mutant
                    row["caught"] = rc != 0
                elif expect == "fail":
                    row["caught"] = rc != 0
                rows.append(row)
        finally:
            path.write_text(original)
        if git("status", "--porcelain", "--untracked-files=all"):
            raise SystemExit(f"{name}: source not restored")
        mutation_results.append({"name": name, "file": rel, "old": old, "new": new, "runs": rows})
    (RECORDS / "mutations.json").write_text(json.dumps(mutation_results, indent=2) + "\n")

    if not SKIP_VERIFY_LIB:
        run("verify_lib_full", cargo("-p", "trust-cg-verify", "--lib"), gz=True, expect="fail")
    after = source_record()
    (RECORDS / "source.json").write_text(json.dumps({"before": before, "after": after}, indent=2) + "\n")
    shutil.rmtree(RETAINED / "m4-blr-clobber-set-dropped", ignore_errors=True)
    return 0 if before == after else 3


if __name__ == "__main__":
    sys.exit(main())
