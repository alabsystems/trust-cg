from __future__ import annotations

import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import textwrap
import unittest


ROOT = Path(__file__).resolve().parents[2]
RELEASE_CHECKS = ROOT / "scripts" / "run_public_release_checks.sh"
CODEGEN_RUNNER = ROOT / "scripts" / "run_public_release_codegen_tests.sh"
HARNESS = ROOT / "benchmarks" / "beat-llvm" / "run.py"

# The release gate must parse the authoritative differential harness with the
# interpreter's own parser (not a regex, not a grep) and must name the harness
# file explicitly: a syntax regression in run.py is otherwise invisible to a
# release smoke, which never runs the harness's timing lanes. The command may
# be wrapped in the gate's recorded `lane <name>` helper.
GATE_RE = re.compile(
    r"^\s*(?:lane [a-z0-9-]+ )?python3 -c '(?P<program>import ast, pathlib, sys; ast\.parse\([^']*\))' \\\n"
    r"\s+benchmarks/beat-llvm/run\.py\n",
    re.MULTILINE,
)

DARWIN = "aarch64-apple-darwin"
LINUX = "aarch64-unknown-linux-gnu"
X86_DARWIN = "x86_64-apple-darwin"
X86_LINUX = "x86_64-unknown-linux-gnu"
# The exact Trust compilers each AArch64 host's gate accepts: the one list both
# gate scripts read, which crates/trust-cg-codegen/fixture_toolchain.rs must
# certify (ReleaseTrustCompilerListTests holds the two equal).
RELEASE_TRUST_COMPILERS = ROOT / "scripts" / "release_trust_compilers.txt"
FIXTURE_TOOLCHAIN = ROOT / "crates" / "trust-cg-codegen" / "fixture_toolchain.rs"


def certified_trust_compilers() -> dict[str, list[str]]:
    """host -> the `trustc --version` lines release_trust_compilers.txt lists."""
    certified: dict[str, list[str]] = {}
    for raw in RELEASE_TRUST_COMPILERS.read_text().splitlines():
        if not raw or raw.startswith("#"):
            continue
        host, line = raw.split("\t")
        certified.setdefault(host, []).append(line)
    return certified


CERTIFIED_TRUSTC = certified_trust_compilers()
# The compiler each host's fake package reports unless a test overrides it.
EXPECTED_TRUSTC = {host: lines[0] for host, lines in CERTIFIED_TRUSTC.items()}
UNCERTIFIED_TRUSTC = "rustc 1.99.0-dev (012345678 2026-01-01) (trustc 0.1.0)"


def targo_line(trustc_line: str) -> str:
    """The targo `--version` line of the build whose trustc says `trustc_line`."""
    return trustc_line.replace("rustc ", "targo ", 1).replace("(trustc ", "(targo ", 1)


EXPECTED_TARGO = {host: targo_line(line) for host, line in EXPECTED_TRUSTC.items()}
SOLVER_SKIP_TESTS = {
    "test_cegis_cache_hit_on_repeat",
    "test_cegis_codegen_layer_a_mul_zero_i32_matches_hand_movz",
    "test_cegis_codegen_layer_b_movz_add_max_imm12_matches_hand_addri",
    "test_cegis_codegen_layer_b_movz_add_small_imm_matches_hand_addri",
    "test_cegis_flag_is_noop_when_disabled",
    "test_cegis_flag_runs_pass",
    "test_full_pipeline_with_cegis_flag",
    "ay_pbo_aarch64_execution_differential",
    "natural_keep_better_does_not_keep_worse_whole_vreg_ay",
    "teeth_ay_path_detects_a_corrupted_instruction",
}
# Every file the two gates read before their first lane runs.
SANDBOX_FILES = (
    "scripts/run_public_release_checks.sh",
    "scripts/run_public_release_codegen_tests.sh",
    "scripts/release_gate_summary.py",
    "scripts/rust_guard_transcript.py",
    "scripts/run_with_timeout.py",
    "scripts/trust_toolchain.py",
    "scripts/trust_cargo.sh",
    "scripts/release_trust_compilers.txt",
    "crates/rustc-codegen-trust-cg/rust-toolchain.toml",
)
CONTROLLED_ENVIRONMENT = (
    "AY_SOLVER_PATH", "TCG_SOLVER_PATH", "TCG_EXTERNAL_CLEAN_CHECKER", "TCG_CLEAN_CHECKER",
    "TRUST_CG_PROOF_GATE", "TRUST_SYSROOT", "TRUST_ROOT", "RUST_TEST_THREADS",
    "TRUST_TARGO",
)


def _gate_program() -> str:
    match = GATE_RE.search(RELEASE_CHECKS.read_text())
    if match is None:
        raise AssertionError(
            f"{RELEASE_CHECKS.relative_to(ROOT)} has no ast.parse gate over "
            f"{HARNESS.relative_to(ROOT)}"
        )
    return match.group("program")


def _run_gate(target: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, "-c", _gate_program(), str(target)],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )


class ReleaseHarnessSyntaxGateTests(unittest.TestCase):
    def test_release_checks_parse_the_differential_harness(self) -> None:
        _gate_program()

    def test_gate_accepts_the_committed_harness(self) -> None:
        result = _run_gate(HARNESS)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_release_checks_parse_the_harness_helper_modules(self) -> None:
        # run.py imports these; each must be parsed by an ast.parse gate too.
        text = RELEASE_CHECKS.read_text()
        helpers = re.search(
            r"^\s*(?:lane [a-z0-9-]+ )?python3 -c '(?P<program>import ast, pathlib, sys; \[ast\.parse\([^']*\) for p in "
            r"sys\.argv\[1:\]\])' \\\n\s+(?P<files>[^\n]+)\n",
            text, re.MULTILINE)
        self.assertIsNotNone(helpers, "no ast.parse gate over the beat-llvm helper modules")
        files = helpers.group("files").split()
        for module in ("peak_rss.py", "hostinfo.py"):
            self.assertIn(f"benchmarks/beat-llvm/{module}", files)
        harness_source = HARNESS.read_text()
        for module in ("hostinfo", "peak_rss"):
            self.assertRegex(harness_source, rf"(?m)^import {module}\b")
        result = subprocess.run(
            [sys.executable, "-c", helpers.group("program"), *files],
            cwd=ROOT, capture_output=True, text=True, check=False)
        self.assertEqual(result.returncode, 0, result.stderr)
        with tempfile.TemporaryDirectory() as tmp:
            broken = Path(tmp) / "hostinfo.py"
            broken.write_text((ROOT / files[-1]).read_text() + "\ndef broken(:\n")
            result = subprocess.run(
                [sys.executable, "-c", helpers.group("program"), files[0], str(broken)],
                cwd=ROOT, capture_output=True, text=True, check=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("SyntaxError", result.stderr)

    def test_gate_rejects_a_syntax_regression(self) -> None:
        # A same-quote nested f-string is exactly the shape that once broke the
        # harness on pre-PEP 701 interpreters; an unterminated string is a
        # regression every interpreter rejects, so the gate must fail on it.
        with tempfile.TemporaryDirectory() as tmp:
            broken = Path(tmp) / "run.py"
            broken.write_text(HARNESS.read_text() + '\nrow["reason"] = f"unterminated\n')
            result = _run_gate(broken)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("SyntaxError", result.stderr)


class GateSandbox:
    """A copy of the gate scripts with a fake installed Trust package.

    `trustc`/`targo` live in `tools/bin`, so `tools` is the package root (its
    sysroot) and, being a PATH entry named `bin`, an aterm package prefix; the
    fake targo may only report its version.
    """

    def __init__(self, root: Path, *, darwin_floor: bool = False) -> None:
        self.root = root
        self.repo = root / "repo"
        for relative in SANDBOX_FILES:
            destination = self.repo / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / relative, destination)
        if darwin_floor:
            self.write_executable(self.repo / "scripts/check_darwin_aarch64.py", "exit 97")
        # A PATH entry named `bin` makes its parent an aterm package prefix.
        self.bin = root / "tools" / "bin"
        self.bin.mkdir(parents=True)
        self.sysroot = root / "tools"
        for host in (DARWIN, LINUX, X86_DARWIN, X86_LINUX):
            private = self.sysroot / "lib" / "rustlib" / host / "lib"
            private.mkdir(parents=True)
            for crate in ("rustc_middle", "rustc_codegen_ssa"):
                (private / f"lib{crate}-fixture.rmeta").touch()
        self.cargo_log = root / "cargo.log"
        self.cargo_invocations = root / "cargo-invocations.log"
        # FAKE_TRUSTC_VERSION, when set, is the build the package reports.
        identity = (
            'case "$FAKE_HOST" in\n'
            f'    {LINUX}) line="{EXPECTED_TRUSTC[LINUX]}" ;;\n'
            f'    *) line="{EXPECTED_TRUSTC[DARWIN]}" ;;\n'
            "esac\n"
            'if [ -n "${FAKE_TRUSTC_VERSION:-}" ]; then line="$FAKE_TRUSTC_VERSION"; fi\n'
        )
        self.write_executable(self.bin / "trustc", identity + (
            'if [ "$1" = "-vV" ]; then\n'
            '    printf "%s\\nbinary: trustc\\ncommit-hash: %s\\nhost: %s\\n" "$line" '
            f'"{"3" * 40}" "$FAKE_HOST"\n'
            "    exit 0\n"
            "fi\n"
            'if [ "$1 $2" = "--print sysroot" ]; then\n'
            f'    echo "{self.sysroot}"\n'
            "    exit 0\n"
            "fi\n"
            'echo "$line"'
        ))
        # Identity probes (`--version`) are how the gate names its package;
        # any other targo invocation is a Cargo run and is logged.
        self.write_executable(self.bin / "targo", identity + (
            'if [ "$1" = "--version" ] || [ "$1 $2" = "--unverified --version" ]; then\n'
            '    echo "$line" | sed -e "s/^rustc /targo /" -e "s/(trustc /(targo /"\n'
            "    exit 0\n"
            "fi\n"
            f'echo "$*" >> "{self.cargo_invocations}"\n'
            f'echo "$*" >> "{self.cargo_log}"\n'
            "exit 99"
        ))
        # A PATH directory outside the Trust package, for tools that must not
        # be mistaken for the package's own.
        self.path_bin = root / "path-bin"
        self.path_bin.mkdir()
        (self.bin / "python3").symlink_to(sys.executable)
        self.home = root / "home"
        self.home.mkdir()
        self.evidence = root / "evidence"

    @staticmethod
    def write_executable(path: Path, body: str) -> Path:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f"#!/bin/sh\n{body}\n")
        path.chmod(0o755)
        return path

    def tool(self, name: str) -> Path:
        """An explicit-override proof tool outside every discovery root."""
        return self.write_executable(self.root / "explicit" / name, f'echo "fake {name} 1.0"')

    def toolchain_ay(self) -> Path:
        """Make the Trust package's sysroot ship bin/ay."""
        return self.write_executable(self.sysroot / "bin" / "ay", 'echo "toolchain ay"')

    def packaged_tool(self, name: str) -> Path:
        return self.write_executable(
            self.root / "tools" / "store" / name / "current" / "bin" / name, f'echo "packaged {name} 1.0"'
        )

    def environment(self, host: str, overrides: dict) -> dict:
        environment = {
            key: value for key, value in os.environ.items()
            if key not in CONTROLLED_ENVIRONMENT and not key.startswith(("TCG_", "TRUST_CG_"))
        }
        environment.update(
            PATH=os.pathsep.join((str(self.bin), str(self.path_bin), "/usr/bin", "/bin")),
            HOME=str(self.home), TMPDIR=str(self.root), FAKE_HOST=host,
        )
        environment.update(overrides)
        return environment

    def run(self, command: list, host: str, overrides: dict, cwd: Path | None = None) -> subprocess.CompletedProcess:
        return subprocess.run(
            command, cwd=cwd or self.root, env=self.environment(host, overrides),
            capture_output=True, text=True, timeout=300, check=False,
        )

    def gate(self, *args: str, host: str = DARWIN, shell: str = "", dry_run: bool = True,
             **overrides: str) -> subprocess.CompletedProcess:
        script = str(self.repo / "scripts/run_public_release_checks.sh")
        command = [shell, script] if shell else [script]
        plan_flag = ["--dry-run"] if dry_run else []
        return self.run([*command, *plan_flag, "--evidence-dir", str(self.evidence), *args], host, overrides)

    def codegen(self, *args: str, host: str = DARWIN, **overrides: str) -> subprocess.CompletedProcess:
        return self.run([str(self.repo / "scripts/run_public_release_codegen_tests.sh"), *args], host, overrides)

    def summary(self, path: Path | None = None) -> dict:
        return json.loads((path or self.evidence / "summary.json").read_text())

    def assert_cargo_never_ran(self, case: unittest.TestCase) -> None:
        case.assertFalse(self.cargo_log.exists(), self.cargo_log.read_text() if self.cargo_log.exists() else "")

    def assert_no_cargo_invocations(self, case: unittest.TestCase) -> None:
        case.assertFalse(self.cargo_invocations.exists())


def lanes(document: dict) -> dict:
    return {lane["name"]: lane for lane in document["lanes"]}


def exclusions(document: dict) -> dict:
    return {(row["lane"], row["kind"]): row for row in document["exclusions"]}


class PublicReleaseGateModeTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()

    def sandbox(self, **options: bool) -> GateSandbox:
        return GateSandbox(self.root, **options)

    def test_auto_without_solver_records_every_exclusion_as_non_qualifying(self) -> None:
        box = self.sandbox()
        result = box.gate()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("DRY RUN", result.stdout)
        self.assertIn("NON-QUALIFYING", result.stderr)
        document = box.summary()
        self.assertEqual((document["mode"], document["host"], document["status"]), ("auto", DARWIN, "dry-run"))
        self.assertFalse(document["qualifying"])
        applied = exclusions(document)
        self.assertEqual(applied[("workspace", "cargo-exclude")]["value"], "trust-cg-verify")
        self.assertEqual(set(applied[("codegen-complement", "cargo-skip")]["value"].split()), SOLVER_SKIP_TESTS)
        self.assertEqual(
            document["partitions"],
            [{"package": "trust-cg-codegen", "from_lane": "workspace", "covered_by": "codegen"}],
        )
        planned = lanes(document)
        self.assertIn("--exclude trust-cg-verify", planned["workspace"]["detail"])
        self.assertIn("--release", planned["codegen"]["detail"])
        self.assertEqual(planned["pgo-runtime"]["status"], "planned")
        self.assertEqual(planned["codegen-capstones"]["status"], "planned")
        self.assertIn("AY-backed tests skipped", planned["codegen-complement"]["detail"])
        self.assertEqual(planned["darwin-aarch64-floor"]["status"], "unavailable")
        # OD-08: the companion pins must agree with Cargo.lock on every AArch64 host.
        self.assertEqual(planned["companion-coherence"]["status"], "planned")
        self.assertIn("scripts/check_companion_coherence.py", planned["companion-coherence"]["detail"])
        # OD-04: the Darwin bridge runner is a required release lane.
        bridge_runner = planned["darwin-aarch64-bridge"]
        self.assertEqual(bridge_runner["status"], "planned")
        self.assertIn("scripts/check_darwin_aarch64_bridge.py", bridge_runner["detail"])
        self.assertIn(f"--target-dir {box.repo}/target/rustc-codegen-trust-cg-trust", bridge_runner["detail"])
        self.assertEqual(bridge_runner["output"], str(box.evidence / "darwin-aarch64-bridge"))
        self.assertNotIn("proof-gate", planned)
        self.assertNotIn("linux-aarch64-floor", planned)
        self.assertNotIn("aarch64-aot-arithmetic", planned)
        # The bridge crate pins the trust channel; its test lane must use that
        # driver and the availability probe's cache, not a stale nightly.
        bridge_tests = planned["bridge-tests"]["detail"]
        self.assertIn(f"CARGO_TARGET_DIR={box.repo}/target/rustc-codegen-trust-cg-trust", bridge_tests)
        self.assertIn("--unverified test --release --locked", bridge_tests)
        self.assertIn('pins exactly channel = "trust"', planned["bridge-toolchain-pin"]["detail"])
        self.assertIn("found 'trust'", planned["bridge-toolchain-pin"]["detail"])
        box.assert_cargo_never_ran(self)

    def test_require_without_solver_refuses_before_any_lane(self) -> None:
        box = self.sandbox(darwin_floor=True)
        result = box.gate(TRUST_CG_PROOF_GATE="require")
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("needs AY and Clean", result.stderr)
        document = box.summary()
        self.assertEqual((document["mode"], document["status"]), ("require", "fail"))
        self.assertEqual(document["lanes"], [])
        box.assert_cargo_never_ran(self)

    def test_require_never_takes_ay_from_path_or_the_package_store(self) -> None:
        # crates/trust-cg-verify/src/ay_identity.rs consults neither.
        box = self.sandbox(darwin_floor=True)
        GateSandbox.write_executable(box.path_bin / "ay", 'echo "ay on PATH"')
        box.packaged_tool("ay")
        box.packaged_tool("clean")
        result = box.gate(TRUST_CG_PROOF_GATE="require")
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("AY: unresolved", result.stderr)
        box.assert_cargo_never_ran(self)

    def test_require_refuses_a_generic_clean_on_path(self) -> None:
        box = self.sandbox(darwin_floor=True)
        GateSandbox.write_executable(box.path_bin / "clean", 'echo "an unrelated clean command"')
        result = box.gate(TRUST_CG_PROOF_GATE="require", AY_SOLVER_PATH=str(box.tool("ay")))
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("Clean: unresolved", result.stderr)

    def test_require_refuses_darwin_without_a_native_floor_runner(self) -> None:
        box = self.sandbox()
        result = box.gate(
            TRUST_CG_PROOF_GATE="require",
            AY_SOLVER_PATH=str(box.tool("ay")), TCG_EXTERNAL_CLEAN_CHECKER=str(box.tool("clean")),
        )
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("refuses every exclusion", result.stderr)
        self.assertIn("darwin-aarch64-floor: unavailable", result.stderr)
        document = box.summary()
        self.assertEqual(document["status"], "fail")
        for tool in ("ay", "clean"):
            record = document["solver"][tool]
            self.assertEqual(record["pinning"], "pinned")
            self.assertEqual(len(record["sha256"]), 64)
        box.assert_cargo_never_ran(self)

    def test_require_with_pinned_toolchain_ay_and_packaged_clean_plans_a_zero_exclusion_run(self) -> None:
        box = self.sandbox(darwin_floor=True)
        toolchain_ay = box.toolchain_ay()
        box.packaged_tool("clean")
        result = box.gate(TRUST_CG_PROOF_GATE="require")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertNotIn("NON-QUALIFYING:", result.stderr)
        document = box.summary()
        self.assertEqual(document["exclusions"], [])
        self.assertEqual(document["solver"]["ay"]["route"], "toolchain-sysroot")
        self.assertEqual(document["solver"]["ay"]["path"], str(toolchain_ay.resolve()))
        self.assertEqual(document["solver"]["clean"]["route"], "aterm-packaged")
        planned = lanes(document)
        self.assertEqual({lane["status"] for lane in planned.values()}, {"planned"})
        self.assertIn("proof-gate", planned)
        self.assertNotIn("--exclude trust-cg-verify", planned["workspace"]["detail"])
        self.assertIn("AY-backed tests included, not skipped", planned["codegen-complement"]["detail"])
        self.assertEqual(planned["darwin-aarch64-floor"]["output"], str(box.evidence / "darwin-aarch64-floor"))
        # OD-09: the floor judges the pinned companions and never fetches.
        self.assertIn("--require-offline-deps", planned["darwin-aarch64-floor"]["detail"])
        self.assertEqual(planned["darwin-aarch64-bridge"]["status"], "planned")
        # A dry run is never qualifying: nothing executed.
        self.assertFalse(document["qualifying"])
        self.assertTrue(any("planned but not executed" in reason for reason in document["non_qualifying_reasons"]))
        self.assertFalse(any(reason.startswith("mode=") for reason in document["non_qualifying_reasons"]))
        box.assert_cargo_never_ran(self)

    def test_linux_host_dispatches_the_native_floor_and_bridge_runners(self) -> None:
        box = self.sandbox()
        result = box.gate(host=LINUX)
        self.assertEqual(result.returncode, 0, result.stderr)
        document = box.summary()
        planned = lanes(document)
        floor = planned["linux-aarch64-floor"]
        self.assertIn("scripts/check_linux_aarch64.py --require-offline-deps --out", floor["detail"])
        self.assertEqual(floor["output"], str(box.evidence / "linux-aarch64-floor"))
        bridge = planned["linux-aarch64-bridge"]
        self.assertIn("scripts/check_linux_aarch64_bridge.py", bridge["detail"])
        self.assertIn(f"--target-dir {box.repo}/target/rustc-codegen-trust-cg-trust", bridge["detail"])
        self.assertEqual(bridge["output"], str(box.evidence / "linux-aarch64-bridge"))
        self.assertNotIn("darwin-aarch64-floor", planned)
        self.assertNotIn("darwin-aarch64-bridge", planned)
        applied = exclusions(document)
        self.assertIn(("pgo-runtime", "host"), applied)
        self.assertIn(("codegen-capstones", "host"), applied)
        self.assertEqual(planned["pgo-runtime"]["status"], "excluded")
        self.assertEqual(planned["codegen-capstones"]["status"], "excluded")
        # OD-12: without AY and Clean the required AOT matrix is an exclusion,
        # never a silently absent lane.
        self.assertEqual(planned["aarch64-aot-arithmetic"]["status"], "excluded")
        self.assertIn(("aarch64-aot-arithmetic", "solver"), applied)
        box.assert_cargo_never_ran(self)

    def test_linux_with_pinned_tools_builds_the_cli_the_aot_matrix_judges(self) -> None:
        box = self.sandbox()
        result = box.gate(
            host=LINUX, AY_SOLVER_PATH=str(box.tool("ay")),
            TCG_EXTERNAL_CLEAN_CHECKER=str(box.tool("clean")),
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        document = box.summary()
        matrix = lanes(document)["aarch64-aot-arithmetic"]
        self.assertEqual(matrix["status"], "planned")
        self.assertEqual(matrix["output"], str(box.evidence / "aarch64-aot-arithmetic"))
        # OD-13: the lane builds the CLI from the checked-out tree, then judges it.
        self.assertIn("build --release --locked -p trust-cg-cli --bin trust-cg", matrix["detail"])
        self.assertIn("scripts/check_aarch64_aot_arithmetic.py --trust-cg target/release/trust-cg "
                      "--require-clean", matrix["detail"])
        self.assertNotIn(("aarch64-aot-arithmetic", "solver"), exclusions(document))
        box.assert_cargo_never_ran(self)

    def test_every_listed_compiler_passes_the_identity_check_on_its_host(self) -> None:
        # A compiler fixture_toolchain.rs certifies must not be refused here:
        # 94d9dc8f0 qualified 450403669 on aarch64-apple-darwin while this gate
        # still named 321aaeda7 alone, so it refused a certified host.
        for host, lines in CERTIFIED_TRUSTC.items():
            for line in lines:
                with self.subTest(host=host, compiler=line), tempfile.TemporaryDirectory() as tmp:
                    box = GateSandbox(Path(tmp).resolve())
                    result = box.gate(host=host, FAKE_TRUSTC_VERSION=line)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertEqual(box.summary()["host"], host)
                    box.assert_cargo_never_ran(self)

    def test_a_compiler_the_list_does_not_certify_for_the_host_is_refused(self) -> None:
        darwin_only = next(line for line in CERTIFIED_TRUSTC[DARWIN] if line not in CERTIFIED_TRUSTC[LINUX])
        for host, line in ((DARWIN, UNCERTIFIED_TRUSTC), (LINUX, UNCERTIFIED_TRUSTC), (LINUX, darwin_only)):
            with self.subTest(host=host, compiler=line), tempfile.TemporaryDirectory() as tmp:
                box = GateSandbox(Path(tmp).resolve())
                result = box.gate(host=host, FAKE_TRUSTC_VERSION=line)
                self.assertEqual(result.returncode, 1, result.stdout)
                self.assertIn(f"expected one of the {host} compilers", result.stderr)
                self.assertIn(f"got {line}", result.stderr)
                box.assert_cargo_never_ran(self)

    def test_a_missing_compiler_list_refuses_before_any_lane(self) -> None:
        box = self.sandbox()
        (box.repo / "scripts" / "release_trust_compilers.txt").unlink()
        result = box.gate()
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn(f"certifies no Trust compiler for {DARWIN}", result.stderr)
        box.assert_cargo_never_ran(self)

    def test_linux_require_refuses_its_host_exclusions(self) -> None:
        box = self.sandbox()
        result = box.gate(
            host=LINUX, TRUST_CG_PROOF_GATE="require",
            AY_SOLVER_PATH=str(box.tool("ay")), TCG_EXTERNAL_CLEAN_CHECKER=str(box.tool("clean")),
        )
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("pgo-runtime", result.stderr)
        self.assertIn("codegen-capstones", result.stderr)
        box.assert_cargo_never_ran(self)

    def test_x86_hosts_retain_accounting_only_plans_without_invoking_cargo(self) -> None:
        for host, prefix in ((X86_DARWIN, "darwin-x86_64"), (X86_LINUX, "linux-x86_64")):
            with self.subTest(host=host):
                box = GateSandbox(self.root / host)
                result = box.gate(host=host)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("DRY RUN (NON-QUALIFYING", result.stdout)
                document = box.summary()
                self.assertEqual((document["host"], document["status"], document["qualifying"]),
                                 (host, "dry-run", False))
                planned = lanes(document)
                self.assertEqual(set(planned), {
                    f"{prefix}-floor", f"{prefix}-bridge", "pgo-runtime", "codegen-capstones",
                })
                self.assertEqual(planned[f"{prefix}-floor"]["status"], "unavailable")
                self.assertEqual(planned[f"{prefix}-bridge"]["status"], "unavailable")
                self.assertEqual(planned["pgo-runtime"]["status"], "excluded")
                self.assertEqual(planned["codegen-capstones"]["status"], "excluded")
                self.assertIn("no Cargo lanes were executed", planned[f"{prefix}-floor"]["detail"])
                # Linux x86-64's diagnostic runners exist and are named, never run.
                runners = ("scripts/check_linux_x86_64.py", "scripts/check_linux_x86_64_bridge.py")
                for lane_name, runner in zip(("floor", "bridge"), runners):
                    detail = planned[f"{prefix}-{lane_name}"]["detail"]
                    if host == X86_LINUX:
                        self.assertIn(runner, detail)
                        self.assertIn("not release qualification", detail)
                    else:
                        self.assertNotIn(runner, detail)
                self.assertEqual(document["partitions"], [])
                self.assertEqual(set(exclusions(document)), {("pgo-runtime", "host"),
                                                             ("codegen-capstones", "host")})
                self.assertTrue(any("accounting-only" in reason for reason in
                                    document["non_qualifying_reasons"]))
                self.assertFalse(any("unsupported host profile" in reason for reason in
                                     document["non_qualifying_reasons"]))
                box.assert_no_cargo_invocations(self)

    def test_x86_non_dry_run_refuses_without_invoking_cargo(self) -> None:
        for host in (X86_DARWIN, X86_LINUX):
            with self.subTest(host=host):
                box = GateSandbox(self.root / host)
                result = box.gate(host=host, dry_run=False)
                self.assertEqual(result.returncode, 1, result.stderr)
                self.assertIn("x86 release lanes are unavailable", result.stderr)
                document = box.summary()
                self.assertEqual((document["status"], document["qualifying"]), ("fail", False))
                self.assertFalse(any(lane["status"] in ("planned", "running", "pass") for lane in
                                     document["lanes"]))
                box.assert_no_cargo_invocations(self)

    def test_x86_require_cannot_qualify_even_with_pinned_tools(self) -> None:
        box = self.sandbox()
        result = box.gate(
            host=X86_DARWIN, TRUST_CG_PROOF_GATE="require",
            AY_SOLVER_PATH=str(box.tool("ay")), TCG_EXTERNAL_CLEAN_CHECKER=str(box.tool("clean")),
        )
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn("require refuses the x86 accounting-only profile", result.stderr)
        document = box.summary()
        self.assertEqual(document["mode"], "require")
        self.assertEqual(document["status"], "fail")
        self.assertIsNone(document["solver"])
        self.assertFalse(document["qualifying"])
        self.assertTrue(any("accounting-only" in reason for reason in document["non_qualifying_reasons"]))
        box.assert_no_cargo_invocations(self)

    def test_rejects_unknown_modes_hosts_and_arguments(self) -> None:
        box = self.sandbox()
        self.assertEqual(box.gate(TRUST_CG_PROOF_GATE="skip").returncode, 2)
        self.assertEqual(box.gate(host="riscv64-unknown-linux-gnu").returncode, 1)
        self.assertEqual(box.gate("--bogus").returncode, 2)
        self.assertFalse(box.evidence.exists())

    def test_evidence_must_lie_outside_the_source_tree(self) -> None:
        box = self.sandbox()
        inside = box.repo / "evidence"
        result = box.run(
            [str(box.repo / "scripts/run_public_release_checks.sh"), "--dry-run", "--evidence-dir", str(inside)],
            DARWIN, {},
        )
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertFalse(inside.exists())
        relative = box.run(
            [str(box.repo / "scripts/run_public_release_checks.sh"), "--dry-run", "--evidence-dir", "relative-evidence"],
            DARWIN, {}, cwd=self.root,
        )
        self.assertEqual(relative.returncode, 0, relative.stderr)
        self.assertTrue((self.root / "relative-evidence" / "summary.json").is_file())

    def test_retained_summary_is_never_overwritten(self) -> None:
        box = self.sandbox()
        box.evidence.mkdir()
        (box.evidence / "summary.json").write_text("prior evidence\n")
        result = box.gate()
        self.assertEqual(result.returncode, 1)
        self.assertEqual((box.evidence / "summary.json").read_text(), "prior evidence\n")

    def test_empty_ay_override_is_authoritative_not_a_fallthrough(self) -> None:
        box = self.sandbox()
        GateSandbox.write_executable(box.path_bin / "ay", 'echo "ay on PATH"')
        result = box.gate(AY_SOLVER_PATH="")
        self.assertEqual(result.returncode, 0, result.stderr)
        applied = exclusions(box.summary())
        self.assertIn("override is not an absolute path to an executable",
                      applied[("workspace", "cargo-exclude")]["reason"])
        self.assertIn(("codegen-complement", "cargo-skip"), applied)

    def test_legacy_solver_alias_selects_the_canonical_override(self) -> None:
        box = self.sandbox()
        result = box.gate(TCG_SOLVER_PATH=str(box.tool("ay")))
        self.assertEqual(result.returncode, 0, result.stderr)
        document = box.summary()
        self.assertEqual(document["solver"]["ay"]["route"], "env-override:AY_SOLVER_PATH")
        self.assertNotIn(("workspace", "cargo-exclude"), exclusions(document))
        self.assertNotIn(("codegen-complement", "cargo-skip"), exclusions(document))

    @unittest.skipUnless(Path("/bin/dash").is_file(), "dash is not installed")
    def test_dry_run_is_posix_under_dash(self) -> None:
        box = self.sandbox()
        result = box.gate(host=LINUX, shell="/bin/dash")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("linux-aarch64-floor", lanes(box.summary()))


LANE_HELPERS = (
    "# The lane list is evaluated twice"
    + RELEASE_CHECKS.read_text().split("# The lane list is evaluated twice", 1)[1].split("gate_lanes() {", 1)[0]
)


class PublicReleaseLaneExecutorTests(unittest.TestCase):
    """The run-phase executor retains each transcript without weakening set -e."""

    def run_lane(self, body: str, shell: str = "/bin/sh") -> tuple:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            calls = root / "summary.calls"
            script = "\n".join((
                "set -eu",
                f"EVIDENCE_DIR='{root}'",
                f"summary() {{ printf '%s\\n' \"$*\" >> '{calls}'; }}",
                LANE_HELPERS,
                "PHASE=run",
                body,
                "echo AFTER_LANES",
            ))
            result = subprocess.run([shell, "-c", script], capture_output=True, text=True, timeout=60, check=False)
            logs = {path.name: path.read_text() for path in (root / "lanes").glob("*")} if (root / "lanes").is_dir() else {}
            return result, calls.read_text() if calls.exists() else "", logs

    def shells(self) -> list:
        return [shell for shell in ("/bin/sh", "/bin/dash", "/bin/bash") if Path(shell).is_file()]

    def test_passing_lane_retains_its_transcript_and_records_pass(self) -> None:
        for shell in self.shells():
            with self.subTest(shell=shell):
                result, calls, logs = self.run_lane("lane demo sh -c 'echo out; echo err >&2'", shell)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("AFTER_LANES", result.stdout)
                self.assertEqual(logs, {"demo.log": "out\nerr\n"})
                self.assertIn("lane --name demo --status running --log", calls)
                self.assertIn("lane --name demo --status pass", calls)

    def test_failing_command_status_survives_the_tee(self) -> None:
        for shell in self.shells():
            with self.subTest(shell=shell):
                result, calls, logs = self.run_lane("lane demo sh -c 'echo partial; exit 7'", shell)
                self.assertEqual(result.returncode, 7)
                self.assertNotIn("AFTER_LANES", result.stdout)
                self.assertNotIn("--status pass", calls)
                self.assertEqual(logs["demo.log"], "partial\n")
                self.assertIn("lane demo failed (status 7", result.stderr)

    def test_function_lane_stops_at_its_first_failing_step(self) -> None:
        # A function whose last step succeeds must still fail when an earlier
        # step fails: the executor must not run lanes inside an AND-OR list.
        body = "\n".join((
            "two_steps() {",
            "    false",
            "    echo SECOND_STEP_RAN",
            "}",
            "lane demo two_steps",
        ))
        for shell in self.shells():
            with self.subTest(shell=shell):
                result, calls, logs = self.run_lane(body, shell)
                self.assertEqual(result.returncode, 1)
                self.assertNotIn("SECOND_STEP_RAN", result.stdout + logs.get("demo.log", ""))
                self.assertNotIn("--status pass", calls)


BRIDGE_PIN_HELPERS = (
    "EXPECTED_BRIDGE_CHANNEL="
    + RELEASE_CHECKS.read_text().split("EXPECTED_BRIDGE_CHANNEL=", 1)[1].split("bridge_release_tests() {", 1)[0]
)


class PublicReleaseBridgePinTests(unittest.TestCase):
    """The bridge pin is an exact release contract, not a shape check."""

    def check_pin(self, toolchain: str) -> subprocess.CompletedProcess:
        with tempfile.TemporaryDirectory() as temporary:
            pin = Path(temporary) / "rust-toolchain.toml"
            pin.write_text(toolchain)
            script = "\n".join((
                "set -eu",
                f"BRIDGE_TOOLCHAIN_FILE='{pin}'",
                f"REPO_ROOT='{temporary}'",
                BRIDGE_PIN_HELPERS,
                "bridge_toolchain_pin",
                "echo PIN_ACCEPTED",
            ))
            return subprocess.run(["/bin/sh", "-c", script], capture_output=True, text=True, timeout=60, check=False)

    def test_the_committed_bridge_pin_is_accepted(self) -> None:
        committed = (ROOT / "crates/rustc-codegen-trust-cg/rust-toolchain.toml").read_text()
        result = self.check_pin(committed)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("PIN_ACCEPTED", result.stdout)

    def test_any_other_channel_is_refused(self) -> None:
        for toolchain in (
            '[toolchain]\nchannel = "nightly-2026-04-20"\n',
            '[toolchain]\nchannel = "stable"\n',
            '[toolchain]\nchannel = "trust"\nchannel = "trust"\n',
            '[toolchain]\n',
        ):
            with self.subTest(toolchain=toolchain):
                result = self.check_pin(toolchain)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertNotIn("PIN_ACCEPTED", result.stdout)


class PublicReleaseCodegenRunnerModeTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.box = GateSandbox(Path(self.temporary.name).resolve())

    def own_summary(self, result: subprocess.CompletedProcess) -> dict:
        match = re.search(r"plan recorded in (\S+)$", result.stdout, re.MULTILINE)
        self.assertIsNotNone(match, result.stdout)
        return self.box.summary(Path(match.group(1)))

    def test_standalone_plan_without_solver_records_each_skip(self) -> None:
        result = self.box.codegen("--plan")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("NON-QUALIFYING", result.stderr)
        document = self.own_summary(result)
        self.assertEqual(document["gate"], "run_public_release_codegen_tests")
        self.assertEqual(document["status"], "dry-run")
        skipped = exclusions(document)[("codegen-complement", "cargo-skip")]["value"].split()
        self.assertEqual(len(skipped), len(SOLVER_SKIP_TESTS))
        self.assertEqual(set(skipped), SOLVER_SKIP_TESTS)
        self.box.assert_cargo_never_ran(self)

    def test_require_mode_refuses_without_solver_from_flag_or_environment(self) -> None:
        self.assertEqual(self.box.codegen("--plan", "--proof-gate=require").returncode, 1)
        result = self.box.codegen("--plan", TRUST_CG_PROOF_GATE="require")
        self.assertEqual(result.returncode, 1)
        self.assertIn("needs AY and Clean", result.stderr)
        self.box.assert_cargo_never_ran(self)

    def test_require_mode_with_pinned_tools_plans_without_exclusions(self) -> None:
        result = self.box.codegen(
            "--plan", "--proof-gate=require",
            AY_SOLVER_PATH=str(self.box.tool("ay")), TCG_EXTERNAL_CLEAN_CHECKER=str(self.box.tool("clean")),
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        document = self.own_summary(result)
        self.assertEqual(document["exclusions"], [])
        self.assertEqual(document["solver"]["clean"]["route"], "env-override:TCG_EXTERNAL_CLEAN_CHECKER")

    def test_linux_plan_records_the_capstone_host_exclusion(self) -> None:
        result = self.box.codegen("--plan", host=LINUX)
        self.assertEqual(result.returncode, 0, result.stderr)
        document = self.own_summary(result)
        self.assertEqual(lanes(document)["codegen-capstones"]["status"], "excluded")
        self.assertIn(("codegen-capstones", "host"), exclusions(document))
        refused = self.box.codegen(
            "--plan", "--proof-gate=require", host=LINUX,
            AY_SOLVER_PATH=str(self.box.tool("ay")), TCG_EXTERNAL_CLEAN_CHECKER=str(self.box.tool("clean")),
        )
        self.assertEqual(refused.returncode, 1)
        self.assertIn("refuses every exclusion", refused.stderr)

    def test_darwin_complement_runs_the_source_bound_jit_rows_exactly(self) -> None:
        # L11-P8/L08-P9: on Darwin the 25 source-bound object/JIT tests
        # leave the complement's single process and run one cargo process
        # each; Linux keeps them in the complement.
        darwin = self.own_summary(self.box.codegen("--plan"))
        self.assertIn("the 25 source-bound object/JIT tests then run exactly",
                      lanes(darwin)["codegen-complement"]["detail"])
        linux = self.own_summary(self.box.codegen("--plan", host=LINUX))
        self.assertNotIn("source-bound", lanes(linux)["codegen-complement"]["detail"])
        runner = (ROOT / "scripts" / "run_public_release_codegen_tests.sh").read_text()
        rows = re.search(r"source_bound_rows\(\) \{\n    cat <<'EOF'\n(.*?)\nEOF", runner, re.DOTALL)
        self.assertIsNotNone(rows)
        targets = {}
        for row in rows.group(1).splitlines():
            target, total, selected, coverage, names = row.split("|")
            self.assertEqual((total, selected, coverage), (str(len(names.split())),) * 2 + ("full",))
            targets[target] = names.split()
        expected_counts = {
            "aarch64_framed_identity_control": 1,
            "aarch64_nonleaf_frame_control": 2,
            "jit_cert_cache_identity_aarch64": 9,
            "jit_fail_closed_proof_policy": 9,
            "jit_source_bound_arithmetic": 4,
        }
        self.assertEqual(sorted(targets), sorted(expected_counts))
        self.assertEqual({target: len(names) for target, names in targets.items()}, expected_counts)
        self.assertEqual(sum(map(len, targets.values())), 25)
        for target, names in targets.items():
            source = (ROOT / "crates" / "trust-cg-codegen" / "tests" / f"{target}.rs").read_text()
            for name in names:
                self.assertIn(f"fn {name.rsplit('::', 1)[-1]}(", source, f"{target}::{name}")
        self.box.assert_cargo_never_ran(self)

    def test_capstone_only_mode_is_refused_off_darwin(self) -> None:
        result = self.box.codegen(host=LINUX)
        self.assertEqual(result.returncode, 1)
        self.assertIn("capstone-only mode requires", result.stderr)
        self.box.assert_cargo_never_ran(self)

    def test_every_listed_compiler_passes_the_runner_identity_check(self) -> None:
        for host, lines in CERTIFIED_TRUSTC.items():
            for line in lines:
                with self.subTest(host=host, compiler=line):
                    result = self.box.codegen("--plan", host=host, FAKE_TRUSTC_VERSION=line)
                    self.assertEqual(result.returncode, 0, result.stderr)
        self.box.assert_cargo_never_ran(self)

    def test_runner_refuses_a_compiler_the_list_does_not_certify_for_the_host(self) -> None:
        darwin_only = next(line for line in CERTIFIED_TRUSTC[DARWIN] if line not in CERTIFIED_TRUSTC[LINUX])
        for host, line in ((DARWIN, UNCERTIFIED_TRUSTC), (LINUX, darwin_only)):
            with self.subTest(host=host, compiler=line):
                result = self.box.codegen("--plan", host=host, FAKE_TRUSTC_VERSION=line)
                self.assertEqual(result.returncode, 1, result.stdout)
                self.assertIn(f"expected one of the {host} compilers", result.stderr)
        self.box.assert_cargo_never_ran(self)

    def test_rejects_invalid_arguments(self) -> None:
        for arguments in (
            ("--plan", "--proof-gate=skip"),
            ("--release", "--complement"),
            ("--self-test", "--summary=anything.json"),
            ("--unknown",),
            ("--plan", "--summary="),
            ("--plan", "--summary=relative/summary.json"),
        ):
            with self.subTest(arguments=arguments):
                self.assertEqual(self.box.codegen(*arguments).returncode, 2)
        missing = self.box.codegen("--plan", f"--summary={self.box.root / 'missing.json'}")
        self.assertEqual(missing.returncode, 2)
        self.box.assert_cargo_never_ran(self)



class KernelLayoutFixtureQualificationModeTests(unittest.TestCase):
    """Exercise the real maintained runner with synthetic compiled inventories."""

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.box = GateSandbox(Path(self.temporary.name).resolve())
        source = CODEGEN_RUNNER.read_text()
        policy = re.search(r"policy_rows\(\) \{\n    cat <<'EOF'\n(.*?)\nEOF", source, re.DOTALL)
        self.assertIsNotNone(policy)
        self.cases = {}
        for row in policy.group(1).splitlines():
            target, total, _, _, names = row.split("|")
            selected = names.split()
            self.cases[target] = selected + [
                f"{target}_complement_{index}" for index in range(int(total) - len(selected))
            ]
            path = self.box.repo / "crates/trust-cg-codegen/tests" / f"{target}.rs"
            path.parent.mkdir(parents=True, exist_ok=True)
            path.touch()
        self.inventory = self.box.root / "compiled-cases.json"
        self.inventory.write_text(json.dumps(self.cases))
        self.calls = self.box.root / "layout-calls.jsonl"
        fake = self.box.bin / "targo"
        fake.write_text(f"#!{sys.executable}\n" + textwrap.dedent(r'''
            import json
            import os
            from pathlib import Path
            import sys

            args = sys.argv[1:]
            if args in [["--version"], ["--unverified", "--version"]]:
                line = os.environ.get("FAKE_TRUSTC_VERSION") or json.loads(
                    os.environ["LAYOUT_FAKE_VERSIONS"]
                )[os.environ["FAKE_HOST"]]
                print(line.replace("rustc ", "targo ", 1).replace("(trustc ", "(targo ", 1))
                raise SystemExit(0)
            if args[:1] == ["--unverified"]:
                args = args[1:]
            with Path(os.environ["LAYOUT_CALLS"]).open("a") as log:
                log.write(json.dumps(args) + "\n")
            cases = json.loads(Path(os.environ["LAYOUT_CASES"]).read_text())
            mode = os.environ.get("LAYOUT_FAKE_MODE", "")
            target = args[args.index("--test") + 1]
            names = cases[target][:]
            if "--list" in args:
                if mode == "list-failure":
                    raise SystemExit(9)
                if mode == "zero-inventory":
                    names = []
                if mode == "missing-selected":
                    names[0] = "replacement_without_the_selected_name"
                if target == "e2e_frontend_roundtrip":
                    if mode == "duplicate-complement":
                        names[-1] = names[-2]
                    if mode == "missing-complement":
                        names.pop()
                    if mode == "malformed-complement":
                        names[-1] = "not a libtest name"
                for name in names:
                    print(f"{name}: test")
                raise SystemExit(0)
            assert "--locked" in args and "--all-features" in args
            assert "--include-ignored" in args and "--test-threads=1" in args
            name = args[args.index("--exact") + 1]
            assert name in names
            if mode == "exact-failure":
                raise SystemExit(7)
            if mode == "empty-execution":
                raise SystemExit(0)
            if mode == "zero-execution":
                print("running 0 tests")
                print(f"test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; {len(names)} filtered out; finished in 0.01s")
                raise SystemExit(0)
            print("running 1 test")
            actual = "wrong_case" if mode == "wrong-execution" else name
            print(f"test {actual} ... ok")
            if mode == "duplicate-execution":
                print(f"test {actual} ... ok")
            if mode != "missing-result":
                filtered = len(names) if mode == "wrong-filtered" else len(names) - 1
                print(f"test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; {filtered} filtered out; finished in 0.01s")
            if mode == "trailing-error":
                print("error: execution failed after result")
        '''))
        fake.chmod(0o755)

    def run_layout(self, mode: str = "", **overrides: str) -> subprocess.CompletedProcess:
        return self.box.codegen(
            "--qualify-kernel-layout-fixtures",
            LAYOUT_CASES=str(self.inventory), LAYOUT_CALLS=str(self.calls),
            LAYOUT_FAKE_VERSIONS=json.dumps(EXPECTED_TRUSTC), LAYOUT_FAKE_MODE=mode,
            **overrides,
        )

    def document(self, result: subprocess.CompletedProcess) -> dict:
        match = re.search(r"release summary: (.+)$", result.stderr, re.MULTILINE)
        self.assertIsNotNone(match, result.stderr)
        return self.box.summary(Path(match.group(1)))

    def test_all_compiled_cases_include_every_complement_and_execute_once(self) -> None:
        result = self.run_layout(RUST_TEST_THREADS="8")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        calls = [json.loads(line) for line in self.calls.read_text().splitlines()]
        listed = [call for call in calls if "--list" in call]
        executed = [call for call in calls if "--exact" in call]
        expected = {(target, name) for target, names in self.cases.items() for name in names}
        actual = [(call[call.index("--test") + 1], call[call.index("--exact") + 1])
                  for call in executed]
        self.assertEqual(len(listed), 11)
        self.assertEqual(len(actual), 118)
        self.assertEqual(set(actual), expected)
        self.assertEqual(len(set(actual)), len(actual))
        document = self.document(result)
        self.assertEqual(document["gate"], "kernel_layout_fixture_qualification")
        self.assertEqual(document["status"], "pass")
        self.assertFalse(document["qualifying"])
        self.assertIn("not full release qualification", document["scope"])
        self.assertEqual(set(lanes(document)), {"kernel-layout-fixtures"})
        evidence = Path(lanes(document)["kernel-layout-fixtures"]["output"])
        self.assertEqual(len(list(evidence.glob("*.inventory.log"))), 11)
        self.assertEqual(len(list(evidence.glob("case-*.log"))), 118)
        self.assertIn("118/118 cases", result.stdout)
        self.assertIn("not full release or proof qualification", result.stdout)

    def test_bad_inventory_or_selected_name_never_qualifies(self) -> None:
        for mode in ["list-failure", "zero-inventory", "missing-selected",
                     "duplicate-complement", "missing-complement", "malformed-complement"]:
            with self.subTest(mode=mode):
                result = self.run_layout(mode)
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(self.document(result)["status"], "fail")
                self.assertNotIn("Kernel-layout fixture qualification: PASS", result.stdout)

    def test_failed_empty_wrong_or_partial_exact_execution_never_qualifies(self) -> None:
        for mode in ["exact-failure", "empty-execution", "zero-execution", "wrong-execution",
                     "duplicate-execution", "missing-result", "wrong-filtered", "trailing-error"]:
            with self.subTest(mode=mode):
                result = self.run_layout(mode)
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(self.document(result)["status"], "fail")
                self.assertNotIn("Kernel-layout fixture qualification: PASS", result.stdout)

    def test_zero_policy_total_refuses_before_inventory(self) -> None:
        runner = self.box.repo / "scripts/run_public_release_codegen_tests.sh"
        runner.write_text(runner.read_text().replace(
            "e2e_binding_defeq|5|5|full|", "e2e_binding_defeq|0|5|full|"
        ))
        result = self.run_layout()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("nonzero inventory", result.stderr)
        self.assertFalse(self.calls.exists())

    def test_existing_runner_selftest_covers_complete_inventory_failures(self) -> None:
        result = self.box.codegen("--self-test", LAYOUT_FAKE_VERSIONS=json.dumps(EXPECTED_TRUSTC))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Public-release codegen runner self-test: PASS", result.stdout)
        self.assertFalse(self.calls.exists())

    def test_other_host_and_uncertified_compiler_remain_refused(self) -> None:
        for overrides in [
            {"host": LINUX},
            {"FAKE_TRUSTC_VERSION":
             "rustc 1.101.0-dev (012345678 2026-10-27) (trustc 0.11.0+g012345678)"},
        ]:
            with self.subTest(overrides=overrides):
                result = self.run_layout(**overrides)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertFalse(self.calls.exists())

    def test_require_keeps_proof_tool_preconditions_without_claiming_release(self) -> None:
        missing = self.run_layout(TRUST_CG_PROOF_GATE="require")
        self.assertEqual(missing.returncode, 1)
        self.assertIn("needs AY and Clean", missing.stderr)
        self.assertFalse(self.calls.exists())
        result = self.run_layout(
            TRUST_CG_PROOF_GATE="require",
            AY_SOLVER_PATH=str(self.box.tool("ay")),
            TCG_EXTERNAL_CLEAN_CHECKER=str(self.box.tool("clean")),
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        document = self.document(result)
        self.assertEqual(document["status"], "pass")
        self.assertFalse(document["qualifying"])
        self.assertIn("layout-fixture qualification only", document["non_qualifying_reasons"][0])


class ReleaseTrustCompilerListTests(unittest.TestCase):
    """scripts/release_trust_compilers.txt is the Trust half of what
    crates/trust-cg-codegen/fixture_toolchain.rs certifies, host for host."""

    TRUST_LITERAL = re.compile(r'"(rustc [^"\n]*\(trustc [^"\n]*\))"')
    TARGET_LITERAL = re.compile(r'"((?:aarch64|x86_64)-[a-z0-9_-]+)"')

    def certified_by_fixture_toolchain(self) -> dict[str, set[str]]:
        """Each Trust compiler literal in fixture_toolchain.rs -> the targets
        named in the rest of its statement (empty: the literal is target-free)."""
        text = FIXTURE_TOOLCHAIN.read_text()
        certified: dict[str, set[str]] = {}
        for match in self.TRUST_LITERAL.finditer(text):
            rest = text[match.end():]
            end = min((index for index in (rest.find(";"), rest.find("}")) if index >= 0), default=len(rest))
            certified.setdefault(match.group(1), set()).update(self.TARGET_LITERAL.findall(rest[:end]))
        return certified

    def test_the_list_names_exactly_the_certified_trust_compilers(self) -> None:
        certified = self.certified_by_fixture_toolchain()
        self.assertTrue(certified, f"no Trust compiler literal found in {FIXTURE_TOOLCHAIN}")
        listed = {line for lines in CERTIFIED_TRUSTC.values() for line in lines}
        self.assertEqual(listed, set(certified))

    def test_each_listed_compiler_is_on_the_host_its_certification_names(self) -> None:
        for compiler, targets in self.certified_by_fixture_toolchain().items():
            hosts = {host for host, lines in CERTIFIED_TRUSTC.items() if compiler in lines}
            with self.subTest(compiler=compiler):
                if targets:
                    self.assertEqual(hosts, targets)
                else:
                    self.assertEqual(len(hosts), 1, hosts)

    def test_each_hosts_soundness_pin_is_a_listed_compiler(self) -> None:
        # scripts/soundness_attestation.py reads one pin per host from the
        # release gate's `expected_trustc` spelling; the gate itself accepts
        # the whole list, so the pin must be on it.
        spec = importlib.util.spec_from_file_location(
            "soundness_attestation_for_pins", ROOT / "scripts" / "soundness_attestation.py")
        attestation = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(attestation)
        pins = attestation.trustc_pins(RELEASE_CHECKS.read_text())
        self.assertEqual(set(pins), set(CERTIFIED_TRUSTC))
        for host, pin in pins.items():
            with self.subTest(host=host):
                self.assertIn(pin, CERTIFIED_TRUSTC[host])

    def test_the_list_covers_both_aarch64_hosts_without_repeats(self) -> None:
        self.assertEqual(set(CERTIFIED_TRUSTC), {DARWIN, LINUX})
        for host, lines in CERTIFIED_TRUSTC.items():
            self.assertEqual(len(lines), len(set(lines)), host)
            for line in lines:
                self.assertRegex(line, r"^rustc \S+ \([0-9a-f]{9} \d{4}-\d{2}-\d{2}\) \(trustc [^)]+\)$")


if __name__ == "__main__":
    unittest.main()
