"""Unit tests for the release-gate summary document and proof-tool resolution."""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import atpkg_prelude_fixture as SHIMS  # noqa: E402


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("release_gate_summary", ROOT / "scripts" / "release_gate_summary.py")
assert SPEC is not None and SPEC.loader is not None
SUMMARY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SUMMARY)
HOST = "aarch64-apple-darwin"
LINUX_HOST = "aarch64-unknown-linux-gnu"
X86_DARWIN = "x86_64-apple-darwin"
X86_LINUX = "x86_64-unknown-linux-gnu"
CODEGEN_LANES = ("codegen-complement", "codegen-doctests", "codegen-capstones")
FULL_DARWIN_LANES = (
    "authority-preflight", "companion-coherence", "python-unit-tests", "harness-syntax",
    "harness-helper-syntax", "timeout-runner-tests", "soundness-harness-tests", "sat-fixtures",
    "vendor-licenses", "cargo-metadata", "cargo-check-workspace", "cargo-check-fuzz",
    "pgo-runtime", "proof-gate", "workspace", "codegen", "bridge-toolchain-pin", "bridge-env",
    "bridge-tests", *CODEGEN_LANES, "darwin-aarch64-floor", "darwin-aarch64-bridge",
)
PARTITION = {"package": "trust-cg-codegen", "from_lane": "workspace", "covered_by": "codegen"}


def executable(path: Path, body: str = "echo tool") -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(f"#!/bin/sh\n{body}\n")
    path.chmod(0o755)
    return path


def qualifying_document() -> dict:
    tool = {"path": "/x", "sha256": "0" * 64, "size": 1, "route": "aterm-packaged", "pinning": "pinned"}
    return {
        "schema": SUMMARY.SCHEMA, "gate": "run_public_release_checks", "host": HOST,
        "mode": "require", "status": "pass",
        "lanes": [{"name": name, "status": "pass"} for name in FULL_DARWIN_LANES],
        "exclusions": [],
        "partitions": [dict(PARTITION)],
        "solver": {"ay": dict(tool), "clean": dict(tool)}, "solver_drift": [],
    }


def x86_accounting_document(host: str) -> dict:
    document = qualifying_document()
    prefix = "darwin-x86_64" if host == X86_DARWIN else "linux-x86_64"
    document["host"] = host
    document["lanes"] = [
        {"name": f"{prefix}-floor", "status": "unavailable"},
        {"name": f"{prefix}-bridge", "status": "unavailable"},
        {"name": "pgo-runtime", "status": "excluded"},
        {"name": "codegen-capstones", "status": "excluded"},
    ]
    document["partitions"] = []
    return document


class ResolutionTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.home = self.root / "home"
        self.home.mkdir()
        self.bin = self.root / "prefix" / "bin"
        self.bin.mkdir(parents=True)

    def resolve(self, tool: str, platform: str = "darwin", **environ: str):
        environment = {"PATH": str(self.bin), "HOME": str(self.home)}
        environment.update(environ)
        return SUMMARY.resolve_tool(tool, HOST, environment, platform)

    def test_nothing_resolves_in_an_empty_environment(self) -> None:
        self.assertIsNone(self.resolve("ay"))
        self.assertIsNone(self.resolve("clean"))

    def build_toolchain(self, name: str = "sysroot") -> Path:
        """A `rustc` on PATH whose sysroot ships a `bin/ay`, as a Trust toolchain does."""
        sysroot = self.root / name
        ay = executable(sysroot / "bin/ay")
        executable(self.bin / "trustc", f'[ "$1 $2" = "--print sysroot" ] && echo "{sysroot}"')
        return ay

    def test_build_toolchain_ay_is_the_automatic_route_and_is_pinned(self) -> None:
        toolchain_ay = self.build_toolchain()
        found, route = self.resolve("ay")
        self.assertEqual((found, route), (toolchain_ay, "toolchain-sysroot"))
        self.assertEqual(SUMMARY.route_pinning(route), "pinned")

    def test_rustc_env_names_the_build_compiler(self) -> None:
        # cargo hands build.rs its RUSTC; the gate asks the same compiler.
        other = self.root / "other-sysroot"
        other_ay = executable(other / "bin/ay")
        rustc = executable(self.root / "wrapped/rustc", f'echo "{other}"')
        self.build_toolchain()
        self.assertEqual(self.resolve("ay", RUSTC=str(rustc)), (other_ay, "toolchain-sysroot"))

    def test_a_path_launcher_shim_is_followed_to_its_package_never_run(self) -> None:
        # The package targo builds with the package trustc, not the PATH shim,
        # whose prelude the resolver reads but never runs
        # (DR-ATPKG-PRELUDE-SHIM-20261015); this prelude names another sysroot.
        package = SHIMS.make_package(self.root / "pkg")
        package_ay = executable(package / "bin/ay")
        forged = self.root / "forged-sysroot"
        executable(forged / "bin/ay")
        log = self.root / "shim-calls.log"
        shim = SHIMS.lying_shim(self.bin / "trustc", package / "bin" / "trustc", log,
                                {"--print sysroot": str(forged)})
        lied = subprocess.run([str(shim), "--print", "sysroot"], text=True, capture_output=True,
                              timeout=60, check=True)
        self.assertEqual(lied.stdout.strip(), str(forged))
        log.unlink()
        self.assertEqual(self.resolve("ay"), (package_ay, "toolchain-sysroot"))
        self.assertEqual(SHIMS.logged(log), [], "the summary executed a PATH launcher shim")

    def test_toolchain_without_ay_resolves_nothing(self) -> None:
        # A stock toolchain (the public-clone pin) ships no AY; nothing else is tried.
        executable(self.bin / "trustc", f'echo "{self.root / "stock"}"')
        executable(self.bin / "ay")
        self.assertIsNone(self.resolve("ay"))

    def test_explicit_override_wins_and_is_pinned(self) -> None:
        self.build_toolchain()
        explicit = executable(self.root / "explicit/ay")
        found, route = self.resolve("ay", AY_SOLVER_PATH=str(explicit))
        self.assertEqual((found, route), (explicit, "env-override:AY_SOLVER_PATH"))
        self.assertEqual(SUMMARY.route_pinning(route), "pinned")

    def test_bare_ay_override_is_refused_not_looked_up_on_path(self) -> None:
        # ay_identity.rs refuses it (TCG-AY-IDENTITY-OVERRIDE-NOT-ABSOLUTE).
        executable(self.bin / "my-ay")
        self.build_toolchain()
        with self.assertRaises(SUMMARY.ResolveError):
            self.resolve("ay", AY_SOLVER_PATH="my-ay")

    def test_broken_overrides_never_fall_through(self) -> None:
        self.build_toolchain()
        executable(self.root / "prefix/store/clean/current/bin/clean")
        cases = (
            ("ay", {"AY_SOLVER_PATH": ""}),
            ("ay", {"AY_SOLVER_PATH": "   "}),
            ("ay", {"AY_SOLVER_PATH": str(self.root / "missing")}),
            ("ay", {"AY_SOLVER_PATH": "relative/ay"}),
            ("clean", {"TCG_EXTERNAL_CLEAN_CHECKER": ""}),
            ("clean", {"TCG_CLEAN_CHECKER": "clean"}),
        )
        for tool, overrides in cases:
            with self.subTest(tool=tool, overrides=overrides):
                with self.assertRaises(SUMMARY.ResolveError):
                    self.resolve(tool, **overrides)

    def test_non_executable_override_is_rejected(self) -> None:
        plain = self.root / "plain-ay"
        plain.write_text("not executable\n")
        with self.assertRaises(SUMMARY.ResolveError):
            self.resolve("ay", AY_SOLVER_PATH=str(plain))

    def test_role_named_clean_override_precedes_the_legacy_alias(self) -> None:
        external = executable(self.root / "external/clean")
        legacy = executable(self.root / "legacy/clean")
        found = self.resolve("clean", TCG_EXTERNAL_CLEAN_CHECKER=str(external), TCG_CLEAN_CHECKER=str(legacy))
        self.assertEqual(found, (external, "env-override:TCG_EXTERNAL_CLEAN_CHECKER"))
        self.assertEqual(self.resolve("clean", TCG_CLEAN_CHECKER=str(legacy)), (legacy, "env-override:TCG_CLEAN_CHECKER"))

    def test_platform_default_package_store(self) -> None:
        darwin = executable(self.home / "Library/Application Support/aterm/pkg/store/clean/current/bin/clean")
        linux = executable(self.home / ".local/share/aterm/pkg/store/clean/current/bin/clean")
        self.assertEqual(self.resolve("clean", platform="darwin"), (darwin, "aterm-packaged"))
        self.assertEqual(self.resolve("clean", platform="linux"), (linux, "aterm-packaged"))

    def test_package_current_link_resolves_to_the_versioned_binary(self) -> None:
        versioned = executable(self.root / "prefix/store/clean/42/bin/clean")
        (self.root / "prefix/store/clean/current").symlink_to("42")
        self.assertEqual(self.resolve("clean"), (versioned, "aterm-packaged"))

    def trust_toolchain_clean(self, transcript: str, code: int) -> Path:
        """A `rustc` on PATH whose Trust sysroot ships a `bin/clean` replaying `transcript`."""
        sysroot = self.root / "trust"
        (sysroot / "lib/rustlib").mkdir(parents=True, exist_ok=True)
        executable(sysroot / "bin/trustc")
        clean = executable(sysroot / "bin/clean", f"printf '%s\\n' '{transcript}'\nexit {code}")
        executable(self.bin / "trustc", f'[ "$1 $2" = "--print sysroot" ] && echo "{sysroot}"')
        return clean

    def test_build_toolchain_clean_leads_when_it_verifies_the_control_proof(self) -> None:
        # obligation_cert_store.rs: the checker must read the toolchain AY's proofs.
        packaged = executable(self.root / "prefix/store/clean/current/bin/clean")
        capable = self.trust_toolchain_clean(
            "External certificate verification: PASSED\n  Type: Alethe SMT proof\n"
            "  Proof status: fully verified", 0,
        )
        found, route = self.resolve("clean")
        self.assertEqual((found, route), (capable, "toolchain-sysroot"))
        self.assertEqual(SUMMARY.route_pinning(route), "pinned")
        # A Trust sysroot clean built without carcara-verify is skipped for the package.
        self.trust_toolchain_clean(
            "External certificate verification: FAILED\n"
            "  Error: carcara-verify feature required for tier 1 verification", 1,
        )
        self.assertEqual(self.resolve("clean"), (packaged, "aterm-packaged"))

    def test_stock_toolchain_names_no_clean(self) -> None:
        # A sysroot without bin/trustc is not a Trust toolchain, whatever bin/clean holds.
        stock = self.root / "stock"
        (stock / "lib/rustlib").mkdir(parents=True)
        executable(stock / "bin/clean", "printf 'External certificate verification: PASSED\\n'")
        executable(self.bin / "trustc", f'echo "{stock}"')
        self.assertIsNone(self.resolve("clean"))

    def test_generic_clean_on_path_is_never_a_checker(self) -> None:
        executable(self.bin / "clean")
        self.assertIsNone(self.resolve("clean"))

    def test_environment_ay_locations_are_never_consulted(self) -> None:
        # The verifier never searches for AY, so none of these is evidence of one.
        executable(self.bin / "ay")
        executable(self.root / "prefix/store/ay/current/bin/ay")
        executable(self.home / "Library/Application Support/aterm/pkg/store/ay/current/bin/ay")
        executable(self.home / f"trust/build/{HOST}/stage2/bin/ay")
        executable(self.home / "trust/first-party/ay/target/release/ay")
        executable(self.home / "ay/target/release/ay")
        executable(self.root / "trust-sysroot/bin/ay")
        self.assertIsNone(
            self.resolve("ay", TRUST_SYSROOT=str(self.root / "trust-sysroot"), TRUST_ROOT=str(self.home / "trust"))
        )
        toolchain_ay = self.build_toolchain()
        self.assertEqual(
            self.resolve("ay", TRUST_SYSROOT=str(self.root / "trust-sysroot"), TRUST_ROOT=str(self.home / "trust")),
            (toolchain_ay, "toolchain-sysroot"),
        )


class VerdictTests(unittest.TestCase):
    def test_complete_require_run_is_qualifying(self) -> None:
        self.assertEqual(SUMMARY.non_qualifying_reasons(qualifying_document()), [])

        linux = qualifying_document()
        linux["host"] = LINUX_HOST
        linux["lanes"] = [lane for lane in linux["lanes"]
                          if lane["name"] not in ("darwin-aarch64-floor", "darwin-aarch64-bridge")]
        linux["lanes"].extend({"name": name, "status": "pass"} for name in
                              ("linux-aarch64-floor", "linux-aarch64-bridge", "aarch64-aot-arithmetic"))
        self.assertEqual(SUMMARY.non_qualifying_reasons(linux), [])

        codegen = qualifying_document()
        codegen["gate"] = "run_public_release_codegen_tests"
        codegen["lanes"] = [{"name": name, "status": "pass"} for name in CODEGEN_LANES]
        codegen["partitions"] = []
        self.assertEqual(SUMMARY.non_qualifying_reasons(codegen), [])

    def assert_reason(self, document: dict, fragment: str) -> None:
        reasons = SUMMARY.non_qualifying_reasons(document)
        self.assertTrue(any(fragment in reason for reason in reasons), reasons)

    def test_exact_lane_roster_is_required(self) -> None:
        for name in FULL_DARWIN_LANES:
            with self.subTest(missing=name):
                document = qualifying_document()
                document["lanes"] = [lane for lane in document["lanes"] if lane["name"] != name]
                self.assert_reason(document, f"required lane {name}: missing")

        document = qualifying_document()
        document["lanes"].append({"name": "workspace", "status": "pass"})
        self.assert_reason(document, "required lane workspace: recorded 2 times")

        document = qualifying_document()
        document["lanes"].append({"name": "unlisted-lane", "status": "pass"})
        self.assert_reason(document, "unexpected lane unlisted-lane")

    def test_exact_partition_is_required(self) -> None:
        for partitions, fragment in (
            ([], "required partition trust-cg-codegen from workspace to codegen: recorded 0 times"),
            ([dict(PARTITION), dict(PARTITION)], "required partition trust-cg-codegen from workspace to codegen: recorded 2 times"),
            ([{**PARTITION, "covered_by": "workspace"}], "required partition trust-cg-codegen from workspace to codegen: recorded 0 times"),
            ([dict(PARTITION), {"package": "other", "from_lane": "workspace", "covered_by": "codegen"}],
             "unexpected partition"),
        ):
            with self.subTest(partitions=partitions):
                document = qualifying_document()
                document["partitions"] = partitions
                self.assert_reason(document, fragment)

    def test_gate_and_host_profile_are_required(self) -> None:
        for gate, host, fragment in (
            ("unknown-gate", HOST, "unknown gate"),
            ("run_public_release_checks", "riscv64-unknown-linux-gnu", "unsupported host profile"),
            ("run_public_release_checks", "", "unsupported host profile"),
        ):
            with self.subTest(gate=gate, host=host):
                document = qualifying_document()
                document["gate"], document["host"] = gate, host
                self.assert_reason(document, fragment)

    def test_x86_accounting_profiles_cannot_qualify(self) -> None:
        for host in (X86_DARWIN, X86_LINUX):
            with self.subTest(host=host):
                document = x86_accounting_document(host)
                reasons = SUMMARY.non_qualifying_reasons(document)
                self.assertTrue(any("accounting-only" in reason for reason in reasons), reasons)
                self.assertTrue(any("floor: unavailable" in reason for reason in reasons), reasons)
                self.assertTrue(any("bridge: unavailable" in reason for reason in reasons), reasons)
                self.assertFalse(any("unsupported host profile" in reason for reason in reasons), reasons)
                self.assertFalse(any("required partition" in reason for reason in reasons), reasons)

                # Even a fabricated zero-exclusion, all-pass summary cannot
                # turn this diagnostic profile into release qualification.
                for lane in document["lanes"]:
                    lane["status"] = "pass"
                self.assert_reason(document, "accounting-only")

                document["lanes"] = [lane for lane in document["lanes"] if not lane["name"].endswith("-bridge")]
                self.assert_reason(document, "required lane")

    def test_linux_native_floor_and_bridge_cannot_be_omitted(self) -> None:
        document = qualifying_document()
        document["host"] = LINUX_HOST
        document["lanes"] = [lane for lane in document["lanes"] if lane["name"] != "darwin-aarch64-floor"]
        self.assert_reason(document, "required lane linux-aarch64-floor: missing")
        self.assert_reason(document, "required lane linux-aarch64-bridge: missing")

    def test_standalone_codegen_rejects_parent_lanes_and_partition(self) -> None:
        document = qualifying_document()
        document["gate"] = "run_public_release_codegen_tests"
        self.assert_reason(document, "unexpected lane workspace")
        self.assert_reason(document, "unexpected partition")

    def test_each_defect_is_non_qualifying(self) -> None:
        document = qualifying_document()
        document["mode"] = "auto"
        self.assert_reason(document, "mode=auto")

        document = qualifying_document()
        document["exclusions"].append({"lane": "workspace", "kind": "cargo-exclude", "value": "trust-cg-verify", "reason": "r"})
        self.assert_reason(document, "exclusion: lane workspace cargo-exclude trust-cg-verify")

        for status, fragment in (("fail", "failed"), ("running", "did not complete"),
                                 ("planned", "planned but not executed"), ("unavailable", "unavailable"),
                                 ("excluded", "excluded")):
            with self.subTest(status=status):
                document = qualifying_document()
                document["lanes"].append({"name": "extra", "status": status})
                self.assert_reason(document, fragment)

        document = qualifying_document()
        document["lanes"] = [lane for lane in document["lanes"] if lane["name"] != "codegen"]
        self.assert_reason(document, "covering lane codegen is missing")

        document = qualifying_document()
        document["solver"]["clean"] = None
        self.assert_reason(document, "no clean identity")

        document = qualifying_document()
        document["solver"]["ay"]["pinning"] = "unpinned"
        document["solver"]["ay"]["route"] = "unpinned:path"
        self.assert_reason(document, "unpinned route unpinned:path")

        document = qualifying_document()
        document["solver_drift"] = ["ay: sha256 changed"]
        self.assert_reason(document, "solver identity changed")

        document = qualifying_document()
        document["lanes"] = []
        document["partitions"] = []
        self.assert_reason(document, "no lane was recorded")

    def test_blockers_filter_by_lane_prefix(self) -> None:
        document = qualifying_document()
        document["exclusions"] = [
            {"lane": "pgo-runtime", "kind": "host", "value": "v", "reason": "r"},
            {"lane": "codegen-capstones", "kind": "host", "value": "v", "reason": "r"},
        ]
        document["lanes"].append({"name": "darwin-aarch64-floor", "status": "unavailable"})
        self.assertEqual(len(SUMMARY.blockers(document)), 3)
        self.assertEqual(
            SUMMARY.blockers(document, "codegen-"),
            ["exclusion: lane codegen-capstones host v (r)"],
        )


class CommandTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.path = self.root / "evidence" / "summary.json"

    def call(self, *arguments: str) -> tuple:
        stdout, stderr = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
            status = SUMMARY.main([*arguments, "--path", str(self.path)])
        return status, stdout.getvalue(), stderr.getvalue()

    def document(self) -> dict:
        return json.loads(self.path.read_text())

    def init(self, mode: str = "require") -> None:
        status, _, _ = self.call("init", "--gate", "run_public_release_checks", "--mode", mode,
                                 "--host", HOST, "--evidence-dir", str(self.root))
        self.assertEqual(status, 0)

    def record_complete_lanes(self) -> None:
        for name in FULL_DARWIN_LANES:
            self.call("lane", "--name", name, "--status", "pass")
        self.call("partition", "--package", PARTITION["package"], "--from-lane", PARTITION["from_lane"],
                  "--covered-by", PARTITION["covered_by"])

    def test_init_never_overwrites_retained_evidence(self) -> None:
        self.init()
        before = self.path.read_text()
        status, _, stderr = self.call("init", "--gate", "g", "--mode", "auto", "--host", HOST, "--evidence-dir", "x")
        self.assertEqual(status, 1)
        self.assertIn("refusing to overwrite", stderr)
        self.assertEqual(self.path.read_text(), before)

    def test_complete_layout_profile_never_claims_full_release_or_proof_qualification(self) -> None:
        self.call("init", "--gate", SUMMARY.KERNEL_LAYOUT_GATE, "--mode", "require",
                  "--host", HOST, "--evidence-dir", str(self.root))
        self.call("lane", "--name", "kernel-layout-fixtures", "--status", "pass")
        self.record_tools()
        status, _, _ = self.finish()
        self.assertEqual(status, 0)
        document = self.document()
        self.assertEqual(document["status"], "pass")
        self.assertEqual(document["scope"], SUMMARY.KERNEL_LAYOUT_SCOPE)
        self.assertFalse(document["qualifying"])
        self.assertEqual(document["non_qualifying_reasons"], [
            "layout-fixture qualification only: not full release or proof qualification"
        ])
        status, _, _ = self.finish("--require-qualifying")
        self.assertEqual(status, SUMMARY.NOT_QUALIFYING)

    def test_exclusions_and_partitions_are_recorded_once(self) -> None:
        self.init("auto")
        for _ in range(2):
            self.call("exclusion", "--lane", "codegen-complement", "--kind", "cargo-skip", "--value", "a b", "--reason", "r")
            self.call("partition", "--package", "trust-cg-codegen", "--from-lane", "workspace", "--covered-by", "codegen")
        document = self.document()
        self.assertEqual(len(document["exclusions"]), 1)
        self.assertEqual(len(document["partitions"]), 1)
        self.assertFalse(document["qualifying"])

    def test_lane_updates_keep_detail_and_output(self) -> None:
        self.init()
        self.call("lane", "--name", "floor", "--status", "planned", "--detail", "cmd", "--output", "/out")
        self.call("lane", "--name", "floor", "--status", "pass")
        (lane,) = self.document()["lanes"]
        self.assertEqual((lane["status"], lane["detail"], lane["output"]), ("pass", "cmd", "/out"))

    def record_tools(self) -> Path:
        ran = self.root / "ay-was-executed"
        ay = executable(self.root / "tools/ay", f'touch "{ran}"; echo "ay 1.0"')
        clean = executable(self.root / "tools/clean", 'echo "clean 1.0"')
        status, _, _ = self.call("solver", "--ay", str(ay), "--ay-route", "env-override:AY_SOLVER_PATH",
                                 "--clean", str(clean), "--clean-route", "env-override:TCG_EXTERNAL_CLEAN_CHECKER")
        self.assertEqual(status, 0)
        return ay

    def finish(self, *extra: str) -> tuple:
        environment = {"AY_SOLVER_PATH": str(self.root / "tools/ay"),
                       "TCG_EXTERNAL_CLEAN_CHECKER": str(self.root / "tools/clean")}
        saved = {key: os.environ.get(key) for key in (*environment, "TCG_CLEAN_CHECKER")}
        os.environ.update(environment)
        os.environ.pop("TCG_CLEAN_CHECKER", None)
        try:
            return self.call("finish", "--status", "pass", *extra)
        finally:
            for key, value in saved.items():
                if value is None:
                    os.environ.pop(key, None)
                else:
                    os.environ[key] = value

    def test_require_finish_is_qualifying_only_for_a_complete_run(self) -> None:
        self.init()
        self.record_tools()
        self.record_complete_lanes()
        status, stdout, _ = self.finish("--require-qualifying")
        self.assertEqual((status, stdout.strip()), (0, "qualifying"))
        document = self.document()
        self.assertTrue(document["qualifying"])
        # AY is recorded by its bytes and never executed; Clean is still probed.
        self.assertEqual(document["solver"]["ay"]["version"], {"not_executed": SUMMARY.AY_NOT_EXECUTED})
        self.assertEqual(len(document["solver"]["ay"]["sha256"]), 64)
        self.assertFalse((self.root / "ay-was-executed").exists())
        self.assertEqual(document["solver"]["clean"]["version"]["stdout"], "clean 1.0\n")

    def test_lone_workspace_pass_is_not_qualifying(self) -> None:
        self.init()
        self.record_tools()
        self.call("lane", "--name", "workspace", "--status", "pass")
        status, stdout, _ = self.finish("--require-qualifying")
        self.assertEqual((status, stdout.strip()), (SUMMARY.NOT_QUALIFYING, "non-qualifying"))
        self.assertFalse(self.document()["qualifying"])
        self.assertEqual(self.document()["status"], "fail")
        self.assertIn("required lane proof-gate: missing", self.document()["non_qualifying_reasons"])

    def test_require_finish_refuses_a_non_qualifying_verdict(self) -> None:
        self.init()
        self.record_tools()
        self.record_complete_lanes()
        self.call("exclusion", "--lane", "workspace", "--kind", "cargo-exclude", "--value", "x", "--reason", "r")
        status, stdout, stderr = self.finish("--require-qualifying")
        self.assertEqual((status, stdout.strip()), (SUMMARY.NOT_QUALIFYING, "non-qualifying"))
        self.assertIn("NON-QUALIFYING", stderr)
        self.assertEqual(self.document()["status"], "fail")
        self.assertTrue(any("exclusion: lane workspace" in reason for reason in
                            self.document()["non_qualifying_reasons"]))

    def test_solver_bytes_changed_during_the_run_are_non_qualifying(self) -> None:
        self.init()
        ay = self.record_tools()
        self.record_complete_lanes()
        ay.write_text("#!/bin/sh\necho replaced\n")
        status, stdout, _ = self.finish()
        self.assertEqual((status, stdout.strip()), (0, "non-qualifying"))
        self.assertTrue(any("ay: sha256" in drift for drift in self.document()["solver_drift"]))

    def test_resolve_exit_codes(self) -> None:
        saved = os.environ.get("AY_SOLVER_PATH")
        try:
            os.environ["AY_SOLVER_PATH"] = ""
            with contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(SUMMARY.main(["resolve", "--tool", "ay", "--host", HOST]), SUMMARY.RESOLVE_INVALID_OVERRIDE)
            ay = executable(self.root / "tools/ay")
            os.environ["AY_SOLVER_PATH"] = str(ay)
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                self.assertEqual(SUMMARY.main(["resolve", "--tool", "ay", "--host", HOST]), 0)
            self.assertEqual(stdout.getvalue(), f"{ay}\tenv-override:AY_SOLVER_PATH\tpinned\n")
        finally:
            if saved is None:
                os.environ.pop("AY_SOLVER_PATH", None)
            else:
                os.environ["AY_SOLVER_PATH"] = saved

    def test_documents_of_another_schema_are_refused(self) -> None:
        self.path.parent.mkdir(parents=True)
        self.path.write_text(json.dumps({"schema": "other"}))
        with self.assertRaises(SystemExit):
            self.call("lane", "--name", "x", "--status", "pass")


if __name__ == "__main__":
    unittest.main()
