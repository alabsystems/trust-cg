from __future__ import annotations

import contextlib
import gzip
import hashlib
import importlib.util
import inspect
import io
import json
import os
import re
from pathlib import Path
import subprocess
import signal
import shlex
import sys
import tempfile
import time
import types
import unittest
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "check_linux_aarch64.py"
SPEC = importlib.util.spec_from_file_location("check_linux_aarch64", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
GATE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GATE)



def trust_lane_provenance(build_tool: str) -> dict:
    """The keys main() and the target commands require of preflight's
    provenance, the Trust development lane being the floor's only lane (a
    missing key must raise, not pass), with `build_tool` as the lane's whole
    build command."""
    return {
        "lane": "trust-unverified", "build_command": [build_tool], "runtime_checker_environment": {},
        "compiler_environment": {}, "compiler_tool_identities": {},
    }


# Exact rows rendered by trust-cg-verify's opcode evidence inventory
# (coverage_gate.rs: "  [{tag}] {:32} {}"), copied from a retained run.
INVENTORY_EXCERPT = (
    "Evidence audit: aarch64 (294 opcodes; 152/250 emitted value/effect obligations accepted = 60.8%; "
    "27 explicitly excluded; ratio is NOT a correctness-proof percentage)\n"
    "  [accepted] AArch64::AddRR                   RECONSTRUCTED from real AddRR operands — representative "
    "obligation evaluates Valid [reconstruction] (default evaluator acceptance is regression evidence, "
    "NOT a formal proof)\n"
    "  [RED     ] AArch64::AddRIShift12            HONESTLY DEFERRED (RED in denominator): emitted "
    "ADD-immediate-with-LSL#12 can materialize numeric values as well as addresses\n"
    "  [skip    ] AArch64::Phi                     pseudo/trap — no equivalence proof obligation\n"
    "  [exclude ] AArch64::AlignNop                fail-closed allowlist: alignment padding NOP: no value "
    "semantics to prove\n"
    "  [skip    ] riscv::Ebreak                    pseudo/trap — no equivalence proof obligation\n"
    "  [skip    ] x86_64::Ud2                      pseudo/trap — no equivalence proof obligation\n"
)


def transcript(passed=1, failed=0, ignored=0, filtered=0, prefix="", started=None):
    if started is None:
        started = passed + failed + ignored
    state = "FAILED" if failed else "ok"
    return (
        f"running {started} tests\n{prefix}"
        f"test result: {state}. {passed} passed; {failed} failed; "
        f"{ignored} ignored; 0 measured; {filtered} filtered out; finished in 0.01s\n"
    )


def proof_tool_record(pinned: bool = True, sha: str = "c" * 64) -> dict:
    """A proof_tool_identities record: both tools pinned through a package prefix, or unresolved."""
    if not pinned:
        return {"ay": {"resolved": None, "route": None, "pinned": False},
                "clean": {"resolved": None, "route": None, "pinned": False}}
    return {
        tool: {"resolved": f"/fixture/pkg/store/{tool}/current/bin/{tool}", "route": "aterm-packaged",
               "pinned": True, "sha256": sha, "bytes": 7}
        for tool in ("ay", "clean")
    }


def dependency_record(resolves: bool = True, tree: str = "a" * 64, lock: str = "b" * 64) -> dict:
    """A scripts/dependency_identity.py record with one companion source."""
    return {
        "schema": "trust-cg-dependency-identity-v1", "lockfile_sha256": lock, "errors": [],
        "offline_ready": resolves,
        "sources": [{
            "url": "https://example.invalid/companion.git", "revision": "c" * 40,
            "database": {
                "path": "/fixture/db/companion", "present": True, "revision_resolves": resolves,
                "detail": "resolves" if resolves else "absent",
            },
            "checkout": {
                "path": "/fixture/checkouts/companion/ccccccc", "present": resolves, "cargo_ok": resolves,
                "head_matches": resolves, "modifications": [], "errors": [], "tree_sha256": tree if resolves else None,
            },
        }],
    }


# The unpatched lookup and audit (setUp stubs them for orchestration fixtures).
SELECTED_BUILD_TOOL = GATE.selected_build_tool
CARGO_CONFIG_RECORD = GATE.cargo_config_record


def cargo_config_record(problems: tuple[str, ...] = (), sha: str = "c" * 64) -> dict:
    """A cargo_config audit record: the committed repository config, and any problems."""
    return {
        "cwd": "/fixture", "cargo_home": "/fixture/.cargo", "environment": {},
        "files": [{"path": "/fixture/.cargo/config.toml", "sha256": sha, "bytes": 1,
                   "exempt": "the repository's committed config"}],
        "problems": list(problems),
    }


# The selected interpreter can live below "Application Support". A kernel
# shebang splits such a path; this shell/Python header execs the exact quoted
# interpreter and preserves the fixture argv. Python sees the exec as a string.
PYTHON_FIXTURE_HEADER = (
    "#!/bin/sh\n'''exec' " + shlex.quote(sys.executable) + ' "$0" "$@"\n' + "' '''\n"
)


class LinuxAarch64GateTests(unittest.TestCase):
    def setUp(self):
        # Orchestration fixtures mock provenance with a fake git; the Cargo
        # config audit is stubbed clean, and the Trust package's targo is not
        # looked up, unless a test replaces them.
        for name, value in (
            ("cargo_config_record", cargo_config_record()), ("selected_build_tool", "/fixture/pkg/bin/targo"),
        ):
            patcher = mock.patch.object(GATE, name, return_value=value)
            patcher.start()
            self.addCleanup(patcher.stop)

    def test_required_inventory_keeps_layout_hva_and_native_execution_targets(self):
        # The Linux floor has no source census (Darwin's census checks only
        # Linux rows missing from Darwin), so the bare count is what catches a
        # row silently dropped from TARGETS. Move it only with the row itself
        # (254: adds the geometry-only Storage native target; no old row
        # or denominator is removed).
        self.assertEqual(len(GATE.TARGETS), 254)
        self.assertIn(("trust-cg-codegen", "storage_geometry"), GATE.TARGETS)
        self.assertEqual(GATE.TARGET_MINIMUM_PASSES[("trust-cg-codegen", "storage_geometry")], 4)
        for target in ("aarch64_select_flags_across_call", "aarch64_unroll_trip_test_reader"):
            self.assertIn(("trust-cg-codegen", target), GATE.TARGETS)
            self.assertEqual(GATE.TARGET_MINIMUM_PASSES[("trust-cg-codegen", target)], 1)
        # LD-56: sited assertion delivery, a native-helper target, is required
        # on both floors at its file census (two tests).
        sited = ("trust-cg-codegen", "sited_assert_delivery_native")
        self.assertIn(sited, GATE.TARGETS)
        self.assertEqual(GATE.TARGET_MINIMUM_PASSES[sited], 2)
        # L10-P1: post-allocation value flow, pinned at its file census
        # (twenty-two tests); added from a Darwin host, not yet run on Linux.
        post_ra = ("trust-cg-codegen", "e2e_aarch64_post_ra_value_flow")
        self.assertIn(post_ra, GATE.TARGETS)
        self.assertEqual(GATE.TARGET_MINIMUM_PASSES[post_ra], 22)
        # L09-P3: composed transition records, pinned at their file census
        # (nine tests); added from a Darwin host, not yet run on Linux.
        composed = ("trust-cg-codegen", "e2e_aarch64_composed_transition")
        self.assertIn(composed, GATE.TARGETS)
        self.assertEqual(GATE.TARGET_MINIMUM_PASSES[composed], 9)
        self.assertIn(("trust-cg-verify", "bridge_copy_types"), GATE.TARGETS)
        # X-HOST-P13 second audit: the AY cache-root agreement target (one
        # test, so the default minimum of one executed pass).
        self.assertIn(("trust-cg-verify", "ay_cache_root_agreement"), GATE.TARGETS)
        self.assertEqual(GATE.target_minimum_passes("trust-cg-verify", "ay_cache_root_agreement"), 1)
        # L07-P2: the memory-effect binding and the corpus decomposition,
        # pinned at their file census; added from a Darwin host.
        for package, target, minimum in (
            ("trust-cg-codegen", "aarch64_memory_effect_binding", 4),
            ("trust-cg-codegen", "aarch64_nounwind_tail_frame", 2),
            ("trust-cg-codegen", "a64_refine_byte_invariance", 6),
            ("trust-cg-verify", "aarch64_memory_effect_queries", 2),
            # L03-P3: the memory-order mapping, pinned at its Linux file
            # census; added from a Darwin host.
            ("trust-cg-codegen", "aarch64_memory_order_obligations", 4),
            # L04-P6: the live NEON silicon differential and the vector
            # admission differential, not yet run here.
            ("trust-cg-verify", "aarch64_neon_silicon_differential", 11),
            ("trust-cg-codegen", "e2e_aarch64_neon_admission", 3),
            # L04-P3: the scalar FP IEEE 754 differentials, not yet run here.
            ("trust-cg-verify", "aarch64_fp_ieee_differential", 10),
            ("trust-cg-codegen", "e2e_aarch64_fp_ieee_lowering", 5),
            # L04-P1 / X-OPCODES-P2: the atomic and scalar memory-effect
            # silicon differentials, not yet run here.
            ("trust-cg-verify", "aarch64_atomic_silicon_differential", 2),
            ("trust-cg-verify", "aarch64_scalar_memory_silicon_differential", 1),
            # L04-P1: the CRC32/CRC32C silicon differential, not yet run here.
            ("trust-cg-verify", "aarch64_crc32_silicon_differential", 2),
            # L04-P1: the SUBS #imm silicon differential, not yet run here.
            ("trust-cg-verify", "aarch64_subs_imm_silicon_differential", 2),
            # L04-P1: the NEON LD1/ST1 form-theorem silicon differential, not
            # yet run here.
            ("trust-cg-verify", "aarch64_neon_structure_silicon_differential", 2),
            # L04-P12: the trap-expansion binding; added from a Darwin host.
            ("trust-cg-codegen", "aarch64_trap_expansion_binding", 4),
            # X-LEAN-P3: the Lean A64 golden corpus binding; added from a
            # Darwin host.
            ("trust-cg-codegen", "lean_a64_encode_golden_binding", 4),
            ("trust-cg-codegen", "aarch64_memory_source_binding", 4),
            # L10-P5: the identity-admission controls, added from a Darwin host.
            ("trust-cg-opt", "mach_id_admission", 6),
            ("trust-cg-codegen", "mach_id_admission_property", 5),
            # L11-P2: the installed-artifact replay through the public API;
            # added from a Darwin host.
            ("trust-cg-codegen", "jit_installed_artifact_replay", 3),
            # L04-P12: the trap-guard obligations, pinned at their file census.
            ("trust-cg-verify", "aarch64_trap_guard_obligations", 22),
        ):
            self.assertIn((package, target), GATE.TARGETS)
            self.assertEqual(GATE.TARGET_MINIMUM_PASSES[(package, target)], minimum)
        # L02-P14 includes both Linux native comparisons. The two ABI
        # targets still have only their host-neutral rows on Linux.
        for target, minimum in (("c_string_escapes_e2e", 4), ("sret_abi_e2e", 2), ("int_ext_abi_e2e", 2)):
            self.assertIn(("trust-cg-llvm-import", target), GATE.TARGETS)
            self.assertEqual(GATE.TARGET_MINIMUM_PASSES[("trust-cg-llvm-import", target)], minimum)
            self.assertEqual(GATE.TARGET_FEATURES[("trust-cg-llvm-import", target)], ("driver",))
        # L05-P7: the corpus round-trip gate and the construct property
        # generator, host-neutral, pinned at their file census.
        for target, minimum in (("trust_ir_corpus_roundtrip", 4), ("tmbc_roundtrip_prop", 6)):
            self.assertIn(("trust-cg-codegen", target), GATE.TARGETS)
            self.assertEqual(GATE.TARGET_MINIMUM_PASSES[("trust-cg-codegen", target)], minimum)
        # L13-P7: every trust-cg-fuzz integration target (the differential JIT
        # harness) is in the floor, derived from the package's tests directory.
        self.assertEqual(
            {target for package, target in GATE.TARGETS if package == "trust-cg-fuzz"},
            {path.stem for path in (ROOT / "crates" / "trust-cg-fuzz" / "tests").glob("*.rs")},
        )
        for package, target in GATE.TARGETS:
            self.assertTrue((ROOT / "crates" / package / "tests" / f"{target}.rs").is_file())

    def test_feature_gated_importer_targets_are_built_with_their_driver_feature(self):
        self.assertEqual(GATE.feature_problems(), [])
        importer = [row for row in GATE.TARGETS if row[0] == "trust-cg-llvm-import"]
        self.assertIn(("trust-cg-llvm-import", "bitreverse_intrinsics"), importer)
        for package, target in importer:
            self.assertEqual(GATE.target_features(package, target), ("driver",))
            self.assertEqual(GATE.feature_arguments(package, target), ["--features", "driver"])
        self.assertEqual(set(GATE.TARGET_FEATURES), set(importer))
        # A default feature covers its own file-level gate (codegen's `verify`).
        self.assertIn("verify", GATE.enabled_features("trust-cg-codegen", ()))
        self.assertEqual(GATE.target_features("trust-cg-codegen", "e2e_aarch64_exclusive_status_linux"), ())
        self.assertEqual(GATE.feature_arguments("trust-cg-codegen", "e2e_aarch64_link_runtime"), [])

    def test_feature_problems_refuse_uncovered_gates_and_stale_or_malformed_entries(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            tests = root / "crates" / "pkg" / "tests"
            tests.mkdir(parents=True)
            (root / "crates" / "pkg" / "Cargo.toml").write_text(
                '[package]\nname = "pkg"\n\n[features]\n# comment\ndefault = ["base"]\n'
                'base = ["inner"]\ninner = []\ndriver = [\n    "dep:other",\n]\n\n[dependencies]\n'
            )
            (tests / "gated.rs").write_text('#![cfg(feature = "driver")]\n#[test]\nfn t() {}\n')
            (tests / "default_gated.rs").write_text('#![cfg(feature = "inner")]\n#[test]\nfn t() {}\n')
            (tests / "plain.rs").write_text("#[test]\nfn t() {}\n")
            rows = (("pkg", "gated"), ("pkg", "default_gated"), ("pkg", "plain"))
            self.assertEqual(GATE.package_features("pkg", root)["driver"], ("dep:other",))
            self.assertEqual(GATE.enabled_features("pkg", (), root), {"default", "base", "inner"})
            cases = {
                "neither a default feature nor in TARGET_FEATURES": {},
                "names no required target": {("pkg", "gated"): ("driver",), ("pkg", "gone"): ("driver",)},
                "are not declared by pkg": {("pkg", "gated"): ("driver", "missing")},
                "nonempty tuple of distinct feature names": {("pkg", "gated"): ()},
            }
            for message, table in cases.items():
                with self.subTest(message=message), mock.patch.object(GATE, "TARGET_FEATURES", table):
                    problems = GATE.feature_problems(rows, root)
                    self.assertTrue(any(message in problem for problem in problems), problems)
            # The runner's pre-run check ignores entries for rows it does not run.
            stale = {("pkg", "gated"): ("driver",), ("pkg", "gone"): ("driver",)}
            with mock.patch.object(GATE, "TARGET_FEATURES", stale):
                self.assertEqual(GATE.feature_problems(rows, root, stale_entries=False), [])
            with mock.patch.object(GATE, "TARGET_FEATURES", {("pkg", "gated"): ("driver",)}):
                self.assertEqual(GATE.feature_problems(rows, root), [])

    def test_three_linker_targets_run_with_lld_and_gold_required(self):
        # L02-P10 ninth closure audit: the native legs through GNU ld, gold and
        # LLD must fail, not print SKIP, when LLD or gold is missing.
        self.assertEqual(GATE.environment_problems(), [])
        both = {"TCG_REQUIRE_LLD": "1", "TCG_REQUIRE_GOLD": "1"}
        for row in (("trust-cg-codegen", "e2e_aarch64_link_runtime"), ("trust-cg-cli", "link_options")):
            self.assertIn(row, GATE.TARGETS)
            self.assertEqual(GATE.target_environment(*row), both)
        # L02-P6 fifth closure audit: the relocation-model LLD legs are required.
        self.assertEqual(
            GATE.target_environment("trust-cg-codegen", "e2e_aarch64_elf_relocation_model"),
            {"TCG_REQUIRE_LLD": "1"},
        )
        for row in GATE.TARGET_ENVIRONMENT:
            self.assertIn(row, GATE.TARGETS)
        self.assertEqual(GATE.target_environment("trust-cg-codegen", "e2e_aarch64_switch"), {})
        # The LLVM importer's symbol linkage row also runs its llc twin legs,
        # which must fail, not print SKIP, when no llc is found.
        self.assertEqual(
            GATE.target_environment("trust-cg-llvm-import", "symbol_linkage_elf"),
            {**both, "TCG_REQUIRE_LLC": "1"},
        )
        self.assertEqual(
            GATE.target_environment("trust-cg-llvm-import", "c_string_escapes_e2e"),
            {**both, "TCG_REQUIRE_LLC": "1"},
        )
        # A caller cannot change the table through what it was handed.
        GATE.target_environment("trust-cg-cli", "link_options")["TCG_REQUIRE_LLD"] = "0"
        self.assertEqual(GATE.target_environment("trust-cg-cli", "link_options"), both)
        # The x86-64 twin runs none of them and sets no environment.
        spec = importlib.util.spec_from_file_location("check_linux_x86_64", ROOT / "scripts" / "check_linux_x86_64.py")
        twin = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(twin)
        self.assertEqual(twin.SHARED.TARGET_ENVIRONMENT, {})
        self.assertEqual(twin.SHARED.environment_problems(), [])

    def test_environment_problems_refuse_stale_malformed_and_unread_entries(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            tests = root / "crates" / "pkg" / "tests"
            tests.mkdir(parents=True)
            (tests / "native.rs").write_text(
                '#[test]\nfn t() { assert!(std::env::var_os("TCG_REQUIRE_LLD").is_none()); }\n'
            )
            rows = (("pkg", "native"),)
            cases = {
                "names no required target": {("pkg", "native"): {"TCG_REQUIRE_LLD": "1"}, ("pkg", "gone"): {"TCG_REQUIRE_LLD": "1"}},
                "is not read by crates/pkg/tests/native.rs": {("pkg", "native"): {"TCG_REQUIRE_GOLD": "1"}},
                "is not a TCG_REQUIRE_<NAME>=1 requirement": {("pkg", "native"): {"TCG_REQUIRE_LLD": "0"}},
                "'PATH'='/x' is not": {("pkg", "native"): {"PATH": "/x"}},
                "environment must be a nonempty mapping": {("pkg", "native"): {}},
            }
            for message, table in cases.items():
                with self.subTest(message=message), mock.patch.object(GATE, "TARGET_ENVIRONMENT", table):
                    problems = GATE.environment_problems(rows, root)
                    self.assertTrue(any(message in problem for problem in problems), problems)
            stale = {("pkg", "native"): {"TCG_REQUIRE_LLD": "1"}, ("pkg", "gone"): {"TCG_REQUIRE_LLD": "1"}}
            with mock.patch.object(GATE, "TARGET_ENVIRONMENT", stale):
                self.assertEqual(GATE.environment_problems(rows, root, stale_entries=False), [])
            with mock.patch.object(GATE, "TARGET_ENVIRONMENT", {("pkg", "native"): {"TCG_REQUIRE_LLD": "1"}}):
                self.assertEqual(GATE.environment_problems(rows, root), [])

    def test_environment_reaches_only_its_own_target_and_is_recorded(self):
        # The requirement reaches the second target's test executable through
        # the Cargo target runner, and never the build tool's own process,
        # whose compiler refuses TCG_* variables.
        with tempfile.TemporaryDirectory() as temp:
            seen = Path(temp) / "cargo-environment"
            fixture = Path(temp) / "cargo-fixture"
            fixture.write_text(
                f"{PYTHON_FIXTURE_HEADER}"
                "import json, os, sys\n"
                "target = sys.argv[sys.argv.index('--test') + 1]\n"
                "runner = [json.loads(arg.split('=', 1)[1]) for arg in sys.argv if arg.startswith('target.')]\n"
                f"open({str(seen)!r}, 'a').write(json.dumps([target, os.environ.get('TCG_REQUIRE_LLD'), runner]) + '\\n')\n"
                f"print({transcript()!r})\n"
            )
            fixture.chmod(0o700)
            output = Path(temp) / "results"
            provenance = {
                "source_sha": "fixture-source", "dirty": False, "git_status": [],
                "tools": {"targo": str(fixture), "env": "/usr/bin/env", "git": "fixture-git"}, "host": GATE.HOST,
                "source_fingerprint": "fixture-fingerprint", **trust_lane_provenance(str(fixture)),
            }
            rows = (("fixture", "first"), ("fixture", "second"))
            with mock.patch.object(GATE, "TARGETS", rows), \
                    mock.patch.object(GATE, "TARGET_ENVIRONMENT", {("fixture", "second"): {"TCG_REQUIRE_LLD": "1"}}), \
                    mock.patch.object(GATE, "environment_problems", return_value=[]), \
                    mock.patch.object(GATE, "feature_problems", return_value=[]), \
                    mock.patch.object(GATE, "preflight", return_value=provenance), \
                    mock.patch.object(GATE, "source_provenance", return_value=provenance), \
                    mock.patch.object(GATE, "dependency_identity", return_value=dependency_record()), \
                    mock.patch.object(GATE, "proof_tool_identities", return_value=proof_tool_record()), \
                    mock.patch.dict(os.environ, {}, clear=False), \
                    contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                os.environ.pop("TCG_REQUIRE_LLD", None)
                code = GATE.main(["--out", str(output), "--timeout-seconds", "5"])
                self.assertNotIn("TCG_REQUIRE_LLD", os.environ)
            report = json.loads((output / "report.json").read_text())
            first, second = (json.loads(line) for line in seen.read_text().splitlines())
        self.assertEqual(code, 0)
        self.assertEqual(first, ["first", None, []])
        self.assertEqual(second, ["second", None, [["/usr/bin/env", "TCG_REQUIRE_LLD=1"]]])
        self.assertEqual(report["required_target_environment"], {"fixture/second": {"TCG_REQUIRE_LLD": "1"}})
        self.assertEqual([row["environment"] for row in report["targets"]], [{}, {"TCG_REQUIRE_LLD": "1"}])
        self.assertEqual([row["set_environment"] for row in report["targets"]], [{}, {}])

    def test_environment_problems_refuse_the_run_before_any_target(self):
        with tempfile.TemporaryDirectory() as temp, \
                mock.patch.object(GATE, "environment_problems", return_value=["pkg/t: fixture problem"]):
            code, report, _, marker = self.run_main_with_fixture(temp, {})
        self.assertEqual(code, 1)
        self.assertEqual(report["status"], "fail")
        self.assertFalse(marker.exists(), "a malformed environment table must not run Cargo")
        self.assertIn("required target environment: pkg/t: fixture problem", report["errors"])

    def test_features_reach_only_their_own_target_and_are_recorded(self):
        with tempfile.TemporaryDirectory() as temp:
            arguments = Path(temp) / "cargo-arguments"
            fixture = Path(temp) / "cargo-fixture"
            fixture.write_text(
                f"{PYTHON_FIXTURE_HEADER}"
                "import sys\n"
                f"open({str(arguments)!r}, 'a').write(' '.join(sys.argv[1:]) + '\\n')\n"
                f"print({transcript()!r})\n"
            )
            fixture.chmod(0o700)
            output = Path(temp) / "results"
            provenance = {
                "source_sha": "fixture-source", "dirty": False, "git_status": [],
                "tools": {"targo": str(fixture), "env": "/usr/bin/env", "git": "fixture-git"}, "host": GATE.HOST,
                "source_fingerprint": "fixture-fingerprint", **trust_lane_provenance(str(fixture)),
            }
            rows = (("fixture", "first"), ("fixture", "second"))
            with mock.patch.object(GATE, "TARGETS", rows), \
                    mock.patch.object(GATE, "TARGET_FEATURES", {("fixture", "second"): ("driver",)}), \
                    mock.patch.object(GATE, "feature_problems", return_value=[]), \
                    mock.patch.object(GATE, "preflight", return_value=provenance), \
                    mock.patch.object(GATE, "source_provenance", return_value=provenance), \
                    mock.patch.object(GATE, "dependency_identity", return_value=dependency_record()), \
                    mock.patch.object(GATE, "proof_tool_identities", return_value=proof_tool_record()), \
                    contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                code = GATE.main(["--out", str(output), "--timeout-seconds", "5"])
            report = json.loads((output / "report.json").read_text())
            first, second = arguments.read_text().splitlines()
        self.assertEqual(code, 0)
        self.assertNotIn("--features", first.split())
        self.assertIn("-p fixture --features driver --test second --", second)
        self.assertEqual(report["required_target_features"], {"fixture/second": ["driver"]})
        self.assertEqual([row["features"] for row in report["targets"]], [[], ["driver"]])

    def test_feature_problems_refuse_the_run_before_any_target(self):
        with tempfile.TemporaryDirectory() as temp, \
                mock.patch.object(GATE, "feature_problems", return_value=["pkg/t: fixture problem"]):
            code, report, _, marker = self.run_main_with_fixture(temp, {})
        self.assertEqual(code, 1)
        self.assertEqual(report["status"], "fail")
        self.assertFalse(marker.exists(), "an uncovered feature gate must not run Cargo")
        self.assertIn("required target features: pkg/t: fixture problem", report["errors"])

    def test_list_names_each_targets_features(self):
        stdout = io.StringIO()
        with mock.patch.object(GATE, "preflight", side_effect=AssertionError("probed")), \
                contextlib.redirect_stdout(stdout):
            self.assertEqual(GATE.main(["--list"]), 0)
        lines = stdout.getvalue().splitlines()
        self.assertEqual(len(lines), len(GATE.TARGETS))
        self.assertIn("trust-cg-llvm-import cast_e2e --features driver", lines)
        self.assertIn("trust-cg-codegen e2e_aarch64_link_runtime TCG_REQUIRE_GOLD=1 TCG_REQUIRE_LLD=1", lines)
        self.assertIn("trust-cg-cli link_options TCG_REQUIRE_GOLD=1 TCG_REQUIRE_LLD=1", lines)
        self.assertIn("trust-cg-codegen e2e_aarch64_switch", lines)

    def run_fixture(self, source, timeout=5):
        with tempfile.TemporaryDirectory() as temp:
            result = GATE.run_target(
                [sys.executable, "-c", source], Path(temp) / "fixture.log", timeout,
                root=ROOT, grace_seconds=0.05,
            )
            retained = (Path(temp) / "fixture.log").read_text()
        return result, retained

    def test_real_fixture_process_accepts_complete_positive_execution(self):
        result, retained = self.run_fixture(f"print({transcript(3)!r})")
        self.assertEqual(result["status"], "pass", result)
        self.assertEqual(result["counts"]["passed"], 3)
        self.assertIn("3 passed", retained)
        self.assertEqual(len(result["log_sha256"]), 64)

    def test_real_process_failures_are_not_laundered_by_a_green_summary(self):
        skipped = transcript(1, prefix="SKIP: native host unavailable\n")
        cases = (
            (f"print({transcript()!r}); raise SystemExit(7)", 7),
            ("print('running 1 test'); raise SystemExit(0)", 0),
            ("print('compiler unavailable'); raise SystemExit(0)", 0),
            (f"print({transcript(0)!r})", 0),
            (f"print({transcript(1, ignored=1)!r})", 0),
            (f"print({transcript(1, filtered=2)!r})", 0),
            (f"print({skipped!r})", 0),
        )
        for source, code in cases:
            with self.subTest(source=source):
                result, _ = self.run_fixture(source)
                self.assertEqual(result["status"], "fail", result)
                self.assertEqual(result["returncode"], code)

    def test_ambient_proptest_controls_never_reach_a_target(self):
        # An ambient PROPTEST_CASES=1 would silently shrink every panic-fuzz
        # family to one case; every target runs without PROPTEST_*.
        source = (
            "import os\n"
            "leaked = sorted(name for name in os.environ if name.startswith('PROPTEST_'))\n"
            f"print({transcript(1)!r} if not leaked else 'leaked ' + ' '.join(leaked))\n"
        )
        ambient = {"PROPTEST_CASES": "1", "PROPTEST_RNG_SEED": "7", "PROPTEST_MAX_SHRINK_ITERS": "0"}
        with mock.patch.dict(os.environ, ambient):
            result, retained = self.run_fixture(source)
            self.assertEqual(GATE.scrubbed_environment(os.environ), sorted(ambient))
        self.assertEqual(result["status"], "pass", retained)
        self.assertEqual(result["scrubbed_environment"], sorted(ambient))
        self.assertNotIn("leaked", retained)
        # A name merely containing the prefix elsewhere is not a proptest control.
        self.assertEqual(GATE.scrubbed_environment({"NOT_PROPTEST_CASES": "1", "PATH": "/bin"}), [])

    def test_variables_cargo_sets_for_its_children_never_reach_a_target(self):
        # An ambient CARGO_FEATURE_* Cargo does not overwrite would reach build
        # scripts; config variables stay (the audit refuses the bad ones).
        children = {
            "CARGO_FEATURE_NEGATIVE_CONTROL": "1", "CARGO_PKG_NAME": "x", "CARGO_MANIFEST_DIR": "/x",
            "CARGO_MAKEFLAGS": "-j1", "CARGO_CFG_TARGET_OS": "linux", "TARGO_PKG_NAME": "x",
        }
        kept = {"CARGO_TARGET_DIR": "/t", "CARGO_HOME": "/h", "TARGO_HOME": "/h"}
        self.assertEqual(GATE.scrubbed_environment({**children, **kept, "PATH": "/bin"}), sorted(children))
        source = (
            "import os\n"
            "leaked = sorted(name for name in os.environ if name.startswith(('CARGO_FEATURE_', 'CARGO_PKG_')))\n"
            f"print({transcript(1)!r} if not leaked else 'leaked ' + ' '.join(leaked))\n"
        )
        with mock.patch.dict(os.environ, children):
            result, retained = self.run_fixture(source)
        self.assertEqual(result["status"], "pass", retained)
        self.assertEqual(result["scrubbed_environment"], sorted(children))

    def test_fixture_timeout_uses_shared_process_group_runner(self):
        result, retained = self.run_fixture("import time; time.sleep(60)", timeout=0.1)
        self.assertEqual(result["returncode"], 124)
        self.assertEqual(result["status"], "fail")
        self.assertIn("command exceeded", retained)

    def test_checker_overrides_are_isolated_only_for_pure_planning(self):
        overrides = {
            "TCG_EXTERNAL_CLEAN_CHECKER": "/fixture/checker",
            "TCG_CLEAN_CHECKER": "/fixture/legacy-checker",
            "AY_SOLVER_PATH": "/fixture/solver",
            "TCG_UNKNOWN_CONTROL_TEST": "must-still-reach-admission",
        }
        for target in ("core_jit_planning", "jit_fail_closed_proof_policy"):
            with self.subTest(target=target), tempfile.TemporaryDirectory() as temp:
                removed = GATE.target_unset_environment("trust-cg-codegen", target)
                expected = {key: value for key, value in overrides.items() if key not in removed}
                fixture = (
                    "import os; "
                    f"assert {{key: os.environ[key] for key in {list(overrides)!r} "
                    f"if key in os.environ}} == {expected!r}; print({transcript()!r})"
                )
                with mock.patch.dict(os.environ, overrides):
                    result = GATE.run_target(
                        [sys.executable, "-c", fixture], Path(temp) / "fixture.log", 5,
                        unset_environment=removed,
                    )
                    self.assertEqual(os.environ["TCG_EXTERNAL_CLEAN_CHECKER"], overrides["TCG_EXTERNAL_CLEAN_CHECKER"])
                self.assertEqual(result["status"], "pass", result)
                self.assertEqual(result["unset_environment"], list(removed))
                self.assertEqual(bool(removed), target == "core_jit_planning")
        self.assertEqual(GATE.target_unset_environment("another-package", "core_jit_planning"), ())

    def test_set_environment_reaches_the_child_over_unset_and_ambient_values(self):
        fixture = (
            "import os; "
            "assert os.environ['TCG_REQUIRE_LLD'] == '1', os.environ.get('TCG_REQUIRE_LLD'); "
            "assert 'TCG_REQUIRE_GOLD' not in os.environ; "
            f"print({transcript()!r})"
        )
        with tempfile.TemporaryDirectory() as temp, \
                mock.patch.dict(os.environ, {"TCG_REQUIRE_LLD": "0", "TCG_REQUIRE_GOLD": "1"}):
            result = GATE.run_target(
                [sys.executable, "-c", fixture], Path(temp) / "fixture.log", 5,
                unset_environment=("TCG_REQUIRE_GOLD", "TCG_REQUIRE_LLD"),
                set_environment={"TCG_REQUIRE_LLD": "1"},
            )
            self.assertEqual(os.environ["TCG_REQUIRE_LLD"], "0")
        self.assertEqual(result["status"], "pass", result)
        self.assertEqual(result["set_environment"], {"TCG_REQUIRE_LLD": "1"})

    def test_missing_executable_and_signal_are_failures(self):
        result, _ = self.run_fixture("import os, signal; os.kill(os.getpid(), signal.SIGTERM)")
        self.assertEqual(result["status"], "fail")
        self.assertEqual(result["returncode"], 143)
        with tempfile.TemporaryDirectory() as temp:
            result = GATE.run_target(
                [str(Path(temp) / "absent")], Path(temp) / "missing.log", 5,
                grace_seconds=0.05,
            )
        self.assertEqual(result["returncode"], 127)
        self.assertEqual(result["status"], "fail")

    @unittest.skipUnless(sys.platform == "linux", "Linux process cleanup control")
    def test_cancelling_gate_cleans_up_signal_resistant_command(self):
        for signum in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
            with self.subTest(signal=signum), tempfile.TemporaryDirectory() as temp:
                ready = Path(temp) / "ready"
                log = Path(temp) / "command.log"
                command = (
                    "import os, signal, time; from pathlib import Path; "
                    "signal.signal(signal.SIGINT, signal.SIG_IGN); "
                    "signal.signal(signal.SIGTERM, signal.SIG_IGN); "
                    "signal.signal(signal.SIGHUP, signal.SIG_IGN); "
                    f"Path({str(ready)!r}).write_text(str(os.getpid())); time.sleep(60)"
                )
                runner = (
                    "import json, runpy, sys; from pathlib import Path; "
                    f"gate=runpy.run_path({str(SCRIPT)!r}); "
                    f"result=gate['run_target']([sys.executable, '-c', {command!r}], "
                    f"Path({str(log)!r}), 60, grace_seconds=0.05); "
                    "print(json.dumps(result)); sys.exit(1 if result['status']=='fail' else 0)"
                )
                supervisor = subprocess.Popen(
                    [sys.executable, "-c", runner], stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE, text=True, start_new_session=True,
                )
                child = None
                try:
                    deadline = time.monotonic() + 5
                    while not ready.exists() and time.monotonic() < deadline:
                        time.sleep(0.02)
                    self.assertTrue(ready.exists(), "command never reached signal-ready state")
                    child = int(ready.read_text())
                    supervisor.send_signal(signum)
                    stdout, stderr = supervisor.communicate(timeout=5)
                    self.assertEqual(supervisor.returncode, 1, stderr)
                    result = json.loads(stdout)
                    self.assertEqual(result["interrupted_signal"], signum)
                    self.assertEqual(result["status"], "fail")
                    self.assertFalse(Path(f"/proc/{child}").exists(), "command survived cancellation")
                finally:
                    if supervisor.poll() is None:
                        supervisor.kill()
                        supervisor.communicate(timeout=5)
                    if child is not None and Path(f"/proc/{child}").exists():
                        os.killpg(child, signal.SIGKILL)

    def test_rejects_mismatched_or_duplicated_suite_and_inline_skip(self):
        for text in (
            transcript(1, started=2),
            transcript() + transcript(),
            transcript(prefix="test native ... skipping: cc unavailable\n"),
            transcript(prefix="[SKIP] missing target\n"),
            transcript(1, failed=1),
        ):
            with self.subTest(text=text):
                self.assertEqual(GATE.classify_result(0, text)["status"], "fail")

    def test_pinned_minimum_passes_fail_a_shrunken_suite(self):
        self.assertEqual(GATE.minimum_problems(), [])
        self.assertEqual(GATE.target_minimum_passes("trust-cg-verify", "aarch64_scalar_cell_link"), 7)
        self.assertEqual(GATE.target_minimum_passes("trust-cg-codegen", "flat_gep_semantics"), 14)
        self.assertEqual(GATE.target_minimum_passes("trust-cg-codegen", "e2e_aarch64_switch"), 3)
        self.assertEqual(GATE.target_minimum_passes("trust-cg-codegen", "e2e_aarch64_indirect_call"), 2)
        self.assertEqual(GATE.target_minimum_passes("trust-cg-codegen", "aarch64_elf_symbol_binding"), 83)
        self.assertEqual(GATE.target_minimum_passes("trust-cg-codegen", "v41_abi_residue_objects"), 18)
        self.assertEqual(GATE.target_minimum_passes("trust-cg-llvm-import", "symbol_linkage_elf"), 31)
        self.assertEqual(GATE.target_minimum_passes("trust-cg-codegen", "e2e_aarch64_elf_relocation_model"), 21)
        # X-DARWIN-P7's Darwin-only campaign is not a Linux floor target: the
        # host matrix requires every native Linux-floor file to run natively
        # on Linux (scripts/native_test_host_matrix.py).
        self.assertNotIn(("trust-cg-codegen", "e2e_aarch64_eh_raii_darwin"), GATE.TARGETS)
        # L13-P7: every fuzz family row is pinned at its Linux test census.
        fuzz_rows = [
            row for row in GATE.TARGETS if row[0] == "trust-cg-fuzz" or row[1].startswith("panic_fuzz_")
        ]
        self.assertEqual(len(fuzz_rows), 35)
        self.assertTrue(set(fuzz_rows) <= set(GATE.TARGET_MINIMUM_PASSES))
        self.assertEqual(sum(GATE.target_minimum_passes(*row) for row in fuzz_rows), 259)
        self.assertEqual(GATE.target_minimum_passes("trust-cg-codegen", "panic_fuzz_compile_x86_64"), 3)
        self.assertEqual(GATE.target_minimum_passes("trust-cg-fuzz", "sweep3_wide_shifts_bitops"), 39)
        self.assertEqual(GATE.target_minimum_passes("trust-cg-lower", "aarch64_variadic_abi"), 1)
        for package, target in GATE.TARGET_MINIMUM_PASSES:
            self.assertIn((package, target), GATE.TARGETS)
        result = GATE.classify_result(0, transcript(3), minimum=3)
        self.assertEqual(result["status"], "pass", result)
        self.assertEqual(result["minimum"], 3)
        result = GATE.classify_result(0, transcript(2), minimum=3)
        self.assertEqual(result["status"], "fail", result)
        self.assertTrue(any("below the required minimum 3" in error for error in result["errors"]), result)
        # The old two host-neutral C-string passes cannot stand in for the
        # newly required native Linux comparisons.
        minimum = GATE.target_minimum_passes("trust-cg-llvm-import", "c_string_escapes_e2e")
        self.assertEqual(GATE.classify_result(0, transcript(2), minimum=minimum)["status"], "fail")
        self.assertEqual(GATE.classify_result(0, transcript(4), minimum=minimum)["status"], "pass")
        # The default keeps the one-pass floor for every unpinned target.
        self.assertEqual(GATE.classify_result(0, transcript(1))["minimum"], 1)
        self.assertEqual(GATE.classify_result(0, transcript(0))["status"], "fail")

    def test_minimum_problems_refuse_stale_malformed_and_overstated_entries(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            tests = root / "crates" / "pkg" / "tests"
            tests.mkdir(parents=True)
            (tests / "two.rs").write_text("#[test]\nfn a() {}\n#[test]\nfn b() {}\n")
            rows = (("pkg", "two"),)
            cases = {
                "names no required target": {("pkg", "two"): 2, ("pkg", "gone"): 1},
                "minimum must be a positive integer": {("pkg", "two"): 0},
                "minimum 3 exceeds its #[test] functions": {("pkg", "two"): 3},
            }
            for message, table in cases.items():
                with self.subTest(message=message), mock.patch.object(GATE, "TARGET_MINIMUM_PASSES", table):
                    problems = GATE.minimum_problems(rows, root)
                    self.assertTrue(any(message in problem for problem in problems), problems)
            # The runner's pre-run check ignores entries for rows it does not run.
            stale = {("pkg", "two"): 2, ("pkg", "gone"): 1}
            with mock.patch.object(GATE, "TARGET_MINIMUM_PASSES", stale):
                self.assertEqual(GATE.minimum_problems(rows, root, stale_entries=False), [])
            with mock.patch.object(GATE, "TARGET_MINIMUM_PASSES", {("pkg", "two"): 2}):
                self.assertEqual(GATE.minimum_problems(rows, root), [])

    def test_opcode_inventory_skip_labels_are_not_runtime_skips(self):
        result = GATE.classify_result(0, transcript(3, prefix=INVENTORY_EXCERPT))
        self.assertEqual(result["status"], "pass", result)
        self.assertEqual(result["inventory_skip_labels"], 3)
        self.assertEqual(GATE.classify_result(0, transcript(1))["inventory_skip_labels"], 0)

    def test_retained_coverage_inventory_that_was_misclassified_now_passes(self):
        # The 2026-09-17 arithmetic report's external wrapper classified this
        # exact complete, 40-pass run as a runtime skip because of its 28
        # pseudo/trap inventory rows. Classify it exactly as that wrapper did.
        # Moved byte for byte from reports/perf/2026-09-17-source-bound-arithmetic/
        # records/; scripts/tests/fixtures/linux_aarch64_gate/README.md.
        records = ROOT / (
            "scripts/tests/fixtures/linux_aarch64_gate/"
            "source-bound-alu-boundary-regressions-second"
        )
        stdout = gzip.decompress((records / "coverage_gate_tests.stdout.log.gz").read_bytes())
        stderr = gzip.decompress((records / "coverage_gate_tests.stderr.log.gz").read_bytes())
        retained = (stdout + stderr).decode("utf-8", errors="replace")
        self.assertIn("  [skip    ] AArch64::Phi ", retained)
        result = GATE.classify_result(0, retained)
        self.assertEqual(result["status"], "pass", result)
        self.assertEqual(result["counts"]["passed"], 40)
        self.assertEqual(result["inventory_skip_labels"], 28)

    def test_runtime_skips_still_fail_beside_or_disguised_as_inventory_labels(self):
        label = "  [skip    ] AArch64::Phi                     pseudo/trap — no equivalence proof obligation"
        for text in (
            INVENTORY_EXCERPT + "SKIP: native host unavailable\n",
            INVENTORY_EXCERPT + "test native ... skipped\n",
            "[skip] AArch64::Phi pseudo/trap — no equivalence proof obligation\n",
            label.replace("[skip ", "[SKIP ") + "\n",
            label + "; SKIP: cc unavailable\n",
            label.replace("AArch64::Phi", "native execution") + "\n",
            "  [skip    ] AArch64::Phi                     native toolchain unavailable\n",
            "test native ... " + label + "\n",
            "  [skip] missing target\n",
        ):
            with self.subTest(text=text):
                result = GATE.classify_result(0, transcript(3, prefix=text))
                self.assertEqual(result["status"], "fail", result)
                self.assertTrue(any(
                    error.startswith("explicit skipped execution in transcript: ")
                    for error in result["errors"]
                ), result)
        result = GATE.classify_result(0, transcript(3, prefix=INVENTORY_EXCERPT + "SKIP: native host unavailable\n"))
        self.assertIn("SKIP: native host unavailable", " ".join(result["errors"]))
        self.assertEqual(result["inventory_skip_labels"], 3)

    def test_resident_set_receipt_requires_one_within_ceiling_receipt(self):
        prefix = GATE.RSS_RECEIPT_PREFIX
        self.assertEqual(prefix, GATE.timeout_runner_module().RSS_RECEIPT)
        within = f"{prefix} ceiling_gib=16 peak_mib=2467 samples=48 outcome=within"
        receipt, errors = GATE.rss_receipt(f"noise\n{within}\n", 16.0)
        self.assertEqual(errors, [])
        self.assertEqual(receipt, {"ceiling_gib": 16.0, "sampled_peak_mib": 2467, "samples": 48, "outcome": "within"})
        _, errors = GATE.rss_receipt(within.replace("peak_mib=2467", "peak_mib=16384") + "\n", 16.0)
        self.assertEqual(errors, [])
        for text, expected in (
            ("no receipt\n", "exactly one"),
            (f"{within}\n{within}\n", "exactly one"),
            (f"{prefix} ceiling_gib=16 peak_mib=many samples=1 outcome=within\n", "malformed"),
            (f"{prefix} ceiling_gib=16 peak_mib=2 samples=1 outcome=ok\n", "malformed"),
            (within.replace("ceiling_gib=16", "ceiling_gib=32") + "\n", "differs from requested"),
            (within.replace("within", "exceeded") + "\n", "exceeded"),
            (within.replace("within", "unmeasurable") + "\n", "unmeasurable"),
            (within.replace("samples=48", "samples=0") + "\n", "no sample"),
            (within.replace("peak_mib=2467", "peak_mib=16385") + "\n", "peak above its ceiling"),
        ):
            with self.subTest(text=text):
                _, errors = GATE.rss_receipt(text, 16.0)
                self.assertTrue(any(expected in error for error in errors), errors)

    def test_ceiling_reaches_the_runner_and_its_receipt_is_retained(self):
        with tempfile.TemporaryDirectory() as temp:
            stub = Path(temp) / "runner.py"
            stub.write_text(
                "import subprocess, sys\n"
                "args = sys.argv[1:]\n"
                "at = args.index('--max-rss-gib')\n"
                "ceiling = float(args[at + 1])\n"
                "command = args[at + 3:]\n"
                "code = subprocess.call(command)\n"
                "print(f'run_with_timeout: RSS_RECEIPT ceiling_gib={ceiling:g} peak_mib=12 '\n"
                "      f'samples=3 outcome=within', file=sys.stderr)\n"
                "sys.exit(code)\n"
            )
            with mock.patch.object(GATE, "TIMEOUT_RUNNER", stub):
                result = GATE.run_target(
                    [sys.executable, "-c", f"print({transcript(2)!r})"], Path(temp) / "fixture.log", 5,
                    grace_seconds=0.05, max_rss_gib=16.0,
                )
                forged = GATE.run_target(
                    [sys.executable, "-c",
                     f"print({transcript(2)!r}); print('{GATE.RSS_RECEIPT_PREFIX} ceiling_gib=16 "
                     "peak_mib=1 samples=1 outcome=within')"],
                    Path(temp) / "forged.log", 5, grace_seconds=0.05, max_rss_gib=16.0,
                )
        self.assertEqual(result["status"], "pass", result)
        self.assertEqual(result["max_rss_gib"], 16.0)
        self.assertEqual(result["rss"]["sampled_peak_mib"], 12)
        self.assertIn("--max-rss-gib", result["bounded_command"])
        self.assertEqual(forged["status"], "fail", forged)
        self.assertIn("expected exactly one resident-set supervision receipt, observed 2", forged["errors"])
        without, _ = self.run_fixture(f"print({transcript(1)!r})")
        self.assertIsNone(without["rss"])
        self.assertNotIn("--max-rss-gib", without["bounded_command"])

    @unittest.skipIf(sys.platform == "linux", "hosts without /proc supervision")
    def test_real_runner_refuses_a_ceiling_it_cannot_enforce(self):
        with tempfile.TemporaryDirectory() as temp:
            marker = Path(temp) / "ran"
            result = GATE.run_target(
                [sys.executable, "-c", f"open({str(marker)!r}, 'w').close(); print({transcript()!r})"],
                Path(temp) / "fixture.log", 5, grace_seconds=0.05, max_rss_gib=4.0,
            )
            self.assertFalse(marker.exists(), "an unsupported ceiling must not run the command")
        self.assertEqual(result["returncode"], 125)
        self.assertEqual(result["status"], "fail")
        self.assertIn("expected exactly one resident-set supervision receipt, observed 0", result["errors"])

    @unittest.skipUnless(sys.platform == "linux", "Linux /proc resident-set supervision")
    def test_real_runner_enforces_the_ceiling_on_linux(self):
        with tempfile.TemporaryDirectory() as temp:
            within = GATE.run_target(
                [sys.executable, "-c", f"import time; time.sleep(0.5); print({transcript()!r})"],
                Path(temp) / "within.log", 30, grace_seconds=0.05, max_rss_gib=4.0,
            )
            exceeded = GATE.run_target(
                [sys.executable, "-c",
                 f"import time; data = b'\\x01' * (256 << 20); time.sleep(60); print({transcript()!r})"],
                Path(temp) / "exceeded.log", 60, grace_seconds=0.05, max_rss_gib=0.0625,
            )
        self.assertEqual(within["status"], "pass", within)
        self.assertEqual(within["rss"]["outcome"], "within")
        self.assertGreaterEqual(within["rss"]["samples"], 1)
        self.assertEqual(exceeded["returncode"], 122)
        self.assertEqual(exceeded["status"], "fail")
        self.assertEqual(exceeded["rss"]["outcome"], "exceeded")
        self.assertLess(exceeded["elapsed_seconds"], 30)

    def test_list_is_read_only_and_does_not_probe_tools(self):
        with mock.patch.object(GATE, "preflight", side_effect=AssertionError("probed")):
            with mock.patch.object(GATE.tempfile, "mkdtemp", side_effect=AssertionError("wrote")):
                self.assertEqual(GATE.main(["--list"]), 0)

    def test_existing_output_is_preserved(self):
        with tempfile.TemporaryDirectory() as temp:
            marker = Path(temp) / "report.json"
            marker.write_text("existing evidence")
            self.assertEqual(GATE.main(["--out", temp]), 1)
            self.assertEqual(marker.read_text(), "existing evidence")

    def test_preflight_error_is_retained_and_cannot_pass(self):
        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp) / "new"
            with mock.patch.object(GATE, "preflight", side_effect=RuntimeError("required tool is missing: cc")):
                self.assertEqual(GATE.main(["--out", str(output)]), 1)
            report = json.loads((output / "report.json").read_text())
        self.assertEqual(report["status"], "fail")
        self.assertEqual(report["targets"], [])
        self.assertIn("required tool is missing: cc", report["errors"])

    def host_tools_fixture(self, root: Path) -> Path:
        """cc, c++ and readelf stand-ins, so preflight reaches its Trust and
        llc checks on any development host."""
        tools = root.resolve() / "host-tools"
        tools.mkdir()
        for name in ("cc", "c++", "readelf"):
            (tools / name).write_text(f"{PYTHON_FIXTURE_HEADER}print('{name} fixture')\n")
            (tools / name).chmod(0o700)
        return tools

    def test_wrong_host_fails_even_with_present_tools(self):
        # The Trust package's own triple decides, and preflight never looks up a
        # stock cargo or rustc (the retired lane's tools) on the way.
        original_which = GATE.shutil.which
        looked_up = []

        def which(name, *args, **kwargs):
            looked_up.append(name)
            return original_which(name, *args, **kwargs)

        with tempfile.TemporaryDirectory() as temp:
            binary = self.trust_package_fixture(Path(temp), host="aarch64-apple-darwin")
            path = os.pathsep.join((str(binary), str(self.host_tools_fixture(Path(temp))), os.environ["PATH"]))
            with mock.patch.dict(os.environ, {"PATH": path}), mock.patch.object(GATE.shutil, "which", which), \
                    mock.patch.object(GATE.sys, "platform", "linux"), \
                    self.assertRaisesRegex(RuntimeError, r"required Linux host is aarch64-unknown-linux-gnu, "
                                                         r"observed \['aarch64-apple-darwin'\]"):
                GATE.preflight()
        self.assertEqual(looked_up, ["trustc", "trustdoc", "targo", "env", "git", "cc", "c++", "readelf"])

    def trust_package_fixture(
        self, root: Path, *, change_tool: bool = False, llc: bool = True, host: str = GATE.HOST,
    ) -> Path:
        # The gate resolves the selected compiler's path, so the fixture must
        # name it resolved too: on macOS the temporary directory lives under
        # the /var -> /private/var symlink and an unresolved path never matches.
        root = root.resolve()
        package = root / "trust"
        binary = package / "bin"
        binary.mkdir(parents=True)
        (package / "lib/rustlib" / GATE.HOST / "lib").mkdir(parents=True)
        if llc:
            # A Trust package ships its LLVM tools, llc among them, in its
            # sysroot's lib/rustlib/<host>/bin.
            llvm_bin = package / "lib/rustlib" / GATE.HOST / "bin"
            llvm_bin.mkdir(parents=True)
            (llvm_bin / "llc").write_text(
                f"{PYTHON_FIXTURE_HEADER}print('LLVM (http://llvm.org/):\\n  LLVM version 22.fixture-trust')\n"
            )
            (llvm_bin / "llc").chmod(0o700)
        driver = (f"binary: trustc\ncommit-hash: {'a' * 40}\nhost: {host}\n"
                  "release: 1.99.0-fixture\nLLVM version: 22.1.2\n")
        (binary / "trustc").write_text(
            f"{PYTHON_FIXTURE_HEADER}import sys\n"
            f"print({driver!r} if sys.argv[1:] == ['-vV'] else {str(package)!r})\n"
        )
        (binary / "trustdoc").write_text(f"{PYTHON_FIXTURE_HEADER}")
        (binary / "targo").write_text(
            f"{PYTHON_FIXTURE_HEADER}import os, pathlib, sys\n"
            "assert sys.argv[1] == '--unverified', sys.argv\n"
            f"assert os.environ['RUSTC'] == {str(binary / 'trustc')!r}\n"
            f"assert os.environ['RUSTDOC'] == {str(binary / 'trustdoc')!r}\n"
            "if sys.argv[2:] == ['--version']:\n"
            " print('targo fixture')\n"
            "else:\n"
            " args = sys.argv[2:]\n"
            " if args[:1] == ['--config']: args = args[2:]\n"
            " assert args[0] == 'test'\n"
            " assert 'TCG_LLC' not in os.environ, 'test-only llc selection reached the compiler'\n"
            " assert all(flag in sys.argv for flag in ['--locked', '--offline', '--nocapture', '--test-threads=1'])\n"
            f" print({transcript()!r})\n"
            f" if {change_tool!r}:\n"
            "  with open(__file__, 'a') as f: f.write('# changed during the target\\n')\n"
        )
        for path in binary.iterdir():
            path.chmod(0o700)
        return binary

    @unittest.skipUnless(sys.platform == "linux", "the gate refuses non-Linux hosts before trust-mode binding runs")
    def test_trust_mode_binds_build_and_proof_resolution_to_selected_compiler(self):
        for changed in (False, True):
            with self.subTest(changed=changed), tempfile.TemporaryDirectory() as temp:
                root = Path(temp)
                binary = self.trust_package_fixture(root, change_tool=changed)
                output = root / "results"
                provenance = {"source_fingerprint": "fixture", "dirty": False}
                environment = {"PATH": str(binary) + os.pathsep + os.environ["PATH"],
                               "RUSTC": "/stale/rustc", "RUSTDOC": "/stale/rustdoc",
                               "TCG_LLC": str(binary.parent / "lib/rustlib" / GATE.HOST / "bin/llc")}
                proof = mock.Mock(return_value=proof_tool_record())
                admission = mock.Mock(return_value=({"admitted": True}, []))
                with mock.patch.dict(os.environ, environment), \
                        mock.patch.object(GATE, "TARGETS", (("fixture", "whole-target"),)), \
                        mock.patch.object(GATE, "source_provenance", return_value=provenance), \
                        mock.patch.object(GATE, "dependency_identity", return_value=dependency_record()), \
                        mock.patch.object(GATE, "proof_tool_identities", proof), \
                        mock.patch.object(GATE, "ay_admission_preflight", admission), \
                        contextlib.redirect_stdout(io.StringIO()):
                    self.assertEqual(GATE.main([
                        "--trust-unverified", "--require-clean", "--require-offline-deps",
                        "--require-proof-tools", "--out", str(output),
                    ]), int(changed))
                    self.assertEqual(os.environ["RUSTC"], "/stale/rustc")
                report = json.loads((output / "report.json").read_text())
                self.assertEqual(report["provenance"]["lane"], "trust-unverified")
                # The admission preflight builds with the selected Trust package.
                (call,) = admission.call_args_list
                self.assertEqual(call.args[0]["lane"], "trust-unverified")
                self.assertEqual(call.args[0]["build_command"], report["provenance"]["build_command"])
                self.assertEqual(call.args[1], proof_tool_record()["ay"])
                self.assertTrue(call.kwargs["offline"])
                self.assertEqual(report["ay_admission"], {"admitted": True})
                self.assertEqual(report["targets"][0]["status"], "pass")
                self.assertEqual(report["provenance"]["llc"]["route"], "TCG_LLC")
                self.assertEqual(
                    report["provenance"]["runtime_checker_environment"]["TCG_LLC"],
                    environment["TCG_LLC"],
                )
                self.assertIn(
                    "TCG_LLC=" + environment["TCG_LLC"],
                    " ".join(report["targets"][0]["command"]),
                )
                self.assertEqual(len(proof.call_args_list), 2)
                for call in proof.call_args_list:
                    self.assertEqual(call.args[0]["RUSTC"], str(binary / "trustc"))
                if changed:
                    self.assertIn("Trust compiler/build-tool bytes changed", report["errors"][0])
                else:
                    self.assertEqual(report["final_compiler_tool_identities"],
                                     report["provenance"]["compiler_tool_identities"])

    @staticmethod
    def host_tool_fixtures(root: Path) -> dict[str, str]:
        # Executable stand-ins for the preflight's ordinary host tools, which
        # it only locates and asks for a version.
        tools = root / "host-tools"
        tools.mkdir()
        fixtures = {}
        for name in ("cc", "c++", "readelf"):
            path = tools / name
            path.write_text(f"{PYTHON_FIXTURE_HEADER}print('{name} fixture')\n")
            path.chmod(0o700)
            fixtures[name] = str(path)
        return fixtures

    def test_preflight_resolves_the_llc_twins_llc_or_names_the_trust_remedy(self):
        # symbol_linkage_elf's llc twin legs run under TCG_REQUIRE_LLC, so the
        # floor refuses to start without the llc they will find, and says how
        # the Trust package provides it.
        self.assertTrue(GATE.llc_required())
        original_which = GATE.shutil.which

        for present in (True, False):
            with self.subTest(trust_package_llc=present), tempfile.TemporaryDirectory() as temp:
                binary = self.trust_package_fixture(Path(temp), llc=present)
                # The Linux-host check and the readelf lookup run before the
                # llc resolution; pin the host and give readelf a fixture so
                # the resolution under test is reached on any development host
                # (a macOS release host has no readelf).
                readelf = Path(temp).resolve() / "host-tools/readelf"
                readelf.parent.mkdir()
                readelf.write_text(f"{PYTHON_FIXTURE_HEADER}print('GNU readelf fixture')\n")
                readelf.chmod(0o700)

                def which_without_llc(name, *args, **kwargs):
                    if name == "readelf":
                        return str(readelf)
                    return None if name == "llc" else original_which(name, *args, **kwargs)

                with mock.patch.dict(os.environ, {"PATH": str(binary) + os.pathsep + os.environ["PATH"]}), \
                        mock.patch.object(GATE.sys, "platform", "linux"), \
                        mock.patch.object(GATE.shutil, "which", which_without_llc):
                    if present:
                        record = GATE.preflight()["llc"]
                        expected = binary.parent / "lib/rustlib" / GATE.HOST / "bin/llc"
                        self.assertEqual((record["path"], record["route"]), (str(expected), "sysroot"))
                        self.assertEqual(record["version"], "LLVM version 22.fixture-trust")
                    else:
                        with self.assertRaisesRegex(
                            RuntimeError,
                            rf"required tool is missing: llc .*the Trust package {re.escape(str(binary.parent))} "
                            rf"ships its LLVM tools at lib/rustlib/{GATE.HOST}/bin/llc",
                        ) as refused:
                            GATE.preflight()
                        self.assertNotIn("rustup", str(refused.exception))
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            sysroot, on_path = root / "package", root / "path"
            on_path.mkdir()
            package_llc = sysroot / "lib/rustlib" / GATE.HOST / "bin/llc"
            compiler_version = "binary: trustc\nrelease: 1.99.0-fixture\nLLVM version: 22.1.2\n"
            remedy = (f"the Trust package {sysroot} ships its LLVM tools at lib/rustlib/{GATE.HOST}/bin/llc; "
                      "use a Trust package that carries them")

            def resolve(search_path=str(on_path), environ=None, version=compiler_version):
                return GATE.resolve_llc(sysroot, search_path=search_path, compiler="/fixture/trustc",
                                        compiler_version=version, environ={} if environ is None else environ)

            def llc_fixture(path: Path, version: str, mode: int = 0o700) -> Path:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(f"{PYTHON_FIXTURE_HEADER}print('  LLVM version {version}')\n")
                path.chmod(mode)
                return path

            with self.assertRaisesRegex(RuntimeError, rf"required tool is missing: llc .*{re.escape(remedy)}"):
                resolve()
            llc_fixture(package_llc, "22.fixture")
            record = resolve()
            self.assertEqual(
                {key: record[key] for key in ("path", "route", "version", "llvm_major", "compiler",
                                              "compiler_release", "sysroot")},
                {"path": str(package_llc), "route": "sysroot", "version": "LLVM version 22.fixture",
                 "llvm_major": 22, "compiler": "/fixture/trustc", "compiler_release": "1.99.0-fixture",
                 "sysroot": str(sysroot)},
            )
            # The test's own order: TCG_LLC, then an absolute PATH entry, then
            # the sysroot. A non-executable file and a relative entry are not
            # candidates.
            llc_fixture(on_path / "llc", "22.fixture", mode=0o600)
            self.assertEqual(resolve()["route"], "sysroot")
            relative = root / "relative"
            llc_fixture(relative / "llc", "22.fixture")
            self.assertEqual(resolve(search_path=os.pathsep.join(["relative", str(on_path)]))["route"], "sysroot")
            (on_path / "llc").chmod(0o700)
            self.assertEqual(resolve()["route"], "PATH")
            self.assertEqual(resolve(environ={"TCG_LLC": str(package_llc)})["route"], "TCG_LLC")
            for environ, problem in (
                ({"TCG_LLC": str(root / "gone")}, "which is not an executable file"),
                ({"TCG_LLC": str(llc_fixture(root / "noexec/llc", "22.fixture", mode=0o600))},
                 "which is not an executable file"),
            ):
                with self.assertRaisesRegex(RuntimeError, problem):
                    resolve(environ=environ)
            # The llc's LLVM major must equal the lane compiler's.
            old = llc_fixture(root / "old/llc", "18.1.3")
            with self.assertRaisesRegex(RuntimeError, rf"reports 'LLVM version 18.1.3', but the lane compiler "
                                                      rf"/fixture/trustc is LLVM 22; .*{re.escape(remedy)}"):
                resolve(environ={"TCG_LLC": str(old)})
            with self.assertRaisesRegex(RuntimeError, "reports 'no LLVM version line'"):
                none = root / "none/llc"
                none.parent.mkdir()
                none.write_text(f"{PYTHON_FIXTURE_HEADER}print('no version here')\n")
                none.chmod(0o700)
                resolve(environ={"TCG_LLC": str(none)})
            with self.assertRaisesRegex(RuntimeError, "reports no LLVM version to match"):
                resolve(version="binary: trustc\nrelease: 1.99.0-fixture\n")
        # A floor whose targets run no llc twin legs (the x86-64 twin) does not
        # require one.
        spec = importlib.util.spec_from_file_location("check_linux_x86_64", ROOT / "scripts" / "check_linux_x86_64.py")
        twin = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(twin)
        self.assertFalse(twin.SHARED.llc_required())

    def test_preflight_refuses_a_missing_host_tool_and_a_non_linux_host(self):
        # The stubs the llc test uses do not weaken the preflight: a host tool
        # that is not found, or a host that is not Linux, still stops the
        # floor before any llc resolution, on every host.
        original_which = GATE.shutil.which
        with tempfile.TemporaryDirectory() as temp:
            binary = self.trust_package_fixture(Path(temp))
            fixtures = self.host_tool_fixtures(Path(temp).resolve())
            path = {"PATH": str(binary) + os.pathsep + os.environ["PATH"]}
            for missing in ("cc", "c++", "readelf"):
                def which_without(name, *args, missing=missing, **kwargs):
                    if name == missing:
                        return None
                    return fixtures.get(name) or original_which(name, *args, **kwargs)

                with self.subTest(missing=missing), mock.patch.dict(os.environ, path), \
                        mock.patch.object(GATE.shutil, "which", which_without), \
                        mock.patch.object(GATE.sys, "platform", "linux"), \
                        mock.patch.object(GATE, "resolve_llc") as resolve_llc:
                    with self.assertRaisesRegex(RuntimeError, rf"^required tool is missing: {re.escape(missing)}$"):
                        GATE.preflight()
                    resolve_llc.assert_not_called()

            def which_all(name, *args, **kwargs):
                return fixtures.get(name) or original_which(name, *args, **kwargs)

            for platform in ("darwin", "freebsd14"):
                with self.subTest(platform=platform), mock.patch.dict(os.environ, path), \
                        mock.patch.object(GATE.shutil, "which", which_all), \
                        mock.patch.object(GATE.sys, "platform", platform), \
                        mock.patch.object(GATE, "resolve_llc") as resolve_llc:
                    with self.assertRaisesRegex(
                        RuntimeError,
                        rf"^required Linux host is {re.escape(GATE.HOST)}, observed "
                        rf"\['{re.escape(GATE.HOST)}'\] on {platform}$",
                    ):
                        GATE.preflight()
                    resolve_llc.assert_not_called()

    def test_trust_mode_rejects_missing_mixed_stock_and_mismatched_packages(self):
        for defect in ("missing", "mixed", "stock", "sysroot", "targo", "wrapper"):
            with self.subTest(defect=defect), tempfile.TemporaryDirectory() as temp:
                root = Path(temp)
                binary = self.trust_package_fixture(root)
                overrides = {"PATH": str(binary) + os.pathsep + os.environ["PATH"]}
                expected = {"missing": "missing", "mixed": "same package", "stock": "branded trustc",
                            "sysroot": "package mismatch", "targo": "branded Targo",
                            "wrapper": "without wrappers"}[defect]
                if defect == "mixed":
                    (root / "other").mkdir()
                    (binary / "trustdoc").rename(root / "other/trustdoc")
                    (binary / "trustdoc").symlink_to(root / "other/trustdoc")
                elif defect == "stock":
                    tool = binary / "trustc"
                    tool.write_text(tool.read_text().replace("binary: trustc", "binary: rustc"))
                elif defect == "sysroot":
                    tool = binary / "trustc"
                    tool.write_text(tool.read_text().replace(repr(str(binary.parent)), repr(str(root))))
                elif defect == "targo":
                    tool = binary / "targo"
                    tool.write_text(tool.read_text().replace("targo fixture", "cargo fixture"))
                elif defect == "wrapper":
                    overrides["RUSTC_WRAPPER"] = "/unrecorded-wrapper"
                original_which = GATE.shutil.which
                def which(name):
                    return None if defect == "missing" and name == "targo" else original_which(name)
                with mock.patch.dict(os.environ, overrides), mock.patch.object(GATE.shutil, "which", which):
                    with self.assertRaisesRegex(RuntimeError, expected):
                        GATE.preflight()

    @unittest.skipUnless(sys.platform == "linux", "the gate refuses non-Linux hosts before trust-mode binding runs")
    def test_trust_mode_checker_overrides_reach_tests_but_never_compiler_probes(self):
        with tempfile.TemporaryDirectory() as temp:
            binary = self.trust_package_fixture(Path(temp))
            # Make an accidental leak into either compiler or build tool fatal.
            for name in ("trustc", "targo"):
                tool = binary / name
                text = tool.read_text().splitlines(keepends=True)
                tool.write_text(text[0] + "import os\nassert not any(k.startswith('TCG_') for k in os.environ)\n"
                                + "".join(text[1:]))
            override = str(Path(temp) / 'checker with "quotes"')
            with mock.patch.dict(os.environ, {
                "PATH": str(binary) + os.pathsep + os.environ["PATH"],
                "TCG_EXTERNAL_CLEAN_CHECKER": override,
            }):
                provenance = GATE.preflight()
            command = GATE.target_build_command(provenance, ())
            runner = json.loads(command[command.index("--config") + 1].split("=", 1)[1])
            self.assertEqual(runner, [provenance["tools"]["env"], f"TCG_EXTERNAL_CLEAN_CHECKER={override}"])
            pure_plan = GATE.target_build_command(
                provenance, GATE.target_unset_environment("trust-cg-codegen", "core_jit_planning"),
            )
            self.assertNotIn("--config", pure_plan)

    def test_target_requirements_reach_only_the_test_runner(self):
        package, target = "trust-cg-codegen", "e2e_aarch64_link_runtime"
        required = GATE.target_environment(package, target)
        self.assertTrue(required)
        trust = {
            "lane": "trust-unverified", "build_command": ["env", "targo", "--unverified"],
            "tools": {"env": "/usr/bin/env"},
            "runtime_checker_environment": {"TCG_EXTERNAL_CLEAN_CHECKER": "/checker"},
        }
        # Without a checker selection or a requirement there is no runner.
        bare = {**trust, "runtime_checker_environment": {}}
        self.assertEqual(GATE.target_build_command(bare, ()), ["env", "targo", "--unverified"])
        command = GATE.target_build_command(trust, (), required)
        runner = json.loads(command[command.index("--config") + 1].split("=", 1)[1])
        self.assertEqual(runner[0], "/usr/bin/env")
        self.assertIn("TCG_EXTERNAL_CLEAN_CHECKER=/checker", runner)
        for name, value in required.items():
            self.assertIn(f"{name}={value}", runner)
        self.assertFalse(any(part.startswith("TCG_") for part in command[:command.index("--config")]))

    def test_orchestration_retains_each_real_process_and_requires_every_target(self):
        for fail_second in (False, True):
            with self.subTest(fail_second=fail_second), tempfile.TemporaryDirectory() as temp:
                fixture = Path(temp) / "cargo-fixture"
                fixture.write_text(
                    f"{PYTHON_FIXTURE_HEADER}"
                    "import sys\n"
                    "assert '--locked' in sys.argv\n"
                    "assert '--nocapture' in sys.argv\n"
                    "assert '--test-threads=1' in sys.argv\n"
                    "target = sys.argv[sys.argv.index('--test') + 1]\n"
                    f"broken = {fail_second!r} and target == 'second'\n"
                    f"print({transcript()!r})\n"
                    "if broken: raise SystemExit(9)\n"
                )
                fixture.chmod(0o700)
                output = Path(temp) / "results"
                provenance = {
                    "source_sha": "fixture-source", "dirty": True,
                    "tools": {"targo": str(fixture), "env": "/usr/bin/env", "git": "fixture-git"}, "host": GATE.HOST,
                    "source_fingerprint": "fixture-fingerprint", **trust_lane_provenance(str(fixture)),
                }
                with mock.patch.object(GATE, "TARGETS", (("fixture", "first"), ("fixture", "second"))):
                    with mock.patch.object(GATE, "preflight", return_value=provenance):
                        with mock.patch.object(GATE, "source_provenance", return_value=provenance):
                            with mock.patch.object(GATE, "dependency_identity", return_value=dependency_record()):
                                code = GATE.main(["--out", str(output), "--timeout-seconds", "5"])
                report = json.loads((output / "report.json").read_text())
                self.assertEqual(code, 1 if fail_second else 0)
                self.assertEqual(report["status"], "fail" if fail_second else "pass")
                self.assertEqual(report["provenance"]["source_sha"], "fixture-source")
                self.assertEqual(len(report["targets"]), 2)
                self.assertEqual(report["targets"][0]["status"], "pass")
                self.assertEqual(report["targets"][1]["returncode"], 9 if fail_second else 0)
                for target in report["targets"]:
                    self.assertTrue((output / target["log"]).is_file())

    def run_main_with_fixture(
        self, temp: str, provenance_overrides: dict, *extra: str, identities: tuple[dict, ...] | None = None,
        proof_tools: tuple[dict, ...] | None = None, ay_admission: tuple[dict, list] | None = None,
    ) -> tuple[int, dict, str, Path]:
        marker = Path(temp) / "cargo-ran"
        arguments = Path(temp) / "cargo-arguments"
        fixture = Path(temp) / "cargo-fixture"
        fixture.write_text(
            f"{PYTHON_FIXTURE_HEADER}"
            "import sys\n"
            f"open({str(marker)!r}, 'a').close()\n"
            f"open({str(arguments)!r}, 'a').write(' '.join(sys.argv[1:]) + '\\n')\n"
            f"print({transcript()!r})\n"
        )
        fixture.chmod(0o700)
        output = Path(temp) / "results"
        provenance = {
            "source_sha": "fixture-source", "dirty": False, "git_status": [],
            "tools": {"targo": str(fixture), "env": "/usr/bin/env", "git": "fixture-git"}, "host": GATE.HOST,
            "source_fingerprint": "fixture-fingerprint", **trust_lane_provenance(str(fixture)),
            **provenance_overrides,
        }
        recorded = mock.Mock(side_effect=list(identities or (dependency_record(), dependency_record())))
        tools = mock.Mock(side_effect=list(proof_tools or (proof_tool_record(), proof_tool_record())))
        admission = mock.Mock(return_value=ay_admission or ({"admitted": True}, []))
        stderr = io.StringIO()
        with mock.patch.object(GATE, "TARGETS", (("fixture", "first"),)):
            with mock.patch.object(GATE, "preflight", return_value=provenance):
                with mock.patch.object(GATE, "source_provenance", return_value=provenance):
                    with mock.patch.object(GATE, "dependency_identity", recorded):
                        with mock.patch.object(GATE, "proof_tool_identities", tools), \
                                mock.patch.object(GATE, "ay_admission_preflight", admission):
                            with contextlib.redirect_stderr(stderr), contextlib.redirect_stdout(io.StringIO()):
                                code = GATE.main(["--out", str(output), "--timeout-seconds", "5", *extra])
        report = json.loads((output / "report.json").read_text())
        report["_cargo_arguments"] = arguments.read_text().splitlines() if arguments.exists() else []
        report["_identity_calls"] = [call.args for call in recorded.call_args_list]
        report["_admission_calls"] = admission.call_args_list
        return code, report, stderr.getvalue(), marker

    def test_cargo_config_problems_refuse_the_run_before_any_build_tool(self):
        injected = cargo_config_record(("/fixture/.cargo-home/config.toml: [env]",))
        with mock.patch.object(GATE, "cargo_config_record", return_value=injected), \
                tempfile.TemporaryDirectory() as temp:
            code, report, stderr, marker = self.run_main_with_fixture(temp, {})
            self.assertFalse(marker.exists(), "a refused Cargo config must not run Cargo")
        self.assertEqual(code, 1)
        self.assertEqual(report["targets"], [])
        # Refused before preflight, whose version probes run the build tool.
        self.assertNotIn("provenance", report)
        self.assertEqual(report["cargo_config"], injected)
        self.assertIn("cargo config: /fixture/.cargo-home/config.toml: [env]", report["errors"])
        self.assertIn("a Cargo config would change the targets", stderr)

    def test_the_audit_runs_before_preflight_with_the_selected_build_tool(self):
        # preflight's version probes run the build tool, so the audit comes
        # first (GATE.preflight is the fixture's mock while main runs).
        calls = []

        def record(git, tool):
            calls.append((tool, GATE.preflight.called))
            return cargo_config_record()

        # The Trust lane is the only lane: with or without the flag that named
        # it, the floor audits and runs the Trust package's targo.
        for flag in ((), ("--trust-unverified",)):
            calls.clear()
            with self.subTest(flag=flag), tempfile.TemporaryDirectory() as temp, \
                    mock.patch.object(GATE, "cargo_config_record", side_effect=record), \
                    mock.patch.object(GATE, "selected_build_tool", return_value="/pkg/bin/targo"):
                code, report, _, _ = self.run_main_with_fixture(temp, {}, *flag)
                self.assertEqual(calls, [("/pkg/bin/targo", False), ("/pkg/bin/targo", True)], report["errors"])
                self.assertEqual(report["final_cargo_config"], cargo_config_record())

    def test_selected_build_tool_is_found_on_path_without_running_it(self):
        with tempfile.TemporaryDirectory() as temp:
            ran = Path(temp) / "ran"
            for name in ("cargo", "targo"):
                tool = Path(temp) / name
                tool.write_text(f"#!/bin/sh\ntouch {ran}\n")
                tool.chmod(0o700)
            with mock.patch.dict(os.environ, {"PATH": temp}):
                self.assertEqual(SELECTED_BUILD_TOOL(), str(Path(temp) / "targo"))
            with mock.patch.dict(os.environ, {"PATH": str(Path(temp) / "empty")}):
                with self.assertRaisesRegex(RuntimeError, "required tool is missing: targo"):
                    SELECTED_BUILD_TOOL()
            # A PATH that holds only a stock cargo has no build tool for the floor.
            (Path(temp) / "targo").unlink()
            with mock.patch.dict(os.environ, {"PATH": temp}):
                with self.assertRaisesRegex(RuntimeError, "required tool is missing: targo"):
                    SELECTED_BUILD_TOOL()
            self.assertFalse(ran.exists())

    def test_the_trust_lane_is_the_only_lane(self):
        # The stock cargo/rustc floor is retired (owner directive 2026-09-28):
        # no entry point selects it and no helper keeps a branch for it.
        for retired in ("is_trust_build", "target_environment_delivery", "pinned_toolchain"):
            self.assertFalse(hasattr(GATE, retired), retired)
        self.assertEqual(list(inspect.signature(GATE.preflight).parameters), [])
        self.assertEqual(list(inspect.signature(SELECTED_BUILD_TOOL).parameters), [])
        self.assertNotIn("trust", inspect.signature(GATE.resolve_llc).parameters)
        self.assertEqual(GATE.TRUST_BUILD_TOOL, "targo")
        self.assertEqual(inspect.signature(CARGO_CONFIG_RECORD).parameters["tool"].default, "targo")
        # A provenance without the Trust build command cannot run a target
        # through a PATH cargo: it is refused, not given a fallback.
        with self.assertRaises(KeyError):
            GATE.target_build_command({"tools": {"cargo": "/usr/bin/cargo"}, "runtime_checker_environment": {}}, ())

    def test_cargo_config_change_during_the_run_fails(self):
        records = mock.Mock(side_effect=[cargo_config_record(), cargo_config_record(sha="d" * 64)])
        with mock.patch.object(GATE, "cargo_config_record", records), tempfile.TemporaryDirectory() as temp:
            code, report, _, marker = self.run_main_with_fixture(temp, {})
            self.assertTrue(marker.exists())
        self.assertEqual(code, 1)
        self.assertEqual(report["status"], "fail")
        self.assertTrue(any(error.startswith("Cargo config changed while the floor was running")
                            for error in report["errors"]), report["errors"])

    def test_the_real_audit_reads_the_config_cargo_would_read(self):
        # The floor records and refuses exactly what scripts/cargo_config_audit.py
        # reports for the checkout; an injected Cargo home is found through the
        # environment it is given.
        with tempfile.TemporaryDirectory() as temp:
            home = Path(temp) / "cargo-home"
            home.mkdir()
            (home / "config.toml").write_text('[env]\nPROPTEST_CASES = { value = "0", force = true }\n')
            environment = {"CARGO_HOME": str(home), "HOME": temp, "PATH": "/usr/bin"}
            record = GATE.cargo_config_auditor().audit(
                GATE.ROOT, environment, GATE.cargo_config_auditor().committed_config(GATE.ROOT),
            )
        injected = [entry for entry in record["files"] if entry["path"] == str(home / "config.toml")]
        self.assertEqual(len(injected), 1)
        # Without tomllib (Python < 3.11) the auditor refuses every non-empty
        # config it cannot parse rather than reading it as clean.
        expected = ["[env]"] if GATE.cargo_config_auditor().tomllib is not None else [
            "cannot be audited without tomllib"
        ]
        self.assertEqual(injected[0]["problems"], expected)
        committed = [entry for entry in record["files"] if entry["path"] == str(GATE.ROOT / ".cargo" / "config.toml")]
        self.assertEqual(committed[0].get("exempt"), "the repository's committed config")

    def test_shrink_wrap_native_matrix_is_required(self):
        row = ("trust-cg-codegen", "aarch64_shrink_wrap_region_exit")
        self.assertIn(row, GATE.TARGETS)
        self.assertEqual(GATE.TARGET_MINIMUM_PASSES[row], 2)
        self.assertEqual(GATE.target_required_lines(*row),
                         ("SHRINK_WRAP_REGION_EXIT_NATIVE levels=4 checked_per_level=24",))

    def test_every_panic_fuzz_family_must_print_its_default_case_count(self):
        self.assertEqual(len(GATE.PROPTEST_CASE_DEFAULTS), 7)
        for (package, target), default in GATE.PROPTEST_CASE_DEFAULTS.items():
            with self.subTest(target=target):
                self.assertEqual(GATE.target_required_lines(package, target),
                                 (f"panic-fuzz proptest cases: configured={default} run={default}",))
                self.assertIn((package, target), GATE.TARGETS)
                source = (ROOT / "crates" / package / "tests" / f"{target}.rs").read_text()
                # One case-count function feeds the probe and the properties.
                self.assertEqual(source.count(f".unwrap_or({default})"), 1)
                self.assertEqual(source.count("cases: panic_fuzz_cases(),"), 1)
                self.assertNotIn('std::env::var("PROPTEST_CASES")\n            .ok()', source)
                self.assertIn('"panic-fuzz proptest cases: configured={configured} run={}"', source)
                self.assertIn("fn panic_fuzz_runs_its_configured_case_count()", source)
        self.assertEqual(GATE.target_required_lines("trust-cg-lower", "aarch64_variadic_abi"), ())
        line = GATE.proptest_case_line(256)
        with tempfile.TemporaryDirectory() as temp:
            for printed, expected in (
                (line, "pass"),
                # libtest --nocapture prints a test's output after its name.
                ("test panic_fuzz_runs_its_configured_case_count ... " + line, "pass"),
                ("panic-fuzz proptest cases: configured=0 run=0", "fail"),
                ("test x ... panic-fuzz proptest cases: configured=2560 run=2560", "fail"),
                ("prefix" + line, "fail"),
                ("", "fail"),
            ):
                with self.subTest(printed=printed):
                    source = f"print({printed!r}); print({transcript(1)!r})"
                    result = GATE.run_target(
                        [sys.executable, "-c", source], Path(temp) / f"probe-{expected}-{len(printed)}.log", 5,
                        root=ROOT, grace_seconds=0.05, required_lines=(line,),
                    )
                    self.assertEqual(result["status"], expected, result)
                    self.assertEqual(result["required_lines"], [line])

    def test_require_clean_refuses_a_dirty_tree_before_any_target(self):
        dirty = {"dirty": True, "git_status": [" M scripts/check_linux_aarch64.py", "?? crates/new.rs"]}
        with tempfile.TemporaryDirectory() as temp:
            code, report, stderr, marker = self.run_main_with_fixture(temp, dirty, "--require-clean")
            self.assertFalse(marker.exists(), "a refused dirty tree must not run Cargo")
        self.assertEqual(code, 1)
        self.assertEqual(report["status"], "fail")
        self.assertEqual(report["targets"], [])
        self.assertTrue(report["controls"]["require_clean"])
        self.assertTrue(any(error.startswith("--require-clean:") for error in report["errors"]), report["errors"])
        self.assertIn("git status --porcelain", stderr)
        self.assertIn(" M scripts/check_linux_aarch64.py", stderr)
        self.assertIn("?? crates/new.rs", stderr)

    def test_require_clean_runs_a_clean_tree_and_dirty_runs_are_labelled(self):
        with tempfile.TemporaryDirectory() as temp:
            code, report, stderr, marker = self.run_main_with_fixture(temp, {}, "--require-clean")
            self.assertTrue(marker.exists())
        self.assertEqual((code, report["status"]), (0, "pass"), report)
        self.assertEqual(report["controls"], {
            "require_clean": True, "max_rss_gib": None, "rss_supervision": "not-requested",
            "require_offline_deps": False, "require_proof_tools": False,
            "trust_driver": None,
        })
        with tempfile.TemporaryDirectory() as temp:
            code, report, stderr, _ = self.run_main_with_fixture(
                temp, {"dirty": True, "git_status": ["?? scratch.txt"]},
            )
        # Without the control a dirty run keeps its historical result, but it
        # can no longer be mistaken for a clean-source qualification.
        self.assertEqual((code, report["status"]), (0, "pass"), report)
        self.assertFalse(report["controls"]["require_clean"])
        self.assertIn("not a clean-source qualification", stderr)
        self.assertIn("?? scratch.txt", stderr)

    def test_requested_ceiling_without_supervision_fails_without_running(self):
        unsupported = types.SimpleNamespace(rss_supervision_support=lambda: None)
        with tempfile.TemporaryDirectory() as temp:
            with mock.patch.object(GATE, "timeout_runner_module", return_value=unsupported):
                code, report, _, marker = self.run_main_with_fixture(temp, {}, "--max-rss-gib", "16")
            self.assertFalse(marker.exists(), "an unenforceable ceiling must not run Cargo")
        self.assertEqual(code, 1)
        self.assertEqual(report["controls"], {
            "require_clean": False, "max_rss_gib": 16.0, "rss_supervision": "unsupported",
            "require_offline_deps": False, "require_proof_tools": False,
            "trust_driver": None,
        })
        self.assertEqual(report["targets"], [])
        self.assertTrue(any("unsupported" in error for error in report["errors"]), report["errors"])

    def test_requested_ceiling_is_passed_to_every_target(self):
        supported = types.SimpleNamespace(rss_supervision_support=lambda: "linux-proc")
        calls = []

        def recording_run_target(command, log_path, timeout_seconds, **options):
            calls.append(options)
            log_path.write_text(transcript())
            return {
                "status": "pass", "interrupted_signal": None, "log": log_path.name,
                "max_rss_gib": options["max_rss_gib"], "errors": [],
            }

        with tempfile.TemporaryDirectory() as temp:
            with mock.patch.object(GATE, "timeout_runner_module", return_value=supported):
                with mock.patch.object(GATE, "run_target", side_effect=recording_run_target):
                    code, report, _, _ = self.run_main_with_fixture(temp, {}, "--max-rss-gib", "16")
        self.assertEqual((code, report["status"]), (0, "pass"), report)
        self.assertEqual(report["controls"]["rss_supervision"], "linux-proc")
        self.assertEqual([call["max_rss_gib"] for call in calls], [16.0])

    def test_dependency_identity_is_recorded_before_and_after_the_targets(self):
        with tempfile.TemporaryDirectory() as temp:
            code, report, stderr, _ = self.run_main_with_fixture(temp, {})
        self.assertEqual((code, report["status"]), (0, "pass"), report)
        self.assertEqual(report["dependency_identity"], dependency_record())
        self.assertEqual(report["final_dependency_identity"], dependency_record())
        self.assertEqual(report["_identity_calls"], [("fixture-git",), ("fixture-git",)])
        self.assertNotIn("--offline", report["_cargo_arguments"][0].split())
        self.assertNotIn("not all local", stderr)

    def test_missing_pinned_revision_is_labelled_and_refused_under_require_offline_deps(self):
        absent = (dependency_record(resolves=False),)
        with tempfile.TemporaryDirectory() as temp:
            code, report, stderr, marker = self.run_main_with_fixture(temp, {}, "--require-offline-deps", identities=absent)
            self.assertFalse(marker.exists(), "a refused Cargo home must not run Cargo")
        self.assertEqual((code, report["status"]), (1, "fail"))
        self.assertEqual(report["targets"], [])
        self.assertTrue(report["controls"]["require_offline_deps"])
        self.assertNotIn("final_dependency_identity", report)
        self.assertTrue(report["errors"])
        self.assertTrue(all(error.startswith("--require-offline-deps: ") for error in report["errors"]), report["errors"])
        self.assertIn("does not resolve in the local Cargo Git database", report["errors"][0])
        self.assertIn("refuses this Cargo home", stderr)
        # Without the control the run keeps its result but says Cargo may fetch.
        with tempfile.TemporaryDirectory() as temp:
            code, report, stderr, _ = self.run_main_with_fixture(
                temp, {}, identities=absent + (dependency_record(resolves=False),),
            )
        self.assertEqual((code, report["status"]), (0, "pass"), report)
        self.assertIn("may fetch them", stderr)
        self.assertIn("does not resolve", stderr)

    def test_require_offline_deps_runs_cargo_offline_when_every_pin_is_local(self):
        with tempfile.TemporaryDirectory() as temp:
            code, report, _, marker = self.run_main_with_fixture(temp, {}, "--require-offline-deps")
            self.assertTrue(marker.exists())
        self.assertEqual((code, report["status"]), (0, "pass"), report)
        arguments = report["_cargo_arguments"][0].split()
        self.assertEqual(arguments[:3], ["test", "--locked", "--offline"])

    def test_dependency_change_during_the_run_fails(self):
        for changed in (dependency_record(tree="d" * 64), dependency_record(lock="e" * 64)):
            with self.subTest(changed=changed["lockfile_sha256"]), tempfile.TemporaryDirectory() as temp:
                code, report, _, _ = self.run_main_with_fixture(temp, {}, identities=(dependency_record(), changed))
                self.assertEqual((code, report["status"]), (1, "fail"))
                self.assertTrue(any(
                    error.startswith("dependency identity changed while required targets were running")
                    for error in report["errors"]
                ), report["errors"])
        # A checkout Cargo fetched and extracted during the run must match its pin.
        extracted = dependency_record()
        extracted["sources"][0]["checkout"]["modifications"] = ["?? generated.rs"]
        with tempfile.TemporaryDirectory() as temp:
            code, report, _, _ = self.run_main_with_fixture(
                temp, {}, identities=(dependency_record(resolves=False), extracted),
            )
        self.assertEqual((code, report["status"]), (1, "fail"))
        self.assertTrue(any("extracted during the run is not bound to the pin" in error for error in report["errors"]), report["errors"])

    def test_default_recorder_reads_this_lockfile_against_the_given_cargo_home(self):
        with tempfile.TemporaryDirectory() as temp:
            identity = GATE.dependency_identity("git", {"CARGO_HOME": temp, "HOME": temp})
        self.assertEqual(identity["cargo_home"], temp)
        self.assertEqual(identity["cargo_home_source"], "CARGO_HOME")
        self.assertEqual(Path(identity["lockfile"]), ROOT / "Cargo.lock")
        urls = {Path(source["url"]).stem for source in identity["sources"]}
        self.assertTrue({"trust-ir", "clean", "ay"} <= urls, urls)
        self.assertFalse(identity["offline_ready"])
        problems = GATE.dependency_recorder().offline_problems(identity)
        self.assertEqual(len(problems), len(identity["sources"]))
        with mock.patch.object(GATE, "DEPENDENCY_RECORDER", ROOT / "scripts" / "absent-recorder.py"):
            with self.assertRaisesRegex(RuntimeError, "recorder is missing"):
                GATE.dependency_identity("git", {"CARGO_HOME": "/nonexistent"})

    def test_invalid_ceiling_is_a_usage_error(self):
        for value in ("0", "-2", "nan", "inf", "lots"):
            with self.subTest(value=value), contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit) as raised:
                    GATE.main(["--max-rss-gib", value, "--list"])
                self.assertEqual(raised.exception.code, 2)

    def test_dirty_state_covers_tracked_edits_and_untracked_files_but_not_ignored_files(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp).resolve()
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            (root / ".gitignore").write_text("ignored/\n")
            tracked = root / "tracked.rs"
            tracked.write_text("fn original() {}\n")
            subprocess.run(["git", "-C", str(root), "add", ".gitignore", "tracked.rs"], check=True)
            subprocess.run([
                "git", "-C", str(root), "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                "-c", "core.hooksPath=/dev/null", "-c", "commit.gpgsign=false", "commit", "-qm", "fixture",
            ], check=True)
            (root / "ignored").mkdir()
            (root / "ignored" / "build.log").write_text("ignored output\n")
            with mock.patch.object(GATE, "ROOT", root):
                clean = GATE.source_provenance("git")
                tracked.write_text("fn changed() {}\n")
                edited = GATE.source_provenance("git")
                tracked.write_text("fn original() {}\n")
                (root / "untracked.rs").write_text("fn new() {}\n")
                untracked = GATE.source_provenance("git")
        self.assertFalse(clean["dirty"], clean["git_status"])
        self.assertEqual(clean["git_status"], [])
        self.assertTrue(edited["dirty"])
        self.assertEqual(edited["git_status"], [" M tracked.rs"])
        self.assertTrue(untracked["dirty"])
        self.assertEqual(untracked["git_status"], ["?? untracked.rs"])

    def test_dirty_state_covers_cargo_config_entries_git_status_does_not_list(self):
        # Cargo reads .cargo/config whatever Git thinks of it; git status lists
        # neither a FIFO nor an ignored file.
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp).resolve()
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            (root / ".gitignore").write_text(".cargo/ignored.toml\n")
            (root / ".cargo").mkdir()
            (root / ".cargo" / "config.toml").write_text("[build]\njobs = 2\n")
            subprocess.run(["git", "-C", str(root), "add", ".gitignore", ".cargo/config.toml"], check=True)
            subprocess.run([
                "git", "-C", str(root), "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                "-c", "core.hooksPath=/dev/null", "-c", "commit.gpgsign=false", "commit", "-qm", "fixture",
            ], check=True)
            with mock.patch.object(GATE, "ROOT", root):
                clean = GATE.source_provenance("git")
                os.mkfifo(root / ".cargo" / "config")
                fifo = GATE.source_provenance("git")
                (root / ".cargo" / "config").unlink()
                (root / ".cargo" / "ignored.toml").write_text("[alias]\n")
                ignored = GATE.source_provenance("git")
                (root / ".cargo" / "ignored.toml").unlink()
                (root / ".cargo" / "config").symlink_to("/dev/stdin")
                symlink = GATE.source_provenance("git")
        self.assertFalse(clean["dirty"], clean["git_status"])
        self.assertEqual(clean["unlisted_cargo_config_entries"], [])
        self.assertTrue(fifo["dirty"])
        self.assertEqual(fifo["git_status"], ["!! .cargo/config (fifo, not listed by git status)"])
        self.assertNotEqual(fifo["source_fingerprint"], clean["source_fingerprint"])
        self.assertEqual(ignored["git_status"], ["!! .cargo/ignored.toml (file, not listed by git status)"])
        # Git lists an untracked symlink itself; it is not reported twice.
        self.assertEqual(symlink["git_status"], ["?? .cargo/config"])
        self.assertEqual(symlink["unlisted_cargo_config_entries"], [])

    def test_source_fingerprint_covers_untracked_contents_and_tracked_edits(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp).resolve()
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            tracked = root / "tracked.rs"
            tracked.write_text("fn original() {}\n")
            subprocess.run(["git", "-C", str(root), "add", "tracked.rs"], check=True)
            subprocess.run([
                "git", "-C", str(root), "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                "-c", "core.hooksPath=/dev/null", "-c", "commit.gpgsign=false", "commit", "-qm", "fixture",
            ], check=True)
            added = root / "new.rs"
            added.write_text("fn first() {}\n")
            with mock.patch.object(GATE, "ROOT", root):
                first = GATE.source_provenance("git")
                added.write_text("fn other() {}\n")
                second = GATE.source_provenance("git")
                tracked.write_text("fn changed() {}\n")
                third = GATE.source_provenance("git")
            self.assertTrue(first["dirty"])
            self.assertEqual(first["untracked_files"][0]["path"], "new.rs")
            self.assertNotEqual(first["source_fingerprint"], second["source_fingerprint"])
            self.assertEqual(first["tracked_diff_sha256"], second["tracked_diff_sha256"])
            self.assertNotEqual(second["tracked_diff_sha256"], third["tracked_diff_sha256"])

    def test_proof_tool_identities_follow_the_verifier_routes(self):
        with tempfile.TemporaryDirectory() as temp:
            home = Path(temp) / "home"
            prefix = Path(temp) / "pkg"
            for tool in ("ay", "clean"):
                store = prefix / "store" / tool / "current" / "bin"
                store.mkdir(parents=True)
                (store / tool).write_text(f"#!/bin/sh\necho {tool}\n")
                (store / tool).chmod(0o700)
            (prefix / "bin").mkdir()
            plain = Path(temp) / "plain" / "bin"
            plain.mkdir(parents=True)
            (plain / "ay").write_text("#!/bin/sh\necho bare\n")
            (plain / "ay").chmod(0o700)
            (plain / "clean").write_text("#!/bin/sh\necho generic\n")
            (plain / "clean").chmod(0o700)
            home.mkdir()
            # A Trust toolchain: `trustc --print sysroot` names a sysroot shipping bin/ay.
            sysroot = Path(temp) / "trust-sysroot"
            (sysroot / "bin").mkdir(parents=True)
            (sysroot / "bin" / "ay").write_text("#!/bin/sh\necho toolchain\n")
            (sysroot / "bin" / "ay").chmod(0o700)
            compiler = Path(temp) / "compiler"
            compiler.mkdir()
            (compiler / "trustc").write_text(f"#!/bin/sh\necho '{sysroot}'\n")
            (compiler / "trustc").chmod(0o700)
            packaged = GATE.proof_tool_identities({"PATH": str(prefix / "bin"), "HOME": str(home)})
            toolchain = GATE.proof_tool_identities(
                {"PATH": os.pathsep.join([str(prefix / "bin"), str(compiler)]), "HOME": str(home)})
            bare = GATE.proof_tool_identities({"PATH": str(plain), "HOME": str(home)})
            override = GATE.proof_tool_identities({
                "PATH": str(plain), "HOME": str(home),
                "AY_SOLVER_PATH": str(plain / "ay"), "TCG_EXTERNAL_CLEAN_CHECKER": str(plain / "clean"),
            })
            broken = GATE.proof_tool_identities({
                "PATH": str(plain), "HOME": str(home), "TCG_EXTERNAL_CLEAN_CHECKER": str(plain / "absent"),
            })
        # Clean comes from the package store; AY never does (ay_identity.rs):
        # only the build toolchain's bin/ay or an absolute override.
        self.assertEqual(packaged["clean"]["route"], "aterm-packaged")
        self.assertTrue(packaged["clean"]["pinned"])
        self.assertEqual(packaged["clean"]["resolved"], str((prefix / "store" / "clean" / "current" / "bin" / "clean").resolve()))
        self.assertEqual(len(packaged["clean"]["sha256"]), 64)
        self.assertIsNone(packaged["ay"]["resolved"])
        self.assertEqual(toolchain["ay"]["route"], "toolchain-sysroot")
        self.assertTrue(toolchain["ay"]["pinned"])
        self.assertEqual(toolchain["ay"]["resolved"], str((sysroot / "bin" / "ay").resolve()))
        self.assertEqual(GATE.proof_tool_problems(toolchain), [])
        for tool in ("ay", "clean"):
            self.assertTrue(override[tool]["pinned"])
            self.assertTrue(override[tool]["route"].startswith("env-override:"))
        self.assertEqual(GATE.proof_tool_problems(override), [])
        problems = GATE.proof_tool_problems(packaged)
        self.assertEqual(len(problems), 1)
        self.assertIn("ay: no executable resolves (build with a Trust toolchain", problems[0])
        # A bare `ay` on PATH is never consulted; a generic `clean` on PATH is
        # never a checker.
        self.assertIsNone(bare["ay"]["resolved"])
        self.assertIsNone(bare["clean"]["resolved"])
        problems = GATE.proof_tool_problems(bare)
        self.assertEqual(len(problems), 2)
        self.assertIn("ay: no executable resolves", problems[0])
        self.assertIn("clean: no executable resolves", problems[1])
        self.assertIn("error", broken["clean"])
        self.assertTrue(any(problem.startswith("clean: TCG_EXTERNAL_CLEAN_CHECKER=") for problem in GATE.proof_tool_problems(broken)))
        self.assertEqual(GATE.proof_tool_changes(toolchain, toolchain), [])
        self.assertEqual(len(GATE.proof_tool_changes(toolchain, bare)), 2)

    def test_require_proof_tools_refuses_unpinned_tools_before_any_target(self):
        unpinned = (proof_tool_record(pinned=False),)
        with tempfile.TemporaryDirectory() as temp:
            code, report, stderr, marker = self.run_main_with_fixture(temp, {}, "--require-proof-tools", proof_tools=unpinned)
            self.assertFalse(marker.exists(), "a refused environment must not run Cargo")
        self.assertEqual((code, report["status"]), (1, "fail"))
        self.assertEqual(report["targets"], [])
        self.assertTrue(report["controls"]["require_proof_tools"])
        self.assertEqual(report["proof_tools"], proof_tool_record(pinned=False))
        self.assertNotIn("final_proof_tools", report)
        self.assertTrue(report["errors"])
        self.assertTrue(all(error.startswith("--require-proof-tools: ") for error in report["errors"]), report["errors"])
        self.assertIn("refuses this environment", stderr)
        self.assertIn("no executable resolves", stderr)
        # Without the control the run keeps its result but is labelled, so a
        # proof-replay failure can be attributed to provisioning.
        with tempfile.TemporaryDirectory() as temp:
            code, report, stderr, marker = self.run_main_with_fixture(temp, {}, proof_tools=unpinned + unpinned)
            self.assertTrue(marker.exists())
        self.assertEqual((code, report["status"]), (0, "pass"), report)
        self.assertFalse(report["controls"]["require_proof_tools"])
        self.assertEqual(report["final_proof_tools"], proof_tool_record(pinned=False))
        self.assertIn("proof-replay targets may fail for that reason alone", stderr)

    def test_require_proof_tools_runs_and_binds_pinned_identities_before_and_after(self):
        with tempfile.TemporaryDirectory() as temp:
            code, report, stderr, marker = self.run_main_with_fixture(temp, {}, "--require-proof-tools")
            self.assertTrue(marker.exists())
        self.assertEqual((code, report["status"]), (0, "pass"), report)
        self.assertEqual(report["proof_tools"], proof_tool_record())
        self.assertEqual(report["final_proof_tools"], proof_tool_record())
        self.assertNotIn("proof-replay targets may fail", stderr)
        self.assertEqual(report["ay_admission"], {"admitted": True})
        self.assertEqual(len(report["_admission_calls"]), 1)
        # Without the control the rule is not asked (nothing is built for it).
        with tempfile.TemporaryDirectory() as temp:
            _, report, _, _ = self.run_main_with_fixture(temp, {})
        self.assertEqual(report["_admission_calls"], [])
        self.assertNotIn("ay_admission", report)

    def test_require_proof_tools_refuses_an_ay_the_identity_rule_does_not_admit_before_any_target(self):
        detail = ("[TCG-AY-IDENTITY-UNMATERIALIZED] /fixture/pkg/store/ay/current/bin/ay (toolchain-pinned-ay) was "
                  "admitted, but no private copy of its bytes could be made to start from: /cache/trust-cg has mode "
                  "0775: others may rename entries in it, so no AY is started beneath it; run `chmod go-w "
                  "/cache/trust-cg` or set XDG_CACHE_HOME to a directory only this user can write")
        refused = ({"admitted": False}, [f"AY admission: the CLI under test refuses AY /fixture/ay: {detail}"])
        with tempfile.TemporaryDirectory() as temp:
            code, report, stderr, marker = self.run_main_with_fixture(
                temp, {}, "--require-proof-tools", ay_admission=refused)
            self.assertFalse(marker.exists(), "a refused AY must not run any target")
        self.assertEqual((code, report["status"]), (1, "fail"))
        self.assertEqual(report["targets"], [])
        self.assertEqual(report["ay_admission"], {"admitted": False})
        self.assertEqual(report["errors"], [f"--require-proof-tools: {refused[1][0]}"])
        self.assertIn("the AY identity rule does not admit the resolved AY", stderr)
        self.assertIn("`chmod go-w /cache/trust-cg`", stderr)
        # An environment already refused is not built for.
        with tempfile.TemporaryDirectory() as temp:
            _, report, _, _ = self.run_main_with_fixture(
                temp, {}, "--require-proof-tools", proof_tools=(proof_tool_record(pinned=False),))
        self.assertEqual(report["_admission_calls"], [])

    def admission_fixture(self, root: Path, *, answer: str = "admitted", build_exit: int = 0,
                          executable: bool = True) -> tuple[dict, Path, Path, Path]:
        """A real AY file and private copy, a fake CLI answering --print-ay-identity, and a fake Cargo."""
        ay = root / "toolchain" / "bin" / "ay"
        ay.parent.mkdir(parents=True)
        ay.write_bytes(b"#!/bin/sh\n# fixture ay\n")
        ay.chmod(0o755)
        sha = hashlib.sha256(ay.read_bytes()).hexdigest()
        copy = root / "cache" / "trust-cg" / "ay-exec" / sha / "ay"
        copy.parent.mkdir(parents=True)
        # Every directory of the cache tree 0700 whatever the umask, as the
        # real CLI creates them: admission judges the copy's canonical path.
        for directory in (root / "cache", root / "cache" / "trust-cg", copy.parent.parent, copy.parent):
            directory.chmod(0o700)
        copy.write_bytes(ay.read_bytes())
        copy.chmod(0o500)
        environment_seen = root / "cli-environment.json"
        report = {"schema": "trust-cg.ay-identity.v2", "admitted": answer == "admitted"}
        if answer == "admitted":
            report.update({"path": str(ay.resolve()), "exec_path": str(copy), "sha256": sha})
        else:
            report.update({"code": "TCG-AY-IDENTITY-UNMATERIALIZED",
                           "detail": "[TCG-AY-IDENTITY-UNMATERIALIZED] /cache/trust-cg has mode 0775; "
                                     "run `chmod go-w /cache/trust-cg`"})
        cli = root / "fake-trust-cg"
        cli.write_text(
            f"{PYTHON_FIXTURE_HEADER}import json, os, sys\n"
            "assert sys.argv[1:] == ['--print-ay-identity'], sys.argv\n"
            f"open({str(environment_seen)!r}, 'w').write(json.dumps(dict(os.environ)))\n"
            f"print(json.dumps({report!r}))\n"
            f"raise SystemExit({0 if answer == 'admitted' else 1})\n"
        )
        cli.chmod(0o700)
        arguments = root / "cargo-arguments"
        artifact = {"reason": "compiler-artifact", "target": {"name": "trust-cg", "kind": ["bin"]},
                    "executable": str(cli)}
        library = {"reason": "compiler-artifact", "target": {"name": "trust-cg-cli", "kind": ["lib"]},
                   "executable": None}
        cargo = root / "cargo-fixture"
        cargo.write_text(
            f"{PYTHON_FIXTURE_HEADER}import json, os, sys\n"
            f"open({str(arguments)!r}, 'w').write(json.dumps([sys.argv[1:], sorted(os.environ)]))\n"
            "print('   Compiling trust-cg-cli (human text on stderr)', file=sys.stderr)\n"
            f"print(json.dumps({library!r}))\n"
            + (f"print(json.dumps({artifact!r}))\n" if executable else "")
            + "print('[1, 2]')\n"
            + f"raise SystemExit({build_exit})\n"
        )
        cargo.chmod(0o700)
        record = {"resolved": str(ay.resolve()), "route": "toolchain-sysroot", "pinned": True, "sha256": sha,
                  "bytes": ay.stat().st_size}
        return record, cargo, arguments, environment_seen

    def run_admission(self, root: Path, provenance: dict, record: dict, **environment: str):
        output = root / "out"
        output.mkdir()
        with mock.patch.dict(os.environ, environment):
            return GATE.ay_admission_preflight(
                provenance, record, output, jobs=3, offline=True, timeout_seconds=30, max_rss_gib=None)

    def test_ay_admission_preflight_asks_the_real_cli_built_with_the_floor_command(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            record, cargo, arguments, seen = self.admission_fixture(root)
            # Trust lane: the checker selection must not become a runner of the build.
            provenance = {"lane": "trust-unverified", "build_command": [str(cargo)],
                          "tools": {"env": "/usr/bin/env"},
                          "runtime_checker_environment": {"TCG_EXTERNAL_CLEAN_CHECKER": "/checker"}}
            result, problems = self.run_admission(
                root, provenance, record, XDG_CACHE_HOME=str(root / "cache"), PROPTEST_CASES="1")
            argv, cargo_environment = json.loads(arguments.read_text())
            cli_environment = json.loads(seen.read_text())
        self.assertEqual(problems, [])
        self.assertTrue(result["admitted"])
        self.assertEqual(result["executable"], str(root / "fake-trust-cg"))
        self.assertEqual(argv, ["build", "--locked", "--offline", "--color", "never", "-j", "3",
                                "-p", "trust-cg-cli", "--bin", "trust-cg",
                                "--message-format", "json-render-diagnostics"])
        self.assertNotIn("PROPTEST_CASES", cargo_environment)
        # The CLI sees the targets' runtime environment: the cache root, not the scrubbed names.
        self.assertEqual(cli_environment["XDG_CACHE_HOME"], str(root / "cache"))
        self.assertNotIn("PROPTEST_CASES", cli_environment)
        self.assertEqual(result["admission"]["report"]["sha256"], record["sha256"])

    def test_ay_admission_preflight_fails_closed_with_the_rules_own_refusal(self):
        cases = {
            "refused": ({"answer": "refused"}, "`chmod go-w /cache/trust-cg`"),
            "build": ({"build_exit": 7}, "building trust-cg-cli to ask the AY identity rule failed (exit 7"),
            "no executable": ({"executable": False}, "Cargo reported no trust-cg executable"),
        }
        for name, (options, expected) in cases.items():
            with self.subTest(name), tempfile.TemporaryDirectory() as temp:
                root = Path(temp)
                record, cargo, _, _ = self.admission_fixture(root, **options)
                result, problems = self.run_admission(root, trust_lane_provenance(str(cargo)), record)
            self.assertEqual(len(problems), 1, problems)
            self.assertTrue(problems[0].startswith("AY admission: "), problems)
            self.assertIn(expected, problems[0])
            self.assertFalse(result.get("admitted", False))
        # Admitted bytes that are not the resolved AY's are refused too.
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            record, cargo, _, _ = self.admission_fixture(root)
            _, problems = self.run_admission(root, trust_lane_provenance(str(cargo)), {**record, "sha256": "d" * 64})
        self.assertTrue(any("not the admitted sha256" in problem or "digest to" in problem for problem in problems),
                        problems)

    def test_built_executable_reads_only_the_bin_artifact(self):
        messages = "\n".join([
            "not json", "[1]", json.dumps({"reason": "build-finished", "success": True}),
            json.dumps({"reason": "compiler-artifact", "target": {"name": "trust-cg", "kind": ["lib"]},
                        "executable": "/wrong/lib"}),
            json.dumps({"reason": "compiler-artifact", "target": {"name": "trust-cg", "kind": ["bin"]},
                        "executable": "/right/trust-cg"}),
        ])
        self.assertEqual(GATE.built_executable(messages, "trust-cg"), "/right/trust-cg")
        self.assertIsNone(GATE.built_executable(messages, "other"))

    def test_proof_tool_identity_change_during_the_run_fails(self):
        swapped = (proof_tool_record(), proof_tool_record(sha="d" * 64))
        with tempfile.TemporaryDirectory() as temp:
            code, report, _, marker = self.run_main_with_fixture(temp, {}, proof_tools=swapped)
            self.assertTrue(marker.exists())
        self.assertEqual((code, report["status"]), (1, "fail"))
        self.assertEqual(report["targets"][0]["status"], "pass")
        self.assertTrue(any(error.startswith("proof tool identity changed while required targets were running: ay:")
                            for error in report["errors"]), report["errors"])


if __name__ == "__main__":
    unittest.main()
