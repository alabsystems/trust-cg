from __future__ import annotations

import ast
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "check_darwin_aarch64.py"
SPEC = importlib.util.spec_from_file_location("check_darwin_aarch64", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
GATE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GATE)
CHANNEL = GATE.toolchain_channel()


def transcript(passed=1, failed=0, ignored=0, filtered=0, output="", started=None, rollup=True):
    """A libtest --show-output transcript with named results."""
    names = [f"case_{index}" for index in range(passed)]
    lines = [f"running {passed + failed + ignored if started is None else started} tests"]
    lines += [f"test {name} ... ok" for name in names]
    lines += [f"test broken_{index} ... FAILED" for index in range(failed)]
    lines += [f"test parked_{index} ... ignored" for index in range(ignored)]
    lines += ["", "successes:", ""]
    if output and names:
        lines += [f"---- {names[0]} stdout ----", output, ""]
    lines += ["", "successes:", *[f"    {name}" for name in names], ""]
    if rollup:
        state = "FAILED" if failed else "ok"
        lines.append(
            f"test result: {state}. {passed} passed; {failed} failed; {ignored} ignored; "
            f"0 measured; {filtered} filtered out; finished in 0.01s"
        )
    return "\n".join(lines) + "\n"


def dependency_record(resolves=True, tree="a" * 64):
    """A scripts/dependency_identity.py record with one companion source."""
    return {
        "schema": "trust-cg-dependency-identity-v1", "lockfile_sha256": "b" * 64, "errors": [],
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


class DarwinAarch64GateTests(unittest.TestCase):
    def test_shrink_wrap_requires_the_complete_native_matrix_marker(self):
        self.assertIn(("trust-cg-codegen", "aarch64_shrink_wrap_region_exit", 2), GATE.TARGETS)
        line = GATE.SHARED.target_required_lines("trust-cg-codegen", "aarch64_shrink_wrap_region_exit")[0]
        with tempfile.TemporaryDirectory() as temp:
            for index, (printed, expected) in enumerate((
                (line, "pass"),
                ("test native ... " + line, "pass"),
                ("SHRINK_WRAP_REGION_EXIT_NATIVE levels=3 checked_per_level=24", "fail"),
                ("SHRINK_WRAP_REGION_EXIT_NATIVE levels=4 checked_per_level=0", "fail"),
                ("prefix" + line, "fail"),
                ("", "fail"),
            )):
                with self.subTest(printed=printed):
                    result = GATE.run_target(
                        [sys.executable, "-c", f"print({transcript(2, output=printed)!r})"],
                        Path(temp) / f"shrink-wrap-{index}.log", 5,
                        root=ROOT, grace_seconds=0.05, minimum=2, required_lines=(line,),
                    )
                    self.assertEqual(result["status"], expected, result)
                    self.assertEqual(result["required_lines"], [line])

    def test_required_inventory_matches_source_census_and_linux_floor(self):
        # Membership is the source census plus the Linux cross-check in
        # inventory_problems(); the rows are not restated here.
        self.assertEqual(GATE.inventory_problems(), [])
        rows = {(package, target) for package, target, _ in GATE.TARGETS}
        self.assertEqual(len(rows), len(GATE.TARGETS))
        self.assertEqual(
            GATE.SHARED.target_features("trust-cg-llvm-import", "bitreverse_intrinsics"), ("driver",)
        )
        self.assertEqual(GATE.SHARED.target_features("trust-cg-llvm-import", "fp_e2e"), ("driver",))
        self.assertIn("trust-cg-codegen/jit_wx_refusal", GATE.linux_only_leg_targets())
        # Every Linux-floor target is either run here or reported uncovered.
        self.assertEqual(set(GATE.SHARED.TARGETS) - rows, set(GATE.DARWIN_COMPILED_OUT))
        for package, target, minimum in GATE.TARGETS:
            self.assertGreaterEqual(minimum, 1)
            self.assertTrue(GATE.target_path(package, target).is_file(), target)
        self.assertIn("trust-cg-codegen/e2e_aarch64_elf_tlsie", GATE.linux_only_leg_targets())
        self.assertIn("trust-cg-codegen/e2e_aarch64_globals_linux", GATE.linux_only_leg_targets())
        # L01-P7: host-neutral minimum; its native rows are Linux-only legs.
        self.assertIn("trust-cg-codegen/e2e_aarch64_f16_abi_linux", GATE.linux_only_leg_targets())
        self.assertIn("trust-cg-codegen/e2e_aarch64_eh_linux", GATE.linux_only_leg_targets())
        self.assertIn(
            "trust-cg-codegen/aarch64_nounwind_tail_frame", GATE.linux_only_leg_targets()
        )
        self.assertIn(("trust-cg-codegen", "aarch64_nounwind_tail_frame", 1), GATE.TARGETS)
        self.assertIn(("trust-cg-codegen", "a64_refine_byte_invariance", 6), GATE.TARGETS)
        # LD-56: the native-helper sited assertion delivery target is required
        # here at its file census; the x86-64 ones are out of scope.
        self.assertIn(("trust-cg-codegen", "sited_assert_delivery_native", 2), GATE.TARGETS)
        for name in ("e2e_x86_64_i128_stack_abi", "e2e_x86_64_jump_table_selector_width"):
            self.assertIn(name, GATE.OUT_OF_SCOPE)
        # Linux-only static ELF scalar-cell binding (file-level target_os = "linux").
        self.assertIn(("trust-cg-verify", "aarch64_scalar_cell_link"), GATE.DARWIN_COMPILED_OUT)
        # L05-P11: the dialect legalization corpus is a floor row on both hosts.
        dialect_row = ("trust-cg-codegen", "dialect_legalization_corpus")
        self.assertIn(dialect_row, rows)
        self.assertIn(dialect_row, set(GATE.SHARED.TARGETS))
        # L07-P2: the memory-effect binding and the corpus decomposition are
        # required on both floors at their file census.
        for row in (
            ("trust-cg-codegen", "aarch64_memory_effect_binding", 4),
            ("trust-cg-verify", "aarch64_memory_effect_queries", 2),
            ("trust-cg-codegen", "aarch64_memory_source_binding", 4),
            # L03-P3: the memory-order mapping (with its macOS clang
            # differential).
            ("trust-cg-codegen", "aarch64_memory_order_obligations", 5),
            # L04-P6: the live NEON silicon differential.
            ("trust-cg-verify", "aarch64_neon_silicon_differential", 11),
            ("trust-cg-codegen", "e2e_aarch64_neon_admission", 3),
            # L11-P2: the installed-artifact replay of the verifying JIT.
            ("trust-cg-codegen", "jit_installed_artifact_replay", 3),
            # L04-P3: the scalar FP IEEE 754 differentials.
            ("trust-cg-verify", "aarch64_fp_ieee_differential", 10),
            ("trust-cg-codegen", "e2e_aarch64_fp_ieee_lowering", 5),
            # L04-P1 / X-OPCODES-P2: the atomic and scalar memory-effect
            # silicon differentials.
            ("trust-cg-verify", "aarch64_atomic_silicon_differential", 2),
            ("trust-cg-verify", "aarch64_scalar_memory_silicon_differential", 1),
            # L04-P1: the CRC32/CRC32C silicon differential.
            ("trust-cg-verify", "aarch64_crc32_silicon_differential", 2),
            # L04-P1: the SUBS #imm silicon differential.
            ("trust-cg-verify", "aarch64_subs_imm_silicon_differential", 2),
            # L04-P1: the NEON LD1/ST1 form-theorem silicon differential.
            ("trust-cg-verify", "aarch64_neon_structure_silicon_differential", 2),
            # X-LEAN-P3: the Lean A64 golden corpus binding.
            ("trust-cg-codegen", "lean_a64_encode_golden_binding", 4),
        ):
            self.assertIn(row, GATE.TARGETS)
            self.assertIn(row[:2], set(GATE.SHARED.TARGETS))
        # L03-P3: the native litmus harness runs on macOS only, so it is a
        # Darwin floor row and stays off the Linux floor.
        litmus = ("trust-cg-codegen", "e2e_aarch64_memory_order_litmus", 2)
        self.assertIn(litmus, GATE.TARGETS)
        self.assertNotIn(litmus[:2], set(GATE.SHARED.TARGETS))
        # L04-P12: the trap-expansion binding is on both floors; its native
        # execution is a Darwin floor row only (macOS-guarded JIT and SIGTRAP).
        self.assertIn(("trust-cg-codegen", "aarch64_trap_expansion_binding", 4), GATE.TARGETS)
        self.assertIn(
            ("trust-cg-codegen", "aarch64_trap_expansion_binding"), set(GATE.SHARED.TARGETS)
        )
        self.assertIn(("trust-cg-codegen", "e2e_aarch64_trap_expansion_native", 1), GATE.TARGETS)
        self.assertNotIn(
            ("trust-cg-codegen", "e2e_aarch64_trap_expansion_native"), set(GATE.SHARED.TARGETS)
        )
        # Three origin/main native files the inventory check found unclassified
        # are Darwin floor rows at their file census.
        for row in (
            ("trust-cg-codegen", "a64_refine_byte_invariance", 6),
            ("trust-cg-codegen", "aarch64_mem_pair_acquire_order", 2),
            ("trust-cg-codegen", "must_refuse_corpus", 5),
        ):
            self.assertIn(row, GATE.TARGETS)
        # L10-P5: the identity-admission corruption controls and freshness
        # property are required on both floors at their file census.
        for row in (
            ("trust-cg-opt", "mach_id_admission", 6),
            ("trust-cg-codegen", "mach_id_admission_property", 5),
        ):
            self.assertIn(row, GATE.TARGETS)
            self.assertIn(row[:2], set(GATE.SHARED.TARGETS))
            self.assertEqual(GATE.SHARED.TARGET_MINIMUM_PASSES[row[:2]], row[2])
        # L02-P5: the linked-image evidence targets are Darwin floor rows, and
        # stay off the Linux floor (their native legs are Mach-O and ld64).
        for row in (
            ("trust-cg-codegen", "macho_linked_image_evidence"),
            ("trust-cg-cli", "linked_image_evidence"),
        ):
            self.assertIn(row, rows)
            self.assertNotIn(row, set(GATE.SHARED.TARGETS))

    def test_classification_tables_have_no_duplicate_keys(self):
        # A dict literal keeps only the last of two equal keys, silently. Two
        # merges once each added an aarch64_scalar_cell_link row to
        # DARWIN_COMPILED_OUT, so one reason vanished at import and deleting
        # either row would have left the target still classified.
        tree = ast.parse(SCRIPT.read_text(encoding="utf-8"), filename=str(SCRIPT))
        duplicates = []
        for node in ast.walk(tree):
            if not isinstance(node, ast.Dict):
                continue
            seen = set()
            for key in node.keys:
                if key is None:
                    continue
                spelled = ast.unparse(key)
                if spelled in seen:
                    duplicates.append(f"line {key.lineno}: {spelled}")
                seen.add(spelled)
        self.assertEqual(duplicates, [])

    def test_inventory_census_refuses_drift_and_inconsistent_rows(self):
        # A macOS-guarded family outside the Linux floor (Swift ABI stays macOS-only).
        without_swift = tuple(row for row in GATE.TARGETS if row[1] != "e2e_aarch64_swift_scalar")
        without_linux = tuple(row for row in GATE.TARGETS if row[1] != "aarch64_cmp_admission")
        cases = {
            "unclassified": without_swift,
            "neither required nor reported": without_linux,
            "duplicate required target": GATE.TARGETS + (GATE.TARGETS[0],),
            "exceeds its #[test] functions": GATE.TARGETS[:-1] + (("trust-cg-codegen", "o3_debug_lldb_line_200loc", 3),),
            "file-level Linux cfg": GATE.TARGETS + (("trust-cg-codegen", "e2e_aarch64_elf_link", 1),),
            "minimum must be a positive integer": GATE.TARGETS[:-1] + (("trust-cg-codegen", "o3_debug_lldb_line_200loc", 0),),
            "missing test file": GATE.TARGETS + (("trust-cg-codegen", "no_such_darwin_target", 1),),
        }
        for message, targets in cases.items():
            with self.subTest(message=message), mock.patch.object(GATE, "TARGETS", targets):
                problems = GATE.inventory_problems()
                self.assertTrue(any(message in problem for problem in problems), problems)
        bogus = {**GATE.DARWIN_COMPILED_OUT, ("trust-cg-codegen", "e2e_aarch64_atomics"): "fixture"}
        with mock.patch.object(GATE, "DARWIN_COMPILED_OUT", bogus):
            problems = GATE.inventory_problems()
        self.assertTrue(any("both required and compiled out" in problem for problem in problems))
        self.assertTrue(any("no file-level Linux cfg" in problem for problem in problems))

    def test_linux_linker_requirements_are_checked_against_both_floors_and_not_set_here(self):
        # The Linux floor's TCG_REQUIRE_LLD/GOLD rows are ELF three-linker legs,
        # compiled out on Darwin: the table is checked against both floors'
        # rows, and the Darwin runner sets no target environment.
        rows = [(package, target) for package, target, _ in GATE.TARGETS]
        all_rows = rows + [row for row in GATE.SHARED.TARGETS if row not in rows]
        self.assertEqual(GATE.SHARED.environment_problems(rows=all_rows), [])
        self.assertIn(("trust-cg-cli", "link_options"), rows)
        self.assertEqual(
            GATE.SHARED.target_environment("trust-cg-cli", "link_options"),
            {"TCG_REQUIRE_LLD": "1", "TCG_REQUIRE_GOLD": "1"},
        )
        self.assertNotIn("set_environment", GATE.run_target.__code__.co_varnames)
        stale = {**GATE.SHARED.TARGET_ENVIRONMENT, ("trust-cg-codegen", "no_such_target"): {"TCG_REQUIRE_LLD": "1"}}
        with mock.patch.object(GATE.SHARED, "TARGET_ENVIRONMENT", stale):
            problems = GATE.inventory_problems()
        self.assertTrue(any("TARGET_ENVIRONMENT entry names no required target" in p for p in problems), problems)

    def test_list_is_read_only_and_does_not_probe_tools(self):
        with mock.patch.object(GATE, "preflight", side_effect=AssertionError("probed")):
            with mock.patch.object(GATE.tempfile, "mkdtemp", side_effect=AssertionError("wrote")):
                stdout = io.StringIO()
                with contextlib.redirect_stdout(stdout):
                    self.assertEqual(GATE.main(["--list"]), 0)
                lines = stdout.getvalue().splitlines()
                self.assertEqual(lines, [
                    " ".join((p, t, str(m), *GATE.SHARED.feature_arguments(p, t))) for p, t, m in GATE.TARGETS
                ])
                self.assertIn("trust-cg-llvm-import cast_e2e 1 --features driver", lines)
                stdout = io.StringIO()
                with contextlib.redirect_stdout(stdout):
                    self.assertEqual(GATE.main(["--list", "--only", "trust-cg-codegen/e2e_aarch64_atomics"]), 0)
                self.assertEqual(stdout.getvalue().splitlines(), ["trust-cg-codegen e2e_aarch64_atomics 3"])
                with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as raised:
                    GATE.main(["--list", "--only", "e2e_aarch64"])
                self.assertEqual(raised.exception.code, 2)

    def test_non_darwin_or_non_arm64_host_is_refused_before_any_tool_probe(self):
        with mock.patch.object(GATE.shutil, "which", side_effect=AssertionError("probed a tool")):
            for platform_name, machine in (("linux", "aarch64"), ("darwin", "x86_64"), ("win32", "ARM64")):
                with self.subTest(platform=platform_name, machine=machine):
                    with mock.patch.object(GATE.sys, "platform", platform_name), \
                            mock.patch.object(GATE.platform, "machine", return_value=machine):
                        with self.assertRaisesRegex(RuntimeError, "required Darwin host is aarch64-apple-darwin"):
                            GATE.preflight({"PATH": "/fixture"})

    def fake_toolchain(
        self, *, rustc_host=GATE.HOST, binary="trustc", cargo=None, machine="arm64",
        sysroot_digest="0" * 64, cargo_configs=(), package_error=None,
    ):
        cargo = "targo 1.99.0-dev (fixture 2026-09-17) (targo 0.1.0)\nrelease: 1.99.0-dev" if cargo is None else cargo
        package = {
            "compiler": "/fixture/pkg/bin/trustc", "targo": "/fixture/pkg/bin/targo",
            "sysroot": "/fixture/pkg", "commit": "a" * 40, "launchers": None, "lane": "unverified",
        }

        def probe(command, environment=None, *, stdout_only=False):
            name = Path(command[0]).name
            if name == "trustc" and command[1:] == ["-vV"]:
                assert not any(key.startswith(("TRUST_CG_", "TCG_")) for key in (environment or {}))
                return f"rustc 1.99.0-dev (fixture)\nbinary: {binary}\nhost: {rustc_host}\nrelease: 1.99.0-dev"
            if name == "targo":
                assert command[1:] == ["--unverified", "-vV"], command
                return cargo
            if name == "uname":
                return machine
            return f"{name} identity fixture"

        def which(name, path=None):
            return f"/fixture/bin/{name}"

        def trust_package(environment):
            if package_error is not None:
                raise RuntimeError(package_error)
            return package

        stack = contextlib.ExitStack()
        stack.enter_context(mock.patch.object(GATE.sys, "platform", "darwin"))
        stack.enter_context(mock.patch.object(GATE.platform, "machine", return_value="arm64"))
        stack.enter_context(mock.patch.object(GATE.shutil, "which", side_effect=which))
        stack.enter_context(mock.patch.object(GATE, "probe", side_effect=probe))
        stack.enter_context(mock.patch.object(GATE, "trust_package", side_effect=trust_package))
        stack.enter_context(mock.patch.object(GATE, "file_sha256", return_value=sysroot_digest))
        stack.enter_context(mock.patch.object(GATE, "cargo_config_files", return_value=list(cargo_configs)))
        stack.enter_context(mock.patch.object(GATE, "source_provenance", return_value={
            "source_sha": "fixture", "dirty": False, "source_fingerprint": "fixture",
        }))
        return stack

    def test_preflight_pins_the_trust_package_and_records_tool_identities(self):
        with self.fake_toolchain():
            provenance = GATE.preflight({"PATH": "/fixture", "TRUST_CG_RUN_FORMAL_PROOF_TESTS": "1"})
        self.assertEqual(provenance["host"], GATE.HOST)
        self.assertEqual(provenance["channel"], "trust")
        self.assertEqual(CHANNEL, "trust")
        self.assertNotIn("path_prelude", provenance)
        for tool in ("cc", "clang", "ld", "otool", "dwarfdump", "lldb", "nm", "objdump", "git"):
            self.assertEqual(provenance["tool_identities"][tool]["identity"], f"{tool} identity fixture")
        self.assertIn(f"host: {GATE.HOST}", provenance["rustc"])
        self.assertTrue(provenance["cargo"].startswith("targo "))
        self.assertEqual(provenance["tools"]["trustc"], "/fixture/pkg/bin/trustc")
        self.assertEqual(provenance["tools"]["targo"], "/fixture/pkg/bin/targo")
        self.assertEqual(provenance["trust_package"]["commit"], "a" * 40)
        self.assertEqual(provenance["tool_identities"]["ld"]["command"], ["ld", "-v"])
        self.assertEqual(provenance["tool_identities"]["codesign"], {
            "command": [GATE.WHAT, "codesign"], "identity": "what identity fixture",
        })
        self.assertEqual(provenance["tools"]["codesign"], "/fixture/bin/codesign")
        self.assertEqual(provenance["rustc_sha256"], "0" * 64)
        self.assertEqual(provenance["cargo_sha256"], "0" * 64)
        # The proof-required JIT targets' results are bound to the
        # toolchain's own AY and Clean (and an overlay's manifest).
        self.assertEqual(provenance["proof_tools"], {
            "sysroot_ay": "0" * 64, "sysroot_clean": "0" * 64, "overlay_manifest": "0" * 64,
        })
        self.assertEqual(provenance["cargo_configs"], {})

    def test_preflight_records_absent_proof_tools_as_null(self):
        def digest(path):
            return None if Path(path).name in ("ay", "clean", "overlay.json") else "0" * 64

        with self.fake_toolchain(), mock.patch.object(GATE, "file_sha256", side_effect=digest):
            provenance = GATE.preflight({"PATH": "/fixture"})
        self.assertEqual(provenance["proof_tools"], {
            "sysroot_ay": None, "sysroot_clean": None, "overlay_manifest": None,
        })
        self.assertEqual(provenance["rustc_sha256"], "0" * 64)

    def test_preflight_refuses_wrong_toolchain_or_bypassing_environment(self):
        cases = (
            ({"rustc_host": "x86_64-apple-darwin"}, {}, "observed trustc host"),
            ({"binary": "rustc"}, {}, "branded trustc"),
            ({"cargo": "cargo 1.99.0-dev (fixture)"}, {}, "required targo"),
            ({"package_error": "no installed Trust package resolves"}, {}, "no installed Trust package"),
            ({"machine": "x86_64"}, {}, "required arm64 machine"),
            ({}, {"RUSTC": "/fixture/rustc"}, "RUSTC would bypass"),
            ({}, {"RUSTC_WRAPPER": "sccache"}, "RUSTC_WRAPPER would bypass"),
            ({}, {"CARGO_BUILD_RUSTC": "/fixture/rustc"}, "CARGO_BUILD_RUSTC would bypass"),
            ({}, {"RUSTUP_TOOLCHAIN": "1.97.1"}, "RUSTUP_TOOLCHAIN selects"),
            ({}, {"CARGO_BUILD_TARGET": "aarch64-unknown-linux-gnu"}, "CARGO_BUILD_TARGET"),
            ({}, {"CARGO_TARGET_AARCH64_APPLE_DARWIN_RUNNER": "/fixture/runner"}, "RUNNER would bypass"),
            ({"sysroot_digest": None}, {}, "lacks bin/targo, bin/trustc"),
        )
        for toolchain, environment, message in cases:
            with self.subTest(message=message), self.fake_toolchain(**toolchain):
                with self.assertRaisesRegex(RuntimeError, message):
                    GATE.preflight({"PATH": "/fixture", **environment})

    def test_cargo_config_compiler_or_runner_reroute_is_refused_and_configs_are_hashed(self):
        rerouting = {
            "table rustc": '[build]\nrustc = "/fixture/trustc"\n',
            "table wrapper": '[build]\njobs = 2\nrustc-wrapper = "sccache"\n',
            "dotted workspace wrapper": 'build.rustc-workspace-wrapper = "/fixture/wrap"\n',
            "triple runner": '[target.aarch64-apple-darwin]\nrunner = "/fixture/runner"\n',
            "dotted cfg runner": "target.'cfg(target_os = \"macos\")'.runner = [\"/fixture/runner\"]\n",
        }
        with tempfile.TemporaryDirectory() as temp:
            for label, text in rerouting.items():
                config = Path(temp) / f"{label.replace(' ', '-')}.toml"
                config.write_text(text)
                with self.subTest(config=label), self.fake_toolchain(cargo_configs=[config]):
                    with self.assertRaisesRegex(RuntimeError, "Cargo config .* sets"):
                        GATE.preflight({"PATH": "/fixture"})
            benign = Path(temp) / "benign.toml"
            benign.write_text('# rustc = "/commented/out"\n[build]\njobs = 2\n[env]\nRUST_MIN_STACK = "1"\n')
            with self.fake_toolchain(cargo_configs=[benign]):
                provenance = GATE.preflight({"PATH": "/fixture"})
            self.assertEqual(list(provenance["cargo_configs"]), [str(benign)])
            self.assertEqual(len(provenance["cargo_configs"][str(benign)]), 64)
        # The repository's own Cargo config is loaded and never mistaken for a reroute.
        repository_config = ROOT / ".cargo" / "config.toml"
        self.assertIsNone(GATE.CARGO_CONFIG_REROUTE.search(repository_config.read_text()))
        with tempfile.TemporaryDirectory() as temp:
            (Path(temp) / "config.toml").write_text("[build]\njobs = 1\n")
            files = GATE.cargo_config_files({"CARGO_HOME": temp})
        self.assertIn(repository_config, files)
        self.assertIn(Path(temp) / "config.toml", files)
        self.assertEqual(len({path.resolve() for path in files}), len(files))

    def test_native_home_and_empty_compatibility_selection_cover_the_actual_config(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            native = root / "native"
            native.mkdir()
            config = native / "config.toml"
            config.write_text('[build]\nrustc = "/wrong/compiler"\n')
            environment = {"TARGO_HOME": str(native), "HOME": temp}
            self.assertIn(config, GATE.cargo_config_files(environment))
            with self.assertRaises(RuntimeError):
                GATE.cargo_config_identity(environment)
            self.assertNotIn(config, GATE.cargo_config_files({**environment, "CARGO_HOME": ""}))

    def test_missing_host_tool_is_refused(self):
        with self.fake_toolchain():
            with mock.patch.object(GATE.shutil, "which", side_effect=lambda name, path=None: None):
                with self.assertRaisesRegex(RuntimeError, "required tool is missing"):
                    GATE.preflight({"PATH": "/fixture"})

    def test_child_environment_keeps_the_callers_path_and_never_auto_installs(self):
        environment = GATE.child_environment({"PATH": "/pkg/bin:/usr/bin", "RUSTUP_AUTO_INSTALL": "1"})
        self.assertEqual(environment["PATH"], "/pkg/bin:/usr/bin")
        self.assertEqual(environment["RUSTUP_AUTO_INSTALL"], "0")
        self.assertEqual(GATE.trust_probe_environment({"PATH": "/p", "TCG_X": "1", "TRUST_CG_Y": "1"}),
                         {"PATH": "/p"})

    # Default bound for fixtures that are meant to FINISH (the timeout test passes 0.2 s itself): 5 s was
    # exceeded by a fake cargo's interpreter start alone at load 29-42 (F-164).
    def run_fixture(self, source, timeout=60, minimum=1, environment=None):
        with tempfile.TemporaryDirectory() as temp:
            result = GATE.run_target(
                [sys.executable, "-c", source], Path(temp) / "fixture.log", timeout,
                minimum=minimum, root=ROOT, grace_seconds=0.05, environment=environment,
            )
            retained = (Path(temp) / "fixture.log").read_text()
        return result, retained

    def test_real_fixture_process_accepts_complete_positive_execution(self):
        result, retained = self.run_fixture(f"print({transcript(3, output='PASS 3 checks')!r})", minimum=3)
        self.assertEqual(result["status"], "pass", result)
        self.assertEqual(result["counts"]["passed"], 3)
        self.assertEqual(result["minimum"], 3)
        self.assertEqual(result["matrix_status"], "pass")
        self.assertIn("3 passed", retained)
        self.assertEqual(len(result["log_sha256"]), 64)

    def test_skip_ignored_filtered_incomplete_and_short_runs_fail(self):
        cases = {
            "captured SKIP": (transcript(1, output="SKIP: needs aarch64-apple-darwin"), 1),
            "named SKIP": (transcript(1, output="SKIP test_bridge_add: no C compiler on PATH"), 1),
            "legacy Skipping": (transcript(1, output="Skipping e2e test: not AArch64 or cc not available"), 1),
            "legacy skipping": (transcript(1, output="skipping #376 lldb check: /usr/bin/lldb is not available"), 1),
            "unattributed SKIP": ("SKIP: before any suite\n" + transcript(1), 1),
            "ignored": (transcript(1, ignored=1), 1),
            "filtered": (transcript(1, filtered=2), 1),
            "failed": (transcript(1, failed=1), 1),
            "no rollup": (transcript(1, rollup=False), 1),
            "declared count mismatch": (transcript(1, started=2), 1),
            "empty suite": (transcript(0), 1),
            "duplicate suite": (transcript() + transcript(), 1),
            "below minimum": (transcript(2), 3),
            "no suite": ("compiler unavailable\n", 1),
        }
        for label, (text, minimum) in cases.items():
            with self.subTest(label=label):
                result, _ = self.run_fixture(f"print({text!r}, end='')", minimum=minimum)
                self.assertEqual(result["status"], "fail", result)
                self.assertTrue(result["errors"], result)

    def test_green_summary_cannot_launder_a_failing_exit(self):
        result, _ = self.run_fixture(f"print({transcript()!r}); raise SystemExit(7)")
        self.assertEqual(result["status"], "fail")
        self.assertEqual(result["returncode"], 7)

    def test_fixture_timeout_uses_shared_process_group_runner(self):
        result, retained = self.run_fixture(
            f"print({transcript()!r}, flush=True); import time; time.sleep(60)", timeout=0.2,
        )
        self.assertEqual(result["returncode"], 124)
        self.assertEqual(result["status"], "fail")
        self.assertTrue(result["timeout_detected"])
        self.assertEqual(result["matrix_status"], "timeout")
        self.assertIn("command exceeded", retained)

    def test_missing_executable_and_signal_are_failures(self):
        result, _ = self.run_fixture("import os, signal; os.kill(os.getpid(), signal.SIGTERM)")
        self.assertEqual(result["status"], "fail")
        self.assertEqual(result["returncode"], 143)
        with tempfile.TemporaryDirectory() as temp:
            result = GATE.run_target(
                [str(Path(temp) / "absent")], Path(temp) / "missing.log", 5, grace_seconds=0.05,
            )
        self.assertEqual(result["returncode"], 127)
        self.assertEqual(result["status"], "fail")

    def test_capture_is_forced_and_checker_overrides_are_isolated_only_for_planning(self):
        overrides = {
            "TCG_EXTERNAL_CLEAN_CHECKER": "/fixture/checker",
            "TCG_CLEAN_CHECKER": "/fixture/legacy-checker",
            "AY_SOLVER_PATH": "/fixture/solver",
            "RUST_TEST_NOCAPTURE": "1",
        }
        for target in ("core_jit_planning", "jit_fail_closed_proof_policy"):
            with self.subTest(target=target), tempfile.TemporaryDirectory() as temp:
                removed = GATE.target_unset_environment("trust-cg-codegen", target)
                expected = {
                    key: value for key, value in overrides.items()
                    if key not in removed and key != "RUST_TEST_NOCAPTURE"
                }
                fixture = (
                    "import os; "
                    f"assert {{key: os.environ[key] for key in {list(overrides)!r} "
                    f"if key in os.environ}} == {expected!r}; print({transcript()!r})"
                )
                environment = GATE.child_environment({**os.environ, **overrides})
                result = GATE.run_target(
                    [sys.executable, "-c", fixture], Path(temp) / "fixture.log", 5,
                    environment=environment, unset_environment=removed,
                )
                self.assertEqual(result["status"], "pass", result)
                self.assertIn("RUST_TEST_NOCAPTURE", result["unset_environment"])
                self.assertEqual(bool(removed), target == "core_jit_planning")

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
                    "import importlib.util, json, sys; from pathlib import Path; "
                    f"spec=importlib.util.spec_from_file_location('gate', {str(SCRIPT)!r}); "
                    "gate=importlib.util.module_from_spec(spec); spec.loader.exec_module(gate); "
                    f"result=gate.run_target([sys.executable, '-c', {command!r}], "
                    f"Path({str(log)!r}), 60, grace_seconds=0.05); "
                    "print(json.dumps(result)); sys.exit(1 if result['status']=='fail' else 0)"
                )
                supervisor = subprocess.Popen(
                    [sys.executable, "-c", runner], stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE, text=True, start_new_session=True,
                )
                child = None
                try:
                    deadline = time.monotonic() + 10
                    while not ready.exists() and time.monotonic() < deadline:
                        time.sleep(0.02)
                    self.assertTrue(ready.exists(), "command never reached signal-ready state")
                    child = int(ready.read_text())
                    supervisor.send_signal(signum)
                    stdout, stderr = supervisor.communicate(timeout=10)
                    self.assertEqual(supervisor.returncode, 1, stderr)
                    result = json.loads(stdout)
                    self.assertEqual(result["interrupted_signal"], signum)
                    self.assertEqual(result["status"], "fail")
                    deadline = time.monotonic() + 5
                    while self.alive(child) and time.monotonic() < deadline:
                        time.sleep(0.02)
                    self.assertFalse(self.alive(child), "command survived cancellation")
                finally:
                    if supervisor.poll() is None:
                        supervisor.kill()
                        supervisor.communicate(timeout=5)
                    if child is not None and self.alive(child):
                        os.killpg(child, signal.SIGKILL)

    @staticmethod
    def alive(pid):
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            return False
        except PermissionError:
            return True
        return True

    def test_existing_or_in_tree_output_is_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            marker = Path(temp) / "report.json"
            marker.write_text("existing evidence")
            with contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(GATE.main(["--out", temp]), 1)
            self.assertEqual(marker.read_text(), "existing evidence")
        inside = ROOT / "target" / "darwin-floor-must-not-exist"
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(GATE.main(["--out", str(inside)]), 1)
        self.assertFalse(inside.exists())

    def run_main(self, argv, **patches):
        stdout, stderr = io.StringIO(), io.StringIO()
        with contextlib.ExitStack() as stack:
            for name, value in patches.items():
                stack.enter_context(mock.patch.object(GATE, name, value))
            stack.enter_context(contextlib.redirect_stdout(stdout))
            stack.enter_context(contextlib.redirect_stderr(stderr))
            code = GATE.main(argv)
        return code, stdout.getvalue(), stderr.getvalue()

    def test_preflight_error_is_retained_and_cannot_pass(self):
        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp) / "new"
            code, _, _ = self.run_main(
                ["--out", str(output)],
                preflight=mock.Mock(side_effect=RuntimeError("required Darwin host is aarch64-apple-darwin, observed linux/aarch64")),
            )
            report = json.loads((output / "report.json").read_text())
        self.assertEqual(code, 1)
        self.assertEqual(report["status"], "fail")
        self.assertEqual(report["targets"], [])
        self.assertIn("required Darwin host", report["errors"][0])
        self.assertIn("compiled_out_linux_floor_targets", report["not_executed_on_darwin"])

    def test_inventory_inconsistency_fails_before_preflight(self):
        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp) / "new"
            code, _, _ = self.run_main(
                ["--out", str(output)],
                inventory_problems=mock.Mock(return_value=["fixture drift"]),
                preflight=mock.Mock(side_effect=AssertionError("probed")),
            )
            report = json.loads((output / "report.json").read_text())
        self.assertEqual(code, 1)
        self.assertEqual(report["status"], "fail")
        self.assertIn("fixture drift", report["errors"][0])

    def orchestrate(
        self, temp, *, argv=(), dirty=False, fail_second=False, final_fingerprint="fixture-fingerprint",
        identities=None, leak_second=False,
    ):
        fixture = Path(temp) / "cargo-fixture"
        arguments = Path(temp) / "cargo-arguments"
        temporaries = Path(temp) / "cargo-temporaries"
        fixture.write_text(
            f"#!{sys.executable}\n"
            "import os, sys\n"
            "assert sys.argv[1:3] == ['--unverified', 'test'], sys.argv\n"
            "assert '--locked' in sys.argv\n"
            "assert '--show-output' in sys.argv\n"
            "assert '--test-threads=1' in sys.argv\n"
            "assert '--nocapture' not in sys.argv\n"
            "assert 'TRUST_CG_KEEP_TEST_OBJECTS' not in os.environ\n"
            f"open({str(arguments)!r}, 'a').write(' '.join(sys.argv[2:]) + '\\n')\n"
            "target = sys.argv[sys.argv.index('--test') + 1]\n"
            "scratch = os.environ['TMPDIR']\n"
            f"open({str(temporaries)!r}, 'a').write(scratch + '\\n')\n"
            "assert os.listdir(scratch) == [], os.listdir(scratch)\n"
            # Every target: the two tool caches in their measured shapes, and
            # a scratch directory it removes.
            "open(os.path.join(scratch, 'xcrun_db'), 'w').write('cache')\n"
            "os.makedirs(os.path.join(scratch, 'lldb'))\n"
            "os.makedirs(os.path.join(scratch, 'removed', 'inner'))\n"
            "__import__('shutil').rmtree(os.path.join(scratch, 'removed'))\n"
            f"if {leak_second!r} and target == 'second':\n"
            "    os.makedirs(os.path.join(scratch, 'trust-cg-leaked-fixture', 'inner'))\n"
            "    open(os.path.join(scratch, 'trust-cg-leaked-fixture', 'inner', 'o'), 'w').write('x' * 10)\n"
            "    open(os.path.join(scratch, 'leaked.o'), 'w').write('y' * 5)\n"
            f"broken = {fail_second!r} and target == 'second'\n"
            f"print({transcript(2)!r})\n"
            "if broken: raise SystemExit(9)\n"
        )
        fixture.chmod(0o700)
        output = Path(temp) / "results"
        provenance = {
            "source_sha": "fixture-source", "dirty": dirty,
            "tools": {"targo": str(fixture), "git": "fixture-git"}, "host": GATE.HOST,
            "source_fingerprint": "fixture-fingerprint",
        }
        final = dict(provenance, source_fingerprint=final_fingerprint)
        preflight = mock.Mock(return_value=provenance)
        recorded = mock.Mock(side_effect=list(identities or (dependency_record(), dependency_record())))
        code, stdout, stderr = self.run_main(
            # Every orchestrate() caller expects the fake cargo to finish; none exercises a timeout (F-164).
            ["--out", str(output), "--timeout-seconds", "60", *argv],
            TARGETS=(("fixture", "first", 2), ("fixture", "second", 2)),
            inventory_problems=mock.Mock(return_value=[]),
            linux_only_leg_targets=mock.Mock(return_value=[]),
            preflight=preflight,
            source_provenance=mock.Mock(return_value=final),
            dependency_identity=recorded,
        )
        report = json.loads((output / "report.json").read_text())
        report["_cargo_arguments"] = arguments.read_text().splitlines() if arguments.exists() else []
        report["_temporaries"] = temporaries.read_text().splitlines() if temporaries.exists() else []
        report["_identity_calls"] = recorded.call_args_list
        report["_stderr"] = stderr
        return code, report, output, stdout

    def test_orchestration_retains_each_real_process_and_requires_every_target(self):
        for fail_second in (False, True):
            with self.subTest(fail_second=fail_second), tempfile.TemporaryDirectory() as temp:
                code, report, output, _ = self.orchestrate(temp, fail_second=fail_second)
                self.assertEqual(code, 1 if fail_second else 0)
                self.assertEqual(report["status"], "fail" if fail_second else "pass")
                self.assertTrue(report["complete_floor"])
                self.assertEqual(report["required_minimum_passes"], 4)
                self.assertEqual(report["executed_passes"], 4)
                self.assertEqual(report["provenance"]["source_sha"], "fixture-source")
                self.assertEqual([row["target"] for row in report["targets"]], ["first", "second"])
                self.assertEqual(report["targets"][0]["status"], "pass")
                self.assertEqual(report["targets"][1]["returncode"], 9 if fail_second else 0)
                for target in report["targets"]:
                    self.assertTrue((output / target["log"]).is_file())

    def test_each_target_gets_its_own_tmpdir_and_a_leftover_fails_it(self):
        for leak_second in (False, True):
            with self.subTest(leak_second=leak_second), tempfile.TemporaryDirectory() as temp, \
                    mock.patch.dict(os.environ, {"TRUST_CG_KEEP_TEST_OBJECTS": "1"}):
                code, report, _, _ = self.orchestrate(temp, leak_second=leak_second)
                first, second = report["targets"]
                self.assertEqual(code, 1 if leak_second else 0)
                self.assertEqual(report["status"], "fail" if leak_second else "pass")
                # Two distinct, fresh, short directories under the caller's
                # temporary directory, both removed once their target ran.
                scratches = [Path(path) for path in report["_temporaries"]]
                self.assertEqual(len(set(scratches)), 2)
                for scratch in scratches:
                    self.assertEqual(scratch.parent.resolve(), Path(tempfile.gettempdir()).resolve())
                    self.assertTrue(scratch.name.startswith(GATE.TEMPORARY_DIRECTORY_PREFIX))
                    self.assertFalse(scratch.exists())
                for row in report["targets"]:
                    self.assertEqual(row["temporary_tool_caches"], ["lldb", "xcrun_db"])
                self.assertEqual((first["status"], first["temporary_leftovers"]), ("pass", []))
                if leak_second:
                    self.assertEqual(second["status"], "fail")
                    self.assertEqual(second["temporary_leftovers"], ["leaked.o", "trust-cg-leaked-fixture"])
                    self.assertEqual(second["temporary_leftover_bytes"], 15)
                    self.assertIn(
                        "left 2 temporary entries (15 bytes) in its own TMPDIR: leaked.o, "
                        "trust-cg-leaked-fixture",
                        second["errors"],
                    )
                else:
                    self.assertEqual((second["status"], second["temporary_leftovers"]), ("pass", []))

    def test_a_tool_cache_name_admits_only_the_shape_the_tool_leaves(self):
        with tempfile.TemporaryDirectory() as temp:
            for name, make, cache in (
                ("xcrun_db", lambda path: path.write_text("cache"), True),
                ("xcrun_db", lambda path: path.mkdir(), False),
                ("xcrun_db", lambda path: path.symlink_to("/nonexistent/target"), False),
                ("lldb", lambda path: path.mkdir(), True),
                ("lldb", lambda path: (path.mkdir(), (path / "12345").mkdir()), False),
                ("lldb", lambda path: (path.mkdir(), (path / "out.o").write_text("x" * 7)), False),
                ("lldb", lambda path: path.write_text("not a directory"), False),
            ):
                with self.subTest(name=name, cache=cache):
                    scratch = Path(tempfile.mkdtemp(dir=temp))
                    make(scratch / name)
                    leftovers = GATE.temporary_leftovers(scratch)
                    if cache:
                        self.assertEqual((leftovers["tool_caches"], leftovers["leaked"]), ([name], []))
                    else:
                        self.assertEqual((leftovers["tool_caches"], leftovers["leaked"]), ([], [name]))
                    result = {"status": "pass", "errors": []}
                    GATE.check_temporary_leftovers(result, scratch)
                    self.assertEqual(result["status"], "pass" if cache else "fail")
                    self.assertFalse(scratch.exists())

    def test_temporary_leftovers_are_named_up_to_the_limit_and_the_directory_is_removed(self):
        with tempfile.TemporaryDirectory() as temp:
            scratch = Path(temp) / "scratch"
            scratch.mkdir()
            for index in range(GATE.TEMPORARY_LEFTOVERS_SHOWN + 3):
                (scratch / f"leak-{index:02}").mkdir()
            (scratch / "link").symlink_to("/nonexistent/target")
            result = {"status": "pass", "errors": []}
            GATE.check_temporary_leftovers(result, scratch)
            self.assertFalse(scratch.exists())
            self.assertEqual(result["status"], "fail")
            self.assertEqual(len(result["temporary_leftovers"]), GATE.TEMPORARY_LEFTOVERS_SHOWN + 4)
            self.assertTrue(result["errors"][0].endswith(" and 4 more"), result["errors"])

    def test_features_reach_only_their_own_target_and_are_recorded(self):
        with tempfile.TemporaryDirectory() as temp, mock.patch.object(
            GATE.SHARED, "TARGET_FEATURES", {("fixture", "second"): ("driver",)},
        ):
            code, report, _, _ = self.orchestrate(temp)
            first, second = (Path(temp) / "cargo-arguments").read_text().splitlines()
        self.assertEqual(code, 0)
        self.assertNotIn("--features", first.split())
        self.assertIn("-p fixture --features driver --test second --", second)
        self.assertEqual(report["required_target_features"], {"fixture/second": ["driver"]})
        self.assertEqual([row["features"] for row in report["targets"]], [[], ["driver"]])

    def test_uncovered_feature_gate_is_an_inventory_problem(self):
        without = {
            key: value for key, value in GATE.SHARED.TARGET_FEATURES.items()
            if key != ("trust-cg-llvm-import", "cast_e2e")
        }
        with mock.patch.object(GATE.SHARED, "TARGET_FEATURES", without):
            problems = GATE.inventory_problems()
        self.assertTrue(any(
            "trust-cg-llvm-import/cast_e2e" in problem and "empty suite" in problem for problem in problems
        ), problems)

    def test_only_is_a_partial_pass_never_the_floor(self):
        with tempfile.TemporaryDirectory() as temp:
            code, report, _, stdout = self.orchestrate(temp, argv=["--only", "second"])
        self.assertEqual(code, 0)
        self.assertEqual(report["status"], "partial-pass")
        self.assertFalse(report["complete_floor"])
        self.assertEqual([row["target"] for row in report["targets"]], ["second"])
        self.assertIn("not the required floor", stdout)

    def test_require_clean_refuses_a_dirty_tree_before_running(self):
        with tempfile.TemporaryDirectory() as temp:
            code, report, _, _ = self.orchestrate(temp, argv=["--require-clean"], dirty=True)
        self.assertEqual(code, 1)
        self.assertEqual(report["status"], "fail")
        self.assertEqual(report["targets"], [])
        self.assertIn("--require-clean refuses", report["errors"][0])
        with tempfile.TemporaryDirectory() as temp:
            code, report, _, _ = self.orchestrate(temp, argv=["--require-clean"], dirty=False)
        self.assertEqual((code, report["status"]), (0, "pass"))
        with tempfile.TemporaryDirectory() as temp:
            code, report, _, _ = self.orchestrate(temp, dirty=True)
        self.assertEqual((code, report["status"]), (0, "pass"))
        self.assertTrue(report["provenance"]["dirty"])

    def test_source_change_during_the_run_fails(self):
        with tempfile.TemporaryDirectory() as temp:
            code, report, _, _ = self.orchestrate(temp, final_fingerprint="changed")
        self.assertEqual(code, 1)
        self.assertEqual(report["status"], "fail")
        self.assertIn("source changed while required targets were running", report["errors"])

    def test_dependency_identity_is_recorded_before_and_after_with_the_child_environment(self):
        with tempfile.TemporaryDirectory() as temp:
            code, report, _, _ = self.orchestrate(temp)
        self.assertEqual((code, report["status"]), (0, "pass"))
        self.assertEqual(report["dependency_identity"], dependency_record())
        self.assertEqual(report["final_dependency_identity"], dependency_record())
        self.assertFalse(report["options"]["require_offline_deps"])
        calls = report["_identity_calls"]
        self.assertEqual(len(calls), 2)
        for call in calls:
            git, environment = call.args
            self.assertEqual(git, "fixture-git")
            # The recorder sees the same environment (and Cargo home) the
            # Trust package's targo will run under.
            self.assertEqual(environment["PATH"], os.environ.get("PATH", ""))
            self.assertEqual(environment["RUSTUP_AUTO_INSTALL"], "0")
        self.assertTrue(all("--offline" not in line.split() for line in report["_cargo_arguments"]))

    def test_missing_pinned_revision_is_labelled_and_refused_under_require_offline_deps(self):
        with tempfile.TemporaryDirectory() as temp:
            code, report, _, _ = self.orchestrate(
                temp, argv=["--require-offline-deps"], identities=(dependency_record(resolves=False),),
            )
        self.assertEqual((code, report["status"]), (1, "fail"))
        self.assertEqual(report["targets"], [])
        self.assertEqual(report["_cargo_arguments"], [])
        self.assertTrue(report["options"]["require_offline_deps"])
        self.assertIn("does not resolve in the local Cargo Git database", report["errors"][0])
        self.assertTrue(report["errors"][0].startswith("--require-offline-deps: "))
        self.assertIn("--require-offline-deps refuses this Cargo home", report["errors"][-1])
        self.assertNotIn("final_dependency_identity", report)
        with tempfile.TemporaryDirectory() as temp:
            code, report, _, _ = self.orchestrate(
                temp, identities=(dependency_record(resolves=False), dependency_record(resolves=False)),
            )
        self.assertEqual((code, report["status"]), (0, "pass"))
        self.assertIn("may fetch them", report["_stderr"])

    def test_require_offline_deps_runs_cargo_offline_when_every_pin_is_local(self):
        with tempfile.TemporaryDirectory() as temp:
            code, report, _, _ = self.orchestrate(temp, argv=["--require-offline-deps"])
        self.assertEqual((code, report["status"]), (0, "pass"))
        self.assertEqual(len(report["_cargo_arguments"]), 2)
        for line in report["_cargo_arguments"]:
            self.assertEqual(line.split()[:3], ["test", "--locked", "--offline"])

    def test_dependency_change_during_the_run_fails(self):
        with tempfile.TemporaryDirectory() as temp:
            code, report, _, _ = self.orchestrate(
                temp, identities=(dependency_record(), dependency_record(tree="d" * 64)),
            )
        self.assertEqual((code, report["status"]), (1, "fail"))
        self.assertIn(
            "dependency identity changed while required targets were running: checkout tree of "
            "https://example.invalid/companion.git cccccccccccc changed during the run",
            report["errors"],
        )

    def test_recorder_is_the_linux_floor_recorder(self):
        self.assertIs(GATE.dependency_identity, GATE.SHARED.dependency_identity)
        self.assertIs(GATE.dependency_recorder, GATE.SHARED.dependency_recorder)


if __name__ == "__main__":
    unittest.main()
