"""Bounded process contracts for build.rs, not Trust/private-API qualification.

Set BRIDGE_PROBE_TARGO and BRIDGE_PROBE_TRUSTC to explicit absolute tools; no
PATH/rustup/stock-Cargo fallback is allowed. Set BRIDGE_PROBE_BINARY only to
exercise a separately retained build-script executable. Ordinary-Rust stand-ins
remain development-unverified process tests, not actual private-API or proof
qualification. All per-case sources, argv, outputs and outcomes are retained.
"""
import json
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "scripts/tests/fixtures/bridge_build_probe"
FIXTURE_TARGET = "aarch64-unknown-linux-gnu"


def explicit_tool(name):
    value = os.environ.get(name)
    if not value or not Path(value).is_absolute() or not Path(value).is_file():
        raise AssertionError(f"{name} must name an explicit absolute tool file")
    return Path(value)


class BridgeBuildProbeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.targo = explicit_tool("BRIDGE_PROBE_TARGO")
        cls.compiler = explicit_tool("BRIDGE_PROBE_TRUSTC")
        # BRIDGE_PROBE_ARTIFACTS names a directory to keep the records in;
        # otherwise they go to a temporary directory removed after the class.
        named = os.environ.get("BRIDGE_PROBE_ARTIFACTS")
        if named:
            cls.artifacts = Path(named).resolve()
        else:
            scratch = tempfile.TemporaryDirectory(prefix="tcg-build-probe-contract-")
            cls.addClassCleanup(scratch.cleanup)
            cls.artifacts = Path(scratch.name).resolve()
        cls.artifacts.mkdir(parents=True, exist_ok=True)
        cls.real_sysroot = subprocess.check_output([str(cls.compiler), "--print", "sysroot"],
                                                   cwd=ROOT, text=True, timeout=20).strip()
        if not Path(cls.real_sysroot).is_absolute():
            raise AssertionError("selected compiler returned a nonabsolute sysroot")
        (cls.artifacts / "tools.json").write_text(json.dumps({
            "targo": {"path": str(cls.targo), "sha256": hashlib.sha256(cls.targo.read_bytes()).hexdigest()},
            "compiler": {"path": str(cls.compiler), "sha256": hashlib.sha256(cls.compiler.read_bytes()).hexdigest()},
            "ordinary_rust_sysroot": cls.real_sysroot,
            "scope": "development-unverified process contracts; no private-API qualification",
        }, indent=2) + "\n")
        supplied = os.environ.get("BRIDGE_PROBE_BINARY")
        if supplied:
            cls.binary = explicit_tool("BRIDGE_PROBE_BINARY")
        else:
            target = Path(os.environ.get("CARGO_TARGET_DIR", str(cls.artifacts / "target"))).resolve()
            environment = dict(os.environ, RUSTC=str(cls.compiler))
            command = [str(cls.targo), "-Zchecksum-freshness", "--unverified", "build",
                                    "--locked", "--offline", "--jobs", "1",
                                    "--message-format=json-render-diagnostics",
                                    "--manifest-path", str(FIXTURE / "Cargo.toml"),
                                    "--target-dir", str(target)]
            (cls.artifacts / "harness-command.json").write_text(json.dumps(command) + "\n")
            build = subprocess.run(command, cwd=ROOT, env=environment,
                                   text=True, capture_output=True, timeout=180)
            (cls.artifacts / "harness-build.stdout").write_text(build.stdout)
            (cls.artifacts / "harness-build.stderr").write_text(build.stderr)
            if build.returncode:
                raise AssertionError(build.stdout + build.stderr)
            artifacts = [json.loads(line) for line in build.stdout.splitlines() if line.startswith("{")]
            binaries = [Path(item["executable"]) for item in artifacts
                        if item.get("reason") == "compiler-artifact"
                        and item.get("target", {}).get("name") == "bridge-build-probe-contract"
                        and item.get("executable")]
            if len(binaries) != 1 or not binaries[0].is_file():
                raise AssertionError("expected exactly one emitted process-harness executable")
            cls.binary = binaries[0]
        cls.records = []

    @classmethod
    def tearDownClass(cls):
        (cls.artifacts / "cases.json").write_text(json.dumps(cls.records, indent=2) + "\n")
        print(f"BUILD_PROBE_CASE_CENSUS cases={len(cls.records)} artifacts={cls.artifacts}")

    def probe(self, mode, *, rustflags=None, encoded=None, label=None, target=FIXTURE_TARGET):
        directory = self.artifacts / (label or mode)
        directory.mkdir()
        compiler = directory / "sysroot/bin/rustc"
        compiler.parent.mkdir(parents=True)
        shutil.copyfile(FIXTURE / "compiler.py", compiler)
        shutil.copyfile(FIXTURE / "sysroot_contract.py", compiler.parent / "sysroot_contract.py")
        compiler.chmod(0o755)
        output = directory / "out"
        output.mkdir()
        if mode == "missing-output-stale":
            (output / "probe_trust_ir_cg_args.rmeta").write_bytes(b"stale successful metadata")
        environment = {"PATH": os.environ["PATH"], "LANG": "C", "LC_ALL": "C",
                       "RUSTC": str(compiler), "OUT_DIR": str(output),
                       "CARGO_CFG_TARGET_OS": "linux", "CARGO_CFG_TARGET_ENV": "gnu",
                       "PROBE_FIXTURE_MODE": mode, "PROBE_FIXTURE_ROOT": str(directory),
                       "PROBE_REAL_COMPILER": str(self.compiler),
                       "PROBE_REAL_SYSROOT": self.real_sysroot,
                       "PROBE_FIXTURE_TARGET": FIXTURE_TARGET,
                       "PYTHONDONTWRITEBYTECODE": "1",
                       "PROBE_FIXTURE_HELP": str(FIXTURE / "trustc-f92d25a5a-Zhelp.txt")}
        if target is not None:
            environment["TARGET"] = target
        if rustflags is not None:
            rustflags = rustflags.replace("{explicit_sysroot}", str(directory / "explicit-sysroot"))
        if encoded is not None:
            encoded = encoded.replace("{explicit_sysroot}", str(directory / "explicit-sysroot"))
        if rustflags is not None:
            environment["RUSTFLAGS"] = rustflags
        if encoded is not None:
            environment["CARGO_ENCODED_RUSTFLAGS"] = encoded
        # Nineteen independent API selectors also compile their retained controls.
        # Allow that complete sequence; compiler.py still bounds each compiler
        # invocation at 20 seconds and every result assertion remains required.
        result = subprocess.run([str(self.binary)], cwd=ROOT, env=environment,
                                text=True, capture_output=True, timeout=90)
        (directory / "stdout").write_text(result.stdout)
        (directory / "stderr").write_text(result.stderr)
        record = {"case": directory.name, "mode": mode, "exit": result.returncode,
                  "cfg": [line for line in result.stdout.splitlines() if line.startswith("cargo:rustc-cfg=")],
                  "rustflags": rustflags, "encoded_rustflags": encoded, "target": target}
        self.records.append(record)
        (directory / "result.json").write_text(json.dumps(record, indent=2) + "\n")
        return result, directory

    def test_target_sysroot_is_forwarded_and_explicit_flags_win(self):
        cases = [(None, None, "target-sysroot"),
                 ("--sysroot {explicit_sysroot}", None, "explicit-separated"),
                 ("--sysroot={explicit_sysroot}", None, "explicit-equals"),
                 ("--sysroot=/wrong-root", "--sysroot\x1f{explicit_sysroot}", "encoded-sysroot"),
                 ("--sysroot=/wrong-root", "", "encoded-empty-sysroot")]
        for flags, encoded, label in cases:
            with self.subTest(case=label):
                result, directory = self.probe("present", rustflags=flags, encoded=encoded, label=label)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                commands = [json.loads(line) for line in (directory / "argv.jsonl").read_text().splitlines()]
                self.assertIn(["--print", "sysroot", "--target", FIXTURE_TARGET], commands)
                probes = [args for args in commands if any(arg.endswith(".rs") for arg in args)]
                self.assertTrue(probes)
                expected = str(directory / ("explicit-sysroot" if label.startswith(("explicit", "encoded-sysroot"))
                                            else "target-sysroot"))
                for args in probes:
                    roots = [args[index + 1] if arg == "--sysroot" else arg.split("=", 1)[1]
                             for index, arg in enumerate(args) if arg == "--sysroot" or arg.startswith("--sysroot=")]
                    self.assertEqual(roots, [expected])

    def test_missing_or_wrong_target_refuses_before_capability_probes(self):
        for target, label, reason in [(None, "missing-target", "TARGET is set by cargo"),
                                      ("x86_64-unknown-linux-gnu", "wrong-target", "requires the exact TARGET")]:
            with self.subTest(case=label):
                result, directory = self.probe("present", target=target, label=label)
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn(reason, result.stderr)
                commands = [json.loads(line) for line in (directory / "argv.jsonl").read_text().splitlines()]
                self.assertFalse(any(arg.endswith(".rs") for args in commands for arg in args))

    def test_present_capabilities_survive_warning_and_policy_flags(self):
        cases = [("present", None, None, "present"),
                 ("present", "-Dwarnings", None, "deny-warnings"),
                 ("present", "--deliberately-invalid", "-Dwarnings", "encoded-precedence"),
                 ("present", "--deliberately-invalid", "", "encoded-empty-precedence"),
                 ("strict-ambient", "-Ztrust-verify=strict -Dwarnings", None, "strict-ambient"),
                 ("strict-ambient", None, "-Dwarnings\x1f-Ztrust-verify=strict", "encoded-strict"),
                 ("legacy-no-off", "-Dwarnings", None, "legacy-no-off")]
        for mode, flags, encoded, label in cases:
            with self.subTest(case=label):
                result, directory = self.probe(mode, rustflags=flags, encoded=encoded, label=label)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("cargo:rustc-cfg=rustc_middle_mir_mono\n", result.stdout)
                self.assertIn("cargo:rustc-cfg=trust_ir_cg_args\n", result.stdout)
                self.assertNotIn("cargo:rustc-flags=", result.stdout)
                self.assertNotIn("cargo:rustc-env=RUSTFLAGS", result.stdout)
                if mode == "strict-ambient":
                    commands = [json.loads(line) for line in (directory / "argv.jsonl").read_text().splitlines()]
                    for command in commands:
                        if any(arg.endswith(".rs") for arg in command):
                            self.assertEqual([arg for arg in command if arg.startswith("-Ztrust-verify=")][-1],
                                             "-Ztrust-verify=off")

    def test_exact_legacy_absence_keeps_only_the_valid_fallback(self):
        for mode, mir, field in [("missing-field", True, False), ("missing-mir", False, True),
                                 ("both-legacy", False, False),
                                 ("trust-missing-field", True, False),
                                 ("trust-missing-mir", False, True),
                                 ("trust-both-legacy", False, False)]:
            with self.subTest(case=mode):
                result, _ = self.probe(mode, rustflags="-Dwarnings")
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual("cargo:rustc-cfg=rustc_middle_mir_mono\n" in result.stdout, mir)
                self.assertEqual("cargo:rustc-cfg=trust_ir_cg_args\n" in result.stdout, field)

    def test_current_trust_help_preserves_multiline_option_descriptions(self):
        for mode, field in [("current-help", True), ("current-help-no-tracked", False)]:
            with self.subTest(case=mode):
                result, _ = self.probe(mode, rustflags="-Dwarnings")
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("cargo:rustc-cfg=rustc_middle_mir_mono\n", result.stdout)
                self.assertEqual("cargo:rustc-cfg=trust_ir_cg_args\n" in result.stdout, field)

    def test_early_session_presence_is_independent_and_exact_absence_stays_legacy(self):
        for mode, present in [("early-session-present", True), ("present", False),
                              ("trust-present", False)]:
            with self.subTest(case=mode):
                result, _ = self.probe(mode, rustflags="-Dwarnings", label=f"session-{mode}")
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual("cargo:rustc-cfg=rustc_session_split\n" in result.stdout, present)
                self.assertIn("cargo:rustc-cfg=rustc_middle_mir_mono\n", result.stdout)
                self.assertIn("cargo:rustc-cfg=trust_ir_cg_args\n", result.stdout)

    def test_early_session_ambiguous_diagnostics_and_incomplete_output_abort(self):
        for suffix in ("extra-error", "unrelated-import", "denied-warning", "wrong-span",
                       "wrong-token", "wrong-code", "wrong-message", "extra-primary",
                       "tool-failure", "missing-output", "malformed-json"):
            mode = f"early-session-{suffix}"
            with self.subTest(case=mode):
                result, _ = self.probe(mode, rustflags="-Dwarnings")
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertNotIn("cargo:rustc-cfg=rustc_session_split\n", result.stdout)

    def test_language_item_path_requires_exact_absence_and_a_working_replacement(self):
        for mode, modern in [("present", False), ("missing-hir-lang-item", True),
                             ("trust-missing-hir-lang-item", True)]:
            with self.subTest(case=mode):
                result, directory = self.probe(mode, rustflags="-Dwarnings",
                                               label="language-item-" + mode)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual("cargo:rustc-cfg=rustc_attr_ir_lang_items\n" in result.stdout,
                                 modern)
                out = directory / "out"
                self.assertTrue((out / "probe_hir_control.rmeta").is_file())
                self.assertEqual((out / "probe_attr_ir_lang_item.command").is_file(), modern)
                if modern:
                    self.assertTrue((out / "probe_attr_ir_lang_item.rmeta").is_file())

    def test_language_item_ambiguous_failures_never_select_a_fallback(self):
        for mode in ("missing-both-lang-items", "hir-lang-item-extra-error",
                     "hir-lang-item-wrong-span", "hir-lang-item-denied-warning",
                     "hir-lang-item-unrelated-import", "hir-lang-item-missing-crate"):
            with self.subTest(case=mode):
                result, _ = self.probe(mode, rustflags="-Dwarnings")
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertNotIn("cargo:rustc-cfg=rustc_attr_ir_lang_items\n", result.stdout)

    def test_memory_authority_probe_is_independent_of_the_retained_namespace(self):
        for mode, modern_namespace, canonical in [
            ("present", False, False),
            ("missing-hir-lang-item", True, False),
            ("missing-memory-lang-items", False, True),
            ("new-memory-and-lang-items", True, True),
            ("trust-missing-memory-lang-items", False, True),
        ]:
            with self.subTest(case=mode):
                result, directory = self.probe(mode, rustflags="-Dwarnings",
                                               label="memory-authority-" + mode)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual("cargo:rustc-cfg=rustc_attr_ir_lang_items\n" in result.stdout,
                                 modern_namespace)
                self.assertEqual("cargo:rustc-cfg=rustc_canonical_memory_symbols\n" in result.stdout,
                                 canonical)
                out = directory / "out"
                self.assertEqual((out / "probe_memory_lang_items.command").is_file(),
                                 not canonical)
                self.assertEqual((out / "probe_canonical_memory_symbols.command").is_file(),
                                 canonical)

    def test_memory_authority_ambiguous_or_partial_apis_are_build_errors(self):
        for mode in ("memory-lang-item-partial", "memory-canonical-missing",
                     "memory-canonical-missing-symbol", "memory-canonical-missing-def-id",
                     "memory-extra-error", "memory-wrong-span", "memory-unrelated-variant",
                     "memory-denied-warning"):
            with self.subTest(case=mode):
                result, directory = self.probe(mode, rustflags="-Dwarnings")
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertNotIn("cargo:rustc-cfg=rustc_canonical_memory_symbols\n", result.stdout)
                if mode == "memory-lang-item-partial":
                    self.assertFalse((directory / "out/probe_canonical_memory_symbols.command").is_file())

    def test_attribute_namespace_and_common_are_independent_capabilities(self):
        for mode, modern_attributes, common, modern_items in [
            ("present", False, True, False),
            ("missing-hir-attributes", True, True, False),
            ("missing-common", False, False, False),
            ("new-attributes-no-common", True, False, False),
            ("new-attributes-new-lang-items", True, True, True),
            ("missing-hir-lang-item", False, True, True),
            ("trust-new-attributes-no-common", True, False, False),
        ]:
            with self.subTest(case=mode):
                result, directory = self.probe(mode, rustflags="-Dwarnings",
                                               label="attribute-capabilities-" + mode)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual("cargo:rustc-cfg=rustc_attr_ir_attributes\n" in result.stdout,
                                 modern_attributes)
                self.assertEqual("cargo:rustc-cfg=rustc_linkage_common\n" in result.stdout,
                                 common)
                self.assertEqual("cargo:rustc-cfg=rustc_attr_ir_lang_items\n" in result.stdout,
                                 modern_items)
                out = directory / "out"
                self.assertTrue((out / "probe_retained_attributes.rmeta").is_file())
                self.assertTrue((out / "probe_common_linkage.command").is_file())

    def test_attribute_ambiguity_or_partial_apis_abort(self):
        for mode in ("missing-both-attributes", "attributes-partial-inline",
                     "attributes-partial-linkage", "attributes-missing-macro",
                     "attributes-extra-error", "attributes-wrong-span",
                     "attributes-unrelated-import", "attributes-denied-warning",
                     "common-extra-error", "common-wrong-span",
                     "common-unrelated-variant", "common-denied-warning"):
            with self.subTest(case=mode):
                result, directory = self.probe(mode, rustflags="-Dwarnings")
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertNotIn("cargo:rustc-cfg=rustc_linkage_common\n", result.stdout)
                if not mode.startswith("common-"):
                    self.assertNotIn("cargo:rustc-cfg=rustc_attr_ir_attributes\n", result.stdout)
                    self.assertFalse((directory / "out/probe_common_linkage.command").is_file())

    def test_fresh_module_artifacts_require_the_complete_selected_carrier(self):
        for mode, legacy in [("present", True), ("module-cache-missing", False),
                             ("trust-module-cache-missing", False),
                             ("module-modern-all", False),
                             ("module-legacy-new-attributes", True)]:
            with self.subTest(case=mode):
                result, directory = self.probe(mode, rustflags="-Dwarnings",
                                               label="fresh-module-" + mode)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual("cargo:rustc-cfg=rustc_compiled_module_cache_links\n" in result.stdout,
                                 legacy)
                self.assertTrue((directory / "out/probe_fresh_compiled_module.rmeta").is_file())

    def test_fresh_module_ambiguous_or_partial_carriers_abort(self):
        for mode in ("module-cache-wrong-type", "module-cache-extra-error",
                     "module-cache-wrong-span", "module-cache-wrong-token",
                     "module-cache-unrelated-field", "module-cache-denied-warning",
                     "module-missing-crate", "module-missing-object", "module-missing-llvm-ir",
                     "module-unexpected-required", "module-object-wrong-type", "module-missing-kind",
                     "module-cache-unknown-type"):
            with self.subTest(case=mode):
                result, _ = self.probe(mode, rustflags="-Dwarnings")
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertNotIn("cargo:rustc-cfg=rustc_compiled_module_cache_links\n", result.stdout)

    def test_compiler_options_select_independent_actual_paths(self):
        for mode, kinds, sample in [("present", False, False),
                                    ("crate-type-modern", True, False),
                                    ("sample-profile-codegen", False, True),
                                    ("options-modern-all", True, True),
                                    ("trust-options-modern-all", True, True)]:
            with self.subTest(case=mode):
                result, directory = self.probe(mode, rustflags="-Dwarnings",
                                               label="compiler-options-" + mode)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual("cargo:rustc-cfg=rustc_structures_crate_type\n" in result.stdout, kinds)
                self.assertEqual("cargo:rustc-cfg=rustc_codegen_sample_profile\n" in result.stdout, sample)
                self.assertTrue((directory / "out/probe_retained_crate_types.rmeta").is_file())
                if sample:
                    self.assertTrue((directory / "out/probe_codegen_sample_profile.rmeta").is_file())

    def test_compiler_option_unknown_or_partial_apis_abort(self):
        for mode in ("crate-type-extra-error", "crate-type-wrong-span", "crate-type-wrong-token",
                     "crate-type-denied-warning", "crate-type-private-import", "crate-type-missing-old",
                     "crate-type-missing-structures", "crate-type-missing-kind",
                     "crate-type-legacy-missing-kind", "crate-type-new-kind",
                     "crate-type-query-wrong-type", "crate-type-query-missing",
                     "sample-extra-error", "sample-wrong-span", "sample-wrong-token",
                     "sample-denied-warning", "sample-unrelated-field", "sample-missing-new",
                     "sample-old-wrong-type", "sample-new-wrong-type", "sample-unknown-type",
                     "options-missing-session"):
            with self.subTest(case=mode):
                result, _ = self.probe(mode, rustflags="-Dwarnings")
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertNotIn("cargo:rustc-cfg=rustc_structures_crate_type\n", result.stdout)
                self.assertNotIn("cargo:rustc-cfg=rustc_codegen_sample_profile\n", result.stdout)

    def test_scalar_pair_shape_is_independent_and_requires_all_components(self):
        for mode, modern, other_modern in [("present", False, False),
                                           ("scalar-pair-modern", True, False),
                                           ("trust-scalar-pair-modern", True, False),
                                           ("options-modern-all", False, True),
                                           ("scalar-pair-modern-all", True, True),
                                           ("trust-scalar-pair-modern-all", True, True)]:
            with self.subTest(case=mode):
                result, directory = self.probe(mode, rustflags="-Dwarnings", label="pair-shape-" + mode)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual("cargo:rustc-cfg=rustc_scalar_pair_struct\n" in result.stdout, modern)
                for flag in ("rustc_attr_ir_lang_items", "rustc_canonical_memory_symbols",
                             "rustc_attr_ir_attributes", "rustc_structures_crate_type",
                             "rustc_codegen_sample_profile"):
                    self.assertEqual("cargo:rustc-cfg=" + flag + "\n" in result.stdout, other_modern)
                for flag in ("rustc_linkage_common", "rustc_compiled_module_cache_links"):
                    self.assertEqual("cargo:rustc-cfg=" + flag + "\n" in result.stdout, not other_modern)
                self.assertTrue((directory / "out/probe_retained_scalar_pair.rmeta").is_file())
                source = (directory / "out/probe_retained_scalar_pair.rs").read_text()
                self.assertIn("ScalarPair { a, b, b_offset }" if modern else "ScalarPair(a, b)", source)
                self.assertNotIn("..", source)

    def test_scalar_pair_unknown_or_partial_shapes_abort(self):
        for mode in ("scalar-pair-wrong-span", "scalar-pair-wrong-token", "scalar-pair-wrong-message",
                     "scalar-pair-extra-primary", "scalar-pair-extra-error", "scalar-pair-denied-warning",
                     "scalar-pair-missing-crate", "scalar-pair-missing-variant", "scalar-pair-missing-offset",
                     "scalar-pair-wrong-offset-type", "scalar-pair-wrong-component-type",
                     "scalar-pair-required-field", "scalar-pair-legacy-partial",
                     "scalar-pair-legacy-third-field", "scalar-pair-legacy-wrong-offset-type",
                     "scalar-pair-missing-output"):
            with self.subTest(case=mode):
                result, _ = self.probe(mode, rustflags="-Dwarnings")
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertNotIn("cargo:rustc-cfg=rustc_scalar_pair_struct\n", result.stdout)

    def test_cast_padding_count_is_independent_and_retains_the_complete_payload(self):
        for mode, count_api, other_modern in [("present", False, False),
                                             ("cast-padding-modern", True, False),
                                             ("trust-cast-padding-modern", True, False),
                                             ("scalar-pair-modern-all", False, True),
                                             ("cast-padding-modern-all", True, True),
                                             ("trust-cast-padding-modern-all", True, True)]:
            with self.subTest(case=mode):
                result, directory = self.probe(mode, rustflags="-Dwarnings", label="cast-padding-" + mode)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual("cargo:rustc-cfg=rustc_cast_pad_count\n" in result.stdout, count_api)
                for flag in ("rustc_attr_ir_lang_items", "rustc_canonical_memory_symbols",
                             "rustc_attr_ir_attributes", "rustc_structures_crate_type",
                             "rustc_codegen_sample_profile", "rustc_scalar_pair_struct"):
                    self.assertEqual("cargo:rustc-cfg=" + flag + "\n" in result.stdout, other_modern)
                for flag in ("rustc_linkage_common", "rustc_compiled_module_cache_links"):
                    self.assertEqual("cargo:rustc-cfg=" + flag + "\n" in result.stdout, not other_modern)
                self.assertTrue((directory / "out/probe_retained_cast_padding.rmeta").is_file())
                source = (directory / "out/probe_retained_cast_padding.rs").read_text()
                self.assertIn("cast, pad_i32_count }" if count_api else "cast, pad_i32 }", source)
                self.assertIn("CastTarget { prefix, rest_offset, rest, attrs }", source)
                self.assertNotIn("..", source)

    def test_cast_padding_unknown_types_shapes_and_diagnostics_abort(self):
        for mode in ("cast-padding-extra-error", "cast-padding-denied-warning",
                     "cast-padding-wrong-span", "cast-padding-wrong-token", "cast-padding-wrong-message",
                     "cast-padding-wrong-code", "cast-padding-extra-primary", "cast-padding-missing-crate",
                     "cast-padding-missing-count", "cast-padding-wrong-count-type",
                     "cast-padding-legacy-wrong-count-type", "cast-padding-wrong-target-type",
                     "cast-padding-legacy-wrong-target-type", "cast-padding-missing-target-field",
                     "cast-padding-required-target-field", "cast-padding-missing-cast",
                     "cast-padding-required-variant-field", "cast-padding-missing-output",
                     "cast-padding-legacy-missing-count", "cast-padding-tuple-shape", "cast-padding-missing-variant",
                     "cast-padding-enum-qualified-message"):
            with self.subTest(case=mode):
                result, _ = self.probe(mode, rustflags="-Dwarnings")
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertNotIn("cargo:rustc-cfg=rustc_cast_pad_count\n", result.stdout)

    def test_indirect_modes_are_independent_and_retain_every_payload(self):
        for mode, mode_api, other_modern in [("present", False, False),
                                            ("indirect-modern", True, False),
                                            ("trust-indirect-modern", True, False),
                                            ("cast-padding-modern-all", False, True),
                                            ("indirect-modern-all", True, True),
                                            ("trust-indirect-modern-all", True, True)]:
            with self.subTest(case=mode):
                result, directory = self.probe(mode, rustflags="-Dwarnings", label="indirect-" + mode)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual("cargo:rustc-cfg=rustc_indirect_modes\n" in result.stdout, mode_api)
                for flag in ("rustc_attr_ir_lang_items", "rustc_canonical_memory_symbols",
                             "rustc_attr_ir_attributes", "rustc_structures_crate_type",
                             "rustc_codegen_sample_profile", "rustc_scalar_pair_struct", "rustc_cast_pad_count"):
                    self.assertEqual("cargo:rustc-cfg=" + flag + "\n" in result.stdout, other_modern)
                for flag in ("rustc_linkage_common", "rustc_compiled_module_cache_links"):
                    self.assertEqual("cargo:rustc-cfg=" + flag + "\n" in result.stdout, not other_modern)
                self.assertTrue((directory / "out/probe_retained_indirect_modes.rmeta").is_file())
                source = (directory / "out/probe_retained_indirect_modes.rs").read_text()
                self.assertIn("attrs, address_space, mode }" if mode_api else
                              "attrs, meta_attrs, on_stack }", source)
                self.assertIn("ArgAttributes { regular, arg_ext, pointee_size, pointee_align }", source)
                self.assertIn("AddressSpace::ZERO", source)
                if mode_api:
                    self.assertIn("IndirectUnsized { attrs, meta_attrs }", source)
                    self.assertIn("IndirectMode::AmdgpuKernelArg", source)
                self.assertNotIn("..", source)

    def test_indirect_unknown_types_shapes_and_diagnostics_abort(self):
        for mode in ("indirect-extra-error", "indirect-denied-warning", "indirect-wrong-span",
                     "indirect-wrong-token", "indirect-wrong-message", "indirect-wrong-code",
                     "indirect-extra-primary", "indirect-missing-crate", "indirect-missing-variant",
                     "indirect-enum-qualified-message", "indirect-missing-output",
                     "indirect-missing-address-space", "indirect-wrong-address-space",
                     "indirect-missing-mode", "indirect-wrong-mode", "indirect-unknown-mode",
                     "indirect-missing-data-attrs", "indirect-wrong-data-attrs", "indirect-required-field",
                     "indirect-unsized-missing-variant", "indirect-unsized-missing-meta",
                     "indirect-unsized-missing-data", "indirect-unsized-wrong-meta",
                     "indirect-unsized-required-field", "indirect-missing-attribute",
                     "indirect-required-attribute", "indirect-missing-zero",
                     "indirect-legacy-wrong-stack", "indirect-legacy-missing-meta",
                     "indirect-legacy-wrong-meta", "indirect-legacy-required-field"):
            with self.subTest(case=mode):
                result, _ = self.probe(mode, rustflags="-Dwarnings")
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertNotIn("cargo:rustc-cfg=rustc_indirect_modes\n", result.stdout)
                minimal = mode in (
                    "indirect-extra-error", "indirect-denied-warning", "indirect-wrong-span",
                    "indirect-wrong-token", "indirect-wrong-message", "indirect-wrong-code",
                    "indirect-extra-primary", "indirect-missing-crate", "indirect-missing-variant",
                    "indirect-enum-qualified-message",
                )
                # An earlier unrelated selector failure cannot satisfy this
                # negative control. Require the intended indirect boundary.
                self.assertIn("probe " + ("boolean_indirect_stack" if minimal else
                                         "retained_indirect_modes"), result.stderr)

    def test_float_and_register_formats_are_independent_complete_enums(self):
        for mode, floating, register, others in [
            ("present", False, False, False),
            ("float-formats-modern", True, False, False),
            ("register-kinds-modern", False, True, False),
            ("formats-modern", True, True, False),
            ("trust-formats-modern", True, True, False),
            ("indirect-modern-all", False, False, True),
            ("float-formats-modern-all", True, False, True),
            ("register-kinds-modern-all", False, True, True),
            ("formats-modern-all", True, True, True),
            ("trust-formats-modern-all", True, True, True),
        ]:
            with self.subTest(case=mode):
                result, directory = self.probe(mode, rustflags="-Dwarnings", label="format-shapes-" + mode)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual("cargo:rustc-cfg=rustc_extended_float_formats\n" in result.stdout, floating)
                self.assertEqual("cargo:rustc-cfg=rustc_ppc_f128_register\n" in result.stdout, register)
                for flag in ("rustc_attr_ir_lang_items", "rustc_canonical_memory_symbols",
                             "rustc_attr_ir_attributes", "rustc_structures_crate_type",
                             "rustc_codegen_sample_profile", "rustc_scalar_pair_struct",
                             "rustc_cast_pad_count", "rustc_indirect_modes"):
                    self.assertEqual("cargo:rustc-cfg=" + flag + "\n" in result.stdout, others)
                for flag in ("rustc_linkage_common", "rustc_compiled_module_cache_links"):
                    self.assertEqual("cargo:rustc-cfg=" + flag + "\n" in result.stdout, not others)
                for name in ("float_formats", "register_kinds"):
                    self.assertTrue((directory / ("out/probe_retained_" + name + ".rmeta")).is_file())
                    source = (directory / ("out/probe_retained_" + name + ".rs")).read_text()
                    self.assertNotIn("..", source)
                    if name == "float_formats":
                        self.assertEqual("Float::F16B" in source, floating)
                        self.assertEqual("Float::PpcF128" in source, floating)
                    else:
                        self.assertEqual("RegKind::PpcF128" in source, register)
                        self.assertIn("Vector { hint_vector_elem }", source)
                        self.assertIn("Option<rustc_abi::Primitive>", source)

    def test_float_format_unknown_enums_and_diagnostics_abort_at_the_right_probe(self):
        diagnostic = ("legacy-extra-error", "legacy-denied-warning", "legacy-wrong-span",
                      "legacy-wrong-token", "legacy-wrong-message", "legacy-wrong-code",
                      "legacy-extra-primary", "legacy-expanded-token", "missing-crate")
        retained = ("missing-output", "missing-ppc", "missing-f16", "tuple-variant",
                    "unknown-variant", "legacy-missing-f128", "legacy-unknown-variant", "legacy-ppc-only")
        for suffix in diagnostic + retained:
            with self.subTest(case=suffix):
                result, _ = self.probe("float-formats-" + suffix, rustflags="-Dwarnings")
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertNotIn("cargo:rustc-cfg=rustc_extended_float_formats\n", result.stdout)
                self.assertIn("probe " + ("bfloat_primitive" if suffix in diagnostic or suffix == "tuple-variant" else
                                         "retained_float_formats"), result.stderr)

    def test_register_kind_unknown_enums_fields_and_diagnostics_abort_at_the_right_probe(self):
        diagnostic = ("legacy-extra-error", "legacy-denied-warning", "legacy-wrong-span",
                      "legacy-wrong-token", "legacy-wrong-message", "legacy-wrong-code",
                      "legacy-extra-primary", "legacy-expanded-token", "missing-crate")
        retained = ("missing-output", "missing-hint", "wrong-hint-type", "required-vector-field",
                    "legacy-missing-hint", "legacy-wrong-hint-type", "legacy-required-vector-field",
                    "unknown-variant", "legacy-unknown-variant", "missing-integer", "tuple-variant")
        for suffix in diagnostic + retained:
            with self.subTest(case=suffix):
                result, _ = self.probe("register-kinds-" + suffix, rustflags="-Dwarnings")
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertNotIn("cargo:rustc-cfg=rustc_ppc_f128_register\n", result.stdout)
                self.assertIn("probe " + ("ppc_f128_register" if suffix in diagnostic or suffix == "tuple-variant" else
                                         "retained_register_kinds"), result.stderr)

    def test_constant_pointer_api_is_independent_and_keeps_typed_consumers(self):
        for mode, direct, others, floating, register in [
            ("present", False, False, False, False),
            ("pointer-modern", True, False, False, False),
            ("trust-pointer-modern", True, False, False, False),
            ("formats-modern-all", False, True, True, True),
            ("pointer-legacy-all", False, True, True, True),
            ("pointer-modern-all", True, True, True, True),
            ("trust-pointer-modern-all", True, True, True, True),
            ("pointer-modern-float", True, False, True, False),
            ("pointer-modern-register", True, False, False, True),
        ]:
            with self.subTest(case=mode):
                result, directory = self.probe(mode, rustflags="-Dwarnings", label="pointer-api-" + mode)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual("cargo:rustc-cfg=rustc_scalar_direct_pointer\n" in result.stdout, direct)
                for flag in ("rustc_attr_ir_lang_items", "rustc_canonical_memory_symbols",
                             "rustc_attr_ir_attributes", "rustc_structures_crate_type",
                             "rustc_codegen_sample_profile", "rustc_scalar_pair_struct",
                             "rustc_cast_pad_count", "rustc_indirect_modes"):
                    self.assertEqual("cargo:rustc-cfg=" + flag + "\n" in result.stdout, others)
                for flag in ("rustc_linkage_common", "rustc_compiled_module_cache_links"):
                    self.assertEqual("cargo:rustc-cfg=" + flag + "\n" in result.stdout, not others)
                self.assertEqual("cargo:rustc-cfg=rustc_extended_float_formats\n" in result.stdout, floating)
                self.assertEqual("cargo:rustc-cfg=rustc_ppc_f128_register\n" in result.stdout, register)
                self.assertTrue((directory / "out/probe_retained_scalar_pointer.rmeta").is_file())
                source = (directory / "out/probe_retained_scalar_pointer.rs").read_text()
                self.assertIn("value.size() != cx.data_layout().pointer_size()", source)
                self.assertIn("prov_and_relative_offset", source)
                self.assertEqual("Some(value.to_pointer(cx))" in source, direct)
                self.assertEqual("value.to_pointer(cx).discard_err()" in source, not direct)
                metadata = json.loads((directory / "pointer_middle_standin.json").read_text())
                self.assertEqual(metadata["exit"], 0)

    def test_constant_pointer_unknown_apis_abort_at_the_intended_probe(self):
        diagnostic = ("extra-error", "denied-warning", "wrong-span", "wrong-token", "wrong-message",
                      "wrong-code", "extra-primary", "expanded-token", "missing-crate")
        minimal = ("missing-conversion", "wrong-return", "legacy-wrong-return", "legacy-wrong-discard")
        retained = ("missing-output", "missing-size", "wrong-size-type", "missing-layout-size",
                    "wrong-layout-size-type", "missing-address-split", "missing-relative-offset",
                    "wrong-relative-offset-type", "legacy-missing-size", "legacy-wrong-size-type",
                    "legacy-missing-layout-size", "legacy-wrong-layout-size-type",
                    "legacy-missing-address-split", "legacy-missing-relative-offset",
                    "legacy-wrong-relative-offset-type")
        for suffix in diagnostic + minimal + retained:
            with self.subTest(case=suffix):
                result, directory = self.probe("pointer-" + suffix, rustflags="-Dwarnings")
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertNotIn("cargo:rustc-cfg=rustc_scalar_direct_pointer\n", result.stdout)
                phase = "scalar_pointer_result" if suffix in diagnostic + minimal else "retained_scalar_pointer"
                self.assertIn("probe " + phase, result.stderr)
                if suffix != "missing-crate":
                    metadata = json.loads((directory / "pointer_middle_standin.json").read_text())
                    self.assertEqual(metadata["exit"], 0)

    def test_synthetic_terminator_shape_is_independent_and_complete(self):
        for mode, attributes, others, pointer in [
            ("present", True, False, False),
            ("terminator-modern", False, False, False),
            ("trust-terminator-modern", False, False, False),
            ("pointer-modern-all", True, True, True),
            ("terminator-legacy-all", True, True, True),
            ("terminator-modern-all", False, True, True),
            ("trust-terminator-modern-all", False, True, True),
            ("terminator-modern-pointer", False, False, True),
            ("terminator-legacy-pointer", True, False, True),
        ]:
            with self.subTest(case=mode):
                result, directory = self.probe(mode, rustflags="-Dwarnings", label="terminator-api-" + mode)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual("cargo:rustc-cfg=rustc_terminator_attributes\n" in result.stdout, attributes)
                self.assertEqual("cargo:rustc-cfg=rustc_scalar_direct_pointer\n" in result.stdout, pointer)
                for flag in ("rustc_attr_ir_lang_items", "rustc_canonical_memory_symbols",
                             "rustc_attr_ir_attributes", "rustc_structures_crate_type",
                             "rustc_codegen_sample_profile", "rustc_scalar_pair_struct",
                             "rustc_cast_pad_count", "rustc_indirect_modes",
                             "rustc_extended_float_formats", "rustc_ppc_f128_register"):
                    self.assertEqual("cargo:rustc-cfg=" + flag + "\n" in result.stdout, others)
                for flag in ("rustc_linkage_common", "rustc_compiled_module_cache_links"):
                    self.assertEqual("cargo:rustc-cfg=" + flag + "\n" in result.stdout, not others)
                self.assertTrue((directory / "out/probe_retained_terminator.rmeta").is_file())
                source = (directory / "out/probe_retained_terminator.rs").read_text()
                self.assertEqual("attributes: Default::default()" in source, attributes)
                self.assertIn("(term.source_info, &term.kind)", source)
                self.assertNotIn("..", source)
                metadata = json.loads((directory / "pointer_middle_standin.json").read_text())
                self.assertEqual(metadata["exit"], 0)

    def test_synthetic_terminator_unknown_shapes_abort_at_the_intended_probe(self):
        diagnostic = ("extra-error", "denied-warning", "wrong-span", "wrong-token", "wrong-message",
                      "wrong-code", "extra-primary", "expanded-token", "missing-crate")
        minimal = ("missing-type", "legacy-missing-type", "legacy-private-attrs", "legacy-wrong-attrs-type")
        retained = ("missing-output", "required-field", "legacy-required-field", "renamed-source",
                    "legacy-renamed-source", "wrong-source-type", "legacy-wrong-source-type",
                    "renamed-kind", "legacy-renamed-kind", "wrong-kind-type", "legacy-wrong-kind-type",
                    "noncopy-source", "legacy-noncopy-source", "missing-source-type", "legacy-missing-source-type")
        for suffix in diagnostic + minimal + retained:
            with self.subTest(case=suffix):
                result, directory = self.probe("terminator-" + suffix, rustflags="-Dwarnings")
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertNotIn("cargo:rustc-cfg=rustc_terminator_attributes\n", result.stdout)
                phase = "terminator_attributes" if suffix in diagnostic + minimal else "retained_terminator"
                self.assertIn("probe " + phase, result.stderr)
                if suffix != "missing-crate":
                    metadata = json.loads((directory / "pointer_middle_standin.json").read_text())
                    self.assertEqual(metadata["exit"], 0)

    def test_clause_queries_select_independently_and_retain_complete_contracts(self):
        cases = [
            ("present", False, False, False),
            ("query-super-modern", True, False, False),
            ("query-own-modern", False, True, False),
            ("query-both-modern", True, True, False),
            ("trust-query-both-modern", True, True, False),
            ("query-super-modern-all", True, False, True),
            ("query-own-modern-all", False, True, True),
            ("query-both-modern-all", True, True, True),
            ("query-legacy-all", False, False, True),
        ]
        for mode, modern_super, modern_own, others in cases:
            with self.subTest(case=mode):
                result, directory = self.probe(mode, rustflags="-Dwarnings", label="clauses-" + mode)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                for flag, expected in [("rustc_super_clauses_query", modern_super),
                                       ("rustc_own_clauses_query", modern_own),
                                       ("rustc_bound_fn_args", others),
                                       ("rustc_backend_lane_count", others),
                                       ("rustc_goto_loop_hints", others)]:
                    self.assertEqual("cargo:rustc-cfg=" + flag + "\n" in result.stdout, expected)
                super_source = (directory / "out/probe_retained_super_clauses.rs").read_text()
                own_source = (directory / "out/probe_retained_own_clauses.rs").read_text()
                self.assertIn("explicit_super_clauses_of" if modern_super else "explicit_super_predicates_of", super_source)
                self.assertNotIn("skip_binder", super_source)
                self.assertNotIn("implied", super_source)
                self.assertIn("EarlyBinder", super_source)
                self.assertIn("GenericClauses { parent, clauses }" if modern_own else "GenericPredicates { parent, predicates }", own_source)
                self.assertNotIn("..", own_source)
                self.assertNotIn("explicit_clauses_of", own_source)
                for name in ["retained_super_clauses", "retained_own_clauses"]:
                    self.assertTrue((directory / ("out/probe_" + name + ".rmeta")).is_file())

    def test_super_query_unknown_contracts_abort_at_the_intended_probe(self):
        diagnostics = ("legacy-extra-error", "legacy-denied-warning", "legacy-wrong-span",
                       "legacy-wrong-token", "legacy-wrong-message", "legacy-wrong-code",
                       "legacy-extra-primary", "legacy-expanded-token", "legacy-missing-crate")
        minimal = ("modern-wrong-result", "modern-wrong-id", "modern-wrong-span-type")
        retained = ("legacy-wrong-result", "legacy-wrong-id", "legacy-wrong-span-type",
                    "legacy-missing-method", "modern-missing-method",
                    "legacy-missing-output", "modern-missing-output")
        for suffix in diagnostics + minimal + retained:
            with self.subTest(case=suffix):
                result, _ = self.probe("query-super-" + suffix, rustflags="-Dwarnings")
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertNotIn("cargo:rustc-cfg=rustc_super_clauses_query\n", result.stdout)
                phase = "retained_super_clauses" if suffix in retained else "super_clauses_query"
                self.assertIn("probe " + phase, result.stderr)

    def test_own_query_unknown_contracts_abort_at_the_intended_probe(self):
        diagnostics = ("legacy-extra-error", "legacy-denied-warning", "legacy-wrong-span",
                       "legacy-wrong-token", "legacy-wrong-message", "legacy-wrong-code",
                       "legacy-extra-primary", "legacy-expanded-token", "legacy-missing-crate")
        minimal = ("modern-wrong-id",)
        retained = ("modern-wrong-parent", "legacy-wrong-parent", "modern-wrong-clauses",
                    "legacy-wrong-clauses", "modern-required-field", "legacy-required-field",
                    "modern-missing-parent", "legacy-missing-parent", "legacy-wrong-id",
                    "modern-wrong-result", "legacy-wrong-result",
                    "legacy-missing-output", "modern-missing-output")
        for suffix in diagnostics + minimal + retained:
            with self.subTest(case=suffix):
                result, _ = self.probe("query-own-" + suffix, rustflags="-Dwarnings")
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertNotIn("cargo:rustc-cfg=rustc_own_clauses_query\n", result.stdout)
                phase = "own_clauses_query" if suffix in diagnostics + minimal else "retained_own_clauses"
                self.assertIn("probe " + phase, result.stderr)

    def test_function_item_binder_is_independent_and_retains_typed_contracts(self):
        for mode, bound, lanes, goto, pair, others in [
            ("present", False, False, False, False, False),
            ("fn-args-modern", True, False, False, False, False),
            ("trust-fn-args-modern", True, False, False, False, False),
            ("fn-args-modern-all", True, True, True, True, True),
            ("fn-args-legacy-all", False, True, True, True, True),
            ("fn-args-modern-lanes", True, True, False, False, False),
            ("fn-args-legacy-lanes", False, True, False, False, False),
            ("fn-args-modern-goto", True, False, True, False, False),
            ("fn-args-legacy-goto", False, False, True, False, False),
        ]:
            with self.subTest(case=mode):
                result, directory = self.probe(mode, rustflags="-Dwarnings", label="fn-item-" + mode)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                for flag, expected in [("rustc_bound_fn_args", bound),
                                       ("rustc_backend_lane_count", lanes),
                                       ("rustc_goto_loop_hints", goto),
                                       ("rustc_scalar_pair_struct", pair),
                                       ("rustc_scalar_direct_pointer", others)]:
                    self.assertEqual("cargo:rustc-cfg=" + flag + "\n" in result.stdout, expected)
                source = (directory / "out/probe_bound_fn_args.rs").read_text()
                self.assertEqual(source.count("no_bound_vars"), 1)
                source = (directory / "out/probe_retained_fn_args.rs").read_text()
                self.assertEqual("args.no_bound_vars()?" in source, bound)
                self.assertEqual("ty::Binder::dummy(args)" in source, bound)
                self.assertIn("Some((args, kind))", source)
                self.assertNotIn("skip_binder", source)
                self.assertNotIn("..", source)
                self.assertTrue((directory / "out/probe_retained_fn_args.rmeta").is_file())
                metadata = json.loads((directory / "pointer_middle_standin.json").read_text())
                self.assertEqual(metadata["exit"], 0)
                ordinary = (directory / "probe_bound_fn_args.ordinary.stderr").read_text()
                if bound:
                    notices = [json.loads(line) for line in ordinary.splitlines() if line]
                    self.assertEqual(len(notices), 1)
                    self.assertEqual(notices[0]["level"], "note")
                    self.assertEqual(notices[0]["message"],
                                     "compiled WITHOUT Trust verification — 0 obligations checked")
                    self.assertIsNone(notices[0]["code"])
                    self.assertEqual(notices[0]["spans"], [])
                    self.assertEqual(notices[0]["children"], [])
                else:
                    self.assertIn("no method named `no_bound_vars`", ordinary)
                    self.assertIn("RawList", ordinary)

    def test_function_item_unknown_binders_abort_at_the_intended_probe(self):
        diagnostic = ("legacy-extra-error", "legacy-denied-warning", "legacy-wrong-span",
                      "legacy-wrong-token", "legacy-wrong-message", "legacy-wrong-code",
                      "legacy-extra-primary", "legacy-expanded-token", "legacy-missing-crate")
        minimal = ("missing-fndef", "required-field", "legacy-required-field",
                   "legacy-wrong-args-type", "missing-method", "wrong-return-type", "noncopy-binder")
        retained = ("wrong-constructor", "wrong-new-result", "wrong-def-id-type", "missing-output")
        for suffix in diagnostic + minimal + retained:
            with self.subTest(case=suffix):
                result, _ = self.probe("fn-args-" + suffix, rustflags="-Dwarnings")
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertNotIn("cargo:rustc-cfg=rustc_bound_fn_args\n", result.stdout)
                phase = "retained_fn_args" if suffix in retained else "bound_fn_args"
                self.assertIn("probe " + phase, result.stderr)

    def test_backend_lane_count_is_independent_and_preserves_borrows(self):
        for mode, wrapped, goto, pair, others in [
            ("present", False, False, False, False),
            ("lanes-modern", True, False, False, False),
            ("trust-lanes-modern", True, False, False, False),
            ("lanes-modern-all", True, True, True, True),
            ("lanes-legacy-all", False, True, True, True),
            ("lanes-modern-goto", True, True, False, False),
            ("lanes-legacy-goto", False, True, False, False),
            ("lanes-modern-pair", True, False, True, False),
            ("lanes-legacy-pair", False, False, True, False),
        ]:
            with self.subTest(case=mode):
                result, directory = self.probe(mode, rustflags="-Dwarnings", label="backend-lanes-" + mode)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual("cargo:rustc-cfg=rustc_backend_lane_count\n" in result.stdout, wrapped)
                self.assertEqual("cargo:rustc-cfg=rustc_goto_loop_hints\n" in result.stdout, goto)
                self.assertEqual("cargo:rustc-cfg=rustc_scalar_pair_struct\n" in result.stdout, pair)
                self.assertEqual("cargo:rustc-cfg=rustc_scalar_direct_pointer\n" in result.stdout, others)
                source = (directory / "out/probe_backend_lane_count.rs").read_text()
                self.assertEqual(source.count("as_u64"), 1)
                source = (directory / "out/probe_retained_backend_lanes.rs").read_text()
                self.assertEqual("count.as_u64()" in source, wrapped)
                self.assertIn("Some((count, repr))", source)
                self.assertNotIn("..", source)
                self.assertTrue((directory / "out/probe_retained_backend_lanes.rmeta").is_file())

    def test_backend_lane_count_unknown_shapes_abort_at_the_intended_probe(self):
        diagnostic = ("legacy-extra-error", "legacy-denied-warning", "legacy-wrong-span",
                      "legacy-wrong-token", "legacy-wrong-message", "legacy-wrong-code",
                      "legacy-extra-primary", "legacy-expanded-token", "legacy-missing-crate")
        minimal = ("missing-variant", "renamed-count", "required-field", "legacy-required-field",
                   "legacy-wrong-count-type", "wrong-result-type", "missing-method", "tuple-variant")
        retained = ("wrong-element-type", "noncopy-consuming-count", "missing-output")
        for suffix in diagnostic + minimal + retained:
            with self.subTest(case=suffix):
                result, _ = self.probe("lanes-" + suffix, rustflags="-Dwarnings")
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertNotIn("cargo:rustc-cfg=rustc_backend_lane_count\n", result.stdout)
                phase = "backend_lane_count" if suffix in diagnostic + minimal else "retained_backend_lanes"
                self.assertIn("probe " + phase, result.stderr)

    def test_goto_hints_are_independent_and_keep_the_original_kind(self):
        for mode, hints, attributes, others, pointer in [
            ("present", False, True, False, False),
            ("goto-modern", True, True, False, False),
            ("trust-goto-modern", True, True, False, False),
            ("goto-modern-all", True, False, True, True),
            ("goto-legacy-all", False, False, True, True),
            ("goto-modern-terminator", True, False, False, False),
            ("goto-legacy-terminator", False, False, False, False),
            ("goto-modern-pointer", True, True, False, True),
            ("goto-legacy-pointer", False, True, False, True),
        ]:
            with self.subTest(case=mode):
                result, directory = self.probe(mode, rustflags="-Dwarnings", label="goto-api-" + mode)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual("cargo:rustc-cfg=rustc_goto_loop_hints\n" in result.stdout, hints)
                self.assertEqual("cargo:rustc-cfg=rustc_terminator_attributes\n" in result.stdout, attributes)
                self.assertEqual("cargo:rustc-cfg=rustc_scalar_direct_pointer\n" in result.stdout, pointer)
                for flag in ("rustc_attr_ir_lang_items", "rustc_canonical_memory_symbols",
                             "rustc_attr_ir_attributes", "rustc_structures_crate_type",
                             "rustc_codegen_sample_profile", "rustc_scalar_pair_struct",
                             "rustc_cast_pad_count", "rustc_indirect_modes",
                             "rustc_extended_float_formats", "rustc_ppc_f128_register"):
                    self.assertEqual("cargo:rustc-cfg=" + flag + "\n" in result.stdout, others)
                for flag in ("rustc_linkage_common", "rustc_compiled_module_cache_links"):
                    self.assertEqual("cargo:rustc-cfg=" + flag + "\n" in result.stdout, not others)
                minimal = (directory / "out/probe_goto_loop_hints.rs").read_text()
                self.assertEqual(minimal.count("loop_hint_attrs"), 1)
                source = (directory / "out/probe_retained_goto.rs").read_text()
                self.assertEqual("loop_hint_attrs: Default::default()" in source, hints)
                self.assertIn("Some((*target, kind))", source)
                self.assertNotIn("..", source)
                self.assertTrue((directory / "out/probe_retained_goto.rmeta").is_file())
                metadata = json.loads((directory / "pointer_middle_standin.json").read_text())
                self.assertEqual(metadata["exit"], 0)

    def test_goto_unknown_shapes_abort_at_the_intended_probe(self):
        diagnostic = ("legacy-extra-error", "legacy-denied-warning", "legacy-wrong-span",
                      "legacy-wrong-token", "legacy-wrong-message", "legacy-wrong-code",
                      "legacy-extra-primary", "legacy-expanded-token", "legacy-missing-crate")
        minimal = ("missing-variant", "legacy-missing-variant", "renamed-target",
                   "legacy-renamed-target", "required-field", "legacy-required-field",
                   "wrong-hints-type", "tuple-variant")
        retained = ("missing-output", "wrong-target-type", "legacy-wrong-target-type",
                    "noncopy-target", "legacy-noncopy-target", "missing-block-type",
                    "legacy-missing-block-type", "wrong-hints-container")
        for suffix in diagnostic + minimal + retained:
            with self.subTest(case=suffix):
                result, directory = self.probe("goto-" + suffix, rustflags="-Dwarnings")
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertNotIn("cargo:rustc-cfg=rustc_goto_loop_hints\n", result.stdout)
                phase = "goto_loop_hints" if suffix in diagnostic + minimal else "retained_goto"
                self.assertIn("probe " + phase, result.stderr)
                if suffix != "legacy-missing-crate":
                    metadata = json.loads((directory / "pointer_middle_standin.json").read_text())
                    self.assertEqual(metadata["exit"], 0)

    def test_ambiguous_failures_are_build_errors_not_absent_capabilities(self):
        cases = [("tool-failure", None), ("help-failure", None), ("help-ambiguous", None),
                 ("invalid-flag", "--deliberately-invalid"), ("verification-refusal", None),
                 ("missing-output", None), ("missing-crate", None), ("missing-both-mono", None),
                 ("extra-error", None), ("wrong-span", None), ("malformed-json", None),
                 ("denied-warning", "-Dwarnings"), ("field-option-mismatch", None),
                 ("duplicate-off", None), ("duplicate-tracked", None), ("duplicate-standard", None),
                 ("malformed-help-row", None), ("help-trailing-error", None),
                 ("help-unknown-header", None), ("orphan-help-continuation", None),
                 ("help-indented-error", None), ("help-unindented-description", None),
                 ("missing-output-stale", None), ("nonunicode-flags", "\udcff")]
        cases += [(mode, None) for mode in (
            "note-wrong-code", "note-wrong-tool", "note-unrelated", "note-child", "note-duplicate",
            "trust-extra-error", "trust-wrong-span", "trust-missing-both-mono",
        )]
        for mode, flags in cases:
            with self.subTest(case=mode):
                result, _ = self.probe(mode, rustflags=flags)
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        result, _ = self.probe("nonunicode-encoded", encoded="\udcff")
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main(verbosity=2)
