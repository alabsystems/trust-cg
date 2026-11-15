"""The per-host required sets of the full test matrix and the Darwin runner's verdicts.

The real-tree cases read Cargo's target list through the installed Trust
package's `targo` (the same denominator scripts/run_full_test_matrix.sh
validates against);
everything else uses synthetic metadata and transcripts.
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


HOSTS = load("_test_full_test_matrix_hosts", ROOT / "scripts" / "full_test_matrix_hosts.py")
RUNNER = load("_test_run_darwin_full_test_matrix", ROOT / "scripts" / "run_darwin_full_test_matrix.py")
sys.path.insert(0, str(Path(__file__).resolve().parent))
import atpkg_prelude_fixture as SHIMS  # noqa: E402


def transcript(passed=("case_a",), failed=(), ignored=(), filtered=0, outputs=None, rollup=True):
    """A plain libtest --show-output transcript with named results."""
    outputs = outputs or {}
    lines = [f"running {len(passed) + len(failed) + len(ignored)} tests"]
    lines += [f"test {name} ... ok" for name in passed]
    lines += [f"test {name} ... FAILED" for name in failed]
    lines += [f"test {name} ... ignored" for name in ignored]
    lines += ["", "successes:", ""]
    for name in passed:
        if name in outputs:
            lines += [f"---- {name} stdout ----", outputs[name], ""]
    lines += ["", "successes:", *[f"    {name}" for name in passed], ""]
    if rollup:
        state = "FAILED" if failed else "ok"
        lines.append(f"test result: {state}. {len(passed)} passed; {len(failed)} failed; {len(ignored)} ignored; "
                     f"0 measured; {filtered} filtered out; finished in 0.01s")
    return "\n".join(lines) + "\n"


class Workspace:
    """A synthetic workspace: source files on disk and the metadata Cargo would report."""

    def __init__(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="tcg-full-matrix-hosts-")
        self.root = Path(self.temporary.name)
        self.packages: dict[str, dict] = {}

    def close(self):
        self.temporary.cleanup()

    def package(self, name, features=None):
        package = {"id": f"{name} 0.1.0", "name": name, "features": features or {}, "targets": []}
        self.packages[name] = package
        return package

    def target(self, package, kind, name, source, *, test=True, doctest=None, required_features=None):
        path = self.root / package / f"{kind}-{name}.rs"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)
        self.packages[package]["targets"].append({
            "kind": [kind], "name": name, "src_path": str(path), "test": test,
            "doctest": kind == "lib" if doctest is None else doctest,
            "required-features": required_features or [],
        })
        return path

    def metadata(self):
        return {"packages": list(self.packages.values()),
                "workspace_members": [package["id"] for package in self.packages.values()]}


class InventoryTests(unittest.TestCase):
    def setUp(self):
        self.workspace = Workspace()
        self.addCleanup(self.workspace.close)
        # The synthetic workspaces start from empty classification tables.
        for table in (HOSTS.SUITE_CLASS, HOSTS.TEST_CLASS, HOSTS.IGNORED_TESTS, HOSTS.SKIP_OUTPUT_EXEMPTIONS):
            patcher = mock.patch.dict(table, clear=True)
            patcher.start()
            self.addCleanup(patcher.stop)

    def classify(self):
        return {suite.id: suite for suite in HOSTS.suites(self.workspace.metadata())}

    def test_every_cargo_test_suite_is_one_suite_with_one_class(self):
        w = self.workspace
        w.package("alpha", features={"default": ["base"], "base": [], "driver": []})
        w.target("alpha", "lib", "alpha", "/// ```\n/// assert!(true);\n/// ```\npub fn f() {}\n#[test] fn t() {}\n")
        w.target("alpha", "bin", "tool", "fn main() {}\n")
        w.target("alpha", "example", "demo", "fn main() {}\n#[test] fn t() {}\n", test=False)
        w.target("alpha", "test", "shared", "#[test] fn t() {}\n")
        w.target("alpha", "test", "macos_only", '#![cfg(all(target_arch = "aarch64", target_os = "macos"))]\n#[test] fn t() {}\n')
        w.target("alpha", "test", "linux_only", '#![cfg(target_os = "linux")]\n#[test] fn t() {}\n')
        w.target("alpha", "test", "x86", '#![cfg(target_arch = "x86_64")]\n#[test] fn t() {}\n')
        w.target("alpha", "test", "gated", '#![cfg(feature = "driver")]\n#[test] fn t() {}\n')
        w.target("alpha", "test", "needs", "#[test] fn t() {}\n", required_features=["driver"])
        found = self.classify()
        self.assertEqual(sorted(found), [
            "alpha/bin/tool", "alpha/doc", "alpha/lib", "alpha/test/gated", "alpha/test/linux_only",
            "alpha/test/macos_only", "alpha/test/needs", "alpha/test/shared", "alpha/test/x86",
        ])
        classes = {suite_id: suite.klass for suite_id, suite in found.items()}
        self.assertEqual(classes["alpha/lib"], "both")
        self.assertEqual(classes["alpha/doc"], "both")
        self.assertEqual(classes["alpha/bin/tool"], "empty")
        self.assertEqual(classes["alpha/test/macos_only"], "darwin")
        self.assertEqual(classes["alpha/test/linux_only"], "linux")
        self.assertEqual(classes["alpha/test/x86"], "neither")
        # A file-level feature gate or required feature is built with that feature, not left empty.
        self.assertEqual(found["alpha/test/gated"].features, ("driver",))
        self.assertEqual(found["alpha/test/needs"].features, ("driver",))
        self.assertEqual(classes["alpha/test/gated"], "both")
        self.assertIn("--features", found["alpha/test/gated"].cargo_arguments())
        self.assertEqual(found["alpha/doc"].cargo_arguments(), ["-p", "alpha", "--doc"])
        for suite in found.values():
            if suite.klass != "both":
                self.assertTrue(suite.reason, suite.id)
            for host in suite.required:
                self.assertGreaterEqual(HOSTS.minimum_passes(suite, host), 1)
            for host in set(HOSTS.HOSTS) - set(suite.required):
                self.assertEqual(HOSTS.minimum_passes(suite, host), 0)

    def test_census_follows_modules_and_ignores_non_rust_or_ignored_doc_blocks(self):
        w = self.workspace
        w.package("beta")
        lib = w.target("beta", "lib", "beta", "mod inner;\n/// ```text\n/// not a test\n/// ```\n"
                       "/// ```ignore\n/// pseudo();\n/// ```\npub fn f() {}\n")
        (lib.parent / "inner.rs").write_text("#[cfg(test)]\nmod tests {\n    #[test]\n    fn t() {}\n}\n")
        found = self.classify()
        self.assertEqual(found["beta/lib"].census, 1)
        self.assertEqual(found["beta/lib"].klass, "both")
        self.assertEqual(found["beta/doc"].klass, "empty")
        self.assertIn("doc-test", found["beta/doc"].reason)

    def test_module_walk_follows_path_attributes_after_other_attributes(self):
        w = self.workspace
        w.package("theta")
        lib = w.target("theta", "lib", "theta", '#[cfg(test)]\n#[path = "theta_tests.rs"]\nmod tests;\npub fn f() {}\n')
        (lib.parent / "theta_tests.rs").write_text("#[test]\nfn found() {}\n")
        found = self.classify()
        self.assertEqual(found["theta/lib"].census, 1)
        self.assertTrue(HOSTS.defines_test(found["theta/lib"], "tests::found"))

    def test_classification_tables_are_checked_against_the_source(self):
        w = self.workspace
        w.package("gamma")
        w.target("gamma", "test", "linux_only", '#![cfg(target_os = "linux")]\n#[test] fn t() {}\n')
        w.target("gamma", "test", "shared", "#[test] fn host_leg() {}\n#[test] fn other() {}\n"
                 "#[test]\n#[ignore = \"slow\"]\nfn parked() {}\n")
        tables = {
            "SUITE_CLASS": {
                "gamma/test/linux_only": ("darwin", "contradicts the file-level cfg"),
                "gamma/test/shared": ("both", "stale: static evidence already says both"),
                "gamma/test/missing": ("darwin", "names no suite"),
            },
            "TEST_CLASS": {
                ("gamma/test/shared", "host_leg"): ("linux", "Linux-only leg"),
                ("gamma/test/shared", "not_defined"): ("darwin", "no such test"),
                ("gamma/test/shared", "other"): ("sometimes", "unknown lane"),
            },
            "IGNORED_TESTS": {
                ("gamma/test/shared", "parked"): "slow",
                ("gamma/test/shared", "other"): "not actually ignored",
            },
        }
        with mock.patch.dict(HOSTS.SUITE_CLASS, tables["SUITE_CLASS"], clear=True), \
                mock.patch.dict(HOSTS.TEST_CLASS, tables["TEST_CLASS"], clear=True), \
                mock.patch.dict(HOSTS.IGNORED_TESTS, tables["IGNORED_TESTS"], clear=True):
            issues = "\n".join(HOSTS.problems(HOSTS.suites(w.metadata())))
            self.assertIn("gamma/test/linux_only: classified darwin but its file-level cfg compiles it out on darwin", issues)
            self.assertIn("gamma/test/shared: SUITE_CLASS entry is stale", issues)
            self.assertIn("SUITE_CLASS names no suite: gamma/test/missing", issues)
            self.assertIn("gamma/test/shared::not_defined: TEST_CLASS names a test its module tree does not define", issues)
            self.assertIn("gamma/test/shared::other: TEST_CLASS entry needs a lane", issues)
            self.assertIn("gamma/test/shared::other: IGNORED_TESTS names a test its module tree does not #[ignore]", issues)
            self.assertNotIn("host_leg", issues)
            self.assertNotIn("parked", issues)
            # An entry in an unknown lane is never silently skipped.
            self.assertEqual(HOSTS.host_skipped_tests("gamma/test/shared", "darwin"), ["host_leg"])

    LANES = {
        ("delta/test/mixed", "a"): ("darwin", "Darwin-only leg"),
        ("delta/test/mixed", "b"): ("linux", "Linux-only leg"),
        ("delta/test/mixed", "c"): ("formal", "strict proof campaign"),
        ("delta/test/mixed", "d"): ("external-cert", "external certificate campaign"),
        ("delta/test/mixed", "e"): ("opt-in", "release-build measurement"),
        ("delta/test/mixed", "f"): ("other-lane", "needs wasm-ld"),
    }

    def test_test_lanes_route_tests_to_skips_or_campaigns(self):
        w = self.workspace
        w.package("delta")
        w.target("delta", "test", "mixed", "#[test] fn a() {}\n#[test] fn b() {}\n#[test] fn c() {}\n"
                 "#[test] fn d() {}\n#[test] fn e() {}\n#[test] fn f() {}\n#[test] fn g() {}\n")
        with mock.patch.dict(HOSTS.TEST_CLASS, self.LANES, clear=True):
            self.assertEqual(HOSTS.problems(HOSTS.suites(w.metadata())), [])
            # Another lane's and an opt-in test are skipped on both hosts.
            self.assertEqual(HOSTS.host_skipped_tests("delta/test/mixed", "darwin"), ["b", "e", "f"])
            self.assertEqual(HOSTS.host_skipped_tests("delta/test/mixed", "linux"), ["a", "e", "f"])
            self.assertEqual(HOSTS.campaign_tests("delta/test/mixed"), {"external-cert": ["d"], "formal": ["c"]})
            # and are named as tests no AArch64 matrix runs.
            self.assertEqual(HOSTS.required_by_neither_host(),
                             {"other-lane": ["delta/test/mixed::f"], "opt-in": ["delta/test/mixed::e"]})

    def test_the_default_invocation_leaves_out_skips_and_campaign_tests_by_exact_name(self):
        with mock.patch.dict(RUNNER.HOSTS.TEST_CLASS, self.LANES, clear=True):
            skipped, campaigns, excluded, libtest = RUNNER.default_invocation("delta/test/mixed", census=False)
            self.assertEqual(skipped, ["b", "e", "f"])
            self.assertEqual(campaigns, {"external-cert": ["d"], "formal": ["c"]})
            self.assertEqual(excluded, ["b", "c", "d", "e", "f"])
            self.assertEqual(libtest, ["--exact", "--skip", "b", "--skip", "c", "--skip", "d", "--skip", "e",
                                       "--skip", "f"])
            self.assertEqual(RUNNER.default_invocation("delta/test/mixed", census=True), ([], {}, [], []))
            self.assertEqual(RUNNER.default_invocation("delta/test/other", census=False), ([], {}, [], []))

    def test_a_test_lane_cannot_name_a_host_its_suite_does_not_require(self):
        w = self.workspace
        w.package("eps")
        w.target("eps", "test", "mac", '#![cfg(target_os = "macos")]\n#[test] fn a() {}\n')
        with mock.patch.dict(HOSTS.TEST_CLASS, {("eps/test/mac", "a"): ("linux", "wrong host")}, clear=True):
            issues = "\n".join(HOSTS.problems(HOSTS.suites(w.metadata())))
        self.assertIn("requires it on linux, which does not require its suite", issues)

    def test_an_unlisted_ignore_and_a_bad_skip_exemption_are_inventory_problems(self):
        w = self.workspace
        w.package("iota")
        w.target("iota", "test", "slow", "#[test]\nfn fast() {}\n#[test]\n#[ignore = \"slow\"]\nfn parked() {}\n"
                 "#[test]\nfn prints() {}\n")
        issues = "\n".join(HOSTS.problems(HOSTS.suites(w.metadata())))
        self.assertIn("iota/test/slow: #[ignore]d test(s) missing from IGNORED_TESTS: parked", issues)
        with mock.patch.dict(HOSTS.IGNORED_TESTS, {("iota/test/slow", "parked"): "slow"}), \
                mock.patch.dict(HOSTS.SKIP_OUTPUT_EXEMPTIONS, {
                    ("iota/test/slow", "prints"): ("SKIP t: ", "checked output"),
                    ("iota/test/slow", "absent"): ("SKIP t: ", "no such test"),
                }, clear=True):
            issues = "\n".join(HOSTS.problems(HOSTS.suites(w.metadata())))
            self.assertNotIn("missing from IGNORED_TESTS", issues)
            self.assertIn("iota/test/slow::absent: SKIP_OUTPUT_EXEMPTIONS names a test", issues)
            self.assertNotIn("::prints", issues)
            self.assertEqual(HOSTS.skip_output_exemptions("iota/test/slow"), {"prints": "SKIP t: ", "absent": "SKIP t: "})

    def test_unknown_cfg_keys_fail_closed(self):
        w = self.workspace
        w.package("zeta")
        w.target("zeta", "test", "odd", '#![cfg(target_mystery = "x")]\n#[test] fn t() {}\n')
        with self.assertRaises(ValueError):
            HOSTS.suites(w.metadata())


class PackageTargoTests(unittest.TestCase):
    """The inventory comes from the package targo the suites build with, never
    from a PATH launcher shim whose prelude the resolver reads but never runs
    (DR-ATPKG-PRELUDE-SHIM-20261015)."""

    HONEST = {"packages": [{"name": "honest", "id": "honest 0.0.0", "targets": []}],
              "workspace_members": ["honest 0.0.0"]}
    GHOST = {"packages": HONEST["packages"] + [{"name": "ghost", "id": "ghost 0.0.0", "targets": []}],
             "workspace_members": ["honest 0.0.0", "ghost 0.0.0"]}

    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="trust-cg-hosts-package-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.package = SHIMS.make_package(self.root / "pkg", metadata=self.HONEST)
        self.log = self.root / "shim-calls.log"
        self.shims = self.root / "atpkg-bin"
        SHIMS.lying_shim(self.shims / "targo", self.package / "bin" / "targo", self.log,
                         {"metadata*": json.dumps(self.GHOST)})
        SHIMS.lying_shim(self.shims / "trustc", self.package / "bin" / "trustc", self.log)

    def test_the_resolved_package_answers_not_the_path_shim(self):
        # Non-vacuity: the shim's own answer would add a suite-less package.
        census = subprocess.run([str(self.shims / "targo"), "metadata"], text=True,
                                capture_output=True, timeout=60, check=True)
        self.assertIn("ghost", census.stdout)
        self.assertEqual(len(SHIMS.logged(self.log)), 1)
        self.log.unlink()
        metadata = HOSTS.load_metadata(self.root, {"PATH": f"{self.shims}:/usr/bin:/bin"})
        self.assertEqual(metadata, self.HONEST)
        self.assertEqual(SHIMS.logged(self.log), [], "the inventory executed a PATH launcher shim")

    def test_trust_targo_names_the_package_when_set(self):
        targo = str(self.package / "bin" / "targo")
        self.assertEqual(HOSTS.load_metadata(self.root, {"PATH": "/usr/bin:/bin", "TRUST_TARGO": targo}),
                         self.HONEST)
        with self.assertRaisesRegex(RuntimeError, "TRUST_TARGO must name an executable file"):
            HOSTS.load_metadata(self.root, {"PATH": f"{self.shims}:/usr/bin:/bin", "TRUST_TARGO": "pkg/bin/targo"})
        self.assertEqual(SHIMS.logged(self.log), [])

    def test_no_resolvable_package_is_an_error_not_a_path_fallback(self):
        with self.assertRaisesRegex(RuntimeError, "trustc"):
            HOSTS.load_metadata(self.root, {"PATH": "/usr/bin:/bin"})


class RealTreeTests(unittest.TestCase):
    """The committed classification of this checkout."""

    @classmethod
    def setUpClass(cls):
        if shutil.which("targo") is None:
            raise AssertionError("targo is required on PATH: the inventory denominator is Cargo's target list")
        cls.found = HOSTS.suites(HOSTS.load_metadata())

    def test_inventory_is_consistent_and_complete(self):
        self.assertEqual(HOSTS.problems(self.found), [])
        ids = [suite.id for suite in self.found]
        self.assertEqual(len(ids), len(set(ids)))
        totals = HOSTS.summary(self.found)
        self.assertEqual(sum(totals["classes"].values()), len(self.found))
        for host in HOSTS.HOSTS:
            self.assertGreater(totals["required"][host], 0)

    def test_every_required_suite_has_a_positive_minimum_and_every_exception_a_reason(self):
        for suite in self.found:
            with self.subTest(suite=suite.id):
                if suite.klass != "both":
                    self.assertTrue(suite.reason.strip())
                for host in suite.required:
                    self.assertGreaterEqual(HOSTS.minimum_passes(suite, host), 1)
        for key, entry in list(HOSTS.TEST_CLASS.items()) + [(key, ("ignored", reason))
                                                             for key, reason in HOSTS.IGNORED_TESTS.items()]:
            with self.subTest(test=key):
                self.assertTrue(entry[1].strip())

    def test_both_floors_are_subsets_of_their_host_sets(self):
        by_id = {suite.id: suite for suite in self.found}
        packages = {suite.package for suite in self.found}
        for package, target, minimum in HOSTS.darwin_floor().TARGETS:
            if package in packages:
                suite = by_id[f"{package}/test/{target}"]
                self.assertIn("darwin", suite.required, suite.id)
                self.assertGreaterEqual(HOSTS.minimum_passes(suite, "darwin"), minimum)
        for package, target in HOSTS.linux_floor().TARGETS:
            if package in packages:
                self.assertIn("linux", by_id[f"{package}/test/{target}"].required, f"{package}/{target}")

    def test_runner_lists_without_probing(self):
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout), \
                mock.patch.object(RUNNER.FLOOR, "preflight", side_effect=AssertionError("probed")):
            self.assertEqual(RUNNER.main(["--list"]), 0)
        listed = stdout.getvalue().splitlines()
        self.assertEqual(len(listed), len(HOSTS.required_set(self.found, "darwin")))
        self.assertTrue(all(" minimum=" in line for line in listed))


class SuiteVerdictTests(unittest.TestCase):
    def verdict(self, text, *, rc=0, minimum=1, filtered=0, ignored=(), doc=False):
        return RUNNER.classify_suite(rc, text, minimum=minimum, filtered=filtered,
                                     ignored=None if doc else list(ignored), doc=doc)

    def test_complete_positive_execution_passes(self):
        result = self.verdict(transcript(("a", "b"), outputs={"a": "PASS 3 checks"}), minimum=2)
        self.assertEqual(result["status"], "pass", result)
        self.assertEqual(result["counts"]["executed_passes"], 2)

    def test_skip_and_opt_in_notices_never_count_as_passes(self):
        notices = (
            "SKIP: needs an x86-64 execution host",
            "Skipping e2e test: no cc",
            "skipping #376 lldb check: /usr/bin/lldb is not available",
            "measurement campaign not requested; set TRUST_CG_RUN_MEASUREMENT_TESTS=1 to run",
            "formal proof campaign not requested; set TRUST_CG_RUN_FORMAL_PROOF_TESTS=1 to run",
            "solver_lane_probe: set TRUST_CG_RUN_FORMAL_PROOF_TESTS=1 to run",
            "dev-AY lane test not run: TRUST_CG_RUN_FORMAL_PROOF_TESTS is not 1",
        )
        for notice in notices:
            with self.subTest(notice=notice):
                result = self.verdict(transcript(("a", "b"), outputs={"a": notice}), minimum=1)
                self.assertEqual(result["status"], "fail", result)
                self.assertIn("a", result["not_executed"])
                self.assertEqual(result["counts"]["executed_passes"], 1)

    def test_skip_lines_outside_a_tests_captured_section_fail(self):
        # A nested section marker inside a test's own output ends the runner's
        # section; matrix_results still attributes the SKIP after it to the test.
        nested = self.verdict(transcript(("a", "b"), outputs={"a": "failures:\nSKIP: needs an x86-64 host"}))
        self.assertEqual(nested["status"], "fail", nested)
        self.assertEqual(nested["counts"]["executed_passes"], 1)
        self.assertTrue(any(error.startswith("runtime SKIP in a:") for error in nested["errors"]), nested)
        self.assertTrue(any("outside any test's captured output" in error for error in nested["errors"]), nested)
        # The floor's broad spelling after a nested marker, and an uncaptured line.
        broad = self.verdict(transcript(("a", "b"), outputs={"a": "successes:\nskipping: lldb is not available"}))
        self.assertEqual(broad["status"], "fail", broad)
        lines = transcript(("a", "b")).splitlines()
        lines.insert(lines.index("test a ... ok") + 1, "skipping: /usr/bin/lldb is not available")
        uncaptured = self.verdict("\n".join(lines) + "\n")
        self.assertEqual(uncaptured["status"], "fail", uncaptured)
        self.assertEqual(RUNNER.stray_skip_lines("\n".join(lines)), ["skipping: /usr/bin/lldb is not available"])
        # libtest's own result and name-list lines are not output, whatever a test is called.
        self.assertEqual(self.verdict(transcript(("skip", "skipped_rows")), minimum=2)["status"], "pass")
        # An exempt line stays exempt when matrix_results attributes it.
        exempt = RUNNER.classify_suite(0, transcript(("a",), outputs={"a": "SKIP t: no authority"}), minimum=1,
                                       filtered=0, ignored=[], doc=False, exemptions={"a": "SKIP t: "})
        self.assertEqual(exempt["status"], "pass", exempt)

    def test_a_campaign_runs_exactly_its_named_tests(self):
        self.assertEqual(RUNNER.classify_campaign(0, transcript(("c", "d")), ["c", "d"])["status"], "pass")
        for label, text in (("one missing", transcript(("c",))), ("one extra", transcript(("c", "d", "e")))):
            with self.subTest(label=label):
                result = RUNNER.classify_campaign(0, text, ["c", "d"])
                self.assertEqual(result["status"], "fail", result)
        extra = RUNNER.classify_campaign(0, transcript(("c", "d", "e")), ["c", "d"])
        self.assertIn("ran 3 tests, expected exactly the 2 campaign tests", extra["errors"])

    def test_report_rows_that_spell_skip_are_not_early_returns(self):
        rows = (
            "[skip    ] AArch64::Brk                     pseudo/trap \u2014 no equivalence proof obligation",
            "skip function=bytecode_dispatch_large_switch reason=Switch detail=bb0 switch has 9 case(s)",
        )
        for row in rows:
            with self.subTest(row=row):
                self.assertEqual(self.verdict(transcript(("a",), outputs={"a": row}))["status"], "pass")
        # The exemption is the exact row shape, never the word.
        result = self.verdict(transcript(("a",), outputs={"a": "[skip] lldb is not available"}))
        self.assertEqual(result["status"], "fail")

    def test_hidden_or_vacuous_outcomes_fail(self):
        cases = {
            "failed": (transcript(("a",), failed=("b",)), {"rc": 101}),
            "empty suite": (transcript(()), {}),
            "below minimum": (transcript(("a",)), {"minimum": 2}),
            "unlisted ignore": (transcript(("a",), ignored=("parked",)), {}),
            "listed ignore that ran": (transcript(("a", "parked")), {"ignored": ("parked",)}),
            "unexpected filter": (transcript(("a",), filtered=1), {}),
            "missing host skip": (transcript(("a",)), {"filtered": 1}),
            "no rollup": (transcript(("a",), rollup=False), {}),
            "two suites": (transcript(("a",)) + transcript(("b",)), {}),
            "nonzero exit": (transcript(("a",)), {"rc": 3}),
        }
        for label, (text, options) in cases.items():
            with self.subTest(label=label):
                result = self.verdict(text, **options)
                self.assertEqual(result["status"], "fail", result)
                self.assertTrue(result["errors"])

    def test_a_skip_exemption_covers_only_its_test_and_prefix(self):
        text = transcript(("a", "b"), outputs={"a": "SKIP t: no authority", "b": "SKIP t: no authority"})
        result = RUNNER.classify_suite(0, text, minimum=1, filtered=0, ignored=[], doc=False,
                                       exemptions={"a": "SKIP t: "})
        self.assertEqual(sorted(result["not_executed"]), ["b"])
        self.assertEqual(result["status"], "fail")
        result = RUNNER.classify_suite(0, transcript(("a",), outputs={"a": "SKIP other: no authority"}),
                                       minimum=1, filtered=0, ignored=[], doc=False, exemptions={"a": "SKIP t: "})
        self.assertEqual(result["status"], "fail")

    def test_listed_ignores_exact_skips_and_doc_ignores_are_accounted(self):
        self.assertEqual(self.verdict(transcript(("a",), ignored=("parked",)), ignored=("parked",))["status"], "pass")
        self.assertEqual(self.verdict(transcript(("a",), filtered=2), filtered=2)["status"], "pass")
        self.assertEqual(self.verdict(transcript(("a",), ignored=("src/lib.rs - f (line 3)",)), doc=True)["status"], "pass")

    def test_matrix_verdict_requires_every_gate_and_every_suite(self):
        green = {"status": "pass"}
        stages = {"coverage_gate": green, "proof_gate": green, "consumer_lane": green}
        base = {"errors": [], "selected": ["x", "y"], "suites": [{"id": "x", **green}, {"id": "y", **green}],
                "stages": stages}
        self.assertEqual(RUNNER.verdict(base, "required", False), "pass")
        self.assertEqual(RUNNER.verdict({**base, "stages": {**stages, "proof_gate": {"status": "fail"}}},
                                        "required", False), "fail")
        self.assertEqual(RUNNER.verdict({**base, "stages": {**stages, "consumer_lane": {"status": "fail"}}},
                                        "required", False), "fail")
        self.assertEqual(RUNNER.verdict({**base, "stages": {}}, "required", True), "partial-pass")
        # A required run that did not run every gate is not green; the
        # downstream-consumer lane (L13-P8) is one of them.
        self.assertEqual(RUNNER.verdict({**base, "stages": {"coverage_gate": green}}, "required", False), "fail")
        self.assertEqual(RUNNER.verdict({**base, "stages": {"coverage_gate": green, "proof_gate": green}},
                                        "required", False), "fail")
        self.assertEqual(RUNNER.verdict({**base, "stages": {}}, "required", False), "fail")
        self.assertEqual(RUNNER.verdict({**base, "suites": base["suites"][:1]}, "required", False), "fail")
        self.assertEqual(RUNNER.verdict({**base, "suites": [{"id": "x", **green}, {"id": "y", "status": "fail"}]},
                                        "required", False), "fail")
        self.assertEqual(RUNNER.verdict(base, "only", False), "partial-pass")
        self.assertEqual(RUNNER.verdict(base, "census", False), "census")
        self.assertEqual(RUNNER.verdict({**base, "errors": ["source changed"]}, "required", False), "fail")

    def test_the_gates_run_their_full_spelling_and_need_its_success_lines(self):
        stages = {stage[0]: stage for stage in RUNNER.GATE_STAGES}
        self.assertEqual(sorted(stages), ["consumer_lane", "coverage_gate", "proof_gate"])
        _, _, command, required = stages["proof_gate"]
        self.assertEqual(list(command), [str(RUNNER.PROOF_GATE), "--test", "full_database_is_formally_verified"])
        self.assertIn("STRICT GATE OK:", required)
        self.assertEqual(list(stages["coverage_gate"][2]), [str(RUNNER.COVERAGE_GATE)])
        # Each success line is one the gate (or the strict test) actually prints.
        sources = (RUNNER.PROOF_GATE.read_text() + RUNNER.COVERAGE_GATE.read_text()
                   + (ROOT / "crates" / "trust-cg-verify" / "tests" / "proof_gate_strict.rs").read_text()
                   + RUNNER.CONSUMER_LANE.read_text())
        for _, _, _, lines in RUNNER.GATE_STAGES:
            for line in lines:
                self.assertIn(line.rstrip("."), sources)
        smoke = ("[proof-gate] package=trust-cg-verify test=proof_gate_strict::representative_arithmetic\n"
                 "proof gate OK (SMOKE): 6 representative arithmetic obligations formally Verified\n")
        full = ("STRICT GATE OK: 2503/2503 formally Verified, 0 soundness failures\n"
                "proof gate OK: full-database zero-soundness/no-statistical-fallback floor passed.\n")
        self.assertEqual(RUNNER.stage_verdict("proof-gate", 0, smoke, required)["status"], "fail")
        self.assertEqual(RUNNER.stage_verdict("proof-gate", 0, full, required)["status"], "pass")
        failed = RUNNER.stage_verdict("proof-gate", 1, "incomplete self-check-rejected\n", required)
        self.assertEqual((failed["status"], failed["residuals"]),
                         ("fail", ["the resolved AY rejected its own proof self-check"]))
        # The whole stage path: a zero exit that printed only the smoke summary fails.
        with tempfile.TemporaryDirectory(prefix="tcg-full-matrix-gate-") as temporary:
            fake = ("proof_gate", "proof-gate", (sys.executable, "-c", f"print({smoke!r})"), required)
            result = RUNNER.run_gate(RUNNER.Supervisor(), fake, Path(temporary), 30, {})
            self.assertEqual((result["returncode"], result["status"]), (0, "fail"), result)

    def test_the_consumer_lane_stage_runs_the_complete_lane_into_its_own_directory(self):
        stage = {stage[0]: stage for stage in RUNNER.GATE_STAGES}["consumer_lane"]
        self.assertEqual(stage[3], ("Darwin consumer lane: PASS",))
        output = Path("/fixture/matrix")
        command = RUNNER.stage_command(stage, output, jobs=3, require_clean=True, offline=False)
        self.assertEqual(command, [sys.executable, str(RUNNER.CONSUMER_LANE), "--out",
                                   str(output / "stage--consumer-lane"), "--jobs", "3", "--require-clean",
                                   "--fetch-consumers"])
        # Never --only (which can only partial-pass), and offline means no fetch.
        self.assertNotIn("--only", command)
        offline = RUNNER.stage_command(stage, output, offline=True)
        self.assertEqual(offline[-1], "--offline")
        self.assertNotIn("--fetch-consumers", offline)
        # The other gates keep their exact spelling.
        proof = {stage[0]: stage for stage in RUNNER.GATE_STAGES}["proof_gate"]
        self.assertEqual(RUNNER.stage_command(proof, output, jobs=3, require_clean=True),
                         [str(RUNNER.PROOF_GATE), "--test", "full_database_is_formally_verified"])
        self.assertEqual(RUNNER.STAGE_MINIMUM_TIMEOUT_SECONDS["consumer_lane"], 14400.0)
        # A lane that printed only a partial pass is a failed stage.
        partial = "Darwin consumer lane: PARTIAL-PASS (selected steps only; not the required lane) (x)\n"
        self.assertEqual(RUNNER.stage_verdict("consumer-lane", 0, partial, stage[3])["status"], "fail")
        self.assertEqual(RUNNER.stage_verdict("consumer-lane", 0, "Darwin consumer lane: PASS (x)\n",
                                              stage[3])["status"], "pass")

    def test_strict_gate_failures_name_host_residuals(self):
        text = "AY + Clean proof toolchain unavailable for floor: clean lacks carcara-verify\n"
        self.assertEqual(RUNNER.host_residuals(text), [
            "AY + Clean proof toolchain unavailable on this host", "the resolved Clean checker lacks carcara-verify",
        ])

    def test_supervised_process_is_bounded_and_logged(self):
        with tempfile.TemporaryDirectory(prefix="tcg-full-matrix-run-") as temporary:
            directory = Path(temporary)
            supervisor = RUNNER.Supervisor()
            done = supervisor.run([sys.executable, "-c", "print('hello')"], directory / "ok.log", 30, {})
            self.assertEqual(done["returncode"], 0)
            self.assertIn("hello", (directory / "ok.log").read_text())
            slow = supervisor.run([sys.executable, "-c", "import time; time.sleep(30)"], directory / "slow.log", 0.2, {})
            self.assertEqual(slow["returncode"], 124)
            with self.assertRaises(FileExistsError):
                supervisor.run([sys.executable, "-c", "pass"], directory / "ok.log", 30, {})

    def test_the_verify_ay_cache_is_admitted_only_in_its_exact_shape(self):
        with tempfile.TemporaryDirectory(prefix="tcg-full-matrix-cache-") as temporary:
            directory = Path(temporary)
            cache = directory / "trust-cg-verify-ay-exec-uid501"
            copy = cache / "trust-cg" / "ay-exec" / ("a" * 64)
            copy.mkdir(parents=True)
            (copy / "ay").write_bytes(b"ay")
            (copy / "ay.first-start").write_text("stamp")
            self.assertTrue(RUNNER.is_verify_ay_cache(cache))
            result = {"errors": [], "status": "pass"}
            RUNNER.check_leftovers(result, directory)
            self.assertEqual((result["status"], result["temporary_tool_caches"]), ("pass", [cache.name]))
            self.assertFalse(directory.exists())
        with tempfile.TemporaryDirectory(prefix="tcg-full-matrix-cache-") as temporary:
            directory = Path(temporary)
            cache = directory / "trust-cg-verify-ay-exec-uid501"
            copy = cache / "trust-cg" / "ay-exec" / ("a" * 64)
            copy.mkdir(parents=True)
            (copy / "ay").write_bytes(b"ay")
            (copy / "output.txt").write_text("not the cache")
            self.assertFalse(RUNNER.is_verify_ay_cache(cache))
            result = {"errors": [], "status": "pass"}
            RUNNER.check_leftovers(result, directory)
            self.assertEqual(result["status"], "fail")
            self.assertEqual(result["temporary_leftovers"], [cache.name])

    def test_archive_stores_the_report_and_cited_logs_in_a_verifiable_inventory(self):
        evidence = load("_test_check_evidence_archive", ROOT / "scripts" / "check_evidence_archive.py")
        with tempfile.TemporaryDirectory(prefix="tcg-full-matrix-archive-") as temporary:
            base = Path(temporary)
            run = base / "run"
            run.mkdir()
            for name, text in (("stage--proof-gate.log", "gate"), ("build--p.log", "build"),
                               ("p--test--red.log", "red"), ("p--test--green.log", "green"),
                               ("stage--consumer-lane.log", "lane"), ("stage--consumer-lane/report.json", "{}")):
                (run / name).parent.mkdir(exist_ok=True)
                (run / name).write_text(text)
            report = {
                "schema": RUNNER.SCHEMA, "status": "fail", "provenance": {"source_sha": "a" * 40},
                "stages": {"proof_gate": {"log": "stage--proof-gate.log", "status": "fail"},
                           "consumer_lane": {"log": "stage--consumer-lane.log", "status": "pass",
                                             "stage_report": "stage--consumer-lane/report.json"}},
                "builds": [{"log": "build--p.log", "status": "pass"}],
                "suites": [{"id": "p/test/red", "status": "fail", "log": "p--test--red.log", "campaigns": []},
                           {"id": "p/test/green", "status": "pass", "log": "p--test--green.log", "campaigns": []}],
            }
            (run / "report.json").write_text(__import__("json").dumps(report))
            destination = base / "record"
            destination.mkdir()
            with self.assertRaises(ValueError):
                RUNNER.archive(run, destination)
            (destination / "README.md").write_text("# Record\n")
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(RUNNER.archive(run, destination), 0)
                self.assertEqual(RUNNER.archive(run, destination / "triage", nested=True), 0)
            stored = sorted(path.relative_to(destination).as_posix() for path in destination.rglob("*") if path.is_file())
            self.assertIn("logs/p--test--red.log.gz", stored)
            # The consumer lane's own report is stored beside its stage log.
            self.assertIn("logs/stage--consumer-lane/report.json.gz", stored)
            self.assertNotIn("logs/p--test--green.log.gz", stored)
            self.assertIn("triage/inventory.json", stored)
            self.assertEqual(evidence.archive_errors(destination), [])
            with self.assertRaises(ValueError):
                RUNNER.archive(run, destination)

    def test_children_never_inherit_campaign_or_capture_controls(self):
        environment = RUNNER.child_environment({
            "PATH": "/usr/bin", "RUST_TEST_NOCAPTURE": "1", "TRUST_CG_RUN_FORMAL_PROOF_TESTS": "1",
            "TRUST_CG_AY_TIMEOUT_MS": "5", "TRUST_CG_KEEP_LINKRUN": "1",
            "PROOF_GATE_FILTER": "representative_arithmetic_is_formally_verified", "COVERAGE_GATE_FEATURES": "x",
        })
        for name in ("RUST_TEST_NOCAPTURE", "TRUST_CG_RUN_FORMAL_PROOF_TESTS", "TRUST_CG_AY_TIMEOUT_MS",
                     "TRUST_CG_KEEP_LINKRUN", "PROOF_GATE_FILTER", "COVERAGE_GATE_FEATURES"):
            self.assertNotIn(name, environment)
        self.assertEqual(environment["RUST_MIN_STACK"], "67108864")

    def test_campaign_environment_names_both_proof_tools_or_refuses(self):
        tools = {"ay": {"resolved": "/pkg/bin/ay", "sha256": "a" * 64},
                 "clean": {"resolved": "/pkg/bin/clean", "sha256": "c" * 64}}
        variables, problems = RUNNER.campaign_environment("external-cert", tools)
        self.assertEqual(problems, [])
        self.assertEqual(variables["AY_SOLVER_PATH"], "/pkg/bin/ay")
        self.assertEqual(variables["TCG_EXTERNAL_CLEAN_CHECKER"], "/pkg/bin/clean")
        self.assertEqual(variables["TCG_JIT_REQUEST_CACHE_AY_SHA256"], "a" * 64)
        self.assertEqual(variables["TCG_JIT_REQUEST_CACHE_CLEAN"], "/pkg/bin/clean")
        _, problems = RUNNER.campaign_environment("external-cert", {"ay": {"resolved": None}})
        self.assertEqual(problems, ["ay: not resolved", "clean: not resolved"])
        self.assertEqual(RUNNER.campaign_environment("formal", {}), ({"TRUST_CG_RUN_FORMAL_PROOF_TESTS": "1"}, []))


if __name__ == "__main__":
    unittest.main()
