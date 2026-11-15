"""The declared leg inventory is the single source of truth, and runs obey it.

Static half: every record() call site in scripts/soundness_check.sh names a leg
of `soundness_leg_inventory` (published by --list-json) and every declared leg
is named by some call site; every run_cargo_gate line is a declared leg with
the right host class.

Executed half: the production script runs in a throwaway constellation
(scripts/tests/soundness_fixture.py) and the rows it records are compared with
the inventory: exactly the declared set in --attest mode, fail-fast at the first
failing leg or failed preflight, --keep-going for a census, and the attest-mode
refusal of leg-weakening settings.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import soundness_fixture as fixture  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "soundness_check.sh"
SOURCE = SCRIPT.read_text()
INVENTORY = fixture.load_inventory(ROOT)
IDS = {leg["id"]: leg["class"] for leg in INVENTORY}
ATTEST_ONLY = re.compile(r"^(attest: |post-run: |inventory: |preflight: leg-weakening settings$|"
                         r"preflight: host trust boundary$)")


def pattern(name: str) -> re.Pattern:
    """A record() name with shell expansions, as a regex over leg ids."""
    parts = re.split(r"(\$\{[^}]+\}|\$[A-Za-z_][A-Za-z0-9_]*)", name)
    return re.compile("".join(".+" if part.startswith("$") else re.escape(part) for part in parts) + r"\Z")


def expected(scope: str = "full", native: bool = False) -> set[str]:
    wanted = {"per-run"}
    if scope == "full":
        wanted |= {"host-independent", "x86_64-native" if native else "dispatch"}
    elif scope == "portable":
        wanted.add("host-independent")
    else:
        wanted.add("x86_64-native")
    return {leg for leg, cls in IDS.items() if cls in wanted}


def recorded(result) -> list[str]:
    logdir = fixture.logdir_of(result)
    assert logdir is not None, result.stdout[-2000:]
    return [line.split("\t", 1)[0] for line in (logdir / "legs.tsv").read_text().splitlines() if line]


class StaticInventoryTests(unittest.TestCase):
    def call_site_names(self) -> list[str]:
        names = re.findall(r'\brecord\s+"([^"]+)"', SOURCE)
        names += re.findall(r'check_repo_worktree_clean\s+"([^"]+)"', SOURCE)
        names += re.findall(r'^\s*local name="([^"]+)"', SOURCE, re.M)
        names += re.findall(r'^\s*inventory_leg="([^"]+)"', SOURCE, re.M)
        # Pure-variable sites are resolved by the definitions collected above.
        return [name for name in names if name not in ("$gate_name", "$name", "$1", "$label", "$inventory_leg")]

    def cargo_gate_names(self) -> list[tuple[str, str]]:
        """(leg id, class) of every literal run_cargo_gate line."""
        legs = []
        for line in SOURCE.splitlines():
            words = line.split()
            if not words or words[0] != "run_cargo_gate" or '"${gate%%|*}"' in line or '"$gate"' in line \
                    or '"$pkg"' in line:
                continue
            package, target = words[2], words[3]
            host_class = words[6] if len(words) > 6 else "host-independent"
            selector = words[5] if len(words) > 5 else "integration"
            leg = (f"{package} --lib {target}" if selector == "lib" else
                   target if package == "trust-cg-verify" else f"{package} --test {target}")
            if len(words) > 7:
                leg += f" --features {words[7]}"
            legs.append((leg, host_class))
        return legs

    @staticmethod
    def loop_cargo_gate_names(source: str = SOURCE) -> list[str]:
        """Leg ids run_trust_cg_cargo_gates records through its array loops.

        The literal-line scan above skips the loop lines, so these are named
        here exactly as run_cargo_gate records them: `<package> --lib
        <filter>` for TRUST_CG_LIB_GATES, `<package> --test <target>` for
        TRUST_CG_PACKAGE_INTEGRATION_GATES (a package other than
        trust-cg-verify, whose integration targets keep their bare names in
        TRUST_CG_GATES).
        """
        legs = []
        for array, selector in (("TRUST_CG_LIB_GATES", "--lib"),
                                ("TRUST_CG_PACKAGE_INTEGRATION_GATES", "--test")):
            for item in (line.strip("'") for line in fixture.bash_array(source, array)):
                package, target = item.split("|", 1)
                legs.append(f"{package} {selector} {target}")
        return legs

    @staticmethod
    def undeclared_loop_cargo_gates(source: str, ids: dict) -> list[str]:
        return [leg for leg in StaticInventoryTests.loop_cargo_gate_names(source)
                if ids.get(leg) != "host-independent"]

    def test_every_loop_driven_cargo_gate_is_a_declared_host_independent_leg(self):
        # A run records every loop-driven Cargo gate (on the host-independent
        # class); a gate the inventory does not declare fails every attested
        # run's inventory leg, so it must be refused here, statically.
        loop = self.loop_cargo_gate_names()
        self.assertTrue(any(" --test " in leg for leg in loop), "no package integration gate was read")
        self.assertTrue(any(" --lib " in leg for leg in loop), "no library gate was read")
        self.assertEqual(self.undeclared_loop_cargo_gates(SOURCE, IDS), [])
        for item in (line.strip("'") for line in fixture.bash_array(SOURCE, "TRUST_CG_PACKAGE_INTEGRATION_GATES")):
            with self.subTest(item=item):
                self.assertNotEqual(item.split("|", 1)[0], "trust-cg-verify",
                                    "trust-cg-verify integration targets belong in TRUST_CG_GATES")

    def test_an_undeclared_loop_driven_cargo_gate_is_caught(self):
        # Negative twins of the check above: a new package gate the inventory
        # does not declare, a declared one filed under the wrong class, and a
        # library gate spelled as an integration target are each reported.
        added = SOURCE.replace("\nTRUST_CG_PACKAGE_INTEGRATION_GATES=(\n",
                               "\nTRUST_CG_PACKAGE_INTEGRATION_GATES=(\n  'trust-cg-codegen|not_a_declared_gate'\n", 1)
        self.assertNotEqual(added, SOURCE)
        self.assertEqual(self.undeclared_loop_cargo_gates(added, IDS),
                         ["trust-cg-codegen --test not_a_declared_gate"])
        integration = [leg for leg in self.loop_cargo_gate_names() if " --test " in leg]
        self.assertTrue(integration)
        misclassed = dict(IDS, **{integration[0]: "x86_64-native"})
        self.assertEqual(self.undeclared_loop_cargo_gates(SOURCE, misclassed), [integration[0]])
        dropped = {leg: cls for leg, cls in IDS.items() if leg != integration[-1]}
        self.assertEqual(self.undeclared_loop_cargo_gates(SOURCE, dropped), [integration[-1]])
        library = next(leg for leg in self.loop_cargo_gate_names() if " --lib " in leg)
        as_test = {leg if leg != library else library.replace(" --lib ", " --test ", 1): cls
                   for leg, cls in IDS.items()}
        self.assertEqual(self.undeclared_loop_cargo_gates(SOURCE, as_test), [library])

    def test_inventory_is_well_formed(self):
        self.assertEqual(len(IDS), len(INVENTORY), "duplicate leg ids")
        self.assertEqual({leg["class"] for leg in INVENTORY},
                         {"per-run", "host-independent", "x86_64-native", "dispatch"})
        for gate in fixture.bash_array(SOURCE, "TRUST_CG_GATES"):
            self.assertIn(gate, IDS)

    def test_every_record_site_names_a_declared_leg(self):
        for name in self.call_site_names():
            with self.subTest(name=name):
                self.assertTrue(any(pattern(name).match(leg) for leg in IDS),
                                f"record() name {name!r} matches no declared leg")

    def test_every_declared_leg_is_recorded_by_some_site(self):
        patterns = [pattern(name) for name in self.call_site_names()]
        cargo = {leg for leg, _ in self.cargo_gate_names()}
        loop = set(fixture.bash_array(SOURCE, "TRUST_CG_GATES"))
        loop |= set(self.loop_cargo_gate_names())
        for leg in IDS:
            with self.subTest(leg=leg):
                self.assertTrue(leg in cargo or leg in loop or any(p.match(leg) for p in patterns),
                                f"declared leg {leg!r} is recorded by no call site")

    def test_every_cargo_gate_line_is_declared_with_its_class(self):
        lines = self.cargo_gate_names()
        self.assertTrue(lines)
        for leg, host_class in lines:
            with self.subTest(leg=leg):
                self.assertIn(leg, IDS)
                self.assertEqual(IDS[leg], host_class)

    def test_x86_native_legs_are_exactly_the_silicon_legs(self):
        native = {leg for leg, cls in IDS.items() if cls == "x86_64-native"}
        self.assertEqual(native, {
            "preflight: native x86-64 host", "x86_sse_lane_gate",
            "trust-cg-codegen --test e2e_x86_64_callee_saved",
            "trust-cg-codegen --test e2e_x86_64_calling_conv",
            "trust-cg-codegen --test e2e_x86_64_swiftcc",
        })
        self.assertEqual(fixture.bash_array(SOURCE, "TRUST_CG_X86_NATIVE_GATES"), ["x86_sse_lane_gate"])
        self.assertEqual({leg for leg, cls in IDS.items() if cls == "dispatch"},
                         {"preflight: x86-64 executor reachable", "x86_64-native: remote record"})

    def test_declared_refinement_guards_have_required_feature_enabled_legs(self):
        for leg in (
            "trust-cg-lower --lib lattice_guard::tests:: --features lattice-guard-elision",
            "trust-cg-codegen --test a64_lattice_guard_elision_differential --features lattice-guard-elision",
        ):
            self.assertEqual(IDS[leg], "host-independent")
            self.assertIn((leg, "host-independent"), self.cargo_gate_names())

    def test_refinement_representation_has_required_independent_legs(self):
        for leg in (
            "trust-cg-lower --test refine_erasure_hazards",
            "trust-cg-codegen --test a64_refine_byte_invariance",
        ):
            self.assertEqual(IDS[leg], "host-independent")
            self.assertIn((leg, "host-independent"), self.cargo_gate_names())

    def test_list_json_is_what_the_attestation_tool_reads(self):
        result = subprocess.run(["bash", str(SCRIPT), "--list-json"], capture_output=True, text=True, check=True)
        sys.path.insert(0, str(ROOT / "scripts"))
        import soundness_attestation as sa
        inventory = sa.parse_inventory(result.stdout)
        self.assertEqual([leg["id"] for leg in inventory["legs"]], list(IDS))


class ExecutedInventoryTests(unittest.TestCase):
    def setUp(self):
        self.temporary = fixture.FixtureDirectory("leg-inventory-")
        self.addCleanup(self.temporary.cleanup)
        self.world = fixture.Constellation(Path(self.temporary.name))

    def local_records(self) -> str:
        return fixture.git(self.world.cg, "for-each-ref", "refs/attest/soundness/*/aarch64-*", "refs/attest/soundness/*/arm64-*")

    def cargo_tests(self) -> list[str]:
        return [line for line in self.world.workloads() if line.startswith("targo --unverified test")]

    def test_attested_run_records_exactly_the_declared_inventory(self):
        result = self.world.run_gate("--attest")
        self.assertEqual(result.returncode, 0, result.stdout[-3000:])
        # Every Cargo leg ran through the Trust package's explicit unverified lane
        # (the workload filter below is not vacuous).
        self.assertTrue([line for line in self.cargo_tests()
                         if line.endswith("--locked -p trust-cg-verify --test proof_gate_strict -- --show-output")])
        self.assertFalse([line for line in self.world.workloads() if line.startswith("cargo ")])
        for args in (
            "--locked -p trust-cg-lower --lib lattice_guard::tests:: --features lattice-guard-elision -- --show-output --test-threads=1",
            "--locked -p trust-cg-codegen --test a64_lattice_guard_elision_differential --features lattice-guard-elision -- --show-output",
            "--locked -p trust-cg-lower --test refine_erasure_hazards -- --show-output",
            "--locked -p trust-cg-codegen --test a64_refine_byte_invariance -- --show-output",
        ):
            self.assertEqual(sum(line.endswith(args) for line in self.cargo_tests()), 1)
        rows = recorded(result)
        self.assertEqual(len(rows), len(set(rows)))
        self.assertEqual(set(rows), expected())
        self.assertIn("inventory: executed legs match the declared inventory", result.stdout)

    def test_a_portable_run_records_exactly_the_portable_inventory(self):
        """--scope portable: every per-run and host-independent leg, no x86-64-native
        leg, no dispatch row and no ssh to an executor, even with one configured."""
        result = self.world.run_gate("--attest", "--scope", "portable")
        self.assertEqual(result.returncode, 0, result.stdout[-3000:])
        rows = recorded(result)
        self.assertEqual(len(rows), len(set(rows)))
        self.assertEqual(set(rows), expected("portable"))
        self.assertFalse({row for row in rows if IDS[row] in ("x86_64-native", "dispatch")})
        self.assertIn("exactly the portable inventory for this host", result.stdout)
        self.assertFalse([line for line in self.world.workloads() if line.startswith("ssh ")])
        self.assertNotIn("TRUST_CG_REQUIRE_X86_SILICON", (fixture.logdir_of(result) / "environment.json").read_text())

    def test_scope_arguments_are_checked(self):
        for args, fragment in ((("--scope",), "--scope takes exactly"), (("--scope", "x86"), "--scope takes exactly"),
                               (("--attest", "--scope", "portable", "--host-legs", "x86_64-native"), "two scopes"),
                               (("--list-json", "--scope", "portable"), "cannot be combined")):
            with self.subTest(args=args):
                result = self.world.run_gate(*args)
                self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                self.assertIn(fragment, result.stderr)

    def test_census_run_records_the_inventory_without_attest_rows(self):
        result = self.world.run_gate()
        self.assertEqual(result.returncode, 0, result.stdout[-3000:])
        self.assertEqual(set(recorded(result)), {leg for leg in expected() if not ATTEST_ONLY.match(leg)})
        self.assertNotIn("Attestation record", result.stdout)
        # A census writes no local record. The dispatched x86-64 run of the same
        # committed tree still imports that host's own (valid) record.
        self.assertEqual(self.local_records(), "")

    def certificate_runs(self) -> list[str]:
        return [line for line in self.world.workloads() if line.startswith("check_x86_icmp_certificates")]

    def test_certificate_leg_runs_against_the_pinned_ay_worktree(self):
        result = self.world.run_gate("--attest")
        self.assertEqual(result.returncode, 0, result.stdout[-3000:])
        runs = self.certificate_runs()
        self.assertEqual(len(runs), 1, runs)
        pinned = Path(self.temporary.name, "deps", f"ay-{self.world.ay_rev}")
        self.assertIn(f"--ay-source {pinned} ", runs[0] + " ")
        self.assertNotIn("--skip-missing-toolchain", runs[0])
        self.assertIn("[PASS] x86 icmp certificates (pinned AY + the rule's Clean)", result.stdout)

    def test_certificate_leg_fails_on_a_finding_and_on_a_missing_input(self):
        for extra in ({"FIXTURE_FAIL": "x86_icmp_certificates"}, {"FIXTURE_X86_ICMP_MISSING": "1"}):
            with self.subTest(extra=extra):
                result = self.world.run_gate(**extra)
                self.assertEqual(result.returncode, 1, result.stdout[-3000:])
                self.assertIn("[FAIL] x86 icmp certificates (pinned AY + the rule's Clean)", result.stdout)

    def test_certificate_skip_is_explicit_loud_and_never_attested(self):
        # Census: the explicit skip turns ONLY a missing input into a SKIP, and
        # a SKIP leaves the run incomplete and nonzero.
        result = self.world.run_gate(SOUNDNESS_SKIP_X86_ICMP_CERTIFICATES="1", FIXTURE_X86_ICMP_MISSING="1")
        self.assertEqual(result.returncode, 1, result.stdout[-3000:])
        self.assertIn("[SKIP] x86 icmp certificates (pinned AY + the rule's Clean)", result.stdout)
        self.assertIn("explicitly skipped (SOUNDNESS_SKIP_X86_ICMP_CERTIFICATES)", result.stdout)
        self.assertIn("--skip-missing-toolchain", self.certificate_runs()[0])
        # A finding is not a missing input: the skip does not cover it.
        result = self.world.run_gate(SOUNDNESS_SKIP_X86_ICMP_CERTIFICATES="1", FIXTURE_FAIL="x86_icmp_certificates")
        self.assertIn("[FAIL] x86 icmp certificates (pinned AY + the rule's Clean)", result.stdout)
        # --attest refuses the skip variable before any leg runs.
        result = self.world.run_gate("--attest", SOUNDNESS_SKIP_X86_ICMP_CERTIFICATES="1")
        self.assertEqual(result.returncode, 1, result.stdout[-3000:])
        self.assertIn("STOPPED at the first failure (preflight)", result.stdout)
        self.assertIn("SOUNDNESS_SKIP_X86_ICMP_CERTIFICATES", result.stdout)
        self.assertEqual(self.certificate_runs(), [])

    def test_lean_axiom_audit_runs_and_fails_closed(self):
        """The formal/lean environment audit runs after the source counts, and its
        failure (a sorryAx or project-axiom dependency) fails the leg."""
        result = self.world.run_gate()
        self.assertEqual(result.returncode, 0, result.stdout[-3000:])
        self.assertIn("lake env lean scripts/AxiomAudit.lean", self.world.workloads())
        self.assertIn("[PASS] formal/lean axiom audit (no sorryAx, no project axiom)", result.stdout)
        result = self.world.run_gate(FIXTURE_FAIL="lean-axiom-audit")
        self.assertEqual(result.returncode, 1, result.stdout[-3000:])
        self.assertIn("[FAIL] formal/lean axiom audit (no sorryAx, no project axiom)", result.stdout)

    def test_attest_stops_at_the_first_failing_leg(self):
        result = self.world.run_gate("--attest", FIXTURE_FAIL="meta_theorems")
        self.assertEqual(result.returncode, 1, result.stdout[-3000:])
        self.assertIn("STOPPED at the first failure (meta_theorems)", result.stdout)
        tests = self.cargo_tests()
        self.assertTrue(any("--test meta_theorems" in line for line in tests), tests)
        self.assertFalse(any("--test mutation_catalog" in line for line in tests), tests)
        self.assertFalse(any(line.startswith("targo --unverified build") for line in self.world.workloads()))
        self.assertEqual(fixture.git(self.world.cg, "for-each-ref", "refs/attest/"), "")

    def test_a_stop_after_the_remote_record_arrived_publishes_nothing(self):
        # The failing leg waits until the dispatched x86-64 record is staged,
        # so this stop provably comes after the import: the staged record is
        # dropped, and no ref under refs/attest/ names it.
        result = self.world.run_gate("--attest", FIXTURE_FAIL="meta_theorems", FIXTURE_FAIL_AFTER_STAGED="1")
        self.assertEqual(result.returncode, 1, result.stdout[-3000:])
        self.assertIn("STOPPED at the first failure (meta_theorems)", result.stdout)
        self.assertIn("fixture: failing after the x86-64 record was staged", self.world.workloads())
        self.assertNotIn("fixture: the x86-64 record was never staged", self.world.workloads())
        self.assertEqual(fixture.git(self.world.cg, "for-each-ref", "refs/attest/"), "")
        self.assertEqual(fixture.git(self.world.cg, "for-each-ref", "refs/soundness/"), "")

    def test_keep_going_runs_every_leg_and_writes_nothing(self):
        result = self.world.run_gate("--attest", "--keep-going", FIXTURE_FAIL="meta_theorems")
        self.assertEqual(result.returncode, 1, result.stdout[-3000:])
        self.assertTrue(any("--test mutation_catalog" in line for line in self.cargo_tests()))
        self.assertIn("no attestation record", result.stdout)
        # Not even the x86-64 record the dispatch brought back is published.
        self.assertIn("[PASS] x86_64-native: remote record", result.stdout)
        self.assertEqual(fixture.git(self.world.cg, "for-each-ref", "refs/attest/"), "")
        self.assertEqual(fixture.git(self.world.cg, "for-each-ref", "refs/soundness/"), "")

    def test_missing_executor_census_retains_reason_without_connecting(self):
        result = self.world.run_gate("--keep-going", SOUNDNESS_X86_HOST="")
        self.assertEqual(result.returncode, 1, result.stdout[-3000:])
        logdir = fixture.logdir_of(result)
        self.assertIsNotNone(logdir)
        diagnostic = (logdir / "remote" / "run.log").read_text()
        self.assertIn("SOUNDNESS_X86_HOST is unset", diagnostic)
        self.assertIn("no remote connection was attempted", diagnostic)
        self.assertIn("x86_64-native: remote record", result.stdout)
        self.assertIn("SOUNDNESS_X86_HOST is unset", result.stdout)
        self.assertTrue(any("--test mutation_catalog" in line for line in self.cargo_tests()))
        self.assertFalse(any(line.startswith("ssh ") for line in self.world.workloads()))
        self.assertEqual(fixture.git(self.world.cg, "for-each-ref", "refs/attest/"), "")
        self.assertEqual(fixture.git(self.world.cg, "for-each-ref", "refs/soundness/"), "")

    def test_failed_preflight_stops_before_any_leg(self):
        for name, extra, fragment in (
            ("no x86 executor", {"SOUNDNESS_X86_HOST": ""}, "SOUNDNESS_X86_HOST is unset"),
            ("unreachable executor", {"FIXTURE_SSH_UNREACHABLE": "1"}, "x86-64 executor reachable"),
            ("fuzz below its floor", {"WASM_CFG_FUZZ_FUNCS": "10"}, "WASM_CFG_FUZZ_FUNCS"),
            ("unknown test control", {"TCG_NO_DECODE_CHECK": "1"}, "TCG_NO_DECODE_CHECK"),
            ("explicit Clean checkout", {"CLEAN_DIR": str(Path(self.temporary.name, "clean"))}, "CLEAN_DIR"),
            ("caller vt tables", {"ISLAND_VT_TABLES": "/dev/null"}, "ISLAND_VT_TABLES"),
            ("cargo runner", {"CARGO_TARGET_AARCH64_APPLE_DARWIN_RUNNER": "true"}, "RUNNER"),
            ("campaign disabled", {"TRUST_CG_RUN_FORMAL_PROOF_TESTS": "0"}, "TRUST_CG_RUN_FORMAL_PROOF_TESTS"),
            # The environment allowlist: leg-affecting caller variables are refused.
            ("python path", {"PYTHONPATH": "/elsewhere"}, "PYTHONPATH"),
            ("node options", {"NODE_OPTIONS": "--require /elsewhere/x.js"}, "NODE_OPTIONS"),
            ("linux preload", {"LD_PRELOAD": "/elsewhere/x.so"}, "LD_PRELOAD"),
            ("lean path", {"LEAN_PATH": "/elsewhere"}, "LEAN_PATH"),
            ("elan toolchain", {"ELAN_TOOLCHAIN": "leanprover/lean4:v4.0.0"}, "ELAN_TOOLCHAIN"),
            ("rustc wrapper", {"RUSTC_WRAPPER": "/elsewhere/wrap"}, "RUSTC_WRAPPER"),
            ("cargo config env", {"CARGO_BUILD_TARGET": "x86_64-apple-darwin"}, "CARGO_BUILD_TARGET"),
            ("bash startup", {"BASH_ENV": "/elsewhere/rc"}, "BASH_ENV"),
            ("forged scrub marker", {"SOUNDNESS_ENV_SCRUBBED": "1", "SOME_UNLISTED_VARIABLE": "x"},
             "SOME_UNLISTED_VARIABLE: not on the environment allowlist"),
        ):
            with self.subTest(name):
                result = self.world.run_gate("--attest", **extra)
                self.assertEqual(result.returncode, 1, result.stdout[-3000:])
                self.assertIn("STOPPED at the first failure (preflight)", result.stdout)
                self.assertIn(fragment, result.stdout)
                self.assertEqual(self.cargo_tests(), [])

    def test_unlisted_variables_never_reach_the_legs(self):
        # An unknown variable is dropped by the re-execution (its name is
        # recorded); the legs see only the allowlist.
        result = self.world.run_gate("--attest", "--preflight-only", SOME_UNLISTED_VARIABLE="x")
        self.assertEqual(result.returncode, 0, result.stdout[-3000:])
        environment = json.loads((fixture.logdir_of(result) / "environment.json").read_text())
        self.assertEqual(environment["policy"], "allowlist-v1")
        self.assertIn("SOME_UNLISTED_VARIABLE", environment["dropped"])
        self.assertNotIn("SOME_UNLISTED_VARIABLE", [row["name"] for row in environment["settings"]])
        self.assertEqual(environment["refused"], [])

    def test_an_uncommitted_cargo_config_above_the_checkout_is_refused(self):
        config = self.world.base / ".cargo" / "config.toml"
        config.parent.mkdir()
        config.write_text('[target.aarch64-apple-darwin]\nrunner = "true"\n')
        try:
            result = self.world.run_gate("--attest", "--preflight-only")
        finally:
            shutil.rmtree(config.parent)
        self.assertEqual(result.returncode, 1, result.stdout[-3000:])
        self.assertIn(f"cargo config {config.resolve()}", result.stdout)

    def test_census_reports_but_does_not_refuse_weak_settings(self):
        result = self.world.run_gate(WASM_CFG_FUZZ_FUNCS="10")
        self.assertEqual(result.returncode, 0, result.stdout[-3000:])
        self.assertIn("census run; --attest would refuse", result.stdout)

    def test_dirty_candidate_cannot_be_attested(self):
        (self.world.cg / "untracked-change").write_text("dirty\n")
        result = self.world.run_gate("--attest")
        self.assertEqual(result.returncode, 1, result.stdout[-3000:])
        self.assertIn("[FAIL] attest: trust-cg worktree clean", result.stdout)
        self.assertEqual(self.cargo_tests(), [])

    def test_a_failing_remote_run_fails_the_attestation(self):
        result = self.world.run_gate("--attest", FIXTURE_X86_GATE_FAIL="1")
        self.assertEqual(result.returncode, 1, result.stdout[-3000:])
        self.assertIn("[FAIL] x86_64-native: remote record", result.stdout)
        self.assertEqual(fixture.git(self.world.cg, "for-each-ref", "refs/attest/"), "")

    def test_preflight_only_runs_no_leg_and_writes_nothing(self):
        result = self.world.run_gate("--attest", "--preflight-only")
        self.assertEqual(result.returncode, 0, result.stdout[-3000:])
        self.assertIn("PREFLIGHT GREEN", result.stdout)
        self.assertEqual(self.cargo_tests(), [])
        self.assertEqual(fixture.git(self.world.cg, "for-each-ref", "refs/attest/"), "")


if __name__ == "__main__":
    unittest.main()
