"""The L14-P7 larger-corpus harness (benchmarks/real-corpus/run.py).

These tests measure nothing. They keep the corpus versioned (every in-repo
row's source still has the manifest's digest), check the manifest's shape and
the selection rules it states, and pin the harness's intent-to-treat
bookkeeping: outcome classification, the warmup/retry protocol, the
exit-status oracle, the object rule for libraries, fail-closed aggregates,
eligibility, feature resolution, `/usr/bin/time` parsing and the crate and
sysroot input checks. A fake toolchain (`FakeToolchain`) stands in for trustc
and for the compiled programs where a row is exercised end to end.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("trust_cg_real_corpus", ROOT / "benchmarks/real-corpus/run.py")
RC = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RC)


def sample(rc=0, timed_out=False, stderr="", wall=1.0, **extra):
    record = {"returncode": rc, "timed_out": timed_out, "wall_s": wall, "user_s": 0.5,
              "sys_s": 0.1, "maxrss_bytes": 100, "instructions": 1000, "cycles": 2000,
              "footprint_bytes": 50, "stderr": stderr, "stdout_bytes": 0}
    record.update(extra)
    return record


def macho_object(text_bytes):
    """A relocatable arm64 Mach-O object with one `__TEXT,__text` section."""
    header = struct.pack("<IiiIIIII", 0xFEEDFACF, 0x0100000C, 0, 1, 1, 152, 0, 0)
    segment = struct.pack("<II16sQQQQiiII", 0x19, 152, b"", 0, text_bytes, 184, text_bytes, 7, 7, 1, 0)
    section = struct.pack("<16s16sQQIIIIIIII", b"__text", b"__TEXT", 0, text_bytes, 184, 2, 0, 0,
                          0x80000400, 0, 0, 0)
    return header + segment + section + b"\x00" * text_bytes


def ok(code=None, stderr=""):
    """A compile that exits 0; a library compile writes an object with `code`
    bytes of code, or none at all when `code` is None."""
    return {"rc": 0, "stderr": stderr, "code": code}


def fail(rc=1, stderr="error: refused [TCG-PROOF-465]"):
    return {"rc": rc, "stderr": stderr, "code": None}


class FakeToolchain:
    """Stands in for `measure`: compiles are scripted per lane (the last
    behaviour repeats), a bin compile writes its `prog`, a lib compile writes
    an object, and running a lane's `prog` exits with that lane's scripted
    statuses (the last one repeats)."""

    def __init__(self, compiles, exits=None):
        self.compiles = {lane: list(script) for lane, script in compiles.items()}
        self.exits = {lane: list(script) for lane, script in (exits or {}).items()}
        self.calls = []

    @staticmethod
    def take(queue):
        return queue.pop(0) if len(queue) > 1 else queue[0]

    def __call__(self, cmd, env, timeout, cwd=None):
        if "--crate-type" not in cmd:
            lane = Path(cmd[0]).parent.name
            self.calls.append(("run", lane))
            return sample(self.take(self.exits[lane]))
        lane = ("diagnostic" if any(a.startswith("-Ztrust-ir-cg-args=") for a in cmd)
                else "bridge" if any(a.startswith("-Zcodegen-backend=") for a in cmd) else "llvm")
        self.calls.append(("compile", lane))
        behaviour = self.take(self.compiles[lane])
        if behaviour["rc"] == 0:
            if "-o" in cmd:
                Path(cmd[cmd.index("-o") + 1]).write_text("#!/bin/sh\n")
            elif behaviour["code"] is not None:
                (Path(cmd[cmd.index("--out-dir") + 1]) / "x.o").write_bytes(macho_object(behaviour["code"]))
        return sample(behaviour["rc"], stderr=behaviour["stderr"])


BIN_ROW = {"id": "real-program/fake", "kind": "real-program", "crate_type": "bin", "run": True,
           "source": {"type": "corpus-guest"}}
LIB_ROW = {"id": "crate/fake-1.0.0", "kind": "real-crate", "crate_type": "lib",
           "source": {"type": "crates-io"}}


def fake_harness(tmp, diagnostic=True):
    """A Harness whose inputs are materialized in place, for bench_row."""
    harness = RC.Harness.__new__(RC.Harness)
    harness.args = argparse.Namespace(diagnostic_lane=diagnostic, keep_work=False, timeout_scale=1.0,
                                      n_compile=3, n_run=5)
    harness.manifest = {"defaults": {"opt_level": "3", "panic": "abort", "timeout_s": 900,
                                     "n_compile": 3, "n_run": 5}}
    harness.repo, harness.work, harness.env = RC.REPO, Path(tmp), {}
    harness.driver = {"compiler": "/fake/trustc", "compiler_flags": []}
    harness.dylib, harness.target = Path("/fake/backend.dylib"), "aarch64-apple-darwin"
    harness.degraded, harness.backend_load_failures = [], []
    plan = {"root": Path(tmp) / "fake.rs", "edition": "2021", "crate_name": None, "cfg": [],
            "features": [], "lines": 1, "source_sha256": "0" * 64, "env": {}}
    harness.materialize = lambda row, work: (plan, None)
    return harness


def git(repo, *args):
    return subprocess.run(["git", "-C", str(repo), "-c", "user.name=t", "-c", "user.email=t@example.invalid",
                           "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null", *args],
                          check=True, capture_output=True, text=True).stdout.strip()


class ManifestTests(unittest.TestCase):
    def setUp(self):
        self.manifest = RC.load_manifest()

    def test_the_committed_manifest_is_well_formed(self):
        self.assertEqual(RC.validate_manifest(self.manifest), [])
        self.assertEqual(self.manifest["schema"], RC.MANIFEST_SCHEMA)

    def test_every_in_repo_row_still_has_its_pinned_digest(self):
        # A changed guest or generator is a new corpus version, never an edit in place.
        self.assertEqual(RC.check_in_repo_digests(self.manifest), [])

    def test_the_corpus_is_larger_than_the_contract_corpus_and_covers_every_kind(self):
        rows = self.manifest["rows"]
        self.assertGreater(len(rows), 18)
        kinds = {row["kind"] for row in rows}
        self.assertEqual(kinds, set(RC.KINDS))
        guests = RC.corpus_guests(ROOT / "crates/rustc-codegen-trust-cg/tests/real_program_corpus/corpus_guests.rs")
        manifested = {row["source"]["guest"] for row in rows if row["source"]["type"] == "corpus-guest"}
        self.assertEqual(manifested, set(guests))  # every shared guest, not a chosen subset

    def test_crate_rows_pin_a_crates_io_checksum_and_compile_alone(self):
        for row in self.manifest["rows"]:
            if row["kind"] != "real-crate":
                continue
            with self.subTest(row=row["id"]):
                self.assertRegex(row["source"]["sha256"], r"^[0-9a-f]{64}$")
                self.assertEqual(row["crate_type"], "lib")
                self.assertFalse(row.get("run"))

    def test_the_sysroot_rows_name_a_revision_and_a_tree(self):
        rows = [r for r in self.manifest["rows"] if r["kind"] == "trust-sysroot"]
        self.assertTrue(rows)
        for row in rows:
            self.assertRegex(row["source"]["revision"], r"^[0-9a-f]{40}$")
            self.assertRegex(row["source"]["tree"], r"^[0-9a-f]{40}$")
            self.assertEqual(row["env"], {"RUSTC_BOOTSTRAP": "1"})

    def test_validation_names_each_defect(self):
        broken = json.loads(json.dumps(self.manifest))
        broken["rows"].append(dict(broken["rows"][0]))
        broken["rows"].append({"id": "x", "kind": "toy", "crate_type": "dylib", "source": {"type": "?"}})
        problems = " ".join(RC.validate_manifest(broken))
        self.assertIn("duplicates id", problems)
        self.assertIn("kind 'toy'", problems)
        self.assertIn("crate_type must be bin or lib", problems)
        self.assertIn("source type '?' unknown", problems)

    def test_a_changed_generator_is_caught(self):
        changed = json.loads(json.dumps(self.manifest))
        row = next(r for r in changed["rows"] if r["source"]["type"] == "generator")
        row["source"]["sha256"] = "0" * 64
        problems = RC.check_in_repo_digests(changed)
        self.assertEqual(len(problems), 1)
        self.assertIn("bump the manifest version", problems[0])


class FeatureTests(unittest.TestCase):
    TABLE = {"default": ["std"], "std": ["alloc"], "alloc": [], "perf": ["dep:memchr"],
             "weak": ["memchr?/std"], "strong": ["serde/std"]}

    def test_default_features_close_transitively(self):
        self.assertEqual(RC.feature_closure(self.TABLE, [], True, {"memchr"}), ["alloc", "std"])

    def test_an_optional_dependency_is_refused(self):
        with self.assertRaisesRegex(RC.ManifestError, "optional dependency"):
            RC.feature_closure(self.TABLE, ["perf"], False, {"memchr"})
        with self.assertRaisesRegex(RC.ManifestError, "optional dependency"):
            RC.feature_closure({}, ["memchr"], False, {"memchr"})

    def test_weak_dependency_features_are_ignored_and_strong_ones_refused(self):
        self.assertEqual(RC.feature_closure(self.TABLE, ["weak"], False, {"memchr"}), ["weak"])
        with self.assertRaisesRegex(RC.ManifestError, "names a dependency"):
            RC.feature_closure(self.TABLE, ["strong"], False, {"memchr"})

    def test_an_undeclared_feature_is_refused(self):
        with self.assertRaisesRegex(RC.ManifestError, "not declared"):
            RC.feature_closure(self.TABLE, ["nope"], False, set())


class CrateInputTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="trust-cg-real-corpus-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def crate(self, cargo_toml, files=None):
        directory = self.root / "c"
        (directory / "src").mkdir(parents=True)
        (directory / "Cargo.toml").write_text(cargo_toml)
        (directory / "src" / "lib.rs").write_text("pub fn f() {}\n")
        for name, text in (files or {}).items():
            (directory / name).write_text(text)
        return directory

    def test_a_plain_crate_gets_its_features_as_cfgs(self):
        directory = self.crate('[package]\nname = "a-b"\nedition = "2018"\n'
                               '[features]\ndefault = ["std"]\nstd = []\n')
        plan = RC.crate_plan(directory, {"edition": "2018"})
        self.assertEqual(plan["crate_name"], "a_b")
        self.assertEqual(plan["cfg"], ["--cfg", 'feature="std"'])

    def test_a_build_script_a_required_dependency_and_an_edition_disagreement_are_refused(self):
        with self.assertRaisesRegex(RC.ManifestError, "build script"):
            RC.crate_plan(self.crate('[package]\nname = "a"\n', {"build.rs": "fn main(){}"}), {})
        self.tmp.cleanup()
        self.root.mkdir()
        with self.assertRaisesRegex(RC.ManifestError, "requires dependencies"):
            RC.crate_plan(self.crate('[package]\nname = "a"\n[dependencies]\nx = "1"\n'), {})
        self.tmp.cleanup()
        self.root.mkdir()
        with self.assertRaisesRegex(RC.ManifestError, "edition"):
            RC.crate_plan(self.crate('[package]\nname = "a"\nedition = "2021"\n'), {"edition": "2018"})

    def test_windows_only_dependencies_do_not_count(self):
        directory = self.crate('[package]\nname = "a"\n[target."cfg(windows)".dependencies]\nw = "1"\n')
        self.assertEqual(RC.crate_plan(directory, {})["features"], [])

    def test_unsafe_archive_members_are_refused(self):
        buffer = io.BytesIO()
        with tarfile.open(fileobj=buffer, mode="w:gz") as tar:
            data = b"x"
            info = tarfile.TarInfo("../escape")
            info.size = len(data)
            tar.addfile(info, io.BytesIO(data))
        with self.assertRaisesRegex(RC.ManifestError, "unsafe archive member"):
            RC.safe_extract(buffer.getvalue(), self.root / "out")
        self.assertFalse((self.root / "escape").exists())

    def test_the_registry_cache_is_found_by_name_and_version(self):
        cache = self.root / "registry" / "cache" / "index.crates.io-x"
        cache.mkdir(parents=True)
        (cache / "a-1.0.0.crate").write_bytes(gzip.compress(b""))
        self.assertEqual(RC.registry_archive(self.root, "a", "1.0.0"), cache / "a-1.0.0.crate")
        self.assertIsNone(RC.registry_archive(self.root, "a", "2.0.0"))


class MaterializeTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="trust-cg-real-corpus-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.harness = fake_harness(self.root / "work")
        del self.harness.materialize  # the real one

    def crate_archive(self):
        buffer = io.BytesIO()
        with tarfile.open(fileobj=buffer, mode="w:gz") as tar:
            for name, text in (("a-1.0.0/Cargo.toml", '[package]\nname = "a"\nedition = "2021"\n'),
                               ("a-1.0.0/src/lib.rs", "pub fn f() {}\n")):
                info = tarfile.TarInfo(name)
                info.size = len(text.encode())
                tar.addfile(info, io.BytesIO(text.encode()))
        cache = self.root / "cargo" / "registry" / "cache" / "index.crates.io-x"
        cache.mkdir(parents=True)
        (cache / "a-1.0.0.crate").write_bytes(buffer.getvalue())
        self.harness.cargo_home = self.root / "cargo"
        return hashlib.sha256(buffer.getvalue()).hexdigest()

    def test_a_crate_archive_must_have_the_manifests_digest(self):
        digest = self.crate_archive()
        row = {"id": "crate/a-1.0.0", "kind": "real-crate", "crate_type": "lib",
               "source": {"type": "crates-io", "name": "a", "version": "1.0.0", "sha256": digest}}
        plan, problem = self.harness.materialize(row, self.root / "ok")
        self.assertIsNone(problem)
        self.assertEqual(plan["crate_name"], "a")
        row["source"]["sha256"] = "0" * 64
        plan, problem = self.harness.materialize(row, self.root / "bad")
        self.assertIsNone(plan)
        self.assertEqual(problem[0], "INVALID-INPUT")
        self.assertIn("archive sha256", problem[1])
        row["source"]["version"] = "2.0.0"
        self.assertEqual(self.harness.materialize(row, self.root / "gone")[1][0], "UNAVAILABLE")

    def test_a_sysroot_row_needs_the_drivers_own_revision(self):
        checkout = self.root / "trust"
        (checkout / "library" / "core" / "src").mkdir(parents=True)
        (checkout / "library" / "core" / "src" / "lib.rs").write_text("#![no_core]\n")
        git(checkout, "init", "-q")
        git(checkout, "add", "-A")
        git(checkout, "commit", "-q", "-m", "x")
        revision, tree = git(checkout, "rev-parse", "HEAD"), git(checkout, "rev-parse", "HEAD:library")
        self.harness.args.trust_checkout = str(checkout)
        row = {"id": "trust-sysroot/core-O3", "kind": "trust-sysroot", "crate_type": "lib",
               "crate_name": "core", "env": {"RUSTC_BOOTSTRAP": "1"},
               "source": {"type": "trust-git", "revision": revision, "path": "library", "tree": tree,
                          "root": "core/src/lib.rs"}}
        self.harness.driver["commit"] = revision
        plan, problem = self.harness.materialize(row, self.root / "ok")
        self.assertIsNone(problem)
        self.assertTrue(plan["root"].is_file())
        self.assertEqual(plan["env"], {"RUSTC_BOOTSTRAP": "1"})
        self.harness.driver["commit"] = "f" * 40
        plan, problem = self.harness.materialize(row, self.root / "other-driver")
        self.assertIsNone(plan)
        self.assertEqual(problem[0], "UNAVAILABLE")
        self.assertIn("is not the source revision", problem[1])
        self.harness.driver["commit"] = revision
        row["source"]["tree"] = "0" * 40
        self.assertEqual(self.harness.materialize(row, self.root / "bad-tree")[1][0], "INVALID-INPUT")


class SamplerTests(unittest.TestCase):
    DARWIN = ("error: refused [TCG-PROOF-465]\n"
              "        2.73 real         1.46 user         0.13 sys\n"
              "           194412544  maximum resident set size\n"
              "                   0  average shared memory size\n"
              "          5783508263  instructions retired\n"
              "          9000000000  cycles elapsed\n"
              "            96781008  peak memory footprint\n")
    GNU = ("compiler said hi\n\tCommand being timed: \"x\"\n\tUser time (seconds): 1.50\n"
           "\tSystem time (seconds): 0.25\n\tMaximum resident set size (kbytes): 2048\n")

    def test_darwin_report_is_split_from_the_commands_stderr(self):
        own, metrics = RC.parse_time_report(self.DARWIN, "darwin")
        self.assertEqual(own, "error: refused [TCG-PROOF-465]\n")
        self.assertEqual(metrics["maxrss_bytes"], 194412544)
        self.assertEqual(metrics["instructions"], 5783508263)
        self.assertEqual(metrics["cycles"], 9000000000)
        self.assertEqual((metrics["user_s"], metrics["sys_s"]), (1.46, 0.13))

    def test_gnu_report_is_normalised_to_bytes(self):
        own, metrics = RC.parse_time_report(self.GNU, "linux")
        self.assertEqual(own, "compiler said hi\n")
        self.assertEqual(metrics["maxrss_bytes"], 2048 * 1024)
        self.assertIsNone(metrics["instructions"])

    def test_a_real_command_is_measured_and_a_timeout_kills_it(self):
        done = RC.measure([sys.executable, "-c", "import sys; sys.exit(3)"], dict(os.environ), 60)
        self.assertEqual(done["returncode"], 3)
        self.assertFalse(done["timed_out"])
        slow = RC.measure([sys.executable, "-c", "import time; time.sleep(30)"], dict(os.environ), 1)
        self.assertTrue(slow["timed_out"])
        self.assertLess(slow["wall_s"], 20)


class OutcomeTests(unittest.TestCase):
    def test_classification(self):
        self.assertEqual(RC.classify_failure(sample(1, stderr="x [TCG-PROOF-465] y")), "INCOMPLETE")
        self.assertEqual(RC.classify_failure(sample(-9, timed_out=True)), "TIMEOUT")
        self.assertEqual(RC.classify_failure(sample(101, stderr="thread 'rustc' panicked at")), "ERROR")
        self.assertEqual(RC.classify_failure(sample(1, stderr="error: linking failed")), "ERROR")
        # A crash that also printed a named refusal is still a crash.
        self.assertEqual(RC.classify_failure(sample(101, stderr="[TCG-PROOF-465]\nthread 'rustc' panicked at x")),
                         "ERROR")
        self.assertEqual(RC.classify_failure(sample(101, stderr="[TCG-PROOF-465] internal compiler error")),
                         "ERROR")
        self.assertEqual(RC.COMPLETED, ("MATCH", "COMPILED"))
        self.assertEqual(RC.tcg_codes("[TCG-MIR-UNSUPPORTED] [TCG-PROOF-465] [TCG-PROOF-465]"),
                         ["[TCG-MIR-UNSUPPORTED]", "[TCG-PROOF-465]"])

    def harness_with(self, outcomes):
        harness = RC.Harness.__new__(RC.Harness)
        harness.degraded = []
        script = iter(outcomes)
        harness.compile = lambda *a, **k: next(script)
        return harness

    def test_a_refusal_is_retried_and_kept_as_incomplete(self):
        refusal = sample(1, stderr="error [TCG-PROOF-465]", wall=2.0)
        harness = self.harness_with([refusal, refusal])
        outcome, record = harness.bridge_lane({"crate_type": "bin"}, {}, "bridge", Path("."), 10, 3)
        self.assertEqual(outcome, "INCOMPLETE")
        self.assertEqual(len(record["attempts"]), 2)
        self.assertEqual(record["tcg_codes"], ["[TCG-PROOF-465]"])
        self.assertEqual(record["refusal_wall_s"], 2.0)

    def test_a_retry_that_compiles_is_never_a_completion(self):
        harness = self.harness_with([sample(1, stderr="[TCG-PROOF-465]"), sample(0)])
        outcome, _ = harness.bridge_lane({"crate_type": "bin"}, {}, "bridge", Path("."), 10, 3)
        self.assertEqual(outcome, "NONDET-FAILCLOSED")

    def test_a_measured_compile_that_fails_is_nondeterministic(self):
        harness = self.harness_with([sample(0), sample(0), sample(1, stderr="[TCG-PROOF-465]")])
        outcome, _ = harness.bridge_lane({"crate_type": "bin"}, {}, "bridge", Path("."), 10, 3)
        self.assertEqual(outcome, "NONDET-FAILCLOSED")

    def test_a_timeout_is_not_retried(self):
        harness = self.harness_with([sample(-9, timed_out=True)])
        outcome, record = harness.bridge_lane({"crate_type": "bin"}, {}, "bridge", Path("."), 10, 3)
        self.assertEqual(outcome, "TIMEOUT")
        self.assertEqual(len(record["attempts"]), 1)

    def test_a_clean_compile_yields_n_samples_and_a_summary(self):
        harness = self.harness_with([sample(0, code_bytes=10, objects=1)]
                                    + [sample(0, wall=w, code_bytes=10, objects=1) for w in (1, 3, 2)])
        outcome, record = harness.bridge_lane({"crate_type": "lib"}, {}, "bridge", Path("."), 10, 3)
        self.assertIsNone(outcome)  # decided by the caller (run oracle or COMPILED)
        self.assertEqual(record["summary"]["wall_s"], 2)
        self.assertEqual(record["code_bytes"], 10)

    def test_a_library_compile_that_exits_0_without_an_object_is_an_error(self):
        for missing in ("warmup", "measured"):
            with self.subTest(missing=missing):
                good = sample(0, code_bytes=10, objects=1)
                empty = sample(0, code_bytes=None, objects=0)
                script = [empty, good, good, good] if missing == "warmup" else [good, good, empty, good]
                outcome, record = self.harness_with(script).bridge_lane(
                    {"crate_type": "lib"}, {}, "bridge", Path("."), 10, 3)
                self.assertEqual(outcome, "ERROR")
                self.assertIn("wrote no object", record["error"])
        self.assertIn("could not be read", RC.object_problem({"code_bytes": None, "objects": 2}))
        self.assertIsNone(RC.object_problem({"code_bytes": 0, "objects": 1}))  # empty code is an object


class AggregateTests(unittest.TestCase):
    def rows(self):
        return [
            {"id": "a", "kind": "real-crate", "outcome": "COMPILED",
             "ratios": {"bridge": {"compile_wall_s": 2.0, "code_bytes": 0.5}}},
            {"id": "b", "kind": "real-crate", "outcome": "COMPILED",
             "ratios": {"bridge": {"compile_wall_s": 0.5, "code_bytes": None}}},
            {"id": "c", "kind": "real-program", "outcome": "INCOMPLETE",
             "lanes": {"bridge": {"tcg_codes": ["[TCG-PROOF-465]"]}}},
            {"id": "d", "kind": "scale-ladder", "outcome": "UNAVAILABLE"},
        ]

    def test_retries_errors_and_baseline_failures_never_complete(self):
        rows = [{"id": o, "kind": "real-crate", "outcome": o} for o in RC.OUTCOMES]
        agg = RC.Harness.aggregates(rows, "outcome", "bridge")
        self.assertEqual(agg["completed"], 2)
        self.assertEqual(sum(agg["counts"].values()), len(rows))
        self.assertEqual(agg["unclassified"], [])
        self.assertEqual(RC.Harness.aggregates([{"id": "x", "kind": "real-crate"}], "outcome",
                                               "bridge")["unclassified"], ["x"])

    def test_a_vacuous_completion_is_reported_apart(self):
        rows = self.rows()
        rows[0]["vacuous"] = True
        agg = RC.Harness.aggregates(rows, "outcome", "bridge")
        self.assertEqual((agg["completed"], agg["completed_with_code"]), (2, 1))
        self.assertEqual(agg["vacuous_completed"], ["a"])
        self.assertEqual(agg["completion_with_code_pct"], 25.0)

    def test_completion_is_intent_to_treat_and_aggregates_fail_closed(self):
        agg = RC.Harness.aggregates(self.rows(), "outcome", "bridge")
        self.assertEqual(agg["rows"], 4)
        self.assertEqual(agg["completed"], 2)
        self.assertEqual(agg["completion_pct"], 50.0)
        self.assertAlmostEqual(agg["ratios"]["compile_wall_s"]["geomean"], 1.0)
        self.assertIsNone(agg["ratios"]["code_bytes"]["geomean"])  # one completed row lacks it
        self.assertEqual(agg["ratios"]["code_bytes"]["missing"], ["b"])
        self.assertEqual(agg["refused_rows_by_code"], {"[TCG-PROOF-465]": 1})
        self.assertEqual(agg["by_kind"]["scale-ladder"]["completion_pct"], 0.0)

    def test_eligibility_names_every_failure(self):
        harness = RC.Harness.__new__(RC.Harness)
        harness.degraded = ["x:bridge"]
        harness.backend_load_failures = ["x:bridge"]
        prov = {"git_dirty": True, "dylib_stale_override": True, "tcg_env": {"TCG_X": "1"},
                "load_threshold": 8.0, "loadavg_before": [9.0, 0, 0], "loadavg_after": [1.0, 0, 0],
                "load_threshold_overridden": True, "runaway_processes": [{"pid": 1}],
                "full_corpus": False, "n_compile": 1, "n_run": 1,
                "proof_checker": {"candidates": []}, "manifest": {"is_committed": False}}
        unclassified = {"bridge": {"unclassified": ["e"]}}
        reasons = " | ".join(harness.ineligible_reasons(prov, self.rows() + [{"outcome": "MISMATCH"}],
                                                        unclassified))
        for needle in ("tracked edits", "stale", "TCG_", "LOADED", "overridden", "runaway",
                       "subset", "below N", "unavailable", "MISMATCH", "proof checker", "DEGRADED",
                       "manifest is not the committed", "failed to load", "without a known outcome"):
            self.assertIn(needle, reasons)
        # A manifest that does not say whether it is the committed one is not.
        self.assertIn("manifest is not the committed",
                      " ".join(harness.ineligible_reasons(dict(prov, manifest={}), [])))
        # One row that ran under load is enough to make a quiet start and end ineligible.
        loud_row = dict(self.rows()[0], loadavg_start=[9.5, 0, 0], loadavg_end=[1.0, 0, 0])
        quiet_ends = dict(prov, git_dirty=False, dylib_stale_override=False, tcg_env={},
                          loadavg_before=[1.0, 0, 0], load_threshold_overridden=False,
                          runaway_processes=[], full_corpus=True, n_compile=3, n_run=5,
                          proof_checker={"candidates": [{"runs": True}]},
                          manifest={"is_committed": True})
        harness.degraded, harness.backend_load_failures = [], []
        self.assertEqual(harness.ineligible_reasons(quiet_ends, [loud_row]),
                         ["1 of 1 rows started or ended LOADED (1-min load above 8.0)"])
        quiet = dict(quiet_ends)
        self.assertEqual(harness.ineligible_reasons(quiet, self.rows()[:3]), [])


class RowTests(unittest.TestCase):
    """bench_row end to end over a fake toolchain: the LLVM baseline, the
    bridge protocol, the exit-status oracle and the library object rule."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="trust-cg-real-corpus-")
        self.addCleanup(self.tmp.cleanup)

    def bench(self, row, compiles, exits=None, diagnostic=True):
        harness = fake_harness(self.tmp.name, diagnostic)
        fake = FakeToolchain(compiles, exits)
        with mock.patch.object(RC, "measure", fake):
            result = harness.bench_row(row)
        self.assertEqual(list(Path(self.tmp.name).iterdir()), [])  # the row's scratch is removed
        return result, harness, fake

    def test_equal_exit_statuses_match(self):
        result, _, fake = self.bench(BIN_ROW, {"llvm": [ok()], "bridge": [ok()], "diagnostic": [ok()]},
                                     {"llvm": [7], "bridge": [7], "diagnostic": [7]})
        self.assertEqual((result["outcome"], result["diagnostic_outcome"]), ("MATCH", "MATCH"))
        self.assertEqual(result["runs"]["expected_exit"], 7)
        self.assertIn("runtime_cycles", result["ratios"]["bridge"])
        # One warmup and five measured runs per lane.
        self.assertEqual(sum(1 for call in fake.calls if call == ("run", "bridge")), 6)

    def test_a_differing_exit_status_is_a_mismatch(self):
        for late in (False, True):
            with self.subTest(late=late):
                bridge = [7, 7, 7, 7, 7, 8] if late else [8]
                result, _, _ = self.bench(BIN_ROW, {"llvm": [ok()], "bridge": [ok()], "diagnostic": [ok()]},
                                          {"llvm": [7], "bridge": bridge, "diagnostic": [7]})
                self.assertEqual(result["outcome"], "MISMATCH")
                self.assertEqual(result["diagnostic_outcome"], "MATCH")
                self.assertNotIn("bridge", result["ratios"])

    def test_a_refused_bridge_is_never_run(self):
        result, _, fake = self.bench(BIN_ROW, {"llvm": [ok()], "bridge": [fail()], "diagnostic": [ok()]},
                                     {"llvm": [7], "diagnostic": [7]})
        self.assertEqual((result["outcome"], result["diagnostic_outcome"]), ("INCOMPLETE", "MATCH"))
        self.assertNotIn(("run", "bridge"), fake.calls)

    def test_an_inconsistent_llvm_program_fails_the_baseline_in_every_lane(self):
        result, _, _ = self.bench(BIN_ROW, {"llvm": [ok()], "bridge": [ok()], "diagnostic": [ok()]},
                                  {"llvm": [7, 9], "bridge": [7], "diagnostic": [7]})
        self.assertEqual((result["outcome"], result["diagnostic_outcome"]),
                         ("BASELINE-FAILED", "BASELINE-FAILED"))
        agg = RC.Harness.aggregates([result], "diagnostic_outcome", "diagnostic")
        self.assertEqual(sum(agg["counts"].values()), agg["rows"])

    def test_an_llvm_compile_failure_skips_the_bridge(self):
        result, _, fake = self.bench(BIN_ROW, {"llvm": [ok(), fail(1, "error: bad input")]})
        self.assertEqual((result["outcome"], result["diagnostic_outcome"]),
                         ("BASELINE-FAILED", "BASELINE-FAILED"))
        self.assertEqual(result["reason"], "error: bad input")
        self.assertEqual({lane for _, lane in fake.calls}, {"llvm"})

    def test_a_library_bridge_compile_without_an_object_is_an_error(self):
        result, _, _ = self.bench(LIB_ROW, {"llvm": [ok(4)], "bridge": [ok(None)], "diagnostic": [ok(40)]})
        self.assertEqual((result["outcome"], result["diagnostic_outcome"]), ("ERROR", "COMPILED"))
        self.assertIn("wrote no object", result["reason"])
        self.assertFalse(result["vacuous"])
        self.assertEqual(result["ratios"]["diagnostic"]["code_bytes"], 10.0)
        self.assertNotIn("bridge", result["ratios"])

    def test_an_llvm_library_compile_without_an_object_fails_the_baseline(self):
        result, _, fake = self.bench(LIB_ROW, {"llvm": [ok(None)], "bridge": [ok(4)], "diagnostic": [ok(4)]})
        self.assertEqual(result["outcome"], "BASELINE-FAILED")
        self.assertIn("LLVM lane: the compile exited 0 but wrote no object", result["reason"])
        self.assertEqual({lane for _, lane in fake.calls}, {"llvm"})

    def test_a_library_whose_llvm_object_holds_no_code_is_vacuous(self):
        result, _, _ = self.bench(LIB_ROW, {"llvm": [ok(0)], "bridge": [ok(16)], "diagnostic": [ok(16)]})
        self.assertEqual(result["outcome"], "COMPILED")
        self.assertTrue(result["vacuous"])
        self.assertNotIn("code_bytes", result["ratios"]["bridge"])  # x/0 is no ratio
        agg = RC.Harness.aggregates([result], "outcome", "bridge")
        self.assertEqual((agg["completed"], agg["completed_with_code"]), (1, 0))

    def test_degraded_and_unloadable_backends_are_recorded(self):
        unloadable = fail(1, "error: could not canonicalize codegen backend `b`: No such file or directory")
        result, harness, _ = self.bench(
            LIB_ROW, {"llvm": [ok(4)], "bridge": [ok(4, stderr=f"warning: {RC.BEAT.DEGRADED_MARKER}")],
                      "diagnostic": [unloadable]})
        self.assertEqual((result["outcome"], result["diagnostic_outcome"]), ("COMPILED", "ERROR"))
        self.assertEqual(set(harness.degraded), {"crate/fake-1.0.0:bridge"})
        self.assertEqual(harness.backend_load_failures, ["crate/fake-1.0.0:diagnostic"] * 2)


PROVENANCE = {
    "git_sha": "1" * 40, "git_dirty": False, "loadavg_before": [0.0, 0, 0],
    "load_threshold": 8.0, "load_threshold_overridden": False, "tcg_env": {},
    "dylib_stale_override": True, "runaway_processes": [], "full_corpus": False,
    "n_compile": 3, "n_run": 5, "proof_checker": {"candidates": []},
    "manifest": {"corpus": "l14-real-corpus", "version": "1.0.0"},
    "timestamp_utc": "2026-10-14T00:00:00+00:00", "target": "aarch64-apple-darwin",
    "host_model": "test", "driver": {"commit": "0" * 40},
    "dylib_sha256": "2" * 64}


class EntryPointTests(unittest.TestCase):
    def test_a_harness_fault_in_one_row_is_an_error_row_not_a_lost_run(self):
        with tempfile.TemporaryDirectory(prefix="trust-cg-real-corpus-") as tmp:
            args = RC.parse_args(["--only", "real-program/p01_interp", "ladder/scale_gate/small",
                                  "--out-dir", tmp, "--work-dir", tmp, "--allow-loaded",
                                  "--allow-stale-dylib", "--dylib", __file__])
            args.n_compile, args.n_run = 3, 5
            harness = RC.Harness(args)
            driver = {"compiler": "/nonexistent/trustc", "compiler_flags": [], "host": "aarch64-apple-darwin",
                      "commit": "0" * 40, "sysroot": tmp}
            calls = []

            def bench_row(row):
                calls.append(row["id"])
                if row["id"].startswith("real-program/"):
                    raise OSError("disk full")
                return {"id": row["id"], "kind": row["kind"], "crate_type": row["crate_type"],
                        "outcome": "INCOMPLETE", "loadavg_start": [0.0], "loadavg_end": [0.0]}

            with mock.patch.object(RC.TRUST_TOOLCHAIN, "resolve", return_value=driver), \
                    mock.patch.object(harness, "bench_row", side_effect=bench_row), \
                    mock.patch.object(harness, "provenance", return_value=dict(PROVENANCE)):
                self.assertEqual(harness.main(), 0)
            self.assertEqual(calls, ["real-program/p01_interp", "ladder/scale_gate/small"])
            written = json.loads(next(Path(tmp).glob("*.json")).read_text())
            first, second = written["rows"]
            self.assertEqual(first["outcome"], "ERROR")
            self.assertIn("harness exception: OSError: disk full", first["reason"])
            self.assertEqual(second["outcome"], "INCOMPLETE")
            self.assertEqual(written["aggregates"]["bridge"]["counts"]["ERROR"], 1)

    def test_path_arguments_are_made_absolute(self):
        args = RC.parse_args(["--dylib", "rel/backend.dylib", "--out-dir", "o", "--work-dir", "w",
                              "--manifest", "m.json", "--trust-checkout", "t", "--cargo-home", "c",
                              "--driver", "trustc"])
        for key in ("dylib", "out_dir", "work_dir", "manifest", "trust_checkout", "cargo_home"):
            with self.subTest(key=key):
                self.assertTrue(os.path.isabs(getattr(args, key)))
        self.assertEqual(args.dylib, os.path.join(os.getcwd(), "rel", "backend.dylib"))
        self.assertEqual(args.driver, "trustc")  # a bare name is looked up, not a path
        self.assertTrue(os.path.isabs(RC.parse_args(["--driver", "bin/trustc"]).driver))

    def test_only_the_committed_manifest_binds_a_run(self):
        with tempfile.TemporaryDirectory(prefix="trust-cg-real-corpus-") as tmp:
            repo = Path(tmp) / "repo"
            committed = repo / RC.MANIFEST_REL
            committed.parent.mkdir(parents=True)
            committed.write_text('{"version": "1.0.0"}\n')
            git(repo, "init", "-q")
            git(repo, "add", "-A")
            git(repo, "commit", "-q", "-m", "x")
            self.assertTrue(RC.manifest_binding(repo, committed)["is_committed"])
            copy = Path(tmp) / "manifest.json"
            copy.write_text(committed.read_text())
            self.assertFalse(RC.manifest_binding(repo, copy)["is_committed"])  # same bytes, other file
            committed.write_text('{"version": "1.0.0", "rows": []}\n')
            binding = RC.manifest_binding(repo, committed)
            self.assertFalse(binding["is_committed"])  # edited after HEAD
            self.assertRegex(binding["committed_sha256"], r"^[0-9a-f]{64}$")

    def test_a_mismatch_makes_the_run_exit_1(self):
        with tempfile.TemporaryDirectory(prefix="trust-cg-real-corpus-") as tmp:
            args = RC.parse_args(["--only", "real-program/p01_interp", "--out-dir", tmp, "--work-dir", tmp,
                                  "--allow-loaded", "--allow-stale-dylib", "--dylib", __file__])
            args.n_compile, args.n_run = 3, 5
            harness = RC.Harness(args)
            driver = {"compiler": "/nonexistent/trustc", "compiler_flags": [], "host": "aarch64-apple-darwin",
                      "commit": "0" * 40, "sysroot": tmp}
            row = {"id": "real-program/p01_interp", "kind": "real-program", "crate_type": "bin",
                   "outcome": "MISMATCH", "loadavg_start": [0.0], "loadavg_end": [0.0]}
            with mock.patch.object(RC.TRUST_TOOLCHAIN, "resolve", return_value=driver), \
                    mock.patch.object(harness, "bench_row", return_value=row), \
                    mock.patch.object(harness, "provenance", return_value=dict(
                        PROVENANCE, manifest={"corpus": "l14-real-corpus", "version": "1.0.0",
                                              "is_committed": True})):
                self.assertEqual(harness.main(), 1)
            written = json.loads(next(Path(tmp).glob("*.json")).read_text())
            self.assertIn("MISMATCH rows", written["ineligible_reasons"])

    def test_check_manifest_compiles_nothing_and_passes(self):
        with mock.patch.object(RC.TRUST_TOOLCHAIN, "resolve", side_effect=AssertionError("no driver")):
            self.assertEqual(RC.main(["--check-manifest"]), 0)

    def test_an_invalid_manifest_is_a_tooling_error(self):
        with tempfile.TemporaryDirectory(prefix="trust-cg-real-corpus-") as tmp:
            bad = Path(tmp) / "m.json"
            bad.write_text(json.dumps({"schema": "nope", "rows": []}))
            self.assertEqual(RC.main(["--manifest", str(bad), "--list"]), 2)


if __name__ == "__main__":
    unittest.main()
