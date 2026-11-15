"""The full matrix must not count a feature-gated target it never ran (TRUSTCG-20)."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import re
import shlex
import unittest


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("matrix_shard_features", ROOT / "scripts/matrix_shard_features.py")
assert SPEC is not None and SPEC.loader is not None
FEATURES = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(FEATURES)


def package(name: str, *targets: dict) -> dict:
    return {"name": name, "targets": list(targets)}


def test_target(name: str, *required: str) -> dict:
    target = {"name": name, "kind": ["test"], "test": True}
    if required:
        target["required-features"] = list(required)
    return target


VERIFY = package(
    "trust-cg-verify",
    {"name": "trust_cg_verify", "kind": ["lib"], "test": True},
    test_target("coverage_gate_tests"),
    test_target("core_byte_store", "core-byte-replay"),
    test_target("core_byte_writer", "core-byte-replay"),
)


def shard(args: str, crate: str = "trust-cg-verify", name: str = "integration"):
    return (crate, name, args.split())


class FeatureGateTests(unittest.TestCase):
    def test_a_tests_shard_without_the_feature_misses_both_gated_targets(self):
        problems = FEATURES.feature_gate_problems([shard("-p trust-cg-verify --tests")], [VERIFY])
        self.assertEqual(len(problems), 2, problems)
        self.assertIn("trust-cg-verify/core_byte_store", problems[0])
        self.assertIn("core-byte-replay", problems[0])
        self.assertIn("trust-cg-verify/core_byte_writer", problems[1])

    def test_every_spelling_that_enables_the_feature_covers_them(self):
        for args in (
            "-p trust-cg-verify --tests --features core-byte-replay",
            "-p trust-cg-verify --tests --features=core-byte-replay",
            "-p trust-cg-verify --tests -F core-byte-replay",
            "-p trust-cg-verify --tests --features fsym,core-byte-replay",
            "-p trust-cg-verify --all-features",
            "-p trust-cg-verify --features core-byte-replay",
        ):
            with self.subTest(args=args):
                self.assertEqual(FEATURES.feature_gate_problems([shard(args)], [VERIFY]), [])

    def test_the_feature_must_be_on_a_shard_that_selects_the_target(self):
        shards = [
            shard("-p trust-cg-verify --tests", name="integration"),
            shard("-p trust-cg-verify --lib --features core-byte-replay", name="lib"),
            shard("-p trust-cg-verify --test core_byte_store --features core-byte-replay", name="store"),
        ]
        problems = FEATURES.feature_gate_problems(shards, [VERIFY])
        self.assertEqual(len(problems), 1, problems)
        self.assertIn("core_byte_writer", problems[0])

    def test_ungated_targets_and_unplanned_packages_are_not_reported_here(self):
        other = package("trust-cg-other", test_target("gated", "x"))
        self.assertEqual(FEATURES.feature_gate_problems([shard("-p trust-cg-verify --all-features")], [VERIFY, other]), [])

    def test_auto_shards_enable_a_targets_features(self):
        self.assertEqual(FEATURES.feature_args(test_target("plain")), [])
        self.assertEqual(
            FEATURES.feature_args(test_target("gated", "b", "a")),
            ["--features", "a,b"],
        )


class CheckedInPlanTests(unittest.TestCase):
    """The plan run_full_test_matrix.sh carries, against the manifests' own
    `[[test]] required-features` rows (read without Cargo, so this runs in the
    release gate's Python lane)."""

    def test_the_checked_in_plan_enables_every_gated_integration_target(self):
        script = (ROOT / "scripts/run_full_test_matrix.sh").read_text()
        plan = script.split("read -r -d '' SHARD_PLAN <<'EOF' || true\n", 1)[1].split("\nEOF\n", 1)[0]
        shards = [
            (parts[0], parts[1], shlex.split(parts[2]))
            for parts in (line.split("|") for line in plan.splitlines() if line.strip())
        ]
        packages = []
        for manifest in sorted((ROOT / "crates").glob("*/Cargo.toml")):
            text = manifest.read_text()
            name = re.search(r'^name = "([^"]+)"', text, re.M)
            targets = []
            for block in re.split(r"^\[\[", text, flags=re.M)[1:]:
                kind, _, body = block.partition("]]")
                target = re.search(r'^name = "([^"]+)"', body, re.M)
                required = re.search(r"^required-features = \[([^\]]*)\]", body, re.M)
                if kind.strip() == "test" and target and required:
                    targets.append(test_target(target[1], *re.findall(r'"([^"]+)"', required[1])))
            if name and targets:
                packages.append(package(name[1], *targets))
        self.assertTrue(
            any(t["name"] == "core_byte_store" for p in packages for t in p["targets"]),
            "the manifest scan must see trust-cg-verify's gated targets",
        )
        self.assertEqual(FEATURES.feature_gate_problems(shards, packages), [])


if __name__ == "__main__":
    unittest.main()
