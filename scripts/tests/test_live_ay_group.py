"""The live-AY batch group is bounded out of the default --lib run and kept in its own lane.

TRUSTCG-21: the `ay_bridge::tests::test_ay_batch_verify_*` tests send whole
proof categories through the external AY solver one obligation at a time and
dominate a `trust-cg-verify --lib` run. Without the `live-ay` feature they are
compiled but ignored with a stated reason; the full matrix runs them in the
`lib-live-ay` shard, and every other lib shard filters them out rather than
counting them as ignored.
"""

from __future__ import annotations

from pathlib import Path
import re
import unittest


ROOT = Path(__file__).resolve().parents[2]
BRIDGE = ROOT / "crates/trust-cg-verify/src/ay_bridge.rs"
MANIFEST = ROOT / "crates/trust-cg-verify/Cargo.toml"
MATRIX = ROOT / "scripts/run_full_test_matrix.sh"
GROUP = "ay_bridge::tests::test_ay_batch_verify_"
GATE = re.compile(
    r'#\[test\]\n\s*#\[cfg_attr\(\n\s*not\(feature = "live-ay"\),\n\s*ignore = "live-AY batch group: [^"]+"\n\s*\)\]\n\s*fn (test_ay_batch_verify_\w+)\('
)


def plan_rows() -> dict[str, list[str]]:
    text = MATRIX.read_text()
    plan = text.split("read -r -d '' SHARD_PLAN <<'EOF' || true\n", 1)[1].split("\nEOF\n", 1)[0]
    return {f"{row[0]}|{row[1]}": row for row in (line.split("|") for line in plan.splitlines() if line.strip())}


SELECTORS = {"--lib", "--tests", "--all-targets", "--bins", "--bin", "--test", "--benches",
             "--bench", "--examples", "--example", "--doc"}


def runs_lib_unit_tests(args: list[str]) -> bool:
    """Whether Cargo arguments build and run the library's unit-test binary."""
    return (
        "--lib" in args or "--tests" in args or "--all-targets" in args
        or not any(arg in SELECTORS for arg in args)
    )


def libtest_selects(filters: str, name: str) -> bool:
    """libtest's rule: any positive filter is a substring of the name (or there
    is none), and no `--skip` filter is."""
    words = filters.split()
    skips = [words[i + 1] for i in range(len(words) - 1) if words[i] == "--skip"]
    positive = [w for i, w in enumerate(words) if w != "--skip" and (i == 0 or words[i - 1] != "--skip")]
    return (not positive or any(p in name for p in positive)) and not any(s in name for s in skips)


class LiveAyGroupTests(unittest.TestCase):
    def test_every_batch_test_is_in_the_feature_gated_group(self):
        source = BRIDGE.read_text()
        batch = set(re.findall(r"fn (test_ay_batch_verify_\w+)\(", source))
        gated = set(GATE.findall(source))
        self.assertGreater(len(batch), 20, "the live-AY batch tests must be found")
        self.assertEqual(batch - gated, set(), "batch tests missing the live-ay gate")

    def test_the_feature_is_declared(self):
        self.assertRegex(MANIFEST.read_text(), r"(?m)^live-ay = \[\]$")

    def test_the_matrix_runs_the_group_in_its_own_shard_and_filters_it_elsewhere(self):
        batch = sorted(f"ay_bridge::tests::{name}" for name in GATE.findall(BRIDGE.read_text()))
        rows = plan_rows()
        live = rows.get("trust-cg-verify|lib-live-ay")
        self.assertIsNotNone(live, "the lib-live-ay shard")
        self.assertIn("--features live-ay", live[2])
        self.assertIn("--lib", live[2].split())
        self.assertEqual([name for name in batch if not libtest_selects(live[3], name)], [],
                         "the lib-live-ay shard must select every batch test")
        checked = 0
        for key, row in rows.items():
            if not key.startswith("trust-cg-verify|") or key.endswith("|lib-live-ay"):
                continue
            args = row[2].split()
            if not runs_lib_unit_tests(args) or "--all-features" in args or "live-ay" in row[2]:
                continue
            checked += 1
            # Any other shard that runs the library's unit tests must not select
            # the group, or it would count the group as ignored.
            with self.subTest(shard=key):
                self.assertEqual([name for name in batch if libtest_selects(row[3], name)], [], row)
        self.assertGreaterEqual(checked, 6, "the lib shards and the --tests integration shard")

    def test_the_filter_model_matches_libtest(self):
        self.assertTrue(libtest_selects("", "a::b"))
        self.assertTrue(libtest_selects("b", "a::b"), "a positive filter is a substring match")
        self.assertFalse(libtest_selects("c", "a::b"))
        self.assertFalse(libtest_selects("--skip a:: b", "a::b"), "--skip wins over a positive filter")
        self.assertTrue(libtest_selects("--skip c b", "a::b"))


if __name__ == "__main__":
    unittest.main()
