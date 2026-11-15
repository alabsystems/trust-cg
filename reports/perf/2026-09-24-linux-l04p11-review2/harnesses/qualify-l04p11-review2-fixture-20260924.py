#!/usr/bin/env python3
"""L04-P11 second review repair: re-run after the walk-query golden fix.

The harness `qualify-l04p11-review2-20260924.py` found at `02b3f18d7` that
`function_verifier::walk_query_resolution_golden` still pinned the two TPREL
queries the repair removed. `fa9144ea1` regenerates that fixture. From a clean
checkout of it, this re-runs `trust-cg-verify --lib -- --skip ay_bridge` and
the decoded-value/verifier/gate/database subsets with the same environment and
capture format, and records HEAD, tree and status before and after in
`records/source-after-fixture.json`.

Usage: qualify-l04p11-review2-fixture-20260924.py <out-dir>
"""

from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("review2", HERE / "qualify-l04p11-review2-20260924.py")
review2 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review2)


def main() -> int:
    git = review2.git
    before = {"head": git("rev-parse", "HEAD"), "tree": git("rev-parse", "HEAD^{tree}"),
              "status_porcelain": git("status", "--porcelain", "--untracked-files=all")}
    if before["status_porcelain"]:
        print("source is dirty; refusing", file=sys.stderr)
        return 2
    cargo = review2.cargo
    review2.run("after-fixture--verify_lib_subsets",
                cargo("-p", "trust-cg-verify", "--lib", "--", "aarch64_value_decode", "function_verifier::",
                      "coverage_gate", "proof_database"))
    review2.run("after-fixture--verify_lib_without_ay_bridge",
                cargo("-p", "trust-cg-verify", "--lib", "--", "--skip", "ay_bridge"), expect="fail")
    after = {"head": git("rev-parse", "HEAD"), "tree": git("rev-parse", "HEAD^{tree}"),
             "status_porcelain": git("status", "--porcelain", "--untracked-files=all")}
    (review2.RECORDS / "source-after-fixture.json").write_text(
        json.dumps({"before": before, "after": after}, indent=2) + "\n")
    return 0 if before == after else 3


if __name__ == "__main__":
    sys.exit(main())
