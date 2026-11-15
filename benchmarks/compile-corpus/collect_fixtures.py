#!/usr/bin/env python3
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
"""Collect the in-repository (non-TY) modules into the compile corpus.

    collect_fixtures.py --bin <compile_corpus>

* ay-jit-matrix: the jit-matrix workload modules built in process by
  trust-cg-jit-matrix (the ay BCP propagation kernels and the parent loop),
  written with `compile_corpus dump-builtin`.
* trust-cg-fixture: TrustIR test fixtures of this repository (real-function
  fsym corpus, aggregate/ABI corpora, fuzz programs), re-encoded as the binary
  container with `compile_corpus rebin` so every corpus file is read by one
  decoder. A fixture the pinned trust-ir can no longer read is skipped and
  named on stderr.

Every copy is taken once and committed: a later edit of the source fixture does
not silently change the corpus a committed baseline was measured on.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]

BUILTINS = [
    "bcp-propagate",
    "bcp-propagate-with-decisions",
    "bcp-watched-literal",
    "bcp-watched-literal-chunked",
    "parent-loop",
]
FIXTURE_GLOBS = [
    "crates/trust-cg-verify/tests/fixtures/fsym_real_function_corpus/*.trust_ir.json",
    "crates/trust-cg-codegen/tests/fixtures/aggregate_insert/*.trust_ir",
    "crates/trust-cg-codegen/tests/fixtures/large_aggregate_args/*.trust_ir",
    "crates/trust-cg-codegen/tests/fixtures/hfa_zero_sized/*.trust_ir",
    "scripts/fuzz/*.trust_ir",
]


def slug(path: Path) -> str:
    name = path.name.replace(".trust_ir.json", "").replace(".trust_ir", "")
    return f"{path.parent.name}--{name}"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--bin", required=True)
    ap.add_argument("--manifest", type=Path, default=HERE / "corpus.json")
    args = ap.parse_args()

    if args.manifest.exists():
        manifest = json.loads(args.manifest.read_text())
    else:
        manifest = {"schema": "trust-cg.compile-corpus.manifest.v1", "entries": []}
    keep = [e for e in manifest["entries"] if e["origin"] not in ("ay-jit-matrix", "trust-cg-fixture")]
    new = []

    out = HERE / "modules" / "jit-matrix"
    out.mkdir(parents=True, exist_ok=True)
    for name in BUILTINS:
        rel = Path("modules") / "jit-matrix" / f"{name}.trust_irbin"
        subprocess.run([args.bin, "dump-builtin", "--module", name, "--out", str(HERE / rel)], check=True)
        new.append({"name": f"ay-jit-matrix/{name}", "file": str(rel), "origin": "ay-jit-matrix",
                    "opt_level": "O2", "lanes": ["jit-raw", "jit-raw-checked", "aot-object"],
                    "provenance": {"builder": f"compile_corpus dump-builtin --module {name}"}})

    out = HERE / "modules" / "fixtures"
    out.mkdir(parents=True, exist_ok=True)
    for pattern in FIXTURE_GLOBS:
        for src in sorted(REPO.glob(pattern)):
            rel = Path("modules") / "fixtures" / f"{slug(src)}.trust_irbin"
            p = subprocess.run([args.bin, "rebin", "--input", str(src), "--out", str(HERE / rel)],
                               capture_output=True, text=True)
            if p.returncode != 0:
                print(f"skip {src.relative_to(REPO)}: {p.stderr.strip()[:200]}", file=sys.stderr)
                continue
            new.append({"name": f"trust-cg-fixture/{slug(src)}", "file": str(rel), "origin": "trust-cg-fixture",
                        "opt_level": "O2", "lanes": ["jit-raw", "jit-raw-checked", "aot-object"],
                        "provenance": {"source": str(src.relative_to(REPO))}})

    manifest["entries"] = new + keep
    args.manifest.write_text(json.dumps(manifest, indent=1) + "\n")
    print(f"{len(new)} non-TY entries; {len(keep)} other entries kept")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
