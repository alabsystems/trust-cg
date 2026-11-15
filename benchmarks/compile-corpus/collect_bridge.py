#!/usr/bin/env python3
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
"""Collect ordinary Rust programs, as the rustc bridge hands them to trust-cg.

    collect_bridge.py --dylib <librustc_codegen_trust_cg> [--driver trustc]

Each program is compiled by the Trust compiler with the trust-cg backend and
`-Ztrust-ir-cg-args=dump-trust-ir=DIR`, which writes every codegen unit's
TrustIR module (the exact input of its `Compiler::compile`) with a JSON sidecar
naming the settings the bridge used (target, opt level, panic strategy, proof
certificates). The whole directory becomes one corpus entry (origin
`rustc-bridge`) and `compile_corpus` compiles its modules in order.

Whether the program's own compile then succeeded does not matter here (on
aarch64-apple-darwin the production certificates-on lane refuses at proof
promotion, reports/perf/2026-09-28-darwin-aarch64-campaign): the dump is taken
before the object compile, and the corpus records its own verdicts.

Programs: the beat-llvm corpus (`benchmarks/beat-llvm/progs`), the formatting /
self-host corpus (`benchmarks/fmt-selfhost/progs`), the shape-coverage corpus
(`benchmarks/shape-coverage/progs`) and the scale gate's generated `medium`
program (200 replicated loop functions, `beat-llvm/scale_gate.py`).
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
PROGRAM_DIRS = [
    ("beat-llvm", REPO / "benchmarks/beat-llvm/progs", "2"),
    ("fmt-selfhost", REPO / "benchmarks/fmt-selfhost/progs", "2"),
    ("shape-coverage", REPO / "benchmarks/shape-coverage/progs", "2"),
]


def scale_gate_program(nfn: int) -> str:
    sys.path.insert(0, str(REPO / "benchmarks/beat-llvm"))
    spec = importlib.util.spec_from_file_location("scale_gate", REPO / "benchmarks/beat-llvm/scale_gate.py")
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module.generate(nfn)


def compile_with_dump(driver: str, dylib: Path, src: Path, opt: str, dump: Path) -> int:
    cmd = [driver, f"-Zcodegen-backend={dylib}", f"-Ztrust-ir-cg-args=dump-trust-ir={dump}",
           "-Ztrust-verify=off", "--edition=2021", "--crate-type", "bin",
           "--target", "aarch64-apple-darwin", "-Cpanic=abort", f"-Copt-level={opt}",
           "-o", str(dump.parent / "a.out"), str(src)]
    return subprocess.run(cmd, capture_output=True, text=True).returncode


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dylib", type=Path, required=True)
    ap.add_argument("--driver", default="trustc")
    ap.add_argument("--manifest", type=Path, default=HERE / "corpus.json")
    args = ap.parse_args()

    manifest = json.loads(args.manifest.read_text())
    keep = [e for e in manifest["entries"] if e["origin"] != "rustc-bridge"]
    out_root = HERE / "modules" / "bridge"
    if out_root.exists():
        shutil.rmtree(out_root)
    out_root.mkdir(parents=True)

    programs: list[tuple[str, Path, str]] = []
    for family, directory, opt in PROGRAM_DIRS:
        for src in sorted(directory.glob("*.rs")):
            programs.append((f"{family}/{src.stem}", src, opt))
    work = Path(tempfile.mkdtemp(prefix="tcg-bridge-corpus-"))
    scale_src = work / "scale_medium.rs"
    scale_src.write_text(scale_gate_program(200))
    programs.append(("scale-gate/medium", scale_src, "3"))

    new = []
    for name, src, opt in programs:
        dump = work / name.replace("/", "--") / "dump"
        dump.mkdir(parents=True)
        rc = compile_with_dump(args.driver, args.dylib, src, opt, dump)
        mods = sorted(dump.glob("*.trust_irbin"))
        if not mods:
            print(f"skip {name}: the bridge dumped no module (trustc exit {rc})", file=sys.stderr)
            continue
        dest = out_root / name.replace("/", "--")
        shutil.copytree(dump, dest)
        new.append({
            "name": f"rustc-bridge/{name}",
            "file": str(dest.relative_to(HERE)),
            "origin": "rustc-bridge",
            "opt_level": {"2": "O2", "3": "O3"}[opt],
            "lanes": ["aot-object", "aot-proofs"],
            "provenance": {
                "source": str(src.relative_to(REPO)) if src.is_relative_to(REPO) else
                "benchmarks/beat-llvm/scale_gate.py generate(200)",
                "rustc_flags": f"-Copt-level={opt} -Cpanic=abort --target aarch64-apple-darwin",
                "bridge_exit": rc,
                "modules": len(mods),
            },
        })
        print(f"{name}: {len(mods)} modules (trustc exit {rc})", file=sys.stderr, flush=True)
    shutil.rmtree(work, ignore_errors=True)
    manifest["entries"] = keep + new
    args.manifest.write_text(json.dumps(manifest, indent=1) + "\n")
    print(f"{len(new)} rustc-bridge entries")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
