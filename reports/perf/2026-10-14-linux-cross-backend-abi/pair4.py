#!/usr/bin/env python3
"""Build a callee.rs / caller.rs pair in all four LLVM / bridge pairings at the
given levels and run each binary; the program exits 42 when its values are
right.

usage: pair4.py DIR BACKEND LEVELS [--trustc PATH]
  DIR      holds callee.rs and caller.rs; work-O<n> directories are created in it
  BACKEND  the bridge backend (librustc_codegen_trust_cg.so)
  LEVELS   comma-separated optimization levels, e.g. 0,1,2,3

The trust-cg halves use the cross-backend runner's flags: Trust's unverified
frontend lane with proof certificates and the refinement solver off.
"""
import argparse
import subprocess
from pathlib import Path

FLAGS = ["-Ztrust-verify=off", "--edition=2021", "-Cpanic=abort", "-Ccodegen-units=1", "-Awarnings"]
KNOBS = ["-Ztrust-ir-cg-args=no-proof-certs", "-Ztrust-ir-cg-args=refine-solver=0"]

parser = argparse.ArgumentParser()
parser.add_argument("dir", type=Path)
parser.add_argument("backend")
parser.add_argument("levels")
parser.add_argument("--trustc", default="trustc")
args = parser.parse_args()


def build(src, kind, opt, crate_type, out, lib=None):
    cmd = [args.trustc, *FLAGS, f"-Copt-level={opt}", "--crate-type", crate_type]
    if kind == "tcg":
        cmd += [f"-Zcodegen-backend={args.backend}", *KNOBS]
    cmd += ["--out-dir", str(out)] if crate_type == "rlib" else ["-o", str(out)]
    if lib:
        cmd += ["-L", str(lib)]
    cmd.append(str(src))
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=600)
    return result.returncode, result.stderr


for opt in (int(level) for level in args.levels.split(",")):
    work = args.dir / f"work-O{opt}"
    work.mkdir(exist_ok=True)
    for callee in ("llvm", "tcg"):
        (work / f"callee-{callee}").mkdir(exist_ok=True)
        code, err = build(args.dir / "callee.rs", callee, opt, "rlib", work / f"callee-{callee}")
        if code:
            print(f"O{opt} callee-{callee} build rc={code}: {err[-600:]}")
    for caller in ("llvm", "tcg"):
        for callee in ("llvm", "tcg"):
            binary = work / f"bin-{caller}-{callee}"
            code, err = build(args.dir / "caller.rs", caller, opt, "bin", binary, work / f"callee-{callee}")
            if code:
                print(f"O{opt} caller={caller} callee={callee}: build rc={code}: {err[-600:]}")
                continue
            run = subprocess.run([str(binary)], capture_output=True, text=True, timeout=30)
            print(f"O{opt} caller={caller:4} callee={callee:4}: exit {run.returncode} out {run.stdout.strip()!r}")
