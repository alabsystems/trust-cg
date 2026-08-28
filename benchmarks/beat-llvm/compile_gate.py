#!/usr/bin/env python3
# benchmarks/beat-llvm/compile_gate.py — the COMPLETENESS gate.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
#
# Compiles every manifest program through the bridge at O0/O2/O3 (18 x 3 = 54)
# and fails if ANY compile fails. This is deliberately separate from run.py:
# run.py judges CORRECTNESS and PERFORMANCE of what compiles; this gate exists
# because a change can be perfectly correct on the programs it still admits
# while silently failing closed on others (the cfa78287 class: bridge->LEA
# emitted PRegs pre-RA and 7/18 programs refused to compile — every emitted
# binary was correct, the SUITE was broken). Run it before landing any
# admission/emission change.
#
# The gate previously lived in a session scratchpad and kept evaporating with
# the session; it lives in-repo now.
#
# Usage:
#   python3 compile_gate.py                # default dylib + repo layout
#   python3 compile_gate.py --allow-stale-dylib   # NOT evidence
#
# Exit codes: 0 = 54/54, 1 = at least one refusal, 2 = environment (stale or
# missing dylib, unknown toolchain).

import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
TOOLCHAIN = "nightly-2026-04-20"
OPT_LEVELS = ["0", "2", "3"]
COMPILE_TIMEOUT = 900


def stale_backend_source(repo, dylib):
    """Mirror of run.py's fail-closed staleness rule (tests/benches/examples
    are not compiled into the cdylib and cannot make it stale)."""
    mtime = dylib.stat().st_mtime
    for src in (repo / "crates").rglob("*.rs"):
        path = str(src)
        if "/target" in path:
            continue
        if any(f"/{d}/" in path for d in ("tests", "benches", "examples")):
            continue
        try:
            if src.stat().st_mtime > mtime:
                return src
        except OSError:
            continue
    return None


def main():
    ap = argparse.ArgumentParser(description="54-compile bridge completeness gate")
    ap.add_argument("--dylib", type=Path,
                    default=REPO / "crates/rustc-codegen-trust-cg/target-bridge/release/librustc_codegen_trust_cg.dylib")
    ap.add_argument("--target", default="x86_64-apple-darwin")
    ap.add_argument("--allow-stale-dylib", action="store_true")
    ap.add_argument("--progs", nargs="*", default=None,
                    help="subset for smoke-testing the gate itself; a PASS on a "
                         "subset is NOT the completeness gate")
    args = ap.parse_args()

    if not args.dylib.is_file():
        print(f"compile-gate: FATAL: dylib missing: {args.dylib}", file=sys.stderr)
        return 2
    stale = stale_backend_source(REPO, args.dylib)
    if stale is not None and not args.allow_stale_dylib:
        print(f"compile-gate: FATAL: dylib is STALE ({stale} is newer). Rebuild:\n"
              f"  (cd {REPO}/crates/rustc-codegen-trust-cg && "
              f"CARGO_TARGET_DIR=target-bridge cargo build --release)", file=sys.stderr)
        return 2

    r = subprocess.run(["rustup", "which", "--toolchain", TOOLCHAIN, "rustc"],
                       capture_output=True, text=True)
    if r.returncode != 0:
        print(f"compile-gate: FATAL: toolchain {TOOLCHAIN} not found", file=sys.stderr)
        return 2
    rustc = r.stdout.strip()

    manifest = json.load(open(HERE / "progs" / "manifest.json"))
    progs = sorted(manifest["programs"])
    if args.progs:
        unknown = [p for p in args.progs if p not in progs]
        if unknown:
            print(f"compile-gate: FATAL: not in manifest: {unknown}", file=sys.stderr)
            return 2
        progs = sorted(args.progs)
        print(f"compile-gate: SUBSET run ({len(progs)}/{len(manifest['programs'])} programs) "
              f"— not the completeness gate")
    total = len(progs) * len(OPT_LEVELS)
    failures = []
    with tempfile.TemporaryDirectory(prefix="tcg-compile-gate-") as td:
        for prog in progs:
            src = HERE / "progs" / f"{prog}.rs"
            for opt in OPT_LEVELS:
                out = Path(td) / f"{prog}.o{opt}"
                cmd = [rustc, f"-Zcodegen-backend={args.dylib}",
                       "--edition=2021", "--crate-type", "bin",
                       "--target", args.target, "-Cpanic=abort",
                       f"-Copt-level={opt}", "-o", str(out), str(src)]
                try:
                    c = subprocess.run(cmd, capture_output=True, text=True,
                                       timeout=COMPILE_TIMEOUT)
                except subprocess.TimeoutExpired:
                    failures.append((prog, opt, "TIMEOUT"))
                    print(f"  FAIL {prog} -O{opt}: timeout", flush=True)
                    continue
                if c.returncode != 0:
                    errl = [l for l in c.stderr.splitlines() if l.startswith("error")]
                    msg = (errl[0] if errl else c.stderr.strip()[-200:])[:200]
                    failures.append((prog, opt, msg))
                    print(f"  FAIL {prog} -O{opt}: {msg}", flush=True)
                else:
                    print(f"  ok   {prog} -O{opt}", flush=True)
    passed = total - len(failures)
    print(f"compile-gate: {passed}/{total}")
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
