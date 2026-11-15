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
# missing dylib, unresolvable toolchain).
#
# Driver: the bridge pins channel = "trust", so every compile uses the Trust
# compiler that pin names. scripts/trust_toolchain.py resolves the PATH
# trustc/targo package, or the package trustc named by --driver, and refuses the
# retired stock nightly-2026-04-20 and any unidentified compiler (exit 2).
# Compiles use Trust's explicit unverified frontend lane (-Ztrust-verify=off), the
# vanilla frontend this gate always drove; that lane is diagnostic and makes no
# Trust-verified compilation claim.

import argparse
import importlib.util
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import corpus  # noqa: E402

REPO = HERE.parent.parent
_TRUST_SPEC = importlib.util.spec_from_file_location(
    "trust_cg_trust_toolchain", REPO / "scripts" / "trust_toolchain.py")
TRUST_TOOLCHAIN = importlib.util.module_from_spec(_TRUST_SPEC)
_TRUST_SPEC.loader.exec_module(TRUST_TOOLCHAIN)
_BACKEND_SPEC = importlib.util.spec_from_file_location(
    "trust_cg_bridge_backend", REPO / "scripts" / "bridge_backend.py")
BRIDGE_BACKEND = importlib.util.module_from_spec(_BACKEND_SPEC)
_BACKEND_SPEC.loader.exec_module(BRIDGE_BACKEND)
OPT_LEVELS = ["0", "2", "3"]
COMPILE_TIMEOUT = 900


def stale_backend_source(repo, dylib):
    """run.py's fail-closed staleness rule, shared through scripts/bridge_backend.py
    (tests/benches/examples are not compiled into the cdylib)."""
    return BRIDGE_BACKEND.stale_source(repo, dylib)


def main():
    ap = argparse.ArgumentParser(description="54-compile bridge completeness gate")
    ap.add_argument("--dylib", type=Path,
                    default=BRIDGE_BACKEND.newest(REPO) or BRIDGE_BACKEND.candidates(REPO)[0],
                    help="bridge backend (default: the newest built one for this host)")
    ap.add_argument("--target", default=None,
                    help="target triple (default: the resolved Trust compiler's host)")
    ap.add_argument("--driver", default=None,
                    help="explicit Trust package trustc (default: the PATH trustc/targo package)")
    ap.add_argument("--allow-stale-dylib", action="store_true")
    ap.add_argument("--progs", nargs="*", default=None,
                    help="subset for smoke-testing the gate itself; a PASS on a "
                         "subset is NOT the completeness gate")
    args = ap.parse_args()

    try:
        manifest = corpus.load_programs(HERE / "progs")
    except corpus.CorpusError as error:
        print(f"compile-gate: FATAL: {error}", file=sys.stderr)
        return 2

    if not args.dylib.is_file():
        print(f"compile-gate: FATAL: dylib missing: {args.dylib}", file=sys.stderr)
        return 2
    stale = stale_backend_source(REPO, args.dylib)
    if stale is not None and not args.allow_stale_dylib:
        print(f"compile-gate: FATAL: dylib is STALE ({stale} is newer). Rebuild:\n"
              f"  (cd {REPO}/crates/rustc-codegen-trust-cg && CARGO_TARGET_DIR=target-bridge "
              f"RUSTC=<trust-package>/bin/trustc <trust-package>/bin/targo --unverified "
              f"build --release)", file=sys.stderr)
        return 2

    try:
        driver = TRUST_TOOLCHAIN.resolve(args.driver)
    except TRUST_TOOLCHAIN.ToolchainError as error:
        print(f"compile-gate: FATAL: cannot resolve the pinned Trust compiler: {error}",
              file=sys.stderr)
        return 2
    rustc = driver["compiler"]
    args.target = args.target or driver["host"]
    print(f"compile-gate: driver {TRUST_TOOLCHAIN.summary(driver)}; target {args.target}")

    progs = sorted(manifest)
    if args.progs:
        unknown = [p for p in args.progs if p not in progs]
        if unknown:
            print(f"compile-gate: FATAL: not in manifest: {unknown}", file=sys.stderr)
            return 2
        progs = sorted(args.progs)
        print(f"compile-gate: SUBSET run ({len(progs)}/{len(manifest)} programs) "
              f"— not the completeness gate")
    total = len(progs) * len(OPT_LEVELS)
    failures = []
    with tempfile.TemporaryDirectory(prefix="tcg-compile-gate-") as td:
        for prog in progs:
            src = HERE / "progs" / f"{prog}.rs"
            for opt in OPT_LEVELS:
                out = Path(td) / f"{prog}.o{opt}"
                cmd = [rustc, *driver["compiler_flags"], f"-Zcodegen-backend={args.dylib}",
                       "--edition=2021", "--crate-type", "bin",
                       *TRUST_TOOLCHAIN.target_arguments(driver, args.target), "-Cpanic=abort",
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
