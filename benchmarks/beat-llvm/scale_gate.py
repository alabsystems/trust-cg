#!/usr/bin/env python3
"""benchmarks/beat-llvm/scale_gate.py — compile cost as a function of CRATE SIZE.

Why this exists
---------------
Every compile-axis number in this repo was historically measured on the
12-line programs in `progs/`. That turns out to hide the shape of the problem,
because trust-cg pays a large FIXED per-process cost (the ~440ms SHA-256 of the
124MB `clean` checker binary — see
docs/archive/session-reports/2026-08-31-compile-axis-is-the-checker-digest.md). On a
toy program that fixed cost IS the measurement; on a real crate it amortizes.

Measured 2026-08-31 (x86_64-apple-darwin, -O3, TCG_NO_PROOF_CERTS=1, min-of-5
wall, min-of-3 peak RSS), the picture is qualitatively different at each size:

    crate    lines    llvm     trust-cg   time      llvm RSS  tcg RSS   mem
    small      355    0.244s   0.976s     4.00x
    medium   2,805    0.670s   1.567s     2.34x
    large   11,205    2.260s   4.220s     1.87x     132.6MB   169.9MB   1.28x
    xlarge  33,605    6.950s  14.800s     2.13x     281.3MB   391.7MB   1.39x

Two recorded beliefs die here, and both died the same way -- by being measured
only on toy inputs:

  * "compile time is ~4.8x behind LLVM" -- that is the TOY number. The ratio
    falls to ~1.9x by 11k lines as the fixed cost amortizes, then flattens.
  * "compile memory is at exact parity with rustc-LLVM (70MB = 70MB)" -- also a
    toy artifact. At scale trust-cg is 1.28x and the ratio GROWS with crate
    size (~46KB of extra peak RSS per function), i.e. there is a real
    per-function retention that a 12-line program cannot show.

So: report BOTH ends. A single-size compile number is not a description of the
compiler, it is a description of one point on a curve.

The curve is also where quadratic behavior shows. On aarch64-apple-darwin on
2026-09-28 xlarge read 12.14x LLVM time and 25.35x peak RSS, because each crate's
`main` is ONE basic block with a call per function. The pre-RA scheduler's
call-barrier edges and three register-allocation scans were quadratic in that
block's call count. After the L14-P6 fixes, with byte-identical objects, the same
gate read 1.50x and 1.45x under a load of 8 to 12
(reports/perf/2026-09-28-darwin-scaling-l14p6/README.md).

Both lanes are INTERLEAVED rep-by-rep, not run one after the other. That is not
a detail: with sequential lanes, three runs of the same binaries reported xlarge
at 1.35x, 1.59x and 1.79x, because the llvm lane alone drifted 28% between them.
A ratio taken from two lanes that saw different machine states is not a ratio.

Usage
-----
    python3 scale_gate.py                 # all sizes, time only
    python3 scale_gate.py --rss           # add peak RSS (slower)
    python3 scale_gate.py --sizes large   # one size
    python3 scale_gate.py --pin-core      # Linux: pin both lanes to one core
    python3 scale_gate.py --target T      # another triple (default: the driver's host)

Both lanes compile for one target: the resolved Trust compiler's host triple
unless --target names another (the header prints which). The gate used to fix
x86_64-apple-darwin, so on any other host it requested a cross compile: on this
Apple silicon host the installed Trust package ships only the
aarch64-apple-darwin standard library, and every lane failed with E0463
(`can't find crate for std`) before a number was taken.

Peak RSS is `getrusage(RUSAGE_CHILDREN).ru_maxrss` from a single-child wrapper
(peak_rss.py, units normalised to bytes on every kernel); it previously parsed
BSD `/usr/bin/time -l` output only and so reported nothing on Linux. A wrapped
rep's wall time is the child's as the wrapper sees it, so the wrapper's own
start-up never enters a timed sample. Every run prints its provenance header:
the CPU model and feature digest (never a hostname), the `-C target-cpu`
policy both lanes were given, the core-affinity policy, and (with --rss) the
sampler's floor and its agreement with `/usr/bin/time`.

`TCG_NO_PROOF_CERTS=1` is currently REQUIRED to compile anything, because of the
upstream [TCG-PROOF-465] break (proof promotion rejects statistical-sampling
evidence). Remove it once that is fixed; the numbers above were taken with it.

Driver
------
The bridge pins channel = "trust", so both lanes use the Trust compiler that pin
names (the numbers above predate that pin and used the retired stock nightly).
scripts/trust_toolchain.py resolves the PATH trustc/targo package, or the package
trustc named by --driver, and refuses the retired stock nightly-2026-04-20 and
any unidentified compiler. Both lanes compile in Trust's explicit unverified
frontend lane (-Ztrust-verify=off), the vanilla frontend this gate always
measured; that lane is diagnostic and makes no Trust-verified compilation claim.
"""

import argparse
import importlib.util
import os
import subprocess
import sys
import tempfile
import time
from pathlib import Path

import hostinfo
import peak_rss

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
_TRUST_SPEC = importlib.util.spec_from_file_location(
    "trust_cg_trust_toolchain", REPO / "scripts" / "trust_toolchain.py")
TRUST_TOOLCHAIN = importlib.util.module_from_spec(_TRUST_SPEC)
_TRUST_SPEC.loader.exec_module(TRUST_TOOLCHAIN)
_BACKEND_SPEC = importlib.util.spec_from_file_location(
    "trust_cg_bridge_backend", REPO / "scripts" / "bridge_backend.py")
BRIDGE_BACKEND = importlib.util.module_from_spec(_BACKEND_SPEC)
_BACKEND_SPEC.loader.exec_module(BRIDGE_BACKEND)

# (name, function count). Each function is a 64-iteration loop over
# mul/xor/shift/rotate with a branch -- shaped to exercise the same lowering
# tiers the progs/ corpus does, but replicated so per-function cost dominates.
SIZES = [("small", 25), ("medium", 200), ("large", 800), ("xlarge", 2400)]


def generate(nfn: int) -> str:
    fns = []
    for i in range(nfn):
        seed = (i * 2654435761) % (1 << 32)
        fns.append(f"""
#[inline(never)]
fn f{i}(mut a: u64, b: u64) -> u64 {{
    let mut acc: u64 = a ^ {seed};
    let mut j: u64 = 0;
    while j < 64 {{
        acc = acc.wrapping_mul(6364136223846793005).wrapping_add(j ^ b);
        acc ^= acc >> 29;
        if acc % 7 == 0 {{ acc = acc.wrapping_add(a); }} else {{ acc ^= j; }}
        a = a.rotate_left(({i}+1) as u32 % 63);
        j += 1;
    }}
    acc
}}""")
    calls = " ^ ".join(f"f{i}(s, {i} as u64)" for i in range(nfn))
    return "\n".join(fns) + f"""
fn main() {{
    let s: u64 = 0x9E3779B97F4A7C15;
    let r = {calls};
    std::process::exit((r % 101) as i32);
}}
"""


def stale_backend_source(repo, dylib):
    """The fail-closed staleness rule run.py and compile_gate.py share
    (scripts/bridge_backend.py). A ratio measured against a backend older than
    the tree describes some other compiler: on 2026-09-16 the dylib on disk was
    517 commits behind HEAD, and without this check the tool would have
    reported it as current."""
    return BRIDGE_BACKEND.stale_source(repo, dylib)


def resolve_driver(explicit=None) -> dict:
    """The pinned Trust compiler record (see Driver above), or exit."""
    try:
        return TRUST_TOOLCHAIN.resolve(explicit)
    except TRUST_TOOLCHAIN.ToolchainError as error:
        sys.exit(f"scale_gate: cannot resolve the pinned Trust compiler: {error}")


def run_once(cmd, env, want_rss, measure=None):
    """Return (wall_seconds, peak_rss_bytes|None), or None if the compile failed.

    With `want_rss` the compile runs under peak_rss.measure: the wall time is
    the child's as the wrapper sees it (the wrapper's own start-up is not in
    it), and a compile that fails, is killed or yields no rusage record is a
    failure rather than a timing without memory.
    """
    if want_rss:
        sample = (measure or peak_rss.measure)(cmd, env=env)
        if sample.returncode != 0 or sample.wall_s is None:
            return None
        return sample.wall_s, sample.peak_rss_bytes
    t = time.perf_counter()
    p = subprocess.run(cmd, capture_output=True, env=env)
    wall = time.perf_counter() - t
    return (wall, None) if p.returncode == 0 else None


def resolve_target(explicit, driver):
    """(target triple, how it was selected): --target when given, else the
    resolved Trust compiler's host, the only target a native bridge build is
    known to load for. run.py and the shell gates select it the same way."""
    if explicit:
        return explicit, "explicit --target"
    host = (driver or {}).get("host")
    if not host:
        sys.exit("scale_gate: the resolved Trust compiler reported no host triple; "
                 "pass --target explicitly")
    return host, "driver host"


def lane_cmd(rustc, backend, name, tag, src, workdir, compiler_flags=(), target=None):
    """The trustc command for one lane: identical except the backend flag.

    `compiler_flags` are the resolved driver's own flags (the explicit
    unverified frontend lane); both lanes receive them identically. `target`
    is the triple both lanes compile for (see resolve_target)."""
    if not target:
        raise ValueError("lane_cmd needs the target triple both lanes compile for")
    return [rustc, *compiler_flags] + backend + [
        "--edition=2021", "--crate-type", "bin", "--target", target,
        "-Cpanic=abort", "-Copt-level=3",
        "-o", str(Path(workdir) / f"{name}.{tag}"), str(src)]


def provenance_lines(rustc, dylib, affinity, rss_check=None, host=None, *,
                     target, target_selection):
    """The provenance header printed before any number: the target and how it
    was selected, CPU identity (never a hostname), the CPU policy both lanes
    were given, affinity and RSS method."""
    host = host or hostinfo.host_provenance()
    policy = hostinfo.cpu_policy_from_cmds(
        lane_cmd(rustc, [], "probe", "llvm", "probe.rs", ".", target=target),
        lane_cmd(rustc, [f"-Zcodegen-backend={dylib}"], "probe", "llvm", "probe.rs", ".",
                 target=target))
    feats = host.get("cpu_features") or []
    lines = [
        f"target: {target} ({target_selection})",
        f"host: {host.get('host_model') or 'CPU model UNAVAILABLE'} "
        f"({host.get('host_model_source')}); machine {host.get('machine_model') or 'unknown'}; "
        f"{len(feats)} CPU features, sha256 {(host.get('cpu_features_sha256') or '')[:16] or 'n/a'}",
        f"cpu policy: -C target-cpu {policy['target_cpu']}, -C target-feature "
        f"{policy['target_feature']}; lane parity {policy['lane_parity']} "
        f"(flags differ only by {policy['bridge_extra_flags'] or 'nothing'}; the tcg lane "
        f"also passes -Ztrust-ir-cg-args=no-proof-certs)",
        f"affinity: {affinity['policy']}"
        + (f" core {affinity['core']} ({affinity['selection']})" if affinity.get("core") is not None
           else "")
        + f"; heterogeneous cores {affinity.get('heterogeneous')} ({affinity.get('topology_source')})",
    ]
    if rss_check is not None:
        lines.append(
            f"peak RSS: {peak_rss.METHOD}; ru_maxrss unit {peak_rss.maxrss_unit()}; sampler "
            f"floor {rss_check.get('sampler_floor_bytes')} B; /usr/bin/time agreement "
            f"{rss_check.get('agree')} (relative difference {rss_check.get('relative_difference')})")
    return lines


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dylib", default=str(
        BRIDGE_BACKEND.newest(REPO) or BRIDGE_BACKEND.candidates(REPO)[0]),
                    help="bridge backend (default: the newest built one for this host)")
    ap.add_argument("--driver", default=None,
                    help="explicit Trust package trustc (default: the PATH trustc/targo package)")
    ap.add_argument("--target", default=None,
                    help="target triple for both lanes (default: the resolved Trust "
                         "compiler's host)")
    ap.add_argument("--sizes", nargs="*", default=[n for n, _ in SIZES])
    ap.add_argument("--n", type=int, default=5, help="reps; the MINIMUM is reported")
    ap.add_argument("--rss", action="store_true", help="also report peak RSS")
    ap.add_argument("--allow-stale-dylib", action="store_true",
                    help="measure a dylib older than the backend sources (NOT evidence)")
    ap.add_argument("--pin-core", nargs="?", const="auto", default=None, metavar="CORE",
                    help="pin both lanes to one core (Linux sched_setaffinity); CORE omitted = "
                         "reports/perf/run_scaling.sh's highest-cpu_capacity core. An "
                         "unpinnable host is an error, never a silently unpinned run")
    args = ap.parse_args()

    driver = resolve_driver(args.driver)
    rustc = driver["compiler"]
    target, target_selection = resolve_target(args.target, driver)
    affinity = hostinfo.unpinned_record(hostinfo.core_topology())
    if args.pin_core is not None:
        try:
            affinity = hostinfo.pin_core(args.pin_core)
        except RuntimeError as error:
            sys.exit(f"scale_gate: --pin-core: {error}")

    if not Path(args.dylib).is_file():
        sys.exit(f"scale_gate: no bridge dylib at {args.dylib}\n"
                 f"  (cd {REPO}/crates/rustc-codegen-trust-cg && "
                 f"CARGO_TARGET_DIR=target-bridge RUSTC={rustc} {driver['targo']} "
                 f"--unverified build --release)")
    stale = stale_backend_source(REPO, Path(args.dylib))
    if stale is not None and not args.allow_stale_dylib:
        sys.exit(f"scale_gate: FATAL: dylib is STALE ({stale} is newer). Rebuild it, or pass\n"
                 f"  --allow-stale-dylib to measure anyway; such a row is NOT evidence, because\n"
                 f"  it attributes an older backend's cost to the current tree.")

    # Minimum, not median: this box is 4 cores and contention only ever ADDS
    # time, so the minimum is the robust estimator. A median here has been
    # measured to disagree with the minimum by 12 percentage points.
    print(f"driver: {TRUST_TOOLCHAIN.summary(driver)}")
    for line in provenance_lines(rustc, args.dylib, affinity,
                                 peak_rss.cross_check() if args.rss else None,
                                 target=target, target_selection=target_selection):
        print(line)
    print(f"compile wall = min-of-{args.n}, -O3, {target}"
          f"{', peak RSS = min-of-3' if args.rss else ''}\n")
    hdr = f"{'crate':>8} {'lines':>7} {'llvm':>9} {'trust-cg':>10} {'time':>7}"
    if args.rss:
        hdr += f" {'llvm RSS':>10} {'tcg RSS':>10} {'mem':>7}"
    print(hdr)

    with tempfile.TemporaryDirectory(prefix="tcg-scale-") as td:
        for name, nfn in SIZES:
            if name not in args.sizes:
                continue
            src = Path(td) / f"scale_{name}.rs"
            text = generate(nfn)
            src.write_text(text)
            lines = len(text.splitlines())

            # INTERLEAVE the lanes. Running llvm's N reps and then tcg's N reps
            # makes the ratio UNPAIRED: this box drifts up to ~17% over hours
            # and much more under load, so the two lanes see different machines.
            # Measured proof of the defect: three sequential-lane runs of the
            # SAME binaries reported xlarge at 1.35x, 1.59x and 1.79x, with the
            # llvm lane alone spanning 28%. Alternating rep-by-rep puts both
            # lanes under the same drift, so the ratio survives a busy box.
            # The trust-cg lane switches proof certificates off through the
            # backend's TRACKED knob option; trustc refuses the former
            # TCG_NO_PROOF_CERTS environment variable as an untracked codegen
            # control (every lane compile failed with it on 2026-09-22).
            specs = {
                "llvm": (dict(os.environ), []),
                "tcg": (dict(os.environ),
                        [f"-Zcodegen-backend={args.dylib}", "-Ztrust-ir-cg-args=no-proof-certs"]),
            }
            walls = {"llvm": [], "tcg": []}
            rsses = {"llvm": [], "tcg": []}
            failed = None
            for i in range(args.n):
                for tag, (env, backend) in specs.items():
                    cmd = lane_cmd(rustc, backend, name, tag, src, td, driver["compiler_flags"],
                                   target=target)
                    got = run_once(cmd, env, args.rss and i < 3)
                    if got is None:
                        failed = tag
                        break
                    walls[tag].append(got[0])
                    if got[1] is not None:
                        rsses[tag].append(got[1])
                if failed:
                    break
            if failed:
                print(f"{name:>8} {failed}: COMPILE FAILED")
                continue
            lanes = {t: (min(walls[t]), min(rsses[t]) if rsses[t] else None)
                     for t in ("llvm", "tcg")}

            lw, lr = lanes["llvm"]
            tw, tr = lanes["tcg"]
            row = f"{name:>8} {lines:>7} {lw:>8.3f}s {tw:>9.3f}s {tw/lw:>6.2f}x"
            if args.rss and lr and tr:
                row += (f" {lr/1048576:>9.1f}M {tr/1048576:>9.1f}M"
                        f" {tr/lr:>6.2f}x")
            print(row, flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
