#!/usr/bin/env python3
"""Independent reproduction: compiler peak RSS (harness sampler peak_rss.measure),
median of N interleaved samples, lanes llvm -O2 / base bridge / head bridge
(no-proof-certs, -O3), plus instructions retired is NOT measured here.
Usage: rss_ab.py <N> <base.dylib> <head.dylib> <src.rs>..."""
import os
import statistics
import subprocess
import sys
import tempfile
from pathlib import Path

W = Path("$HOME/trust-cg/.claude/worktrees/agent-workflow")
sys.path.insert(0, str(W / "benchmarks/beat-llvm"))
import peak_rss  # noqa: E402

TC = str(Path.home() / "Library/Application Support/aterm/pkg/store/trust/9192/bin/trustc")
E = Path(__file__).resolve().parent
n, base, head = int(sys.argv[1]), sys.argv[2], sys.argv[3]
srcs = [Path(s) for s in sys.argv[4:]]
os.environ["MACOSX_DEPLOYMENT_TARGET"] = "13.0"
os.environ.pop("RUSTUP_TOOLCHAIN", None)
COMMON = ["-Ztrust-verify=off", "--edition=2021", "--crate-type", "bin",
          "--target", "aarch64-apple-darwin", "-Cpanic=abort"]
MIB = 1 << 20


def lanes(src, out):
    return {
        "llvm_o2": [TC, *COMMON, "-Copt-level=2", "-o", str(out / "l2"), str(src)],
        "base": [TC, f"-Zcodegen-backend={base}", "-Ztrust-ir-cg-args=no-proof-certs", *COMMON,
                 "-Copt-level=3", "-o", str(out / "b"), str(src)],
        "head": [TC, f"-Zcodegen-backend={head}", "-Ztrust-ir-cg-args=no-proof-certs", *COMMON,
                 "-Copt-level=3", "-o", str(out / "h"), str(src)],
    }


print("load", os.getloadavg(), flush=True)
for src in srcs:
    with tempfile.TemporaryDirectory(dir=E) as tmp:
        cmds = lanes(src, Path(tmp))
        samples = {k: [] for k in cmds}
        for _ in range(n):
            for lane, cmd in cmds.items():
                s = peak_rss.measure(cmd, timeout=1800)
                samples[lane].append(s.peak_rss_bytes if s.returncode == 0 else None)
        med = {k: (statistics.median(v) / MIB if all(v) else None) for k, v in samples.items()}
        spread = {k: ((max(v) - min(v)) / statistics.median(v) if all(v) else None)
                  for k, v in samples.items()}
        print(f"{src.stem}: llvm_o2 {med['llvm_o2']:.1f}  base {med['base']:.1f}  head {med['head']:.1f} MiB"
              f"  | base x-O2 {med['base'] / med['llvm_o2']:.3f}  head x-O2 {med['head'] / med['llvm_o2']:.3f}"
              f"  delta {med['base'] - med['head']:.1f} MiB  spreads "
              + " ".join(f"{k}={v:.3f}" for k, v in spread.items())
              + "  raw " + str({k: [round(x / MIB, 1) for x in v] for k, v in samples.items()}),
              flush=True)
print("load", os.getloadavg(), flush=True)
