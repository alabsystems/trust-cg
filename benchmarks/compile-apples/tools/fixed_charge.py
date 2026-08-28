#!/usr/bin/env python3
"""Fixed per-process charge today: empty `fn main(){}` under LLVM, the bridge,
the bridge with proofs off (TCG_NO_PROOF_CERTS=1) and without the speculative
init sweep. Interleaved, N rounds, min and median wall + child user/sys CPU.
usage: fixed_charge.py N DYLIB"""
import atexit, os, subprocess, sys, time, statistics, resource, tempfile, shutil
n = int(sys.argv[1]); dylib = sys.argv[2]
if n < 1:
    raise SystemExit("N must be at least 1")
home = os.path.expanduser("~")
os.environ["PATH"] = f"{home}/.cargo/bin:{home}/.rustup/toolchains/stable-aarch64-unknown-linux-gnu/lib/rustlib/aarch64-unknown-linux-gnu/bin/gcc-ld:" + os.environ.get("PATH", "")
rustc = subprocess.check_output(["rustup", "which", "--toolchain", "nightly-2026-04-20", "rustc"], text=True).strip()
flags = ["--edition=2021", "--crate-type", "bin", "--target", "aarch64-unknown-linux-gnu", "-Cpanic=abort", "-Copt-level=3"]
d = tempfile.mkdtemp()
atexit.register(shutil.rmtree, d, ignore_errors=True)
src = os.path.join(d, "empty.rs")
with open(src, "w", encoding="utf-8") as source:
    source.write("fn main() {}\n")
lanes = [("llvm", [], {}), ("bridge", [f"-Zcodegen-backend={dylib}"], {}),
         ("bridge no-certs", [f"-Zcodegen-backend={dylib}"], {"TCG_NO_PROOF_CERTS": "1"}),
         ("bridge no-spec-sweep", [f"-Zcodegen-backend={dylib}"], {"TCG_NO_SPECULATIVE_SWEEP": "1"})]
res = {name: [] for name, _, _ in lanes}
for _ in range(n):
    for name, extra, env in lanes:
        e = dict(os.environ, **env)
        r0 = resource.getrusage(resource.RUSAGE_CHILDREN); t0 = time.monotonic()
        subprocess.run([rustc] + extra + flags + [src, "-o", os.path.join(d, "out")], env=e, check=True, capture_output=True)
        t1 = time.monotonic(); r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
        res[name].append(((t1 - t0) * 1000, (r1.ru_utime - r0.ru_utime) * 1000, (r1.ru_stime - r0.ru_stime) * 1000))
print(f"{'lane':22s} {'wall min':>9s} {'wall med':>9s} {'user med':>9s} {'sys med':>8s}")
for name, _, _ in lanes:
    w = [x[0] for x in res[name]]; u = [x[1] for x in res[name]]; s = [x[2] for x in res[name]]
    print(f"{name:22s} {min(w):9.1f} {statistics.median(w):9.1f} {statistics.median(u):9.1f} {statistics.median(s):8.1f}")
