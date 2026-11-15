#!/usr/bin/env python3
"""Byte identity of emitted code, baseline vs candidate backend.

For every corpus program and scale-gate crate: compile with each backend in the
no-proof-certs lane (the only lane that compiles on this host) and compare the
linked image's section digest (emitted_size.image_digest) plus every object
the compile wrote (-C save-temps keeps them); and compile in the production
lane (default knobs), where every program is refused, and compare the
refusal's stderr with temp paths normalized. Prints one line per input and a
summary; exit 1 on any difference."""
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

W = Path("$HOME/trust-cg/.claude/worktrees/agent-workflow")
S = Path("$SCRATCH/l14p10")
sys.path.insert(0, str(W / "benchmarks/beat-llvm"))
import emitted_size  # noqa: E402

TC = str(Path.home() / "Library/Application Support/aterm/pkg/store/trust/9192/bin/trustc")
BASE, CAND = sys.argv[1], sys.argv[2]
env = dict(os.environ, MACOSX_DEPLOYMENT_TARGET="13.0")
COMMON = ["-Ztrust-verify=off", "--edition=2021", "--crate-type", "bin",
          "--target", "aarch64-apple-darwin", "-Cpanic=abort", "-Copt-level=3"]
inputs = sorted((W / "benchmarks/beat-llvm/progs").glob("*.rs"))
if "--scale" in sys.argv:
    inputs = [S / "scale" / f"{n}.rs" for n in ("small", "medium", "large", "xlarge")]


def compile_lane(dylib, src, knobs, workdir):
    out = workdir / src.stem
    cmd = [TC, f"-Zcodegen-backend={dylib}", *[f"-Ztrust-ir-cg-args={k}" for k in knobs],
           *COMMON, "-C", "save-temps", "-o", str(out), str(src)]
    r = subprocess.run(cmd, capture_output=True, text=True, env=env, cwd=workdir, timeout=1800)
    objects = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
               for p in sorted(workdir.glob("*.o"))}
    image = emitted_size.image_digest(out) if r.returncode == 0 and out.exists() else None
    stderr = re.sub(re.escape(str(workdir)), "<dir>", r.stderr)
    stderr = re.sub(r"rustc[A-Za-z0-9]{6}", "rustcXXXXXX", stderr)
    stderr = re.sub(r"\d+(\.\d+)?ms", "<ms>", stderr)
    return r.returncode, image, objects, stderr


differences = 0
for src in inputs:
    row = {}
    for lane, knobs in (("diag", ["no-proof-certs"]), ("prod", [])):
        results = []
        for dylib in (BASE, CAND):
            with tempfile.TemporaryDirectory(dir=S) as tmp:
                results.append(compile_lane(dylib, src, knobs, Path(tmp)))
        (rc_a, img_a, obj_a, err_a), (rc_b, img_b, obj_b, err_b) = results
        same = rc_a == rc_b and img_a == img_b and obj_a == obj_b and err_a == err_b
        row[lane] = {"rc": rc_a, "same": same, "objects": len(obj_a),
                     "image": (img_a or "-")[:12]}
        if not same:
            differences += 1
            row[lane]["detail"] = {
                "rc": [rc_a, rc_b], "image": [img_a, img_b],
                "objects_differ": sorted(k for k in set(obj_a) | set(obj_b) if obj_a.get(k) != obj_b.get(k)),
                "stderr_equal": err_a == err_b,
            }
            if err_a != err_b:
                (S / f"stderr-{src.stem}-{lane}-a.txt").write_text(err_a)
                (S / f"stderr-{src.stem}-{lane}-b.txt").write_text(err_b)
    print(src.stem, json.dumps(row), flush=True)
print("differences:", differences)
sys.exit(1 if differences else 0)
