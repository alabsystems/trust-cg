#!/usr/bin/python3
"""Record each real std-workspace compiler invocation and its explicit backend."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

config = json.loads(Path(os.environ["STD_CORRECTNESS_CONFIG"]).read_text())
args = sys.argv[1:]
def values(option):
    return [args[i + 1] for i, arg in enumerate(args) if arg == option] + [arg.split("=", 1)[1] for arg in args if arg.startswith(option + "=")]
names, targets = values("--crate-name"), values("--target")
assert len(names) <= 1 and len(targets) <= 1, "duplicate compiler crate/target option"
name = names[0] if names else "probe"
target = targets[0] if targets else None
printing = any(arg == "--print" or arg.startswith("--print=") for arg in args)
source_files = [arg for arg in args[1:] if arg.endswith(".rs")]
is_probe = (not names and not source_files and any(arg in {"-vV", "-V", "--version"} for arg in args)) or (name == "___" and printing and not source_files)
assert not printing or is_probe, "a --print-marked actual Rust crate may not bypass full-CG admission"
assert target is None or target == config["target"], "compiler invocation target differs from configured target"
target_crate = not is_probe and target is not None
lane = config["lane"]
cg = target_crate and (lane in {"full-cg", "full-cg-proof"} or (lane == "mixed" and name in {"core", "alloc"}))
if cg:
    assert not any("codegen-backend" in arg for arg in args)
    knobs = "diag-json" + ("" if lane == "full-cg-proof" else " no-proof-certs")
    args += ["-Zcodegen-backend=" + config["backend"]["path"], "-Ztrust-ir-cg-args=" + knobs]
if target_crate:
    # This advisory frontend lane keeps rustc's canonical generic export list.
    # An unverified CG build without it withholds that list, so downstream
    # crates can silently instantiate LLVM copies instead of calling CG code.
    args += ["-Ztrust-ir-lower=on", "-Copt-level=" + str(config["opt"])]
records = Path(config["invocations"])
records.mkdir(exist_ok=True)
stem = records / f"{name}-{os.getpid()}-{time.time_ns()}"
env = {k: v for k, v in os.environ.items() if not k.startswith("STD_CORRECTNESS_")}
selected = {k: v for k, v in env.items() if k.startswith(("CARGO_", "CFG_", "STD_ENV_")) or k in {"PATH", "LD_LIBRARY_PATH", "RUSTC", "RUSTC_BOOTSTRAP", "RUSTUP_TOOLCHAIN", "RUSTDOC", "OUT_DIR", "TARGET", "HOST", "OPT_LEVEL", "DEBUG", "PROFILE", "RUST_MIN_STACK"}}
record = {"schema": "trust-cg.std-compiler-invocation.v1", "command": args,
          "cwd": os.getcwd(), "crate": name, "target": target,
          "target_crate": target_crate, "backend": "cg" if cg else "llvm",
          "canonical_query_providers_requested": target_crate,
          "environment": selected, "complete": False}
record_path = stem.with_suffix(".json")
record_path.write_text(json.dumps(record, indent=2) + "\n")
started = time.monotonic()
with stem.with_suffix(".stdout.log").open("wb") as stdout, stem.with_suffix(".stderr.log").open("wb") as stderr:
    proc = subprocess.run(args, env=env, stdout=stdout, stderr=stderr)
record.update(complete=True, returncode=proc.returncode, wall_seconds=time.monotonic() - started)
for suffix in [".stdout.log", ".stderr.log"]:
    path = stem.with_suffix(suffix)
    record[suffix[1:] + "_sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
record_path.write_text(json.dumps(record, indent=2) + "\n")
with stem.with_suffix(".stdout.log").open("rb") as stream:
    shutil.copyfileobj(stream, sys.stdout.buffer)
with stem.with_suffix(".stderr.log").open("rb") as stream:
    shutil.copyfileobj(stream, sys.stderr.buffer)
raise SystemExit(proc.returncode)
