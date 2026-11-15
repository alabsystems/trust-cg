#!/usr/bin/env python3
"""Qualifying run for ledger L01-P7 (f16 scalar and f16 HFA ABI) on Linux AArch64.

Usage: qualify-f16-abi-20260923.py <repo-root> <out-dir> <probe-dir>

Requires a clean tree (tracked and untracked) before and after. Runs, with
PATH led by the pinned AY/Clean package and ambient TCG_*/TRUST_CG_* removed:

  1. cargo test --test e2e_aarch64_f16_abi_linux (--show-output, one thread)
     with TCG_F16_ABI_RETAIN pointing at <out-dir>/retained;
  2. the four existing f16 natives (premise re-check);
  3. the InsertField shared-storage reproducer through the repository CLI
     (trust-ir text, O0 and O2, i64/f32/f16 pairs), whose non-zero exits are
     the recorded finding;
  4. the DarwinPCS/AAPCS64 HFA stack-placement probe with stock rustc 1.97.1
     (no_core crate, RUSTC_BOOTSTRAP=1, --emit=asm) for both triples;
  5. llvm-objdump -dr of the retained baseline and explicit-fp16 O2 objects.

Stages <out-dir>/archive (records, gzip-compressed objects and logs, this
harness) for copying into reports/perf; README.md and inventory.json are
written afterwards. Nothing here is a proof.
"""

from __future__ import annotations

import ctypes
import datetime
import gzip
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(sys.argv[1]).resolve()
OUT = Path(sys.argv[2]).resolve()
PROBE = Path(sys.argv[3]).resolve()
ARCHIVE = OUT / "archive"
RECORDS = ARCHIVE / "records"
COMMANDS = RECORDS / "commands"
PACKAGE_BIN = Path.home() / ".local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23/bin"


def now() -> str:
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(*args: str) -> str:
    return subprocess.run(["git", *args], cwd=ROOT, check=True, capture_output=True, text=True).stdout


def environment() -> dict[str, str]:
    env = {k: v for k, v in os.environ.items() if not k.startswith(("TCG_", "TRUST_CG_"))}
    env["PATH"] = f"{PACKAGE_BIN}:{Path.home() / '.cargo/bin'}:{env.get('PATH', '')}"
    return env


def run(name: str, argv: list[str], cwd: Path, env: dict[str, str], gz: bool = False) -> dict:
    start = now()
    proc = subprocess.run(argv, cwd=cwd, env=env, capture_output=True)
    end = now()
    log = proc.stdout + (b"\n--- stderr ---\n" + proc.stderr if proc.stderr else b"")
    path = COMMANDS / (f"{name}.log.gz" if gz else f"{name}.log")
    path.write_bytes(gzip.compress(log, mtime=0) if gz else log)
    relevant = {k: env[k] for k in sorted(env) if k in ("PATH", "RUSTC_BOOTSTRAP", "TCG_F16_ABI_RETAIN", "RUST_MIN_STACK")}
    capture = {
        "argv": argv, "cwd": str(cwd), "environment": relevant, "start_utc": start,
        "end_utc": end, "returncode": proc.returncode, "log": path.name,
        "log_sha256": sha256(log), "log_bytes": len(log),
    }
    (COMMANDS / f"{name}.capture.json").write_text(json.dumps(capture, indent=2) + "\n")
    return {"returncode": proc.returncode, "stdout": proc.stdout.decode(errors="replace")}


def tool(path: str, *version: str) -> dict:
    resolved = shutil.which(path) or path
    real = os.path.realpath(resolved)
    line = subprocess.run([resolved, *version], capture_output=True, text=True)
    return {
        "path": resolved, "realpath": real, "sha256": sha256(Path(real).read_bytes()),
        "version": (line.stdout or line.stderr).splitlines()[0] if (line.stdout or line.stderr) else "",
    }


def main() -> int:
    if OUT.exists():
        shutil.rmtree(OUT)
    COMMANDS.mkdir(parents=True)
    status_before = git("status", "--porcelain", "--untracked-files=all")
    if status_before:
        print("tree is not clean:\n" + status_before)
        return 2
    lock = (ROOT / "Cargo.lock").read_text()
    trust_ir = re.search(r'name = "trust-ir"\nversion = "[^"]+"\nsource = "[^"]*#([0-9a-f]+)"', lock)
    source = {
        "head": git("rev-parse", "HEAD").strip(), "tree": git("rev-parse", "HEAD^{tree}").strip(),
        "trust_ir_pin": trust_ir.group(1) if trust_ir else None, "status_before": status_before,
    }
    env = environment()
    libc = ctypes.CDLL(None)
    libc.getauxval.restype = ctypes.c_ulong
    hwcap = libc.getauxval(16)
    features = next(line for line in Path("/proc/cpuinfo").read_text().splitlines() if line.startswith("Features"))
    host = {
        "uname": subprocess.run(["uname", "-a"], capture_output=True, text=True).stdout.strip(),
        "glibc": subprocess.run(["ldd", "--version"], capture_output=True, text=True).stdout.splitlines()[0],
        "at_hwcap": hex(hwcap), "hwcap_fphp": bool(hwcap & (1 << 9)), "hwcap_asimdhp": bool(hwcap & (1 << 10)),
        "cpuinfo_features": features,
    }
    tools = {
        "cc": tool("cc", "--version"), "ld": tool("ld", "--version"),
        "llvm-objdump": tool(str(Path.home() / ".local/bin/llvm-objdump"), "--version"),
        "cargo": tool(str(Path.home() / ".cargo/bin/cargo"), "--version"),
        "rustc": tool(str(Path.home() / ".cargo/bin/rustc"), "--version"),
        "ay": tool(str(PACKAGE_BIN / "ay"), "--version"),
        "python3": tool(sys.executable, "--version"),
    }
    results: dict = {"commands": {}}
    retained = OUT / "retained"
    cargo = [str(Path.home() / ".cargo/bin/cargo"), "test", "-p", "trust-cg-codegen", "--locked", "--offline", "-j", "8"]

    target_env = dict(env, TCG_F16_ABI_RETAIN=str(retained))
    r = run("f16_abi_linux", cargo + ["--test", "e2e_aarch64_f16_abi_linux", "--", "--show-output", "--test-threads=1"], ROOT, target_env)
    results["commands"]["f16_abi_linux"] = {
        "returncode": r["returncode"],
        "summary": re.findall(r"^test result: .*$", r["stdout"], re.M),
        "lines": [l for l in r["stdout"].splitlines() if re.match(r"(baseline|explicit-fp16)-O\d:|native f16 ABI|placement:|controls:|fp16 |fp16-", l)],
    }
    for target in ("e2e_aarch64_f16_scalar", "e2e_aarch64_f16_fcvt", "e2e_aarch64_f16_to_i128", "e2e_aarch64_i128_to_f16"):
        r = run(target, cargo + ["--test", target, "--", "--show-output", "--test-threads=1"], ROOT, env)
        results["commands"][target] = {"returncode": r["returncode"], "summary": re.findall(r"^test result: .*$", r["stdout"], re.M)}

    # 3. InsertField shared-storage reproducer through the CLI.
    build = run("cli_build", [str(Path.home() / ".cargo/bin/cargo"), "build", "-p", "trust-cg-cli", "--locked", "--offline", "-j", "8"], ROOT, env)
    cli = ROOT / "target/debug/trust-cg"
    repro = RECORDS / "insertfield-shared-storage"
    repro.mkdir()
    shutil.copy(PROBE / "insertprobe/swap.c", repro / "swap.c")
    reproduced = {}
    work = OUT / "insertfield-work"
    work.mkdir()
    for tag, ctype in (("i64", "int64_t"), ("f32", "float"), ("f16", "_Float16")):
        shutil.copy(PROBE / f"insertprobe/swap_{tag}.trust_ir", repro / f"swap_{tag}.trust_ir")
        for opt in ("O0", "O2"):
            obj = work / f"swap_{tag}_{opt}.o"
            c = run(f"insertfield-compile-{tag}-{opt}", [str(cli), "--format=text", "-c", f"-{opt}", "--target", "aarch64-unknown-linux-gnu", "-o", str(obj), str(repro / f"swap_{tag}.trust_ir")], work, env)
            binary = work / f"swap_{tag}_{opt}"
            l = run(f"insertfield-link-{tag}-{opt}", ["cc", "-O2", f"-DT={ctype}", str(repro / "swap.c"), str(obj), "-o", str(binary)], work, env)
            x = run(f"insertfield-run-{tag}-{opt}", [str(binary)], work, env)
            (repro / f"swap_{tag}_{opt}.o.gz").write_bytes(gzip.compress(obj.read_bytes(), mtime=0))
            reproduced[f"{tag}-{opt}"] = {"compile": c["returncode"], "link": l["returncode"], "run": x["returncode"], "stdout": x["stdout"].strip()}
    results["insertfield_shared_storage"] = {"cli_build": build["returncode"], "cases": reproduced}

    # 4. Stock-rustc LLVM stack placement of f16/f32 HFAs, Darwin vs Linux.
    probe_dir = RECORDS / "darwinpcs-hfa-probe"
    probe_dir.mkdir()
    shutil.copy(PROBE / "darwinpcs/probe.rs", probe_dir / "probe.rs")
    placements = {}
    for triple in ("aarch64-apple-darwin", "aarch64-unknown-linux-gnu"):
        asm = probe_dir / f"{triple}.s"
        rustc_env = dict(env, RUSTC_BOOTSTRAP="1")
        r = run(f"probe-{triple}", [str(Path.home() / ".cargo/bin/rustc"), "+1.97.1", "--target", triple, "--emit=asm", "-C", "opt-level=2", "-o", str(asm), str(probe_dir / "probe.rs")], probe_dir, rustc_env)
        text = asm.read_text() if asm.exists() else ""
        current, stores = None, {}
        for line in text.splitlines():
            label = re.match(r"^_?(call\w+):", line)
            if label:
                current = label.group(1)
                stores[current] = []
            elif current and re.search(r"\b(str|stp)\s+[hs]\d+", line):
                stores[current].append(" ".join(line.split()))
        placements[triple] = {"returncode": r["returncode"], "stack_stores": stores}
    results["darwinpcs_hfa_probe"] = placements

    # 5. Disassembly of two retained objects.
    objdump = str(Path.home() / ".local/bin/llvm-objdump")
    for label in ("baseline-O2", "explicit-fp16-O2"):
        run(f"objdump-dr-{label}", [objdump, "-dr", "--no-show-raw-insn", str(retained / "corpus" / f"{label}.o")], OUT, env, gz=True)

    # Stage retained sources and objects; binaries are hashed, not archived.
    objects = RECORDS / "objects"
    binaries = {}
    for sub in ("corpus", "controls", "fp16_fadd"):
        for path in sorted((retained / sub).iterdir()):
            dest = objects / sub
            dest.mkdir(parents=True, exist_ok=True)
            data = path.read_bytes()
            if path.suffix == ".o":
                (dest / f"{path.name}.gz").write_bytes(gzip.compress(data, mtime=0))
            elif path.suffix == ".c":
                (dest / path.name).write_bytes(data)
            else:
                binaries[f"{sub}/{path.name}"] = {"sha256": sha256(data), "bytes": len(data)}
    results["binaries_not_archived"] = binaries

    status_after = git("status", "--porcelain", "--untracked-files=all")
    source["status_after"] = status_after
    (RECORDS / "source.json").write_text(json.dumps(source, indent=2) + "\n")
    (RECORDS / "host.json").write_text(json.dumps(host, indent=2) + "\n")
    (RECORDS / "tools.json").write_text(json.dumps(tools, indent=2) + "\n")
    (RECORDS / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    harness = ARCHIVE / "harnesses"
    harness.mkdir()
    shutil.copy(Path(__file__), harness / Path(__file__).name)
    ok = (
        not status_after
        and all(v["returncode"] == 0 for k, v in results["commands"].items())
        and all(case["compile"] == 0 and case["link"] == 0 and case["run"] == 1 for case in reproduced.values())
        and all(p["returncode"] == 0 for p in placements.values())
    )
    print(json.dumps({"ok": ok, "status_after": status_after}, indent=2))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
