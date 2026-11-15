#!/usr/bin/env python3
"""Per-function emitted-code attribution: trust-cg bridge vs LLVM -O3.

For each beat-llvm corpus program this compiles the LLVM -O3 lane and one or
more bridge lanes exactly as benchmarks/beat-llvm/run.py does (Trust driver,
-Ztrust-verify=off, --edition=2021, -Cpanic=abort, -Copt-level=3, bridge
knobs as -Ztrust-ir-cg-args), links once with the system linker's map, and
attributes every live atom of the compile's own objects (emitted_size.py's
definition) to a function. Each function's machine code is disassembled from
the linked image (objdump) and every instruction is put in one class:

  frame     frame-record / callee-save push and pop (stp/ldp x29,x30 or of
            x19-x28/d8-d15 against sp), mov x29,sp, sp adjustments
  spill     other loads/stores addressed off sp or x29
  move      register-to-register moves (mov xN,xM / fmov / orr xzr form)
  const     constant materialization (movz/movk/movn/mov #imm, adr/adrp,
            literal loads)
  nop       nop padding
  check     traps and their branches (brk/udf)
  call      bl/blr/b to another symbol, ret
  branch    b/b.cond/cbz/cbnz/tbz/tbnz within the function
  vector    SIMD/FP-vector instructions (operands naming v/q registers)
  other     everything else (ALU, loads/stores off other bases, compares)

Output: <out>/attrib.json (per program, per lane, per function: bytes and
class counts) and <out>/attrib.md (per-program totals and the class deltas).
Temporary build directories live under <out>/work and are removed unless
--keep-work is given. Numbers are byte counts of one host's linked images:
measurements, not proofs.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(REPO / "benchmarks" / "beat-llvm"))
sys.path.insert(0, str(REPO / "scripts"))
import emitted_size  # noqa: E402

PROGS = REPO / "benchmarks" / "beat-llvm" / "progs"
_SYM = re.compile(r"^0x([0-9A-Fa-f]+)\s+0x([0-9A-Fa-f]+)\s+\[\s*(\d+)\]\s+(.*)$")
_INSN = re.compile(r"^\s*([0-9a-f]+):\s+(?:[0-9a-f]{8}\s+)?(\S+)\s*(.*)$")

CLASSES = ("frame", "spill", "move", "const", "nop", "check", "call", "branch", "vector", "other")


def trustc() -> str:
    path = shutil.which("trustc")
    if not path:
        sys.exit("size_attrib: trustc is not on PATH")
    return path


def compile_lane(src: Path, work: Path, lane: str, dylib: str | None, knobs: list[str]) -> dict:
    lane_dir = work / src.stem / lane
    if lane_dir.exists():
        shutil.rmtree(lane_dir)
    lane_dir.mkdir(parents=True)
    out = lane_dir / src.stem
    map_path = lane_dir / "link.map"
    cmd = [trustc(), "-Ztrust-verify=off", "--edition=2021", "--crate-type", "bin",
           "--target", "aarch64-apple-darwin", "-Cpanic=abort", "-Copt-level=3",
           "-o", str(out), str(src), "-C", f"link-arg=-Wl,-map,{map_path}"]
    if dylib:
        cmd[1:1] = [f"-Zcodegen-backend={dylib}", *[f"-Ztrust-ir-cg-args={k}" for k in knobs]]
    env = {k: v for k, v in os.environ.items()
           if not (k.startswith("TCG_") or k.startswith("TRUST_CG_"))}
    env["MACOSX_DEPLOYMENT_TARGET"] = env.get("MACOSX_DEPLOYMENT_TARGET", "13.0")
    r = subprocess.run(cmd, cwd=lane_dir, capture_output=True, text=True, env=env, timeout=900)
    if r.returncode != 0:
        return {"error": (r.stderr.strip().splitlines() or ["?"])[-1][:300]}
    text = map_path.read_text(errors="replace")
    record = emitted_size.parse_ld64(text, str(lane_dir), cwd=str(lane_dir))
    functions = attribute_functions(text, lane_dir, out)
    run = subprocess.run([str(out)], capture_output=True, timeout=600)
    return {"emitted_bytes": record["bytes"], "sections": record["sections"],
            "exit": run.returncode, "functions": functions}


def attribute_functions(map_text: str, lane_dir: Path, binary: Path) -> dict:
    files, part, atoms = {}, None, []
    for line in map_text.splitlines():
        if line.startswith("#"):
            low = line.lower()
            part = ("objects" if low.startswith("# object files:") else
                    "symbols" if low.startswith("# symbols:") else
                    "dead" if low.startswith("# dead stripped") else part)
            continue
        if part == "objects":
            m = re.match(r"^\[\s*(\d+)\]\s+(.*)$", line)
            if m:
                files[int(m.group(1))] = m.group(2).strip()
        elif part == "symbols":
            m = _SYM.match(line)
            if m:
                atoms.append((int(m.group(1), 16), int(m.group(2), 16), int(m.group(3)), m.group(4)))
    mine = {i for i, p in files.items() if emitted_size.program_object(p, str(lane_dir), str(lane_dir))}
    code = disassemble(binary)
    functions = {}
    for addr, size, index, name in atoms:
        if index not in mine or size == 0:
            continue
        insns = [code[a] for a in range(addr, addr + size, 4) if a in code]
        counts = dict.fromkeys(CLASSES, 0)
        for mnemonic, operands in insns:
            counts[classify(mnemonic, operands)] += 1
        entry = functions.setdefault(demangle(name), {"bytes": 0, "insns": 0, "classes": dict.fromkeys(CLASSES, 0)})
        entry["bytes"] += size
        entry["insns"] += len(insns)
        for k, v in counts.items():
            entry["classes"][k] += v
    return functions


def disassemble(binary: Path) -> dict:
    out = subprocess.run(["objdump", "-d", "--no-show-raw-insn", "--section=__text", str(binary)],
                         capture_output=True, text=True, check=True).stdout
    code = {}
    for line in out.splitlines():
        m = _INSN.match(line)
        if m:
            code[int(m.group(1), 16)] = (m.group(2), m.group(3).split(";")[0].split("//")[0].strip())
    return code


_DEMANGLE_CACHE: dict[str, str] = {}


def demangle(name: str) -> str:
    if name not in _DEMANGLE_CACHE:
        try:
            r = subprocess.run(["c++filt", "-n", name.lstrip("_") if name.startswith("__R") else name],
                               capture_output=True, text=True)
            _DEMANGLE_CACHE[name] = r.stdout.strip() or name
        except OSError:
            _DEMANGLE_CACHE[name] = name
    return _DEMANGLE_CACHE[name]


_CALLEE_SAVED = re.compile(r"\b(x(19|2[0-9])|d(8|9|1[0-5])|fp|lr|x29|x30)\b")


def classify(m: str, ops: str) -> str:
    base = ops.replace(" ", "")
    if m == "nop":
        return "nop"
    if m in ("brk", "udf"):
        return "check"
    if m in ("bl", "blr", "ret", "br", "braa", "blraa", "retab", "retaa"):
        return "call"
    if m in ("b",) and "<" in ops and "+" not in ops.split("<")[-1]:
        return "call"  # a tail branch to another symbol
    if m.startswith("b.") or m in ("b", "cbz", "cbnz", "tbz", "tbnz"):
        return "branch"
    if m in ("stp", "ldp", "str", "ldr") and ("[sp" in base) and _CALLEE_SAVED.search(ops.split("[")[0]) \
            and m in ("stp", "ldp"):
        return "frame"
    if m == "mov" and base in ("x29,sp", "sp,x29"):
        return "frame"
    if m in ("sub", "add") and base.startswith("sp,sp"):
        return "frame"
    if m == "add" and base.startswith("x29,sp"):
        return "frame"
    if m.startswith(("ld", "st")) and ("[sp" in base or "[x29" in base):
        return "spill"
    if m in ("movz", "movk", "movn", "adrp", "adr") or (m == "mov" and "#" in ops):
        return "const"
    if m == "ldr" and "[" not in ops:
        return "const"  # literal-pool load
    if re.search(r"\bv\d+\.|\bq\d+\b", ops):
        return "vector"
    if m in ("mov", "fmov") and "#" not in ops:
        return "move"
    if m == "orr" and re.match(r"^[wx]\d+,[wx]zr,[wx]\d+$", base):
        return "move"
    return "other"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--lane", action="append", default=[], metavar="NAME=DYLIB[:knob,knob]",
                    help="a bridge lane; repeatable")
    ap.add_argument("--progs", nargs="*", default=None)
    ap.add_argument("--out", required=True)
    ap.add_argument("--keep-work", action="store_true")
    args = ap.parse_args()
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    work = out / "work"
    lanes = [("llvm_o3", None, [])]
    for spec in args.lane:
        name, rest = spec.split("=", 1)
        dylib, _, knobs = rest.partition(":")
        lanes.append((name, dylib, [k for k in knobs.split(",") if k]))
    manifest = json.loads((PROGS / "manifest.json").read_text())
    stems = args.progs or sorted(manifest["programs"])
    results = {}
    for stem in stems:
        src = PROGS / f"{stem}.rs"
        results[stem] = {}
        for name, dylib, knobs in lanes:
            results[stem][name] = compile_lane(src, work, name, dylib, knobs)
            r = results[stem][name]
            print(f"{stem:18} {name:12} bytes={r.get('emitted_bytes')} exit={r.get('exit')} {r.get('error', '')}",
                  flush=True)
    (out / "attrib.json").write_text(json.dumps(results, indent=1, sort_keys=True) + "\n")
    (out / "attrib.md").write_text(render(results, [l[0] for l in lanes]))
    if not args.keep_work:
        shutil.rmtree(work, ignore_errors=True)
    return 0


def render(results: dict, lanes: list[str]) -> str:
    rows = ["| program | " + " | ".join(f"{l} B" for l in lanes) + " | "
            + " | ".join(f"{l}/llvm" for l in lanes[1:]) + " |",
            "|---|" + "---:|" * (2 * len(lanes) - 1)]
    import math
    logs = {l: [] for l in lanes[1:]}
    for stem, by_lane in results.items():
        base = by_lane["llvm_o3"].get("emitted_bytes")
        cells = [str(by_lane[l].get("emitted_bytes")) for l in lanes]
        ratios = []
        for l in lanes[1:]:
            b = by_lane[l].get("emitted_bytes")
            if b and base:
                ratios.append(f"{b / base:.3f}")
                logs[l].append(math.log(b / base))
            else:
                ratios.append("-")
        rows.append(f"| {stem} | " + " | ".join(cells) + " | " + " | ".join(ratios) + " |")
    rows.append("| **geomean** | " + " | ".join("" for _ in lanes) + " | "
                + " | ".join(f"**{math.exp(sum(v) / len(v)):.4f}**" if v else "-" for v in logs.values()) + " |")
    text = "\n".join(rows) + "\n\n## Instruction classes (sum over the program's functions)\n\n"
    head = "| program | lane | insns | " + " | ".join(CLASSES) + " |"
    text += head + "\n|---|---|---:|" + "---:|" * len(CLASSES) + "\n"
    for stem, by_lane in results.items():
        for l in lanes:
            fns = by_lane[l].get("functions") or {}
            tot = dict.fromkeys(CLASSES, 0)
            n = 0
            for f in fns.values():
                n += f["insns"]
                for k in CLASSES:
                    tot[k] += f["classes"][k]
            text += f"| {stem} | {l} | {n} | " + " | ".join(str(tot[k]) for k in CLASSES) + " |\n"
    return text


if __name__ == "__main__":
    sys.exit(main())
