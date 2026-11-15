#!/usr/bin/env python3
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
"""Compile-time regression corpus: measure, compare, profile.

    run.py measure --bin <compile_corpus> --out A.json [--reps 3] [--filter S] [--lane L]
    run.py compare A.json B.json [--table out.md]
    run.py tier-cost LOW.json TOP.json [--table out.md]
    run.py profile --bin <compile_corpus> --out prof.txt [--filter S] [--reps 20]

`measure` runs the `compile_corpus` binary (crates/trust-cg-jit-matrix) once
per corpus entry, in a fresh process, and merges the per-entry JSON. Each entry
is compiled `--reps` times in its process; every repetition's verdict, output
digest and frame-net counters are recorded, and the instructions retired /
cycles elapsed of every phase bracket come from the process's own kernel
counters (macOS `proc_pid_rusage`). The whole process is also run under
`/usr/bin/time -l`, whose instructions-retired line is recorded as a check.

`compare` is the byte-identity guard and the cost report. It FAILS (exit 1) if
any (entry, lane) differs between the two runs in any module's verdict, error
text or emitted-code digests, or in the frame-net verifier's counters, or if
either run is not self-consistent across its own repetitions. Only then does it report
instructions: per phase and per entry, the steady-state repetition (the minimum
over repetitions 2..N, or repetition 1 when N = 1) on both sides.

`tier-cost` prices a JIT tier: LOW is a `measure --opt-level <L>` run and TOP
a run at each module's own level (or another `--opt-level`), of the SAME
binary. Their bytes differ by design, so it checks instead that each run is
self-consistent across its repetitions and that both sides reach the same
verdict for every (entry, lane), then reports the steady-state instructions
of LOW against TOP per origin and per entry — what compiling the first tier at
L costs relative to compiling the top tier up front.

`profile` runs the binary under `sample` and attributes every sample to the
innermost compile phase on its stack (PHASES below), so a bracket's
instructions can be split into isel / optimization / regalloc / each
verification pass / encoding / link.
"""

from __future__ import annotations

import argparse
import gzip
import json
import os
import re
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "corpus.json"
TIME_RE = {
    "instructions": re.compile(r"^\s*(\d+)\s+instructions retired\s*$", re.M),
    "cycles": re.compile(r"^\s*(\d+)\s+cycles elapsed\s*$", re.M),
    "max_rss": re.compile(r"^\s*(\d+)\s+maximum resident set size\s*$", re.M),
}


def load_manifest(path: Path) -> dict:
    return json.loads(path.read_text())


def load_json(path: str) -> dict:
    """A measurement document, plain or gzip-compressed (committed baselines)."""
    raw = Path(path).read_bytes()
    if raw[:2] == b"\x1f\x8b":
        raw = gzip.decompress(raw)
    return json.loads(raw)


def select(manifest: dict, filters: list[str]) -> list[dict]:
    entries = manifest["entries"]
    if filters:
        entries = [e for e in entries if any(f in e["name"] for f in filters)]
    return entries


# ---------------------------------------------------------------------------
# measure
# ---------------------------------------------------------------------------


def measure_env(args) -> dict:
    """The harness's environment. By default the global rayon pool (used by
    trust-ir-build's module validation) gets one worker: work-stealing workers
    that spin before they sleep retire instructions of their own, which made
    the whole-process counters of one binary vary by up to 3% between runs of
    a small program; with one worker the spread is 0.4%. `--rayon-default`
    keeps the host's default pool (the setting an embedding process runs)."""
    env = dict(os.environ)
    if not args.rayon_default:
        env["RAYON_NUM_THREADS"] = "1"
    return env


def measure(args) -> int:
    manifest_path = Path(args.manifest).resolve()
    manifest = load_manifest(manifest_path)
    entries = select(manifest, args.filter)
    out = {
        "schema": "trust-cg.compile-corpus.measurement.v1",
        "binary": str(Path(args.bin).resolve()),
        "manifest": str(manifest_path),
        "reps": args.reps,
        "opt_level_override": args.opt_level,
        "rayon_num_threads": measure_env(args).get("RAYON_NUM_THREADS", "default"),
        "started": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "loadavg_start": os.getloadavg(),
        "entries": [],
    }
    for i, entry in enumerate(entries):
        cmd = [
            "/usr/bin/time", "-l", args.bin, "run", "--manifest", str(manifest_path),
            "--entry", entry["name"], "--reps", str(args.reps),
        ]
        for lane in args.lane:
            cmd += ["--lane", lane]
        if args.opt_level:
            cmd += ["--opt-level", args.opt_level]
        with tempfile.NamedTemporaryFile(suffix=".json", delete=False) as tmp:
            result_path = Path(tmp.name)
        cmd += ["--out", str(result_path)]
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=args.timeout, env=measure_env(args))
        if p.returncode != 0:
            print(f"[{i + 1}/{len(entries)}] {entry['name']}: harness exit {p.returncode}\n{p.stderr[-2000:]}",
                  file=sys.stderr)
            return 2
        doc = json.loads(result_path.read_text())
        result_path.unlink()
        process = {k: (int(m.group(1)) if (m := rx.search(p.stderr)) else None) for k, rx in TIME_RE.items()}
        for record in doc["entries"]:
            record["process"] = process
            out["entries"].append(record)
            summary = []
            for lane, reps in record["lanes"].items():
                last = reps[-1]
                summary.append(f"{lane}={last['verdict']}:{last['total']['instructions'] / 1e6:.1f}M")
            print(f"[{i + 1}/{len(entries)}] {entry['name']}: {' '.join(summary)}", file=sys.stderr, flush=True)
        out["counter_source"] = doc.get("counter_source")
        out["host_triple"] = doc.get("host_triple")
    out["finished"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    out["loadavg_end"] = os.getloadavg()
    text = json.dumps(out, indent=1) + "\n"
    if args.out.endswith(".gz"):
        Path(args.out).write_bytes(gzip.compress(text.encode(), mtime=0))
    else:
        Path(args.out).write_text(text)
    return 0


# ---------------------------------------------------------------------------
# compare
# ---------------------------------------------------------------------------

IDENTITY_KEYS = ("verdict", "modules", "frame_net")
SAME_BYTES_LANES = [("jit-raw", "jit-raw-checked")]


def identity(rep: dict) -> dict:
    return {k: rep.get(k) for k in IDENTITY_KEYS}


def module_bytes(rep: dict) -> list[dict]:
    """Each module's verdict, error and emitted-code identity."""
    return [{k: m.get(k) for k in ("module", "verdict", "error", "output", "functions")}
            for m in rep["modules"]]


def steady(reps: list[dict]) -> dict:
    """The steady-state repetition: minimum total instructions over 2..N."""
    pool = reps[1:] if len(reps) > 1 else reps
    return min(pool, key=lambda r: r["total"]["instructions"])


def phase_instr(rep: dict) -> dict[str, int]:
    return {name: c["instructions"] for name, c in rep.get("phases", {}).items()}


def compare(args) -> int:
    a = load_json(args.a)
    b = load_json(args.b)
    ea = {e["name"]: e for e in a["entries"]}
    eb = {e["name"]: e for e in b["entries"]}
    problems = []
    for side, doc in (("A", ea), ("B", eb)):
        for name, e in doc.items():
            for lane, reps in e["lanes"].items():
                ids = [identity(r) for r in reps]
                if any(i != ids[0] for i in ids[1:]):
                    problems.append(f"{side} {name} {lane}: repetitions disagree with each other")
    # Lanes that must emit the same bytes as another lane of the same run
    # (the sealed-function JIT lane skips a re-check, never a byte).
    for side, doc in (("A", ea), ("B", eb)):
        for name, e in doc.items():
            for lane, twin in SAME_BYTES_LANES:
                if lane in e["lanes"] and twin in e["lanes"]:
                    if module_bytes(e["lanes"][lane][0]) != module_bytes(e["lanes"][twin][0]):
                        problems.append(f"{side} {name}: {twin} differs from {lane}")
    common = [n for n in ea if n in eb]
    for name in sorted(set(ea) ^ set(eb)):
        problems.append(f"{name}: present on one side only")
    rows = []
    totals: dict[tuple[str, str], list[int]] = {}
    phase_totals: dict[tuple[str, str], list[int]] = {}
    for name in common:
        for lane in sorted(set(ea[name]["lanes"]) | set(eb[name]["lanes"])):
            ra, rb = ea[name]["lanes"].get(lane), eb[name]["lanes"].get(lane)
            twin = dict((b, a) for a, b in SAME_BYTES_LANES).get(lane)
            if ra is None and rb is not None and twin in ea[name]["lanes"]:
                # A lane the older side did not run is held to its same-bytes
                # twin there (its verifier counters differ by design), and its
                # cost is reported against that twin.
                ra = ea[name]["lanes"][twin]
                ia, ib = identity(ra[0]), identity(rb[0])
                if ia["verdict"] != ib["verdict"] or module_bytes(ra[0]) != module_bytes(rb[0]):
                    problems.append(f"{name} {lane}: differs from {twin} on side A")
                    continue
            elif ra is None or rb is None:
                problems.append(f"{name} {lane}: lane present on one side only")
                continue
            else:
                ia, ib = identity(ra[0]), identity(rb[0])
                if ia != ib:
                    diff = [k for k in IDENTITY_KEYS if ia.get(k) != ib.get(k)]
                    problems.append(f"{name} {lane}: differs in {', '.join(diff)}")
                    continue
            sa, sb = steady(ra), steady(rb)
            origin = ea[name]["origin"]
            ta, tb = sa["total"]["instructions"], sb["total"]["instructions"]
            ca, cb = sa["total"]["cycles"], sb["total"]["cycles"]
            rows.append((origin, name, lane, ia["verdict"], ta, tb, ca, cb))
            for key in ((origin, lane), ("ALL", lane)):
                acc = totals.setdefault(key, [0, 0, 0, 0])
                acc[0] += ta
                acc[1] += tb
                acc[2] += ca
                acc[3] += cb
            pa, pb = phase_instr(sa), phase_instr(sb)
            for phase in sorted(set(pa) | set(pb)):
                acc = phase_totals.setdefault((lane, phase), [0, 0])
                acc[0] += pa.get(phase, 0)
                acc[1] += pb.get(phase, 0)
    lines = []
    lines.append(f"# compile-corpus compare\n\nA: `{a['binary']}` ({a['started']})  \nB: `{b['binary']}` ({b['started']})\n")
    if problems:
        lines.append(f"## IDENTITY FAILURES ({len(problems)})\n")
        lines += [f"* {p}" for p in problems]
        lines.append("")
    else:
        n = len(rows)
        lines.append(f"**Identity: PASS** — {n} (entry, lane) pairs: same verdicts, error texts, emitted-code "
                     "digests and frame-net counters on both sides, every repetition.\n")
    lines.append("## Totals (steady-state instructions retired / cycles elapsed)\n")
    lines.append("| origin | lane | A instr | B instr | B/A | A cycles | B cycles | B/A |")
    lines.append("|---|---|--:|--:|--:|--:|--:|--:|")
    for (origin, lane), (ta, tb, ca, cb) in sorted(totals.items()):
        lines.append(f"| {origin} | {lane} | {ta / 1e6:,.1f} M | {tb / 1e6:,.1f} M | {tb / ta if ta else 0:.4f} | "
                     f"{ca / 1e6:,.1f} M | {cb / 1e6:,.1f} M | {cb / ca if ca else 0:.4f} |")
    lines.append("\n## Per phase bracket (all entries)\n")
    lines.append("| lane | phase | A instr | B instr | B/A |")
    lines.append("|---|---|--:|--:|--:|")
    for (lane, phase), (pa, pb) in sorted(phase_totals.items()):
        lines.append(f"| {lane} | {phase} | {pa / 1e6:,.1f} M | {pb / 1e6:,.1f} M | {pb / pa if pa else 0:.4f} |")
    lines.append("\n## Per entry\n")
    lines.append("| origin | entry | lane | verdict | A instr | B instr | B/A |")
    lines.append("|---|---|---|---|--:|--:|--:|")
    for origin, name, lane, verdict, ta, tb, ca, cb in sorted(rows):
        lines.append(f"| {origin} | {name} | {lane} | {verdict} | {ta / 1e6:,.2f} M | {tb / 1e6:,.2f} M | "
                     f"{tb / ta if ta else 0:.4f} |")
    text = "\n".join(lines) + "\n"
    if args.table:
        Path(args.table).write_text(text)
    print(text)
    return 1 if problems else 0


# ---------------------------------------------------------------------------
# tier-cost
# ---------------------------------------------------------------------------


def tier_cost(args) -> int:
    low = load_json(args.low)
    top = load_json(args.top)
    el = {e["name"]: e for e in low["entries"]}
    et = {e["name"]: e for e in top["entries"]}
    problems = []
    if low.get("binary") != top.get("binary"):
        problems.append(f"different binaries: {low.get('binary')} vs {top.get('binary')}")
    for side, doc in (("LOW", el), ("TOP", et)):
        for name, e in doc.items():
            for lane, reps in e["lanes"].items():
                ids = [identity(r) for r in reps]
                if any(i != ids[0] for i in ids[1:]):
                    problems.append(f"{side} {name} {lane}: repetitions disagree with each other")
    for name in sorted(set(el) ^ set(et)):
        problems.append(f"{name}: present on one side only")
    rows = []
    totals: dict[tuple[str, str], list[int]] = {}
    for name in sorted(set(el) & set(et)):
        for lane in sorted(set(el[name]["lanes"]) & set(et[name]["lanes"])):
            rl, rt = el[name]["lanes"][lane], et[name]["lanes"][lane]
            vl, vt = rl[0]["verdict"], rt[0]["verdict"]
            origin = el[name]["origin"]
            level_l = el[name].get("compiled_opt_level") or el[name]["opt_level"]
            level_t = et[name].get("compiled_opt_level") or et[name]["opt_level"]
            if vl != vt:
                problems.append(f"{name} {lane}: verdict {vl} at {level_l}, {vt} at {level_t}")
                continue
            if vl != "ok":
                continue
            sl, st = steady(rl), steady(rt)
            il, it = sl["total"]["instructions"], st["total"]["instructions"]
            rows.append((origin, name, lane, level_l, level_t, il, it))
            for key in ((origin, lane), ("ALL", lane)):
                acc = totals.setdefault(key, [0, 0, 0])
                acc[0] += il
                acc[1] += it
                acc[2] += 1
    own_level = "each module's own level"
    level_low = low.get("opt_level_override") or own_level
    level_top = top.get("opt_level_override") or own_level
    lines = [f"# compile-corpus tier cost\n\nLOW: `{low['binary']}` at `{level_low}` ({low['started']})  \n"
             f"TOP: `{top['binary']}` at `{level_top}` ({top['started']})\n"]
    if problems:
        lines.append(f"## CONSISTENCY FAILURES ({len(problems)})\n")
        lines += [f"* {p}" for p in problems]
        lines.append("")
    else:
        lines.append(f"**Consistency: PASS** — {len(rows)} (entry, lane) pairs compiled on both sides; every "
                     "repetition of each side agrees with itself; both sides reach the same verdicts.\n")
    lines.append("## Totals (steady-state instructions retired)\n")
    lines.append("| origin | lane | entries | LOW instr | TOP instr | LOW/TOP |")
    lines.append("|---|---|--:|--:|--:|--:|")
    for (origin, lane), (il, it, n) in sorted(totals.items()):
        lines.append(f"| {origin} | {lane} | {n} | {il / 1e6:,.1f} M | {it / 1e6:,.1f} M | "
                     f"{il / it if it else 0:.4f} |")
    lines.append("\n## Per entry\n")
    lines.append("| origin | entry | lane | LOW level | TOP level | LOW instr | TOP instr | LOW/TOP |")
    lines.append("|---|---|---|---|---|--:|--:|--:|")
    for origin, name, lane, level_l, level_t, il, it in rows:
        lines.append(f"| {origin} | {name} | {lane} | {level_l} | {level_t} | {il / 1e6:,.2f} M | "
                     f"{it / 1e6:,.2f} M | {il / it if it else 0:.4f} |")
    text = "\n".join(lines) + "\n"
    if args.table:
        Path(args.table).write_text(text)
    print(text)
    return 1 if problems else 0


# ---------------------------------------------------------------------------
# profile
# ---------------------------------------------------------------------------

# Innermost match wins; for one frame, the LAST matching pattern wins, so a
# specific pattern follows the generic one it refines. Patterns are matched
# against demangled frame names
# (`c++filt` demangles Rust v0 and legacy symbols); a frame of a generic
# instantiated in another crate still names its defining path.
PHASES = [
    ("load", re.compile(r"trust_ir::binary|load_module_from_bytes|decode_binary")),
    ("adapter", re.compile(r"trust_cg_lower::")),
    ("isel", re.compile(r"trust_cg_lower::isel|InstructionSelector|isel_to_ir|run_isel")),
    ("opt", re.compile(r"trust_cg_opt::")),
    ("regalloc", re.compile(r"trust_cg_regalloc::|run_regalloc|ir_to_regalloc|apply_regalloc")),
    ("frame", re.compile(r"trust_cg_codegen::frame")),
    ("verify:other", re.compile(r"trust_cg_verify::")),
    ("verify:post-ra-recheck", re.compile(r"post_regalloc_recheck::")),
    ("verify:reaching-def", re.compile(r"post_ra_reaching_def::")),
    ("verify:frame-net", re.compile(r"post_ra_spill_slots::")),
    ("verify:a64-validate", re.compile(r"validate_aarch64_mach_function|enforce_aarch64_post_regalloc|"
                                       r"reconstruct_aarch64_resolved_cfg|check_aarch64_exclusive_windows|"
                                       r"verify_aarch64_final_call_argument_sequence")),
    ("encode", re.compile(r"encode_function|trust_cg_codegen::aarch64::encode")),
    ("link", re.compile(r"JitCompiler::compile_raw|relocatable_image|local_address_replay")),
    ("object", re.compile(r"trust_cg_codegen::macho|trust_cg_codegen::object_sections|trust_cg_codegen::elf")),
]
# Leaf frames of a thread that is waiting, not working (thread pools idle
# between tasks). Their samples retire no compile work and are reported apart.
IDLE_LEAVES = re.compile(r"^(__psynch_cvwait|__psynch_mutexwait|swtch_pri|__workq_kernreturn|"
                         r"__semwait_signal|mach_msg2_trap|__ulock_wait2?|kevent\w*|__select)$")
LINE_RE = re.compile(r"^(?P<indent>[ +!:|]*)(?P<count>\d+)\s+(?P<name>.+?)\s+\(in [^)]*\)")


def parse_call_graph(text: str) -> list[tuple[int, int, str]]:
    """(depth, inclusive samples, frame name) for every call-graph line."""
    out = []
    in_graph = False
    for line in text.splitlines():
        if line.startswith("Call graph:"):
            in_graph = True
            continue
        if in_graph and (line.startswith("Total number in stack") or line.startswith("Sort by top of stack")):
            break
        if not in_graph:
            continue
        m = LINE_RE.match(line)
        if m:
            out.append((len(m.group("indent")), int(m.group("count")), m.group("name")))
    return out


def attribute(nodes: list[tuple[int, int, str]]) -> tuple[dict[str, int], dict[str, int]]:
    """Self samples per innermost phase, and self samples per frame name."""
    phase_self: dict[str, int] = {}
    frame_self: dict[str, int] = {}
    stack: list[tuple[int, int, str, str]] = []  # depth, count, name, phase
    children_sum: list[int] = []

    def close(level: int) -> None:
        while stack and stack[-1][0] >= level:
            depth, count, name, phase = stack.pop()
            kids = children_sum.pop()
            own = max(count - kids, 0)
            if IDLE_LEAVES.match(name):
                phase = "(idle wait)"
            phase_self[phase] = phase_self.get(phase, 0) + own
            frame_self[name] = frame_self.get(name, 0) + own

    for depth, count, name in nodes:
        close(depth)
        name = re.sub(r"\s+\+\s+\d+.*$", "", name)
        parent_phase = stack[-1][3] if stack else "other"
        phase = parent_phase
        for label, rx in PHASES:
            if rx.search(name):
                phase = label
        if stack:
            children_sum[-1] += count
        stack.append((depth, count, name, phase))
        children_sum.append(0)
    close(0)
    for name in [name for name in frame_self if IDLE_LEAVES.match(name)]:
        del frame_self[name]
    return phase_self, frame_self


def profile(args) -> int:
    manifest_path = Path(args.manifest).resolve()
    cmd = [args.bin, "run", "--manifest", str(manifest_path), "--reps", str(args.reps), "--out", os.devnull]
    for f in args.filter:
        manifest = load_manifest(manifest_path)
        for e in select(manifest, [f]):
            cmd += ["--entry", e["name"]]
    for lane in args.lane:
        cmd += ["--lane", lane]
    if args.opt_level:
        cmd += ["--opt-level", args.opt_level]
    proc = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                            env=dict(os.environ, RAYON_NUM_THREADS="1"))
    raw = Path(args.out).with_suffix(".sample.txt")
    sampler = subprocess.run(["/usr/bin/sample", str(proc.pid), str(args.seconds), "1", "-mayDie",
                              "-file", str(raw)], capture_output=True, text=True)
    proc.wait()
    if sampler.returncode != 0 or not raw.exists():
        print(sampler.stderr, file=sys.stderr)
        return 2
    text = raw.read_text(errors="replace")
    demangled = subprocess.run(["c++filt"], input=text, capture_output=True, text=True)
    if demangled.returncode == 0:
        text = demangled.stdout
    nodes = parse_call_graph(text)
    phase_self, frame_self = attribute(nodes)
    idle = phase_self.pop("(idle wait)", 0)
    total = sum(phase_self.values()) or 1
    lines = [f"# sample profile: {' '.join(cmd)}", f"# working samples: {total} (idle-wait samples excluded: {idle})",
             "", "phase shares (self samples, innermost phase):"]
    for phase, n in sorted(phase_self.items(), key=lambda kv: -kv[1]):
        lines.append(f"  {phase:22s} {n:8d}  {100 * n / total:6.2f}%")
    lines += ["", f"top {args.top} frames by self samples:"]
    for name, n in sorted(frame_self.items(), key=lambda kv: -kv[1])[: args.top]:
        lines.append(f"  {n:8d}  {100 * n / total:6.2f}%  {name[:160]}")
    Path(args.out).write_text("\n".join(lines) + "\n")
    print("\n".join(lines))
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    m = sub.add_parser("measure")
    m.add_argument("--bin", required=True)
    m.add_argument("--manifest", default=str(MANIFEST))
    m.add_argument("--out", required=True)
    m.add_argument("--reps", type=int, default=3)
    m.add_argument("--filter", action="append", default=[])
    m.add_argument("--lane", action="append", default=[])
    m.add_argument("--timeout", type=int, default=3600)
    m.add_argument("--rayon-default", action="store_true",
                   help="keep the default rayon pool (noisier counters; see measure_env)")
    m.add_argument("--opt-level", choices=["O0", "O1", "O2", "O3"],
                   help="compile every module at this level instead of its producer's (see tier-cost)")
    c = sub.add_parser("compare")
    c.add_argument("a")
    c.add_argument("b")
    c.add_argument("--table")
    t = sub.add_parser("tier-cost")
    t.add_argument("low")
    t.add_argument("top")
    t.add_argument("--table")
    p = sub.add_parser("profile")
    p.add_argument("--bin", required=True)
    p.add_argument("--manifest", default=str(MANIFEST))
    p.add_argument("--out", required=True)
    p.add_argument("--reps", type=int, default=20)
    p.add_argument("--seconds", type=int, default=60)
    p.add_argument("--filter", action="append", default=[])
    p.add_argument("--lane", action="append", default=[])
    p.add_argument("--top", type=int, default=40)
    p.add_argument("--opt-level", choices=["O0", "O1", "O2", "O3"],
                   help="profile the compile at this level instead of each module's own")
    args = ap.parse_args()
    return {"measure": measure, "compare": compare, "tier-cost": tier_cost, "profile": profile}[args.cmd](args)


if __name__ == "__main__":
    raise SystemExit(main())
