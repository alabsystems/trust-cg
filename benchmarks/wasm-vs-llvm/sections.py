#!/usr/bin/env python3
"""benchmarks/wasm-vs-llvm/sections.py — where a wasm32 module's file bytes go.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0

Compiles every corpus program (or a --progs subset) with run.py's own flags in
the B1 lane (rustc + LLVM) and in one trust-cg lane per `--bridge NAME=DYLIB`,
and breaks each linked module into its sections: every standard section and
every custom section by name, each counted with its header (id byte and size
LEB), so a module's sections sum to its file bytes exactly (checked). Inside
sections it records what the file-bytes excess is made of:

  - type: entries and distinct entries (a duplicate is a type the module
    could share);
  - code: bodies, and bodies identical in signature and bytes (the bytes an
    identical-function fold could at most remove, before any thunk);
  - data: segments, image bytes and zero bytes in each image;
  - export/import: counts and name bytes;
  - name: the subsections (module, function, local, global, data segment
    and others) with their name bytes, and the bytes of function names that
    carry the crate-private `.tcg.crate.` mark or the internal-ABI `.tcg.mv`
    suffix.

This is a diagnostic, not a measurement of record: it is no part of
run.py's `measurement_sha256`, no ledger row is made from it, and its numbers
apply to the bridge dylib and toolchain they were taken with. It writes
<out>/sections.json (every module's breakdown) and prints corpus totals per
lane, per section, and over the programs whose trust-cg module is larger than
B1's.

Exit: 0 written; 2 tooling error; 3 a module failed to compile in some lane
(it is listed, never silently dropped).
"""

import argparse
import concurrent.futures
import hashlib
import importlib.util
import json
import sys
import tempfile
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent


def _load_run():
    spec = importlib.util.spec_from_file_location("trust_cg_wasm_vs_llvm_run", HERE / "run.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


SECTION_NAMES = {0: "custom", 1: "type", 2: "import", 3: "function", 4: "table", 5: "memory", 6: "global",
                 7: "export", 8: "start", 9: "element", 10: "code", 11: "data", 12: "datacount", 13: "tag"}
NAME_SUBSECTIONS = {0: "module", 1: "function", 2: "local", 3: "label", 4: "type", 5: "table", 6: "memory",
                    7: "global", 8: "elem", 9: "data", 10: "field", 11: "tag"}
CRATE_PRIVATE_MARK = ".tcg.crate."
INTERNAL_ENTRY_SUFFIX = ".tcg.mv"


class Reader:
    def __init__(self, data, pos=0, end=None):
        self.data = data
        self.pos = pos
        self.end = len(data) if end is None else end

    def byte(self):
        if self.pos >= self.end:
            raise ValueError("truncated")
        b = self.data[self.pos]
        self.pos += 1
        return b

    def uleb(self):
        result = shift = 0
        while True:
            b = self.byte()
            result |= (b & 0x7F) << shift
            shift += 7
            if not b & 0x80:
                return result

    def bytes(self, n):
        if self.pos + n > self.end:
            raise ValueError("truncated")
        out = self.data[self.pos:self.pos + n]
        self.pos += n
        return out

    def name(self):
        return self.bytes(self.uleb()).decode("utf-8")

    def done(self):
        return self.pos >= self.end


def _skip_valtype_vec(r):
    out = []
    for _ in range(r.uleb()):
        out.append(r.byte())
    return tuple(out)


def _skip_limits(r):
    flags = r.byte()
    r.uleb()
    if flags & 1:
        r.uleb()


def _skip_const_expr(r):
    # Reads instructions up to the terminating `end` (0x0B). Constant
    # expressions in linked modules use i32/i64/f32/f64.const, global.get and
    # (with extended-const) i32/i64 add/sub/mul.
    while True:
        op = r.byte()
        if op == 0x0B:
            return
        if op in (0x41, 0x42, 0x23):
            r.uleb()
        elif op == 0x43:
            r.bytes(4)
        elif op == 0x44:
            r.bytes(8)
        elif op in (0x6A, 0x6B, 0x6C, 0x7C, 0x7D, 0x7E):
            pass
        else:
            raise ValueError(f"unexpected opcode 0x{op:02x} in a constant expression")


def _name_map(r):
    entries = []
    for _ in range(r.uleb()):
        idx = r.uleb()
        entries.append((idx, r.name()))
    return entries


def decode(data):
    """Returns the module's breakdown; raises ValueError on a malformed module."""
    if data[:8] != b"\0asm\x01\0\0\0":
        raise ValueError("not a wasm 1 module")
    r = Reader(data, 8)
    sections = []
    info = {"file_bytes": len(data), "header_bytes": 8}
    while not r.done():
        start = r.pos
        sid = r.byte()
        size = r.uleb()
        body_start = r.pos
        body = Reader(data, body_start, body_start + size)
        r.pos = body_start + size
        total = r.pos - start
        name = SECTION_NAMES.get(sid, f"unknown{sid}")
        if sid == 0:
            cname = body.name()
            name = f"custom:{cname}"
            if cname == "name":
                info["name"] = _decode_names(body)
        elif sid == 1:
            types = []
            for _ in range(body.uleb()):
                form = body.byte()
                if form != 0x60:
                    raise ValueError(f"type form 0x{form:02x}")
                types.append((_skip_valtype_vec(body), _skip_valtype_vec(body)))
            info["types"] = types
        elif sid == 2:
            imports = []
            for _ in range(body.uleb()):
                mod, field = body.name(), body.name()
                kind = body.byte()
                if kind == 0:
                    body.uleb()
                elif kind == 1:
                    body.byte()
                    _skip_limits(body)
                elif kind == 2:
                    _skip_limits(body)
                elif kind == 3:
                    body.byte()
                    body.byte()
                else:
                    raise ValueError(f"import kind {kind}")
                imports.append((mod, field, kind))
            info["imports"] = imports
        elif sid == 3:
            info["func_types"] = [body.uleb() for _ in range(body.uleb())]
        elif sid == 7:
            exports = []
            for _ in range(body.uleb()):
                ename = body.name()
                kind = body.byte()
                exports.append((ename, kind, body.uleb()))
            info["exports"] = exports
        elif sid == 10:
            bodies = []
            for _ in range(body.uleb()):
                n = body.uleb()
                bodies.append(body.bytes(n))
            info["bodies"] = bodies
        elif sid == 11:
            segments = []
            for _ in range(body.uleb()):
                flags = body.uleb()
                if flags == 0:
                    _skip_const_expr(body)
                elif flags == 2:
                    body.uleb()
                    _skip_const_expr(body)
                segments.append(body.bytes(body.uleb()))
            info["segments"] = segments
        sections.append((name, total))
    info["sections"] = sections
    if sum(t for _, t in sections) + 8 != len(data):
        raise ValueError("sections do not sum to the file size")
    return info


def _decode_names(body):
    subs = {}
    while not body.done():
        sid = body.byte()
        size = body.uleb()
        sub = Reader(body.data, body.pos, body.pos + size)
        header = 1 + len(_uleb_bytes(size))
        body.pos += size
        label = NAME_SUBSECTIONS.get(sid, f"sub{sid}")
        entry = {"bytes": header + size}
        if sid == 1:
            names = _name_map(sub)
            entry["count"] = len(names)
            entry["name_bytes"] = sum(len(n.encode()) for _, n in names)
            entry["crate_private_name_bytes"] = sum(len(n.encode()) for _, n in names if CRATE_PRIVATE_MARK in n)
            entry["crate_private_names"] = sum(1 for _, n in names if CRATE_PRIVATE_MARK in n)
            entry["internal_entry_names"] = sum(1 for _, n in names if n.endswith(INTERNAL_ENTRY_SUFFIX)
                                                or INTERNAL_ENTRY_SUFFIX + "." in n)
            entry["names"] = [n for _, n in names]
        elif sid in (7, 9):
            names = _name_map(sub)
            entry["count"] = len(names)
            entry["name_bytes"] = sum(len(n.encode()) for _, n in names)
            entry["names"] = [n for _, n in names]
        subs[label] = entry
    return subs


def _uleb_bytes(value):
    out = bytearray()
    while True:
        b = value & 0x7F
        value >>= 7
        if value:
            out.append(b | 0x80)
        else:
            out.append(b)
            return bytes(out)


def summarize(info):
    """The JSON-able per-module breakdown."""
    sec = Counter()
    for name, total in info["sections"]:
        sec[name] += total
    types = info.get("types", [])
    nimports = sum(1 for _, _, k in info.get("imports", []) if k == 0)
    func_types = info.get("func_types", [])
    bodies = info.get("bodies", [])
    groups = Counter()
    for i, b in enumerate(bodies):
        sig = types[func_types[i]] if i < len(func_types) and func_types[i] < len(types) else None
        groups[(sig, hashlib.sha256(b).hexdigest())] += 1
    dup_bodies = 0
    dup_bytes = 0
    seen = set()
    for i, b in enumerate(bodies):
        sig = types[func_types[i]] if i < len(func_types) and func_types[i] < len(types) else None
        key = (sig, hashlib.sha256(b).hexdigest())
        if groups[key] > 1:
            if key in seen:
                dup_bodies += 1
                dup_bytes += len(b) + len(_uleb_bytes(len(b)))
            seen.add(key)
    segments = info.get("segments", [])
    names = info.get("name", {})
    fn = names.get("function", {})
    return {
        "file_bytes": info["file_bytes"],
        "sections": dict(sec),
        "types": len(types),
        "distinct_types": len(set(types)),
        "imported_funcs": nimports,
        "defined_funcs": len(bodies),
        "identical_bodies": dup_bodies,
        "identical_body_bytes": dup_bytes,
        "exports": len(info.get("exports", [])),
        "export_name_bytes": sum(len(n.encode()) for n, _, _ in info.get("exports", [])),
        "data_segments": len(segments),
        "data_image_bytes": sum(len(s) for s in segments),
        "data_zero_bytes": sum(s.count(0) for s in segments),
        "name_subsections": {k: {kk: vv for kk, vv in v.items() if kk != "names"} for k, v in names.items()},
        "function_names": fn.get("names", []),
        "global_names": names.get("global", {}).get("names", []),
        "data_names": names.get("data", {}).get("names", []),
        "export_names": sorted(n for n, _, _ in info.get("exports", [])),
        "import_names": sorted(f"{m}.{f}" for m, f, _ in info.get("imports", [])),
    }


def main():
    run = _load_run()
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--rustc")
    ap.add_argument("--bridge", action="append", required=True, metavar="NAME=DYLIB",
                    help="a trust-cg lane: its label and the bridge dylib (repeatable)")
    ap.add_argument("--sysroot")
    ap.add_argument("--wasm-ld")
    ap.add_argument("--progs", nargs="+")
    ap.add_argument("--jobs", type=int, default=2)
    ap.add_argument("--out", required=True, help="output directory (sections.json)")
    ap.add_argument("--keep-modules", action="store_true", help="keep the linked modules under <out>/modules")
    args = ap.parse_args()
    lanes = {}
    for spec in args.bridge:
        label, sep, path = spec.partition("=")
        if not sep or not label or label == "b1":
            run.die(f"--bridge takes NAME=DYLIB with NAME other than b1: {spec}")
        lanes[label] = path
    harness_args = argparse.Namespace(rustc=args.rustc, bridge=next(iter(lanes.values())), sysroot=args.sysroot,
                                      wasm_ld=args.wasm_ld, node=None, wasm_opt=None, modes=None)
    for label, path in lanes.items():
        lanes[label] = run.resolve_tool(path, None, None, f"bridge dylib for {label}")
    sources, _ = run.check_corpus(HERE / "progs" / "manifest.json")
    if args.progs:
        missing = [p for p in args.progs if p not in sources]
        if missing:
            run.die(f"unknown programs {missing}")
        sources = {p: sources[p] for p in args.progs}
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)

    def one(name):
        row = {}
        with tempfile.TemporaryDirectory(prefix=f"sections-{name}-") as tmp:
            for label, dylib in [("b1", None), *lanes.items()]:
                # run.py's file names: wasm-ld names the module after its
                # output file, so every trust-cg lane links `tcg.wasm`.
                lane_dir = Path(tmp) / label
                lane_dir.mkdir()
                wasm = lane_dir / ("b1.wasm" if dylib is None else "tcg.wasm")
                _, error = harness_for(dylib).compile(sources[name], wasm, dylib is not None)
                if error:
                    row[label] = {"error": error}
                    continue
                data = wasm.read_bytes()
                try:
                    row[label] = summarize(decode(data))
                except ValueError as err:
                    row[label] = {"error": f"decode: {err}"}
                if args.keep_modules:
                    (out / "modules").mkdir(exist_ok=True)
                    (out / "modules" / f"{name}.{label}.wasm").write_bytes(data)
        return name, row

    harness_cache = {}

    def harness_for(dylib):
        if dylib not in harness_cache:
            ns = argparse.Namespace(**{**vars(harness_args), "bridge": dylib or harness_args.bridge})
            harness_cache[dylib] = run.Harness(ns)
        return harness_cache[dylib]

    for dylib in [None, *lanes.values()]:
        harness_for(dylib)
    rows = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
        for name, row in pool.map(one, sorted(sources)):
            rows[name] = row
            print(f"{name}: " + " ".join(f"{k}={v.get('file_bytes', 'ERR')}" for k, v in row.items()), flush=True)
    (out / "sections.json").write_text(json.dumps({"lanes": {"b1": "rustc+LLVM", **lanes}, "programs": rows},
                                                  indent=1, sort_keys=True))
    failed = sorted(n for n, row in rows.items() if any("error" in v for v in row.values()))
    report(rows, list(lanes))
    if failed:
        print(f"FAILED in some lane: {failed}", file=sys.stderr)
        return 3
    return 0


def report(rows, labels):
    ok = {n: r for n, r in rows.items() if all("error" not in r.get(l, {"error": 1}) for l in ["b1", *labels])}
    print(f"\nprograms decoded in every lane: {len(ok)}/{len(rows)}")
    for label in labels:
        larger = [n for n, r in ok.items() if r[label]["file_bytes"] > r["b1"]["file_bytes"]]
        smaller = [n for n, r in ok.items() if r[label]["file_bytes"] < r["b1"]["file_bytes"]]
        print(f"\n== {label} vs b1: smaller on {len(smaller)}, larger on {len(larger)}, "
              f"equal on {len(ok) - len(smaller) - len(larger)}")
        for scope_name, scope in (("all", list(ok)), ("larger", larger)):
            tot_b1, tot_t = Counter(), Counter()
            for n in scope:
                tot_b1.update(ok[n]["b1"]["sections"])
                tot_t.update(ok[n][label]["sections"])
            fb1 = sum(ok[n]["b1"]["file_bytes"] for n in scope)
            ft = sum(ok[n][label]["file_bytes"] for n in scope)
            print(f"  [{scope_name}: {len(scope)} programs] file bytes b1={fb1} {label}={ft} excess={ft - fb1}")
            for sec in sorted(set(tot_b1) | set(tot_t), key=lambda s: -(tot_t[s] - tot_b1[s])):
                print(f"    {sec:28s} b1={tot_b1[sec]:8d} {label}={tot_t[sec]:8d} delta={tot_t[sec] - tot_b1[sec]:+8d}")
            for key in ("types", "distinct_types", "defined_funcs", "identical_bodies", "identical_body_bytes",
                        "imported_funcs", "exports", "data_segments", "data_image_bytes", "data_zero_bytes"):
                vb = sum(ok[n]["b1"][key] for n in scope)
                vt = sum(ok[n][label][key] for n in scope)
                print(f"    {key:28s} b1={vb:8d} {label}={vt:8d}")
            for sub in ("module", "function", "global", "data", "local"):
                vb = sum(ok[n]["b1"]["name_subsections"].get(sub, {}).get("bytes", 0) for n in scope)
                vt = sum(ok[n][label]["name_subsections"].get(sub, {}).get("bytes", 0) for n in scope)
                print(f"    name.{sub:23s} b1={vb:8d} {label}={vt:8d}")
            cp = sum(ok[n][label]["name_subsections"].get("function", {}).get("crate_private_name_bytes", 0)
                     for n in scope)
            print(f"    {'crate-private name bytes':28s} {label}={cp:8d}")


if __name__ == "__main__":
    sys.exit(main())
