#!/usr/bin/env python3
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
"""Cross-check the runner's linked-image records with GNU readelf and llvm-objdump.

The runner parses ELF with its own standard-library code. This harness asks two
independent implementations the same questions for every case of one runner
output directory and writes a JSON record:

- GNU readelf -sW: `calculate`'s value (link-time VA) and size in each PIE and
  in each foreign-object PIE;
- GNU readelf -rW: the certified object's relocations (type and section);
- GNU readelf --debug-dump=frames: the FDEs whose decoded pc range starts at
  the function's VA, with their .eh_frame offsets;
- llvm-objdump -d: the instruction words of `calculate` in the object and in
  the PIE.

It agrees for a case only if every tool answer equals the runner's record and
the object/PIE words are equal. It checks tool output, not the runner's code.

    crosscheck_linked_images.py RUN_DIR OUTPUT.json [--readelf PATH] [--objdump PATH]
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command) -> str:
    # Without DEBUGINFOD_URLS, llvm-objdump never tries a network debug-info lookup.
    env = {name: value for name, value in os.environ.items() if name != "DEBUGINFOD_URLS"}
    return subprocess.run([str(part) for part in command], capture_output=True, text=True, check=True,
                          env=env, timeout=60).stdout


def tool_identity(path: Path) -> dict:
    return {"path": str(path), "resolved": str(path.resolve()), "sha256": sha256(path.resolve()),
            "version": run([path, "--version"]).splitlines()[0:2]}


def readelf_symbols(readelf: Path, image: Path, name: str) -> list:
    rows = []
    for line in run([readelf, "-sW", image]).splitlines():
        fields = line.split()
        if len(fields) >= 8 and fields[7] == name and fields[6] != "UND":
            rows.append({"value": int(fields[1], 16), "size": int(fields[2]), "type": fields[3], "bind": fields[4],
                         "ndx": fields[6]})
    return rows


def readelf_relocations(readelf: Path, obj: Path) -> list:
    rows, section = [], None
    for line in run([readelf, "-rW", obj]).splitlines():
        match = re.match(r"Relocation section '([^']+)'", line)
        if match:
            section = match[1]
            continue
        fields = line.split()
        if len(fields) >= 3 and fields[2].startswith("R_AARCH64_"):
            rows.append({"section": section, "offset": int(fields[0], 16), "type": fields[2]})
    return rows


def readelf_fdes(readelf: Path, image: Path, va: int) -> list:
    rows = []
    pattern = re.compile(r"^([0-9a-f]+) [0-9a-f]+ [0-9a-f]+ FDE cie=[0-9a-f]+ pc=([0-9a-f]+)\.\.([0-9a-f]+)")
    for line in run([readelf, "--debug-dump=frames", image]).splitlines():
        match = pattern.match(line)
        if match and int(match[2], 16) == va:
            rows.append({"eh_frame_offset": int(match[1], 16), "pc_begin": int(match[2], 16),
                         "pc_end": int(match[3], 16)})
    return rows


def objdump_words(objdump: Path, path: Path, name: str) -> list:
    words = []
    inside = False
    for line in run([objdump, "-d", f"--disassemble-symbols={name}", path]).splitlines():
        if line.endswith(f"<{name}>:"):
            inside = True
            continue
        match = re.match(r"^\s+[0-9a-f]+:\s+([0-9a-f]{8})\s", line)
        if inside and match:
            words.append(match[1])
    return words


def section_address(readelf: Path, image: Path, name: str) -> int:
    for line in run([readelf, "-SW", image]).splitlines():
        fields = line.replace("[ ", "[").split()
        if len(fields) > 3 and fields[1] == name:
            return int(fields[3], 16)
    raise SystemExit(f"{image}: no {name} section")


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("run_dir", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--readelf", type=Path, default=Path("/usr/bin/readelf"))
    parser.add_argument("--objdump", type=Path, default=Path.home() / ".local/bin/llvm-objdump")
    args = parser.parse_args(argv)
    report_path = args.run_dir / "report.json"
    if not report_path.is_file():
        report_path = args.run_dir / "report.json.gz"
        report = json.loads(gzip.decompress(report_path.read_bytes()))
    else:
        report = json.loads(report_path.read_text())
    rows = []
    for case in report["cases"]:
        name = case["name"]
        directory = args.run_dir / "cases" / name
        image, obj, foreign = directory / name, directory / f"{name}.o", directory / f"{name}-foreign"
        record = case["linked_image"]
        effect = record["relocation_effects"][0]
        symbols = readelf_symbols(args.readelf, image, "calculate")
        foreign_symbols = readelf_symbols(args.readelf, foreign, "calculate")
        relocations = readelf_relocations(args.readelf, obj)
        fdes = readelf_fdes(args.readelf, image, record["function_va"])
        eh_frame = section_address(args.readelf, image, ".eh_frame")
        object_words = objdump_words(args.objdump, obj, "calculate")
        image_words = objdump_words(args.objdump, image, "calculate")
        checks = {
            "image_sha256": sha256(image) == record["image_sha256"],
            "object_sha256": sha256(obj) == case["object_sha256"],
            "readelf_symbol": [(row["value"], row["size"], row["type"]) for row in symbols]
            == [(record["function_va"], record["function_size"], "FUNC")],
            "readelf_relocations": [(row["section"], row["type"]) for row in relocations]
            == [(".rela.eh_frame", "R_AARCH64_PREL32")] and record["object_relocations"]["text"] == 0,
            "readelf_fde": [(row["pc_begin"], row["pc_end"] - row["pc_begin"], eh_frame + row["eh_frame_offset"])
                            for row in fdes]
            == [(effect["resolves_to"], effect["pc_range"], effect["fde_va"])],
            "objdump_words": len(object_words) == record["function_words"] and object_words == image_words,
            "foreign_symbol_differs": len(foreign_symbols) == 1
            and foreign_symbols[0]["size"] != record["function_size"],
        }
        rows.append({
            "case": name, "agree": all(checks.values()), "checks": checks,
            "readelf_symbol": symbols, "readelf_relocations": relocations, "readelf_fdes": fdes,
            "eh_frame_address": eh_frame, "objdump_object_words": object_words, "objdump_image_words": image_words,
            "foreign_readelf_symbol": foreign_symbols,
        })
    result = {
        "schema": "trust-cg-linked-image-crosscheck-v1",
        "run": {"schema": report["schema"], "status": report["status"],
                "source_sha": report.get("provenance", {}).get("source_sha")},
        "tools": {"readelf": tool_identity(args.readelf), "llvm_objdump": tool_identity(args.objdump)},
        "cases": rows,
        "summary": {"cases": len(rows), "agree": sum(row["agree"] for row in rows)},
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"linked-image cross-check: {result['summary']['agree']}/{result['summary']['cases']} cases agree")
    return 0 if result["summary"]["agree"] == len(rows) == 48 else 1


if __name__ == "__main__":
    sys.exit(main())
