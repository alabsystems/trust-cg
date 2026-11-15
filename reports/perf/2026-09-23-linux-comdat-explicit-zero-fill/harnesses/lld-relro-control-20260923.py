#!/usr/bin/env python3
"""Linker control for the L02-P7 `.bss.rel.ro` repair (2026-09-23).

Compiles a C global with an explicit zero-fill section attribute, links it
once with the host GNU ld (`cc`) and once with lld (`cc -fuse-ld=lld -B<dir>`),
runs both, and records each exit status and the lld image's section/segment
listing. `store` programs write the global; `load` programs only read it.
This is evidence about the linkers' placement of the input name, which is
why trust-cg refuses a MUTABLE global in `.bss.rel.ro[.*]`; it does not run
trust-cg output. Writes results.json and the listings under --out.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

SECTIONS = [".bss.rel.ro", ".bss.rel.ro.tcg", ".bss.rel.rox", ".bss.tcg"]
PROGRAMS = {
    "store": "counter = 5; return counter == 5 ? 0 : 1;",
    "load": "return counter == 0 ? 0 : 1;",
}


def run(command, cwd):
    return subprocess.run(command, cwd=cwd, capture_output=True, text=True, check=False)


def relro_sections(listing: str) -> list[str]:
    """The output sections readelf maps into the PT_GNU_RELRO segment."""
    lines = listing.splitlines()
    start = next(i for i, line in enumerate(lines) if line.strip().startswith("Type ")) + 1
    kinds = []
    for line in lines[start:]:
        if not line.strip():
            break
        if line.strip().startswith("["):
            continue
        kinds.append(line.split()[0])
    index = kinds.index("GNU_RELRO")
    mapping = next(i for i, line in enumerate(lines) if "Section to Segment mapping" in line)
    for line in lines[mapping + 2:]:
        fields = line.split()
        if fields and fields[0] == f"{index:02d}":
            return fields[1:]
    return []


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--lld-dir", type=Path, default=Path.home() / ".local/bin")
    args = parser.parse_args()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    work = out / "work"
    work.mkdir()
    env_tools = {tool: (shutil.which(tool) or "") for tool in ["cc", "ld", "readelf"]}
    lld = args.lld_dir / "ld.lld"
    results = {
        "tools": env_tools,
        "lld": str(lld),
        "lld_version": run([str(lld), "--version"], work).stdout.strip(),
        "ld_version": run(["ld", "--version"], work).stdout.splitlines()[0],
        "cases": [],
    }
    ok = True
    for index, section in enumerate(SECTIONS):
        for program, body in PROGRAMS.items():
            stem = f"case{index}-{program}"
            source = work / f"{stem}.c"
            source.write_text(
                f'__attribute__((section("{section}"))) unsigned long counter;\n'
                f"int main(void) {{ {body} }}\n"
            )
            case = {"section": section, "program": program}
            for linker, extra in [("gnu", []), ("lld", ["-fuse-ld=lld", f"-B{args.lld_dir}"])]:
                exe = work / f"{stem}-{linker}"
                link = run(["cc", "-O0", *extra, "-o", str(exe), str(source)], work)
                if link.returncode != 0:
                    case[linker] = {"link_exit": link.returncode, "stderr": link.stderr}
                    ok = False
                    continue
                status = subprocess.run([str(exe)], cwd=work, check=False).returncode
                case[linker] = {"exit": status}
                if linker == "lld":
                    listing = run(["readelf", "-S", "-l", "-W", str(exe)], work).stdout
                    (out / f"{stem}-lld.readelf.txt").write_text(listing)
                    case[linker]["relro_sections"] = relro_sections(listing)
            results["cases"].append(case)
            print(json.dumps(case), flush=True)
    # Expected: GNU ld runs every case; lld faults (SIGSEGV, -11) only for a
    # store into `.bss.rel.ro` or `.bss.rel.ro.*`.
    for case in results["cases"]:
        relro = case["section"] == ".bss.rel.ro" or case["section"].startswith(".bss.rel.ro.")
        expect_lld = -11 if relro and case["program"] == "store" else 0
        case["expected"] = {"gnu": 0, "lld": expect_lld}
        ok &= case.get("gnu", {}).get("exit") == 0 and case.get("lld", {}).get("exit") == expect_lld
        # The fault is the RELRO placement: exactly the `.bss.rel.ro` names
        # put a `.bss.rel.ro` output section inside PT_GNU_RELRO.
        ok &= relro == (".bss.rel.ro" in case.get("lld", {}).get("relro_sections", []))
    shutil.rmtree(work)
    results["verdict"] = "PASS" if ok else "FAIL"
    (out / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    print(f"verdict: {results['verdict']}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
