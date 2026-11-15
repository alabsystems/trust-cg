#!/usr/bin/env python3
"""Source-mutation controls for the L02-P7 COMDAT/explicit zero-fill run.

Each mutation re-introduces one pre-change behavior (or a flipped section
type) with an exact, single-occurrence string replacement, runs the target
whose rows must catch it, records the libtest outcome, and restores the file
with `git checkout --`. A mutation is caught when its target fails and every
named test in `must_fail` is reported FAILED. The source tree must be clean
before and after. Writes results.json, one log and one diff per mutation
under --out (outside the source tree).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

PKG = Path.home() / ".local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23"
PIPELINE = "crates/trust-cg-codegen/src/pipeline.rs"
SECTIONS = "crates/trust-cg-codegen/src/object_sections.rs"

MUTATIONS = [
    {
        "name": "comdat-arm-progbits",
        "what": "the COMDAT arm maps a zero-fill class back to .data/.tdata PROGBITS "
                "(the base behavior)",
        "file": PIPELINE,
        "old": "let implicit = ElfImplicitSection::of(global);",
        "new": "let implicit = match ElfImplicitSection::of(global) { "
               "ElfImplicitSection::Bss => ElfImplicitSection::Data, "
               "ElfImplicitSection::Tbss => ElfImplicitSection::Tdata, other => other };",
        "target": "e2e_aarch64_elf_stack_zero_fill",
        "must_fail": [
            "zero_link_once_globals_and_tls_templates_are_grouped_nobits_without_file_bytes",
            "link_once_oracle_catches_type_group_flag_and_membership_mutations",
            "native::linux_link_once_zero_data_and_tls_share_one_instance_across_objects",
        ],
    },
    {
        "name": "tbss-type-progbits",
        "what": "the .tbss implicit class is typed SHT_PROGBITS (a flipped section type)",
        "file": SECTIONS,
        "old": "Self::Bss | Self::Tbss => SHT_NOBITS,\n"
               "            Self::Data | Self::Rodata | Self::DataRelRo | Self::Tdata => SHT_PROGBITS,",
        "new": "Self::Bss => SHT_NOBITS,\n"
               "            Self::Data | Self::Rodata | Self::DataRelRo | Self::Tdata | Self::Tbss => SHT_PROGBITS,",
        "target": "e2e_aarch64_elf_stack_zero_fill",
        "must_fail": [
            "zero_link_once_globals_and_tls_templates_are_grouped_nobits_without_file_bytes",
            "zero_initialized_globals_and_tls_templates_use_nobits_without_file_bytes",
            "native::linux_link_once_zero_data_and_tls_share_one_instance_across_objects",
        ],
    },
    {
        "name": "explicit-zero-fill-refused",
        "what": "every explicit zero-fill name is refused as [TCG-SECTION-NOBITS] again "
                "(the base behavior)",
        "file": SECTIONS,
        "old": "        if !is_elf_zero_fill(global) {\n            return refuse(",
        "new": "        if true {\n            return refuse(",
        "target": "e2e_aarch64_elf_sections",
        "must_fail": [
            "explicit_zero_fill_sections_are_nobits_without_file_bytes",
            "linux_native::explicit_zero_fill_sections_link_run_and_take_no_file_bytes",
        ],
    },
    {
        "name": "explicit-nonzero-admitted",
        "what": "a nonzero initializer in an explicit zero-fill name is admitted as "
                "NOBITS (the refusal pin must catch it)",
        "file": SECTIONS,
        "old": "        if !is_elf_zero_fill(global) {\n            return refuse(",
        "new": "        if false {\n            return refuse(",
        "target": "e2e_aarch64_elf_sections",
        "must_fail": ["unhonorable_elf_sections_are_refused_by_name"],
    },
    {
        "name": "bss-rel-ro-mutable-admitted",
        "what": "a mutable global in `.bss.rel.ro[.*]` is admitted as writable NOBITS "
                "again (the first L02-P7 change; lld faults on the first store)",
        "file": SECTIONS,
        "old": "if global.mutable && is_dotted(name, \".bss.rel.ro\") {",
        "new": "if false && global.mutable && is_dotted(name, \".bss.rel.ro\") {",
        "target": "e2e_aarch64_elf_sections",
        "must_fail": ["unhonorable_elf_sections_are_refused_by_name"],
    },
]


def run(command, cwd, env=None, **kwargs):
    return subprocess.run(command, cwd=cwd, env=env, capture_output=True, text=True,
                          check=False, **kwargs)


def clean(source: Path) -> bool:
    return run(["git", "status", "--porcelain", "--untracked-files=all"], source).stdout == ""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--jobs", type=int, default=8)
    args = parser.parse_args()
    source, out = args.source.resolve(), args.out.resolve()
    if out.is_relative_to(source):
        parser.error("--out must be outside the source tree")
    out.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ)
    env["PATH"] = f"{PKG / 'bin'}:{Path.home() / '.cargo/bin'}:{env['PATH']}"
    env["LC_ALL"] = "C"
    env.pop("TCG_RETAIN_TEST_EVIDENCE", None)
    head = run(["git", "rev-parse", "HEAD"], source).stdout.strip()
    if not clean(source):
        print("source tree is not clean", file=sys.stderr)
        return 2
    results = {"started": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "head": head,
               "mutations": []}
    all_caught = True
    for mutation in MUTATIONS:
        path = source / mutation["file"]
        text = path.read_text()
        assert text.count(mutation["old"]) == 1, mutation["name"]
        path.write_text(text.replace(mutation["old"], mutation["new"]))
        diff = run(["git", "diff", "--", mutation["file"]], source).stdout
        (out / f"{mutation['name']}.diff").write_text(diff)
        command = ["cargo", "test", "--locked", "--offline", "-j", str(args.jobs), "-p",
                   "trust-cg-codegen", "--test", mutation["target"], "--", "--test-threads=1"]
        try:
            result = run(command, source, env, timeout=3000)
        finally:
            run(["git", "checkout", "--", mutation["file"]], source)
        log = result.stdout + result.stderr
        (out / f"{mutation['name']}.log").write_text(log)
        failed = sorted(set(re.findall(r"^test (\S+) \.\.\. FAILED$", log, re.MULTILINE)))
        lines = [line for line in log.splitlines() if line.startswith("test result:")]
        caught = result.returncode != 0 and all(name in failed for name in mutation["must_fail"])
        all_caught &= caught
        results["mutations"].append({
            "name": mutation["name"], "what": mutation["what"], "file": mutation["file"],
            "target": mutation["target"], "command": command, "exit": result.returncode,
            "result_lines": lines, "failed_tests": failed, "must_fail": mutation["must_fail"],
            "caught": caught, "restored_clean": clean(source),
        })
        print(f"{mutation['name']}: exit={result.returncode} caught={caught} failed={failed}",
              flush=True)
    results["finished"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    results["head_after"] = run(["git", "rev-parse", "HEAD"], source).stdout.strip()
    results["clean_after"] = clean(source)
    results["verdict"] = "PASS" if all_caught and results["clean_after"] and \
        results["head_after"] == head else "FAIL"
    (out / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    print(f"verdict: {results['verdict']}")
    return 0 if results["verdict"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
