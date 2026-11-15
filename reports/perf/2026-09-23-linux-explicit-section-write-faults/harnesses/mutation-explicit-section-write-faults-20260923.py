#!/usr/bin/env python3
"""Source-mutation controls for the L02-P3 explicit-section placement repair
(default-link write faults), 2026-09-23.

Each mutation removes one new refusal (or drifts the GNU column of the
placement table) with an exact, single-occurrence string replacement, runs
the targets whose rows must catch it, records the libtest outcome, and
restores the file with `git checkout --`. A mutation is caught when every
target fails and every test named in `must_fail` is reported FAILED. The
e2e run keeps a private TMPDIR with TCG_RETAIN_TEST_EVIDENCE=1 and
TCG_REQUIRE_LLD=1, so the native control links and runs every object that
escapes its refusal under GNU ld 2.42 and LLD 22.1.6 and leaves it (and its
run record) on disk: removing a refusal lets a faulting object through, and
the object is retained. The source tree must be clean before and after.
Writes results.json, one log per target and one diff per mutation under
--out (outside the source tree); `--only NAME` runs a subset (the archive
merges the per-batch results).
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
SECTIONS = "crates/trust-cg-codegen/src/object_sections.rs"
E2E = ("e2e", ["--test", "e2e_aarch64_elf_sections"])
UNIT = ("unit", ["--lib", "object_sections"])
NATIVE = "linux_native::refused_sections_fault_or_misplace_trust_cg_bytes_under_the_named_linker"

MUTATIONS = [
    {
        "name": "special-names-admitted",
        "what": "names a linker parses, synthesizes, types, drops or discards, or crtstuff "
                "walks, are admitted as data again (the pre-repair catch-all)",
        "old": "    if let Some(reason) = rule.and_then(|rule| rule.special_reason(name)) {",
        "new": "    if let Some(reason) = rule.and_then(|rule| rule.special_reason(name)).filter(|_| false) {",
        "targets": [UNIT, E2E],
        "must_fail": [
            "object_sections::tests::elf_linker_special_names_are_refused_for_data_globals",
            "unhonorable_elf_sections_are_refused_by_name",
            NATIVE,
        ],
    },
    {
        "name": "write-protected-admitted",
        "what": "a mutable global in a read-only or PT_GNU_RELRO output (`.rodata1`, `.toc`, "
                "`.rodata*`, `.data.rel.ro*`) is admitted",
        "old": "    if global.mutable\n        && let Some(reason) = write_protected\n    {",
        "new": "    if false\n        && let Some(reason) = write_protected\n    {",
        "targets": [UNIT, E2E],
        "must_fail": [
            "object_sections::tests::elf_linker_special_names_are_refused_for_data_globals",
            "unhonorable_elf_sections_are_refused_by_name",
            NATIVE,
        ],
    },
    {
        "name": "mutable-tables-admitted",
        "what": "a mutable constructor/destructor table (PT_GNU_RELRO under both linkers) "
                "is admitted",
        "old": "        check_pointer_table(global, what)?;\n        if global.mutable\n",
        "new": "        check_pointer_table(global, what)?;\n        if false\n",
        "targets": [UNIT, E2E],
        "must_fail": [
            "object_sections::tests::elf_linker_special_names_are_refused_for_data_globals",
            "unhonorable_elf_sections_are_refused_by_name",
            NATIVE,
        ],
    },
    {
        "name": "tcommon-admitted",
        "what": "a non-TLS global in `.tcommon` (GNU ld's `.tbss` output) is admitted",
        "old": "        && let Some(reason) = rule.and_then(|rule| rule.thread_local_reason(name))",
        "new": "        && let Some(reason) = rule.and_then(|rule| rule.thread_local_reason(name)).filter(|_| false)",
        "targets": [UNIT, E2E],
        "must_fail": [
            "object_sections::tests::elf_linker_special_names_are_refused_for_data_globals",
            "unhonorable_elf_sections_are_refused_by_name",
            NATIVE,
        ],
    },
    {
        "name": "executable-outputs-narrowed",
        "what": "the executable refusal covers only `.text*`, `.init` and `.fini` again "
                "(the pre-repair rule; `.stub` and `.iplt` admitted)",
        "old": "    if let Some(reason) = rule.and_then(|rule| rule.executable_reason(name)) {",
        "new": "    if let Some(reason) = rule.and_then(|rule| rule.executable_reason(name))"
               ".filter(|_| is_dotted(name, \".text\") || name == \".init\" || name == \".fini\") {",
        "targets": [UNIT, E2E],
        "must_fail": [
            "object_sections::tests::elf_linker_special_names_are_refused_for_data_globals",
            "unhonorable_elf_sections_are_refused_by_name",
            NATIVE,
        ],
    },
    {
        "name": "comdat-collision-admitted",
        "what": "an implicit COMDAT `<base>.<symbol>` that leaves its base's rule "
                "(`rel.ro` -> `.data.rel.ro`/`.bss.rel.ro`) is admitted (the pre-repair naming)",
        "old": "        if same_row {",
        "new": "        if true || same_row {",
        "targets": [UNIT, E2E],
        "must_fail": [
            "object_sections::tests::elf_implicit_comdat_names_stay_in_their_base_rule",
            "implicit_comdat_sections_leaving_their_placement_rule_are_refused_by_name",
            NATIVE,
        ],
    },
    {
        "name": "function-common-admitted",
        "what": "a function section named `COMMON` (folded into `.bss` by both linkers) "
                "is admitted",
        "old": "    if let Some(rule) = elf_name_rule(name)\n        && rule\n",
        "new": "    if let Some(rule) = elf_name_rule(name).filter(|_| false)\n        && rule\n",
        "targets": [UNIT, E2E],
        "must_fail": [
            "object_sections::tests::elf_function_sections_accept_only_executable_names",
            "unhonorable_function_sections_are_refused_by_name",
        ],
    },
    {
        "name": "gnu-column-drift",
        "what": "the table's GNU column forgets that GNU ld folds `.tcommon` into `.tbss` "
                "(the script cross-check must catch the drift)",
        "old": "ElfNameRule::new(&[\".tcommon\"], ThreadLocal(\".tbss\"), Orphan),",
        "new": "ElfNameRule::new(&[\".tcommon\"], Orphan, Orphan),",
        "targets": [UNIT, E2E],
        "must_fail": [
            "object_sections::tests::elf_name_rules_match_the_gnu_ld_2_42_default_script",
            "object_sections::tests::elf_linker_special_names_are_refused_for_data_globals",
            "unhonorable_elf_sections_are_refused_by_name",
            NATIVE,
        ],
    },
]


def failed_names(log: str) -> set[str]:
    """Tests libtest reports FAILED, from the per-test lines and from the
    final `failures:` list (a test that prints under --nocapture ends its
    `test NAME ...` line early)."""
    names = set(re.findall(r"^test (\S+) \.\.\. FAILED$", log, re.MULTILINE))
    for block in re.findall(r"^failures:\n((?:    \S+\n)+)", log, re.MULTILINE):
        names |= {line.strip() for line in block.splitlines()}
    return names


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
    parser.add_argument("--only", action="append", default=[])
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
        if args.only and mutation["name"] not in args.only:
            continue
        path = source / SECTIONS
        text = path.read_text()
        assert text.count(mutation["old"]) == 1, mutation["name"]
        path.write_text(text.replace(mutation["old"], mutation["new"]))
        diff = run(["git", "diff", "--", SECTIONS], source).stdout
        (out / f"{mutation['name']}.diff").write_text(diff)
        runs, failed = [], set()
        try:
            for label, target in mutation["targets"]:
                run_env = dict(env)
                tmp = out / f"{mutation['name']}-tmp-{label}"
                tmp.mkdir()
                run_env["TMPDIR"] = str(tmp)
                run_env["TCG_RETAIN_TEST_EVIDENCE"] = "1"
                run_env["TCG_REQUIRE_LLD"] = "1"
                command = ["cargo", "test", "--locked", "--offline", "-j", str(args.jobs), "-p",
                           "trust-cg-codegen", *target[:1]]
                if target[0] == "--test":
                    command.append(target[1])
                    command += ["--", "--test-threads=1", "--nocapture"]
                else:
                    command += [target[1], "--", "--test-threads=1"]
                result = run(command, source, run_env, timeout=1500)
                log = result.stdout + result.stderr
                (out / f"{mutation['name']}-{label}.log").write_text(log)
                names = failed_names(log)
                failed |= names
                runs.append({
                    "label": label, "command": command, "tmpdir": str(tmp),
                    "exit": result.returncode,
                    "result_lines": [line for line in log.splitlines()
                                     if line.startswith("test result:")],
                    "failed_tests": sorted(names),
                })
        finally:
            run(["git", "checkout", "--", SECTIONS], source)
        caught = all(r["exit"] != 0 for r in runs) and \
            all(name in failed for name in mutation["must_fail"])
        all_caught &= caught
        results["mutations"].append({
            "name": mutation["name"], "what": mutation["what"], "file": SECTIONS,
            "runs": runs, "failed_tests": sorted(failed), "must_fail": mutation["must_fail"],
            "caught": caught, "restored_clean": clean(source),
        })
        print(f"{mutation['name']}: caught={caught} failed={sorted(failed)}", flush=True)
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
