#!/usr/bin/env python3
"""Mutation leg for the L02-P10 per-kind relocation limits (Linux AArch64, 2026-09-23).

Each mutant removes or weakens one new refusal or pin by a single textual
replacement in the source, runs the tests that should catch it, records the
result under RUN/records/mutation, and restores the file byte for byte. A
mutant is killed when every listed command exits non-zero with each listed
test named as FAILED. The tree must be clean before and after.

Usage: mutation-reloc-limits-20260923.py WORKTREE RUN
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path

WORKTREE = Path(sys.argv[1]).resolve()
RUN = Path(sys.argv[2]).resolve()
OUT = RUN / "records" / "mutation"
HOME = Path.home()
ENV = dict(
    os.environ,
    PATH=os.pathsep.join(
        [
            str(HOME / ".local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23/bin"),
            str(HOME / ".cargo/bin"),
            os.environ["PATH"],
        ]
    ),
)
COMMON = ["--locked", "--offline", "-j", "8"]
LIB = ["cargo", "test", "-p", "trust-cg-codegen", "--lib", *COMMON, "--"]
E2E = ["cargo", "test", "-p", "trust-cg-codegen", "--test", "e2e_aarch64_link_runtime", *COMMON, "--"]
FAILED = re.compile(r"^test (\S+) \.\.\. FAILED$", re.M)

PIPELINE = "crates/trust-cg-codegen/src/pipeline.rs"
LINK_DRIVER = "crates/trust-cg-codegen/src/link_driver.rs"
DWARF = "crates/trust-cg-codegen/src/elf/dwarf.rs"
RELOC = "crates/trust-cg-codegen/src/elf/reloc.rs"

MUTANTS = [
    {
        "name": "M1-image-check-disabled",
        "file": LINK_DRIVER,
        "old": "    if uses.is_empty() {\n        return Vec::new();\n    }\n    let reason = match",
        "new": "    if true || uses.is_empty() {\n        return Vec::new();\n    }\n    let reason = match",
        "runs": [
            (LIB + ["got_page_window_output_refusal_names_each_use"],
             ["link_driver::tests::got_page_window_output_refusal_names_each_use"]),
            (E2E + ["got_page_adrp_beyond_4_gib_is_refused_by_the_link_driver"],
             ["linux_native::got_page_adrp_beyond_4_gib_is_refused_by_the_link_driver"]),
        ],
    },
    {
        "name": "M2-image-window-one-page-wider",
        "file": LINK_DRIVER,
        "old": "if farthest_up > i128::from(window.max) || farthest_down",
        "new": "if farthest_up > i128::from(window.max) + 4096 || farthest_down",
        "runs": [
            (LIB + ["got_page_reach_is_decided_from_the_linked_section_layout"],
             ["link_driver::tests::got_page_reach_is_decided_from_the_linked_section_layout"]),
        ],
    },
    {
        "name": "M3-tlsle-refusal-disabled",
        "file": PIPELINE,
        "old": "if minimum > i128::from(window.max) {",
        "new": "if minimum > i128::from(window.max) + (1 << 40) {",
        "runs": [
            (LIB + ["local_exec_tls_lower_bound_above_the_hi12_window_is_refused"],
             ["pipeline::tests::local_exec_tls_lower_bound_above_the_hi12_window_is_refused"]),
            (E2E + ["local_exec_tls_past_the_hi12_window_is_refused_by_name_at_the_edge"],
             ["local_exec_tls_past_the_hi12_window_is_refused_by_name_at_the_edge"]),
        ],
    },
    {
        "name": "M4-tlsle-tcb-not-counted",
        "file": PIPELINE,
        "old": "let minimum = i128::from(crate::elf::reloc::AARCH64_TLS_TCB_BYTES)",
        "new": "let minimum = 0",
        "runs": [
            (LIB + ["local_exec_tls_lower_bound_above_the_hi12_window_is_refused"],
             ["pipeline::tests::local_exec_tls_lower_bound_above_the_hi12_window_is_refused"]),
            (E2E + ["local_exec_tls_past_the_hi12_window_is_refused_by_name_at_the_edge"],
             ["local_exec_tls_past_the_hi12_window_is_refused_by_name_at_the_edge"]),
        ],
    },
    {
        "name": "M5-abs32-addend-edge-off-by-one",
        "file": DWARF,
        "old": "if i128::from(reloc.addend) > i128::from(window.max) {",
        "new": "if i128::from(reloc.addend) > i128::from(window.max) + 1 {",
        "runs": [
            (LIB + ["abs32_section_offset_addend_is_refused_above_the_psabi_window"],
             ["elf::dwarf::tests::abs32_section_offset_addend_is_refused_above_the_psabi_window"]),
        ],
    },
    {
        "name": "M6-tlsdesc-discharge-linker-only",
        "file": RELOC,
        "old": "Self::AdrGotPage | Self::TlsieAdrGottprelPage21 | Self::TlsdescAdrPage21 => {",
        "new": "Self::TlsdescAdrPage21 => window(PAGE21, WindowDischarge::Linker),\n            Self::AdrGotPage | Self::TlsieAdrGottprelPage21 => {",
        "runs": [
            (LIB + ["every_serializable_aarch64_relocation_kind_has_a_pinned_limit",
                    "got_page_relocations_are_the_linked_image_discharged_kinds"],
             ["elf::reloc::tests::every_serializable_aarch64_relocation_kind_has_a_pinned_limit",
              "link_driver::tests::got_page_relocations_are_the_linked_image_discharged_kinds"]),
        ],
    },
    {
        "name": "M7-tlsle-window-one-wider",
        "file": RELOC,
        "old": "                    max: (1 << 24) - 1,\n",
        "new": "                    max: 1 << 24,\n",
        "runs": [
            (LIB + ["every_serializable_aarch64_relocation_kind_has_a_pinned_limit"],
             ["elf::reloc::tests::every_serializable_aarch64_relocation_kind_has_a_pinned_limit"]),
        ],
    },
]


def git(*args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(WORKTREE), *args], check=True, capture_output=True, text=True
    ).stdout.strip()


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    head = git("rev-parse", "HEAD")
    if git("status", "--porcelain", "--untracked-files=all"):
        print("checkout is dirty; refusing to mutate", file=sys.stderr)
        return 1
    results = []
    for mutant in MUTANTS:
        path = WORKTREE / mutant["file"]
        original = path.read_bytes()
        text = original.decode()
        count = text.count(mutant["old"])
        assert count >= 1, f"{mutant['name']}: mutation site not found"
        path.write_text(text.replace(mutant["old"], mutant["new"], 1))
        runs = []
        try:
            for index, (argv, expected) in enumerate(mutant["runs"]):
                completed = subprocess.run(argv, cwd=WORKTREE, env=ENV, capture_output=True, text=True, timeout=2400)
                output = completed.stdout + completed.stderr
                log = OUT / f"{mutant['name']}-{index}.log"
                log.write_text(f"$ {' '.join(argv)}\n{output}--- exit {completed.returncode} ---\n")
                failed = FAILED.findall(output)
                runs.append({
                    "argv": argv,
                    "exit": completed.returncode,
                    "failed_tests": failed,
                    "expected_failures": expected,
                    "killed": completed.returncode != 0 and all(name in failed for name in expected),
                })
        finally:
            path.write_bytes(original)
        killed = all(run["killed"] for run in runs)
        print(f"{mutant['name']}: {'killed' if killed else 'SURVIVED'}", flush=True)
        results.append({"name": mutant["name"], "file": mutant["file"], "old": mutant["old"],
                        "new": mutant["new"], "sites_in_file": count, "runs": runs, "killed": killed})
    status_after = git("status", "--porcelain", "--untracked-files=all")
    (OUT / "results.json").write_text(json.dumps(
        {"schema": "trust-cg.l02-p10-mutation.v1", "head": head, "status_after": status_after,
         "mutants": results}, indent=2) + "\n")
    print("status after clean:", not status_after)
    return 0 if all(m["killed"] for m in results) and not status_after else 1


if __name__ == "__main__":
    sys.exit(main())
