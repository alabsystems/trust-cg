#!/usr/bin/env python3
"""Mutation leg for the staged L02-P10 GOT-page check after the merge with the L02-P9 second repair (Linux AArch64, 2026-09-23).

Each mutant removes or weakens one part of the staged GOT-page check by a single textual
replacement in the source, runs the tests that should catch it, records the
result under RUN/records/mutation, and restores the file byte for byte. A
mutant is killed when every listed command exits non-zero with each listed
test named as FAILED. The tree must be clean before and after.

Usage: mutation-reloc-limits-staged-20260923.py WORKTREE RUN
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
CLI = ["cargo", "test", "-p", "trust-cg-cli", "--test", "link_options", *COMMON, "--"]
E2E = ["cargo", "test", "-p", "trust-cg-codegen", "--test", "e2e_aarch64_link_runtime", *COMMON, "--"]
FAILED = re.compile(r"^test (\S+) \.\.\. FAILED$", re.M)

LINK_DRIVER = "crates/trust-cg-codegen/src/link_driver.rs"

MUTANTS = [
    {
        "name": "S1-got-page-link-not-staged",
        "file": LINK_DRIVER,
        "old": "    if local_exec_uses.is_empty() && got_page.is_empty() {",
        "new": "    if local_exec_uses.is_empty() {",
        "runs": [
            (LIB + ["got_page_window_refusal_never_touches_the_requested_output"],
             ["link_driver::tests::got_page_window_refusal_never_touches_the_requested_output"]),
            (E2E + ["got_page_adrp_beyond_4_gib_is_refused_by_the_link_driver"],
             ["linux_native::got_page_adrp_beyond_4_gib_is_refused_by_the_link_driver"]),
            (CLI + ["a_link_that_writes_no_output_leaves_the_output_file_alone"],
             ["linux_tls::a_link_that_writes_no_output_leaves_the_output_file_alone"]),
        ],
    },
    {
        "name": "S2-got-page-check-reads-the-requested-output",
        "file": LINK_DRIVER,
        "old": "    refused.extend(got_page_window_output_refusals_for(\n        request, got_page, &image,\n    ));",
        "new": "    refused.extend(got_page_window_output_refusals_for(\n        request, got_page, &request.output,\n    ));",
        "runs": [
            (LIB + ["got_page_window_refusal_never_touches_the_requested_output"],
             ["link_driver::tests::got_page_window_refusal_never_touches_the_requested_output"]),
            (E2E + ["got_page_adrp_beyond_4_gib_is_refused_by_the_link_driver"],
             ["linux_native::got_page_adrp_beyond_4_gib_is_refused_by_the_link_driver"]),
        ],
    },
    {
        "name": "S3-unreadable-image-reported-as-overflow",
        "file": LINK_DRIVER,
        "old": "                    LinkDiagnosticKind::Unclassified,\n                    format!(\n                        \"[TCG-LINK-GOT-PAGE-UNCHECKED]",
        "new": "                    LinkDiagnosticKind::RelocationOutOfRange,\n                    format!(\n                        \"[TCG-LINK-GOT-PAGE-UNCHECKED]",
        "runs": [
            (LIB + ["got_page_window_output_refusal_names_each_use",
                    "got_page_window_refusal_never_touches_the_requested_output"],
             ["link_driver::tests::got_page_window_output_refusal_names_each_use",
              "link_driver::tests::got_page_window_refusal_never_touches_the_requested_output"]),
        ],
    },
    {
        "name": "S4-non-regular-output-replaced",
        "file": LINK_DRIVER,
        "old": "        Ok(metadata) if !(metadata.is_file() || metadata.is_symlink()) => {",
        "new": "        Ok(metadata) if false && !(metadata.is_file() || metadata.is_symlink()) => {",
        "runs": [
            (LIB + ["got_page_window_refusal_never_touches_the_requested_output"],
             ["link_driver::tests::got_page_window_refusal_never_touches_the_requested_output"]),
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
        {"schema": "trust-cg.l02-p10-staged-mutation.v1", "head": head, "status_after": status_after,
         "mutants": results}, indent=2) + "\n")
    print("status after clean:", not status_after)
    return 0 if all(m["killed"] for m in results) and not status_after else 1


if __name__ == "__main__":
    sys.exit(main())
