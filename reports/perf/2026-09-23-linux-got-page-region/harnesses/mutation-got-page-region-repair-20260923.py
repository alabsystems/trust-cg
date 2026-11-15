#!/usr/bin/env python3
"""Mutation leg for the L02-P10 second repair: GOT slots in non-allocated sections (Linux AArch64, 2026-09-23).

Each mutant weakens one part of the repaired check by a single textual
replacement in the source, runs the tests that should catch it, records the
result under RUN/records/mutation, and restores the file byte for byte. A
mutant is killed when every listed command exits non-zero with each listed
test named as FAILED. The tree must be clean before and after.

R1 drops the non-allocated sections again, R2 lets a stripped image be
shown in reach by its segments, and R3 ignores a writable non-allocated
section at address 0. S1-S6 are the first repair's mutants, re-run on this
head: S1 restores the name-only region, S2 the region the review suggested
(`.got*` names, the sections holding a dynamic relocation target, every
section only without dynamic targets).

Usage: mutation-got-page-region-repair-20260923.py WORKTREE RUN [MUTANT ...]
With mutant names, only those run, and their entries in an existing
RUN/records/mutation/results.json are replaced.
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
SELECTED = sys.argv[3:]
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

LINK_DRIVER = "crates/trust-cg-codegen/src/link_driver.rs"
REGION_START = "    const SHT_NOBITS: u32 = 8;\n    let mut slots = Vec::new();\n"

PLACED = "        if flags & SHF_ALLOC == 0 && address == 0 && flags & SHF_WRITE == 0 {\n"

MUTANTS = [
    {
        "name": "R1-non-allocated-sections-dropped",
        "file": LINK_DRIVER,
        "old": PLACED,
        # `true ||` keeps SHF_WRITE referenced: the crate denies dead code.
        "new": "        if flags & SHF_ALLOC == 0 && (true || address == 0 && flags & SHF_WRITE == 0) {\n",
        "runs": [
            (LIB + ["a_placed_non_allocated_section_is_a_possible_slot_region"],
             ["link_driver::tests::a_placed_non_allocated_section_is_a_possible_slot_region"]),
            (E2E + ["a_got_in_a_non_allocated_section_is_found"],
             ["linux_native::a_got_in_a_non_allocated_section_is_found"]),
        ],
    },
    {
        "name": "R2-stripped-image-shown-by-segments",
        "file": LINK_DRIVER,
        "old": "        if !self.section_headers {\n",
        "new": "        if false && !self.section_headers {\n",
        "runs": [
            (LIB + ["stripped_section_headers_are_read_through_segments_and_dynamic_tags",
                    "got_page_reach_falls_back_to_loadable_segments"],
             ["link_driver::tests::stripped_section_headers_are_read_through_segments_and_dynamic_tags",
              "link_driver::tests::got_page_reach_falls_back_to_loadable_segments"]),
            (E2E + ["a_got_in_a_non_allocated_section_is_found"],
             ["linux_native::a_got_in_a_non_allocated_section_is_found"]),
        ],
    },
    {
        "name": "R3-writable-section-at-zero-ignored",
        "file": LINK_DRIVER,
        "old": PLACED,
        "new": "        if flags & SHF_ALLOC == 0 && address == 0 && (true || flags & SHF_WRITE == 0) {\n",
        "runs": [
            (LIB + ["a_placed_non_allocated_section_is_a_possible_slot_region"],
             ["link_driver::tests::a_placed_non_allocated_section_is_a_possible_slot_region"]),
        ],
    },
    {
        "name": "S1-name-only-got-region",
        "file": LINK_DRIVER,
        "old": REGION_START,
        "new": (
            "    const SHT_NOBITS: u32 = 8;\n"
            "    if let Some(sections) = sections {\n"
            "        let mut named = Vec::new();\n"
            "        for section in sections {\n"
            "            if section.name == \".got\" || section.name.starts_with(\".got.\") {\n"
            "                named.extend(ImageRegion::new(format!(\"`{}`\", section.name), section.address, section.size)?);\n"
            "            }\n"
            "        }\n"
            "        if !named.is_empty() {\n"
            "            return Ok(named);\n"
            "        }\n"
            "    }\n"
            "    let mut slots = Vec::new();\n"
        ),
        "runs": [
            (LIB + ["a_got_renamed_by_a_linker_script_is_a_possible_slot_region"],
             ["link_driver::tests::a_got_renamed_by_a_linker_script_is_a_possible_slot_region"]),
            (E2E + ["a_got_moved_by_a_linker_script_is_refused_whatever_its_name",
                    "a_got_slot_without_a_dynamic_relocation_is_still_found"],
             ["linux_native::a_got_moved_by_a_linker_script_is_refused_whatever_its_name",
              "linux_native::a_got_slot_without_a_dynamic_relocation_is_still_found"]),
        ],
    },
    {
        "name": "S2-names-and-dynamic-relocations-only",
        "file": LINK_DRIVER,
        "old": REGION_START,
        "new": (
            "    const SHT_NOBITS: u32 = 8;\n"
            "    if let (Some(sections), false) = (sections, targets.is_empty()) {\n"
            "        let mut regions = Vec::new();\n"
            "        for section in sections {\n"
            "            let Some(region) = ImageRegion::new(format!(\"`{}`\", section.name), section.address, section.size)? else { continue };\n"
            "            let named = section.name == \".got\" || section.name.starts_with(\".got.\");\n"
            "            if named || targets.iter().any(|target| region.low <= target.address && target.address <= region.high) {\n"
            "                regions.push(region);\n"
            "            }\n"
            "        }\n"
            "        return Ok(regions);\n"
            "    }\n"
            "    let mut slots = Vec::new();\n"
        ),
        "runs": [
            (LIB + ["a_got_renamed_by_a_linker_script_is_a_possible_slot_region"],
             ["link_driver::tests::a_got_renamed_by_a_linker_script_is_a_possible_slot_region"]),
            (E2E + ["a_got_slot_without_a_dynamic_relocation_is_still_found"],
             ["linux_native::a_got_slot_without_a_dynamic_relocation_is_still_found"]),
        ],
    },
    {
        "name": "S3-dynamic-section-not-read",
        "file": LINK_DRIVER,
        "old": "    let mut targets = dynamic_targets(bytes, &segments)?;\n",
        "new": "    let mut targets = dynamic_targets(bytes, &[])?;\n",
        "runs": [
            (LIB + ["stripped_section_headers_are_read_through_segments_and_dynamic_tags",
                    "a_certain_overflow_needs_a_named_slot_out_of_reach_of_every_code_byte"],
             ["link_driver::tests::stripped_section_headers_are_read_through_segments_and_dynamic_tags",
              "link_driver::tests::a_certain_overflow_needs_a_named_slot_out_of_reach_of_every_code_byte"]),
            (E2E + ["got_page_adrp_beyond_4_gib_is_refused_by_the_link_driver",
                    "a_got_moved_by_a_linker_script_is_refused_whatever_its_name"],
             ["linux_native::got_page_adrp_beyond_4_gib_is_refused_by_the_link_driver",
              "linux_native::a_got_moved_by_a_linker_script_is_refused_whatever_its_name"]),
        ],
    },
    {
        "name": "S4-unproven-reported-as-overflow",
        "file": LINK_DRIVER,
        "old": ("                    None => (\n                        LinkDiagnosticKind::Unclassified,\n"
                "                        format!(\n                            \"[TCG-LINK-GOT-PAGE-UNPROVEN]"),
        "new": ("                    None => (\n                        LinkDiagnosticKind::RelocationOutOfRange,\n"
                "                        format!(\n                            \"[TCG-LINK-GOT-PAGE-UNPROVEN]"),
        "runs": [
            (LIB + ["got_page_window_output_refusal_names_each_use",
                    "got_page_window_refusal_never_touches_the_requested_output"],
             ["link_driver::tests::got_page_window_output_refusal_names_each_use",
              "link_driver::tests::got_page_window_refusal_never_touches_the_requested_output"]),
            (E2E + ["far_code_without_got_references_is_refused_as_unproven",
                    "a_got_moved_by_a_linker_script_is_refused_whatever_its_name"],
             ["linux_native::far_code_without_got_references_is_refused_as_unproven",
              "linux_native::a_got_moved_by_a_linker_script_is_refused_whatever_its_name"]),
        ],
    },
    {
        "name": "S5-certainty-ignores-the-window",
        "file": LINK_DRIVER,
        "old": "            if in_window(nearest) {\n",
        "new": "            if false && in_window(nearest) {\n",
        "runs": [
            (LIB + ["a_certain_overflow_needs_a_named_slot_out_of_reach_of_every_code_byte"],
             ["link_driver::tests::a_certain_overflow_needs_a_named_slot_out_of_reach_of_every_code_byte"]),
            (E2E + ["a_got_moved_by_a_linker_script_is_refused_whatever_its_name"],
             ["linux_native::a_got_moved_by_a_linker_script_is_refused_whatever_its_name"]),
        ],
    },
    {
        "name": "S6-local-symbol-attributed",
        "file": LINK_DRIVER,
        "old": "        if use_.local {\n            return None;\n        }\n",
        "new": "        if false && use_.local {\n            return None;\n        }\n",
        "runs": [
            (LIB + ["a_certain_overflow_needs_a_named_slot_out_of_reach_of_every_code_byte"],
             ["link_driver::tests::a_certain_overflow_needs_a_named_slot_out_of_reach_of_every_code_byte"]),
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
    unknown = [name for name in SELECTED if name not in {m["name"] for m in MUTANTS}]
    assert not unknown, f"unknown mutants {unknown}"
    results_path = OUT / "results.json"
    previous = json.loads(results_path.read_text()) if SELECTED and results_path.exists() else None
    if previous is not None:
        assert previous["head"] == head, "earlier mutants ran on another head"
    results = {m["name"]: m for m in (previous or {}).get("mutants", [])}
    for mutant in MUTANTS:
        if SELECTED and mutant["name"] not in SELECTED:
            continue
        path = WORKTREE / mutant["file"]
        original = path.read_bytes()
        text = original.decode()
        count = text.count(mutant["old"])
        assert count == 1, f"{mutant['name']}: mutation site found {count} times"
        path.write_text(text.replace(mutant["old"], mutant["new"], 1))
        runs = []
        try:
            for index, (argv, expected) in enumerate(mutant["runs"]):
                completed = subprocess.run(argv, cwd=WORKTREE, env=ENV, capture_output=True, text=True, timeout=1150)
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
        results[mutant["name"]] = {"name": mutant["name"], "file": mutant["file"], "old": mutant["old"],
                                   "new": mutant["new"], "sites_in_file": count, "runs": runs, "killed": killed}
    status_after = git("status", "--porcelain", "--untracked-files=all")
    ordered = [results[m["name"]] for m in MUTANTS if m["name"] in results]
    results_path.write_text(json.dumps(
        {"schema": "trust-cg.l02-p10-got-page-region-repair-mutation.v1", "head": head, "status_after": status_after,
         "mutants": ordered}, indent=2) + "\n")
    print("status after clean:", not status_after)
    return 0 if all(m["killed"] for m in ordered) and not status_after else 1


if __name__ == "__main__":
    sys.exit(main())
