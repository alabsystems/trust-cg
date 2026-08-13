#!/usr/bin/env python3
# gen_aarch64_silicon_truth.py — REGENERATOR for aarch64_silicon_truth.json.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
#
# Parses the READ-ONLY silicon ground-truth file
#   <clean>/proofs/aarch64_isa_chip.lean
# (~65k `chip_<op>_<n> : <op> <hexA> [<hexB> [<hexC>]] = <result> := rfl`
# theorems recorded from a REAL Apple M4 Pro) and emits a COMMITTED fixture
# holding the (op, operands, silicon-result) facts for exactly the integer ops
# trust-cg has an IN-HOUSE machine encoder for (aarch64_semantics.rs).
#
# INCLUSION POLICY (no silent truncation):
#   * EVERY boundary/edge fact (all `chip_*` for the in-house-encoder ops) is
#     INCLUDED — these chip theorems are already a curated boundary grid
#     (0, 1, INT_MIN, INT_MAX, all-ones, 0xFFFFFFFF, shift-by-{31,32,33,63,64,65},
#     div-by-0, INT_MIN/-1, ...), so the full per-op set is kept.
#   * Ops with NO in-house encoder in aarch64_semantics.rs are EXCLUDED and the
#     reason is logged into the fixture header (`excluded_ops`). They are NOT
#     silently dropped.
#
# Regenerate:
#   python3 crates/trust-cg-verify/tests/fixtures/gen_aarch64_silicon_truth.py \
#       $HOME/clean/proofs/aarch64_isa_chip.lean \
#       crates/trust-cg-verify/tests/fixtures/aarch64_silicon_truth.json
#   (clean SHA is read via `git -C <clean> rev-parse HEAD`).

import json
import re
import subprocess
import sys
import os

# Map Lean def name -> (bridge op tag, width, arity, arg-roles).
# arity counts the operand literals AFTER the op name. arg-roles documents how
# the literals map onto the trust-cg encoder (see the bridge test).
#
# Only ops with an in-house encoder in aarch64_semantics.rs are INCLUDED.
INCLUDED = {
    # 64-bit (X) arithmetic / logic
    "bvAdd":  ("add",  64, 2), "bvSub":  ("sub",  64, 2), "bvMul":  ("mul",  64, 2),
    "bvAnd":  ("and",  64, 2), "bvOr":   ("orr",  64, 2), "bvXor":  ("eor",  64, 2),
    "bvBic":  ("bic",  64, 2), "bvOrn":  ("orn",  64, 2),
    "bvNot":  ("mvn",  64, 1), "bvNeg":  ("neg",  64, 1),
    "bvShl":  ("lsl",  64, 2), "bvLshr": ("lsr",  64, 2), "bvAsr":  ("asr",  64, 2),
    "bvMadd": ("madd", 64, 3), "bvMsub": ("msub", 64, 3),
    "bvUdiv": ("udiv", 64, 2), "bvSdiv": ("sdiv", 64, 2),
    "bvUbfm": ("ubfm", 64, 3), "bvSbfm": ("sbfm", 64, 3),
    # 32-bit (W) forms — same in-house encoders exercised at 32-bit width.
    "bvAddW":  ("addw",  32, 2), "bvSubW":  ("subw",  32, 2), "bvMulW":  ("mulw",  32, 2),
    "bvAndW":  ("andw",  32, 2), "bvOrW":   ("orrw",  32, 2), "bvXorW":  ("eorw",  32, 2),
    "bvNotW":  ("mvnw",  32, 1), "bvNegW":  ("negw",  32, 1),
    "bvShlW":  ("lslw",  32, 2), "bvLshrW": ("lsrw",  32, 2), "bvAsrW":  ("asrw",  32, 2),
    "bvMaddW": ("maddw", 32, 3), "bvMsubW": ("msubw", 32, 3),
    "bvUdivW": ("udivw", 32, 2), "bvSdivW": ("sdivw", 32, 2),
    "bvUbfmW": ("ubfmw", 32, 3), "bvSbfmW": ("sbfmw", 32, 3),
}

# Ops present in the chip file but NOT covered by an in-house encoder. Logged.
EXCLUDED_REASONS = {
    "bvExtr":  "no in-house EXTR/funnel-shift encoder in aarch64_semantics.rs",
    "bvExtrW": "no in-house EXTR/funnel-shift encoder in aarch64_semantics.rs",
    "bvCsel":  "no in-house CSEL encoder in aarch64_semantics.rs (cond-select family)",
    "bvCselW": "no in-house CSEL encoder in aarch64_semantics.rs (cond-select family)",
    "bvCsinc": "no in-house CSINC encoder", "bvCsincW": "no in-house CSINC encoder",
    "bvCsinv": "no in-house CSINV encoder", "bvCsinvW": "no in-house CSINV encoder",
    "bvCsneg": "no in-house CSNEG encoder", "bvCsnegW": "no in-house CSNEG encoder",
    "addsN": "NZCV flag def; flags are produced via crate::nzcv, not the value encoders here",
    "addsZ": "NZCV flag def", "addsC": "NZCV flag def", "addsV": "NZCV flag def",
    "addsNW": "NZCV flag def", "addsZW": "NZCV flag def", "addsCW": "NZCV flag def", "addsVW": "NZCV flag def",
    "subsN": "NZCV flag def", "subsZ": "NZCV flag def", "subsC": "NZCV flag def", "subsV": "NZCV flag def",
    "subsNW": "NZCV flag def", "subsZW": "NZCV flag def", "subsCW": "NZCV flag def", "subsVW": "NZCV flag def",
    "cmpN": "NZCV flag def", "cmpZ": "NZCV flag def", "cmpC": "NZCV flag def", "cmpV": "NZCV flag def",
    "cmpNW": "NZCV flag def", "cmpZW": "NZCV flag def", "cmpCW": "NZCV flag def", "cmpVW": "NZCV flag def",
    "andsN": "NZCV flag def", "andsZ": "NZCV flag def", "andsV": "NZCV flag def", "andsC": "NZCV flag def",
    "andsNW": "NZCV flag def", "andsZW": "NZCV flag def", "andsVW": "NZCV flag def", "andsCW": "NZCV flag def",
    "tstN": "NZCV flag def", "tstZ": "NZCV flag def", "tstV": "NZCV flag def", "tstC": "NZCV flag def",
}

# A chip theorem line: `theorem chip_<def>_<n> : <def> <args...> = <result> := rfl`
LINE = re.compile(
    r"^theorem\s+chip_([A-Za-z0-9]+)_(\d+)\s*:\s*([A-Za-z0-9]+)\s+(.*?)\s*=\s*(\S+)\s*:=\s*rfl\s*$"
)

def parse_num(tok):
    tok = tok.strip()
    if tok.lower().startswith("0x"):
        return int(tok, 16)
    return int(tok, 10)

def main():
    chip_path = sys.argv[1]
    out_path = sys.argv[2]
    clean_dir = os.path.dirname(os.path.dirname(chip_path))
    try:
        clean_sha = subprocess.check_output(
            ["git", "-C", clean_dir, "rev-parse", "HEAD"]
        ).decode().strip()
    except Exception:
        clean_sha = "UNKNOWN"

    facts = []
    included_counts = {}
    excluded_counts = {}
    seen_defs = set()
    total_chip_lines = 0

    with open(chip_path) as f:
        for line in f:
            line = line.rstrip("\n")
            m = LINE.match(line)
            if not m:
                continue
            total_chip_lines += 1
            def_name_a, idx, def_name_b, args_str, result = m.groups()
            # def_name in the prefix and in the body must agree.
            if def_name_a != def_name_b:
                continue
            seen_defs.add(def_name_a)
            if def_name_a not in INCLUDED:
                excluded_counts[def_name_a] = excluded_counts.get(def_name_a, 0) + 1
                continue
            tag, width, arity = INCLUDED[def_name_a]
            arg_toks = args_str.split()
            if len(arg_toks) != arity:
                # malformed / unexpected arity — log by skipping into a counter.
                excluded_counts.setdefault("__arity_mismatch__", 0)
                excluded_counts["__arity_mismatch__"] += 1
                continue
            try:
                operands = [parse_num(t) for t in arg_toks]
                res = parse_num(result)
            except ValueError:
                excluded_counts.setdefault("__parse_error__", 0)
                excluded_counts["__parse_error__"] += 1
                continue
            facts.append({
                "op": tag,
                "lean_def": def_name_a,
                "width": width,
                "operands": operands,
                "result": res,
                "theorem": f"chip_{def_name_a}_{idx}",
            })
            included_counts[def_name_a] = included_counts.get(def_name_a, 0) + 1

    # Build the excluded-ops log: every seen def NOT included, with a reason.
    excluded_ops = {}
    for d in sorted(seen_defs):
        if d in INCLUDED:
            continue
        excluded_ops[d] = {
            "count": excluded_counts.get(d, 0),
            "reason": EXCLUDED_REASONS.get(d, "not an in-house-encoded integer op"),
        }

    doc = {
        "_header": {
            "purpose": "AArch64 integer silicon ground truth for the B-aarch64-int "
                       "differential bridge: each fact is a REAL Apple M4 Pro result "
                       "(:= rfl chip theorem) for an op trust-cg has an in-house encoder for.",
            "source_file": "proofs/aarch64_isa_chip.lean",
            "source_repo": "clean (sibling tree)",
            "clean_sha": clean_sha,
            "recorded_on": "Apple M4 Pro (real silicon, on-chip differential harness)",
            "regen": "python3 crates/trust-cg-verify/tests/fixtures/"
                     "gen_aarch64_silicon_truth.py <clean>/proofs/aarch64_isa_chip.lean "
                     "crates/trust-cg-verify/tests/fixtures/aarch64_silicon_truth.json",
            "inclusion_policy": "ALL chip theorems for every op with an in-house encoder "
                                "in aarch64_semantics.rs are included (no per-op subsampling): "
                                "the chip grid is already a curated boundary set. Ops with no "
                                "in-house encoder are excluded and logged in excluded_ops.",
            "total_chip_theorem_lines_scanned": total_chip_lines,
            "included_fact_count": len(facts),
            "included_per_op": included_counts,
            "excluded_ops": excluded_ops,
        },
        "facts": facts,
    }

    with open(out_path, "w") as f:
        json.dump(doc, f, indent=1)
        f.write("\n")

    print(f"clean SHA: {clean_sha}")
    print(f"scanned {total_chip_lines} chip theorem lines")
    print(f"included {len(facts)} facts across {len(included_counts)} ops")
    print(f"excluded {len(excluded_ops)} op families (logged in fixture header)")

if __name__ == "__main__":
    main()
