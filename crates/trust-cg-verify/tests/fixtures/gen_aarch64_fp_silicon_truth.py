#!/usr/bin/env python3
# gen_aarch64_fp_silicon_truth.py — REGENERATOR for aarch64_fp_silicon_truth.json.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
#
# Parses the READ-ONLY Apple-M4-silicon FP ground-truth files in the sibling
# Clean tree:
#   <clean>/proofs/aarch64_fp_chip.lean        (classify / FABS / FNEG / FCMP /
#                                                FMIN / FMAX / FMINNM / FMAXNM)
#   <clean>/proofs/aarch64_fp_arith_chip.lean  (FADD / FMUL, RNE)
#   <clean>/proofs/aarch64_fp_cvt_chip.lean    (FCVT widen/narrow + f<->int)
# Each generated theorem body has the shape
#   <def> <listBool-a> [<listBool-b>] = <listBool-or-true/false-result> := rfl
# where a `List Bool` literal is LSB-first ([false, true, ...] -> bit0, bit1...).
# We turn each into a (op, in-bit-widths, operand-integers, result, kind) FACT
# for exactly the ops trust-cg now has an INTEGER-ONLY bit-model for in
# crates/trust-cg-verify/src/fp_bitmodel.rs.
#
# FDIV/FSQRT (aarch64_fp_divsqrt_chip) are NOW PORTED to the Rust bit-model
# (integer-only long-division / digit-by-digit sqrt + remainder-sticky) and are
# INCLUDED. FMIN/FMAX/FMINNM/FMAXNM, the per-flag FCMP, and classify facts are
# also in scope. `deferred_ops` is now empty for AArch64 scalar binary32/binary64.
#
# INCLUSION POLICY (no silent truncation): EVERY chip theorem for every op the
# bit-model implements is INCLUDED. Ops with no bit-model entry are EXCLUDED and
# logged with a reason. Parse failures abort (no quiet drop).
#
# Regenerate:
#   python3 crates/trust-cg-verify/tests/fixtures/gen_aarch64_fp_silicon_truth.py \
#       ~/clean \
#       crates/trust-cg-verify/tests/fixtures/aarch64_fp_silicon_truth.json
#   (clean SHA is read via `git -C <clean> rev-parse HEAD`.)

import json
import re
import subprocess
import sys
import os

# Clean def name -> (bridge op tag, kind, [operand widths], result width/kind).
# kind drives how the bridge re-runs the Rust bit-model. result "bool" => the
# Lean body ends in `= true/false`; otherwise the result is a List Bool integer.
#
# Widths: input/output bit widths of the List Bool operands/result.
INCLUDED = {
    # ---- classify (foundation): one f-operand -> bool.
    "isNaN32": ("isNaN", "classify", [32], "bool"),
    "isNaN64": ("isNaN", "classify", [64], "bool"),
    "isInf32": ("isInf", "classify", [32], "bool"),
    "isInf64": ("isInf", "classify", [64], "bool"),
    "isZero32": ("isZero", "classify", [32], "bool"),
    "isZero64": ("isZero", "classify", [64], "bool"),
    "isNormal32": ("isNormal", "classify", [32], "bool"),
    "isNormal64": ("isNormal", "classify", [64], "bool"),
    "isSubnormal32": ("isSubnormal", "classify", [32], "bool"),
    "isSubnormal64": ("isSubnormal", "classify", [64], "bool"),
    "isQNaN32": ("isQNaN", "classify", [32], "bool"),
    "isQNaN64": ("isQNaN", "classify", [64], "bool"),
    "isSNaN32": ("isSNaN", "classify", [32], "bool"),
    "isSNaN64": ("isSNaN", "classify", [64], "bool"),
    # ---- FABS / FNEG: one f-operand -> f.
    "fabs32": ("fabs", "unary", [32], 32),
    "fabs64": ("fabs", "unary", [64], 64),
    "fneg32": ("fneg", "unary", [32], 32),
    "fneg64": ("fneg", "unary", [64], 64),
    # ---- FCMP -> NZCV per-flag: two f-operands -> bool.
    "fcmpN32": ("fcmpN", "cmp", [32, 32], "bool"),
    "fcmpN64": ("fcmpN", "cmp", [64, 64], "bool"),
    "fcmpZ32": ("fcmpZ", "cmp", [32, 32], "bool"),
    "fcmpZ64": ("fcmpZ", "cmp", [64, 64], "bool"),
    "fcmpC32": ("fcmpC", "cmp", [32, 32], "bool"),
    "fcmpC64": ("fcmpC", "cmp", [64, 64], "bool"),
    "fcmpV32": ("fcmpV", "cmp", [32, 32], "bool"),
    "fcmpV64": ("fcmpV", "cmp", [64, 64], "bool"),
    # ---- FMIN / FMAX / FMINNM / FMAXNM: two f-operands -> f.
    "fmin32": ("fmin", "binary", [32, 32], 32),
    "fmin64": ("fmin", "binary", [64, 64], 64),
    "fmax32": ("fmax", "binary", [32, 32], 32),
    "fmax64": ("fmax", "binary", [64, 64], 64),
    "fminnm32": ("fminnm", "binary", [32, 32], 32),
    "fminnm64": ("fminnm", "binary", [64, 64], 64),
    "fmaxnm32": ("fmaxnm", "binary", [32, 32], 32),
    "fmaxnm64": ("fmaxnm", "binary", [64, 64], 64),
    # ---- FADD / FMUL (RNE): two f-operands -> f.
    "fadd32": ("fadd", "binary", [32, 32], 32),
    "fadd64": ("fadd", "binary", [64, 64], 64),
    "fmul32": ("fmul", "binary", [32, 32], 32),
    "fmul64": ("fmul", "binary", [64, 64], 64),
    # ---- FCVT f<->f.
    "fcvt_widen": ("fcvt_widen", "unary", [32], 64),
    "fcvt_narrow": ("fcvt_narrow", "unary", [64], 32),
    # ---- FCVT f->int (FCVTZS/ZU round-to-zero ; FCVTNS/NU round-to-nearest).
    # tag encodes (op, fp width s/d, int width w/x).
    "fcvtzs_s_w": ("fcvtzs_s_w", "fti", [32], 32),
    "fcvtzs_s_x": ("fcvtzs_s_x", "fti", [32], 64),
    "fcvtzs_d_w": ("fcvtzs_d_w", "fti", [64], 32),
    "fcvtzs_d_x": ("fcvtzs_d_x", "fti", [64], 64),
    "fcvtzu_s_w": ("fcvtzu_s_w", "fti", [32], 32),
    "fcvtzu_s_x": ("fcvtzu_s_x", "fti", [32], 64),
    "fcvtzu_d_w": ("fcvtzu_d_w", "fti", [64], 32),
    "fcvtzu_d_x": ("fcvtzu_d_x", "fti", [64], 64),
    "fcvtns_s_w": ("fcvtns_s_w", "fti", [32], 32),
    "fcvtns_s_x": ("fcvtns_s_x", "fti", [32], 64),
    "fcvtns_d_w": ("fcvtns_d_w", "fti", [64], 32),
    "fcvtns_d_x": ("fcvtns_d_x", "fti", [64], 64),
    "fcvtnu_s_w": ("fcvtnu_s_w", "fti", [32], 32),
    "fcvtnu_s_x": ("fcvtnu_s_x", "fti", [32], 64),
    "fcvtnu_d_w": ("fcvtnu_d_w", "fti", [64], 32),
    "fcvtnu_d_x": ("fcvtnu_d_x", "fti", [64], 64),
    # ---- FCVT int->f (SCVTF/UCVTF). tag encodes (op, int width w/x, fp s/d).
    "scvtf_w_s": ("scvtf_w_s", "itf", [32], 32),
    "scvtf_x_s": ("scvtf_x_s", "itf", [64], 32),
    "scvtf_w_d": ("scvtf_w_d", "itf", [32], 64),
    "scvtf_x_d": ("scvtf_x_d", "itf", [64], 64),
    "ucvtf_w_s": ("ucvtf_w_s", "itf", [32], 32),
    "ucvtf_x_s": ("ucvtf_x_s", "itf", [64], 32),
    "ucvtf_w_d": ("ucvtf_w_d", "itf", [32], 64),
    "ucvtf_x_d": ("ucvtf_x_d", "itf", [64], 64),
    # ---- FP16 (binary16 / ARMv8.2-FP16), proofs/aarch64_fp16_chip.lean.
    # CLASSIFY at width 16 -> bool (the bit-model's is_* at FpFmt F16).
    "isNaN16": ("isNaN16", "classify", [16], "bool"),
    "isInf16": ("isInf16", "classify", [16], "bool"),
    "isZero16": ("isZero16", "classify", [16], "bool"),
    "isNormal16": ("isNormal16", "classify", [16], "bool"),
    "isSubnormal16": ("isSubnormal16", "classify", [16], "bool"),
    "isQNaN16": ("isQNaN16", "classify", [16], "bool"),
    "isSNaN16": ("isSNaN16", "classify", [16], "bool"),
    # FCVT WIDEN h->s/d (EXACT) and NARROW s/d->h (RNE).
    "fcvt_h_to_s": ("fcvt_h_to_s", "unary", [16], 32),
    "fcvt_h_to_d": ("fcvt_h_to_d", "unary", [16], 64),
    "fcvt_s_to_h": ("fcvt_s_to_h", "unary", [32], 16),
    "fcvt_d_to_h": ("fcvt_d_to_h", "unary", [64], 16),
    # scalar FP16 FADD.h / FMUL.h (RNE) — run the width-generic bit-model at F16.
    "fadd16": ("fadd16", "binary", [16, 16], 16),
    "fmul16": ("fmul16", "binary", [16, 16], 16),
    # ---- FDIV / FSQRT (RNE), proofs/aarch64_fp_divsqrt_chip.lean. Now PORTED to
    # fp_bitmodel.rs (integer-only long-division / digit-by-digit sqrt + remainder
    # sticky); previously honest-deferred. FDIV is two f-operands -> f; FSQRT one.
    "fdiv32": ("fdiv32", "binary", [32, 32], 32),
    "fdiv64": ("fdiv64", "binary", [64, 64], 64),
    "fsqrt32": ("fsqrt32", "unary", [32], 32),
    "fsqrt64": ("fsqrt64", "unary", [64], 64),
}

# Ops present in the chip files but DEFERRED (no Rust bit-model port yet). Logged.
# (Now EMPTY for AArch64 scalar binary32/binary64: FDIV/FSQRT are ported above.
# f32-carrier residual is tracked in the soundness manifest, not here, since the
# bit-model itself supports F32 — only the smt.rs eval carrier is f64-lossy.)
DEFERRED_REASONS = {}

# Chip files to scan.
CHIP_FILES = [
    "proofs/aarch64_fp_chip.lean",
    "proofs/aarch64_fp_arith_chip.lean",
    "proofs/aarch64_fp_cvt_chip.lean",
    "proofs/aarch64_fp_divsqrt_chip.lean",
    "proofs/aarch64_fp16_chip.lean",
]

# theorem <name> : <def> <args...> = <result> := rfl
LINE = re.compile(r"^theorem\s+\S+\s*:\s*([A-Za-z0-9_]+)\s+(.*?)\s*=\s*(.+?)\s*:=\s*rfl\s*$")

LISTBOOL = re.compile(r"\[\s*((?:true|false)(?:\s*,\s*(?:true|false))*)\s*\]")


def listbool_to_int(s):
    """Parse a `[false, true, ...]` LSB-first List Bool literal into (int, width)."""
    m = re.fullmatch(r"\[\s*((?:true|false)(?:\s*,\s*(?:true|false))*)\s*\]", s.strip())
    if not m:
        raise ValueError(f"not a List Bool literal: {s[:60]!r}")
    bits = [b.strip() for b in m.group(1).split(",")]
    v = 0
    for i, b in enumerate(bits):
        if b == "true":
            v |= 1 << i
        elif b != "false":
            raise ValueError(f"bad bit token {b!r}")
    return v, len(bits)


def split_listbool_args(args_str):
    """Split a string of one or more space-separated List Bool literals."""
    out = []
    i = 0
    n = len(args_str)
    while i < n:
        if args_str[i].isspace():
            i += 1
            continue
        if args_str[i] != "[":
            raise ValueError(f"expected '[' at {args_str[i:i+20]!r}")
        depth = 0
        j = i
        while j < n:
            if args_str[j] == "[":
                depth += 1
            elif args_str[j] == "]":
                depth -= 1
                if depth == 0:
                    j += 1
                    break
            j += 1
        out.append(args_str[i:j])
        i = j
    return out


def main():
    clean_dir = sys.argv[1]
    out_path = sys.argv[2]
    try:
        clean_sha = subprocess.check_output(
            ["git", "-C", clean_dir, "rev-parse", "HEAD"]
        ).decode().strip()
    except Exception:
        clean_sha = "UNKNOWN"

    facts = []
    included_counts = {}
    deferred_counts = {}
    excluded_counts = {}
    seen_defs = set()
    total_theorem_lines = 0
    parse_errors = 0

    for rel in CHIP_FILES:
        path = os.path.join(clean_dir, rel)
        # Read from git HEAD (the concurrent FP16 workflow may be mid-edit).
        try:
            content = subprocess.check_output(
                ["git", "-C", clean_dir, "show", f"HEAD:{rel}"]
            ).decode()
        except Exception:
            with open(path) as fh:
                content = fh.read()
        for line in content.splitlines():
            m = LINE.match(line)
            if not m:
                continue
            total_theorem_lines += 1
            def_name, args_str, result_str = m.groups()
            # only count the curated/generated facts (skip the in-file sanity
            # theorems whose def is in INCLUDED but whose name is *_sanity_* —
            # those ARE valid facts too, keep them).
            seen_defs.add(def_name)
            if def_name in DEFERRED_REASONS:
                deferred_counts[def_name] = deferred_counts.get(def_name, 0) + 1
                continue
            if def_name not in INCLUDED:
                excluded_counts[def_name] = excluded_counts.get(def_name, 0) + 1
                continue
            tag, kind, in_widths, res_kind = INCLUDED[def_name]
            try:
                arg_toks = split_listbool_args(args_str)
                if len(arg_toks) != len(in_widths):
                    raise ValueError(
                        f"arity {len(arg_toks)} != {len(in_widths)} for {def_name}"
                    )
                operands = []
                for tok, w in zip(arg_toks, in_widths):
                    v, lw = listbool_to_int(tok)
                    if lw != w:
                        raise ValueError(f"{def_name}: operand width {lw} != {w}")
                    operands.append(v)
                if res_kind == "bool":
                    rs = result_str.strip()
                    if rs == "true":
                        result = 1
                        rw = 1
                    elif rs == "false":
                        result = 0
                        rw = 1
                    else:
                        raise ValueError(f"{def_name}: bool result not true/false: {rs!r}")
                else:
                    result, rw = listbool_to_int(result_str)
                    if rw != res_kind:
                        raise ValueError(f"{def_name}: result width {rw} != {res_kind}")
            except ValueError as e:
                parse_errors += 1
                raise SystemExit(f"PARSE ERROR (no silent drop): {e}\n  line: {line[:120]}")
            facts.append({
                "op": tag,
                "lean_def": def_name,
                "kind": kind,
                "in_widths": in_widths,
                "operands": operands,
                "result": result,
                "result_kind": ("bool" if res_kind == "bool" else "bits"),
                "result_width": rw,
            })
            included_counts[def_name] = included_counts.get(def_name, 0) + 1

    # deferred / excluded logs.
    deferred_ops = {}
    for d in sorted(deferred_counts):
        deferred_ops[d] = {
            "count": deferred_counts[d],
            "reason": DEFERRED_REASONS.get(d, "deferred"),
        }
    excluded_ops = {}
    for d in sorted(excluded_counts):
        # only the genuinely-unmapped defs (sanity theorem helper calls etc.).
        excluded_ops[d] = {"count": excluded_counts[d], "reason": "no fp_bitmodel.rs entry"}

    doc = {
        "_header": {
            "purpose": "AArch64 floating-point silicon ground truth for the FP "
                       "bit-model differential bridge: each fact is a REAL Apple "
                       "M4 result (:= rfl chip theorem) for an FP op trust-cg now "
                       "has an INTEGER-ONLY bit-model for (fp_bitmodel.rs). The "
                       "bridge asserts the integer-only model == silicon, evicting "
                       "the host FPU from the FP-verification TCB.",
            "source_files": CHIP_FILES,
            "source_repo": "clean (sibling tree)",
            "clean_sha": clean_sha,
            "recorded_on": "Apple M4 Pro (real silicon, on-chip FP differential harness)",
            "regen": "python3 crates/trust-cg-verify/tests/fixtures/"
                     "gen_aarch64_fp_silicon_truth.py <clean> "
                     "crates/trust-cg-verify/tests/fixtures/aarch64_fp_silicon_truth.json",
            "inclusion_policy": "ALL chip theorems for every op with a fp_bitmodel.rs "
                                "entry are included (no subsampling). FDIV/FSQRT are "
                                "HONEST-DEFERRED (not yet ported) and logged in "
                                "deferred_ops, not silently dropped. Parse errors abort.",
            "total_theorem_lines_scanned": total_theorem_lines,
            "included_fact_count": len(facts),
            "included_per_lean_def": included_counts,
            "deferred_ops": deferred_ops,
            "excluded_ops": excluded_ops,
            "parse_errors": parse_errors,
        },
        "facts": facts,
    }

    with open(out_path, "w") as fh:
        json.dump(doc, fh, indent=1)
        fh.write("\n")

    print(f"wrote {len(facts)} facts to {out_path}")
    print(f"  clean_sha={clean_sha}")
    print(f"  theorem lines scanned={total_theorem_lines}")
    print(f"  included defs={len(included_counts)} deferred defs={len(deferred_counts)} "
          f"excluded defs={len(excluded_counts)}")
    if deferred_counts:
        print(f"  DEFERRED: {dict(deferred_counts)}")
    if excluded_counts:
        print(f"  EXCLUDED: {dict(excluded_counts)}")


if __name__ == "__main__":
    main()
