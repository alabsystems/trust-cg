#!/usr/bin/env python3
"""Bucket the slice-8 class (non-scalar parameters / results / call results)
by the actual LIR types, from the probe's --sig TSV.

usage: bucket.py sig.tsv [failed_roots_names.txt]
"""
import re
import sys
from collections import Counter

SCALAR = {"B1", "I8", "I16", "I32", "I64"}


def split_types(text):
    """Split a Rust Debug list `[A, Struct([I64, I8]), I128]` into items."""
    text = text.strip()
    assert text.startswith("[") and text.endswith("]"), text
    inner = text[1:-1]
    items, depth, cur = [], 0, ""
    for ch in inner:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if ch == "," and depth == 0:
            items.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        items.append(cur.strip())
    return items


def kind(ty):
    """A coarse bucket for one LIR type."""
    if ty in SCALAR:
        return "scalar"
    if ty in ("F32", "F64", "F16"):
        return "float"
    if ty == "I128":
        return "i128"
    if ty in ("V128", "V64"):
        return "vector"
    if ty.startswith("Struct") or ty.startswith("Array"):
        size = type_size(ty)
        floats = "F32" in ty or "F64" in ty or "F16" in ty
        wide = "I128" in ty or "V128" in ty
        tag = "aggregate"
        if floats:
            tag += "-float"
        if wide:
            tag += "-i128/v128"
        if size is None:
            return tag + "-?"
        if size > 16:
            return tag + ">16"
        if size > 8:
            return tag + "9..16"
        return tag + "<=8"
    if ty.startswith("Enum"):
        return "enum"
    return "other:" + ty


def parse(ty):
    """Parse a Debug-printed LIR type into a nested tuple."""
    ty = ty.strip()
    if ty.startswith("Struct("):
        return ("struct", [parse(t) for t in split_types(ty[len("Struct("):-1])])
    if ty.startswith("Array("):
        inner = ty[len("Array("):-1]
        elem, count = inner.rsplit(",", 1)
        return ("array", parse(elem), int(count))
    return ("scalar", ty)


SIZES = {"B1": (1, 1), "I8": (1, 1), "I16": (2, 2), "I32": (4, 4), "I64": (8, 8),
         "I128": (16, 16), "F16": (2, 2), "F32": (4, 4), "F64": (8, 8), "V128": (16, 16),
         "V64": (8, 8)}


def layout(t):
    if t[0] == "scalar":
        return SIZES.get(t[1])
    if t[0] == "struct":
        end, align = 0, 1
        for f in t[1]:
            sa = layout(f)
            if sa is None:
                return None
            s, a = sa
            end = (end + a - 1) // a * a + s
            align = max(align, a)
        return ((end + align - 1) // align * align, align)
    if t[0] == "array":
        sa = layout(t[1])
        if sa is None:
            return None
        return (sa[0] * t[2], sa[1])
    return None


def type_size(ty):
    try:
        sa = layout(parse(ty))
    except Exception:
        return None
    return sa[0] if sa else None


def main():
    rows = [line.rstrip("\n").split("\t") for line in open(sys.argv[1])]
    failed = None
    if len(sys.argv) > 2:
        failed = set(l.strip() for l in open(sys.argv[2]))
    param_b, result_b, call_b, six_b = Counter(), Counter(), Counter(), Counter()
    exact_param, exact_result, exact_call = Counter(), Counter(), Counter()
    n_param = n_result = n_call = n_six = 0
    for name, verdict, params, returns, sret, calls in rows:
        if failed is not None and name not in failed:
            continue
        ps, rs = split_types(params), split_types(returns)
        if "register parameters" in verdict and "at most six" not in verdict:
            n_param += 1
            kinds = sorted({kind(p) for p in ps if kind(p) != "scalar"})
            param_b["+".join(kinds)] += 1
            for p in ps:
                if kind(p) != "scalar":
                    exact_param[p] += 1
        elif "at most six register parameters" in verdict:
            n_six += 1
            kinds = sorted({kind(p) for p in ps if kind(p) != "scalar"}) or ["all-scalar"]
            six_b[f"{len(ps)} params: " + "+".join(kinds)] += 1
        elif "I64 results" in verdict:
            n_result += 1
            kinds = sorted({kind(r) for r in rs if kind(r) != "scalar"})
            result_b["+".join(kinds)] += 1
            for r in rs:
                if kind(r) != "scalar":
                    exact_result[r] += 1
        elif "no scalar result type" in verdict:
            n_call += 1
            # The call results: "callee:[Some(Struct(..))] | ..."
            ks = set()
            for item in calls.split(" | "):
                if not item:
                    continue
                tys = re.findall(r"Some\(((?:[^()]|\([^()]*(?:\([^()]*\))*[^()]*\))*)\)|None", item)
                for t in re.findall(r"Some\((.*?)\)(?:,|\]$)", item.split(":", 1)[1]):
                    ks.add(kind(t))
                    exact_call[t] += 1
                if "None" in item:
                    ks.add("untyped")
            call_b["+".join(sorted(ks))] += 1
    print(f"non-scalar parameter: {n_param}")
    for k, v in param_b.most_common():
        print(f"  {v:5d}  {k}")
    print("  exact parameter types (top 25):")
    for k, v in exact_param.most_common(25):
        print(f"    {v:5d}  {k}")
    print(f"non-scalar result: {n_result}")
    for k, v in result_b.most_common():
        print(f"  {v:5d}  {k}")
    print("  exact result types (top 25):")
    for k, v in exact_result.most_common(25):
        print(f"    {v:5d}  {k}")
    print(f"call result with no scalar type: {n_call}")
    for k, v in call_b.most_common():
        print(f"  {v:5d}  {k}")
    print("  exact call result types (top 20):")
    for k, v in exact_call.most_common(20):
        print(f"    {v:5d}  {k}")
    print(f"more than six register parameters: {n_six}")
    for k, v in six_b.most_common():
        print(f"  {v:5d}  {k}")


main()
