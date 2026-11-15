#!/usr/bin/env python3
"""Attribute each failed root of a Darwin x86-64 core census to the body-lane
class of the function its proof failure names. Usage: root_classes.py <census-out-dir>"""
import re, json, collections, sys
run = sys.argv[1]
last = {}
for line in open(f"{run}/stderr.log", errors="replace"):
    m = re.match(r"\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)", line.rstrip())
    if m: last[m.group(1)] = m.group(2)
def cls(t):
    if "replay=Valid" in t: return "VALID(?)"
    if "replay=" in t or "bound rows" in t: return "bound, not certified (AY)"
    # No key below may hide a mismatch.
    if "mismatch" in t: return "MISMATCH"
    # The O2 refusals (slices 24a and 25) come before the older keys: the
    # row-domain text lists BODY_OPCODES and a quotient's text its chains.
    o2 = [("references a stack slot outside", "stack slot outside the frame (S)"),
          ("; not contracted: ", "merged block not contracted"),
          ("lowers rows of several LIR blocks", "several LIR blocks in one machine block"),
          ("has no machine block", "LIR block with no machine block"),
          ("has no row attributed", "machine block with no attributed row"),
          ("candidate offsets", "indexed candidate offsets"),
          ("outside its dispatch block", "jump table outside its dispatch block")]
    for k, v in o2:
        if k in t: return v
    m = re.search(r"machine row \d+ is outside the body domain \(.*?operand-free Nop\): (\w+)", t)
    if m: return f"machine row outside the body domain: {m.group(1)}"
    rules = [("register parameters", "non-scalar params"), ("I64 results", "non-scalar results"),
             ("blocks (the lane", ">16 blocks"), ("a path of", "long path"), ("a loop", "loop"),
             ("a call or an incoming-memory access", "no observable"), ("(Checked", "checked arith"),
             ("escapes", "slot address escapes"), ("at most six", ">6 params"), ("type hint", "inconsistent type hint"),
             ("CallIndirect", "CallIndirect"), ("non-scalar type", "non-scalar load/extend"),
             ("(Guard", "guards"), ("CtPop", "CtPop"), ("Bnot", "Bnot"), ("Atomic", "atomics"),
             ("shifts by a non-constant", "variable shift"), ("(Udiv", "div/rem"), ("(Urem", "div/rem"), ("(Sdiv", "div/rem"), ("(Srem", "div/rem"),
             ("(Call {", "call shapes"), ("Memcpy", "memcpy/memset"), ("Memset", "memcpy/memset"),
             ("more than", "machine >N rows")]
    for k, v in rules:
        if k in t: return v
    # N11's refusal of a segment (OD-228); none of the keys above occurs in
    # its text. Other refusals of pairs stated over segments keep the classes
    # above.
    s24c = [("both have calls, accesses, rounding operations, stops or indexed accesses",
             "segment: effects in two members (N11)")]
    for k, v in s24c:
        if k in t: return v
    return "other: " + re.sub(r"\d+", "N", t)[:110]
c = collections.Counter(); ex = {}
for l in open(f"{run}/failed_roots.jsonl"):
    r = json.loads(l); msg = r.get("message", "")
    m = re.search(r"non_verified proof entry \S+ in (\S+?): ", msg)
    fn = m.group(1) if m else None
    k = cls(last[fn]) if fn in last else ("(named fn untraced)" if fn else "(no fn in message)")
    c[k] += 1; ex.setdefault(k, (fn or r["symbol"], msg[:400]))
for k, v in c.most_common(40): print(f"{v:5d}  {k}")
for k in ["(named fn untraced)", "(no fn in message)", "VALID(?)"]:
    if k in ex: print("\nEX", k, ex[k][0][:140], "\n  ", ex[k][1])
