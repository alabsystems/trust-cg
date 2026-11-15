#!/usr/bin/env python3
"""Shared parsing for the S25 shape census (read-only over census output dirs).

A census dir holds stderr.log ([TCG-X86-BODY-TRACE] fn=<f> <text> lines; the
LAST line per fn is the refusal that decided it, earlier lines are the other
attempt of the same fn) and failed_roots.jsonl (one row per failed root; a
PROOF-465 message names the fn whose body failed and its emitted opcode
inventory of uncovered rows).
"""
import json, re, collections

RUNS = "$HOME/tcg-scratch/runs/"
TRACE = re.compile(r"\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)")
ROW = re.compile(r"machine row (\d+) is outside the body domain \(.*?operand-free Nop\): (.*)$")
FN_IN_MSG = re.compile(r"non_verified proof entry \S+ in (\S+?): ")
INV = re.compile(r"found (\d+) uncovered non-pseudo opcode\(s\) across (\d+) distinct opcode\(s\) \[([^\]]*)\]")


def traces(cen):
    per = collections.defaultdict(list)
    for line in open(RUNS + cen + "/stderr.log", errors="replace"):
        m = TRACE.match(line.rstrip("\n"))
        if m:
            per[m.group(1)].append(m.group(2))
    return per


def roots(cen):
    out = []
    for l in open(RUNS + cen + "/failed_roots.jsonl"):
        r = json.loads(l)
        msg = r.get("message", "")
        m = FN_IN_MSG.search(msg)
        inv = INV.search(msg)
        out.append(dict(
            symbol=r["symbol"], reason=r["reason"], fn=m.group(1) if m else None,
            message=msg,
            inv_rows=int(inv.group(1)) if inv else None,
            inv=[x.strip().replace("x86_64::", "") for x in inv.group(3).split(",")] if inv else [],
        ))
    return out


def key(fn):
    """Opt-level-independent function key: the mangled `_R...` name without the
    private CGU prefix (CGU numbering differs between O0 and O2)."""
    if fn is None:
        return None
    m = re.search(r"(_R[A-Za-z0-9_]+(?:\.[A-Za-z_]+)*)$", fn)
    return m.group(1) if m else fn


def refusal_class(t):
    """Coarse class of a last trace line (same split as the 2026-11-03 record)."""
    if t is None:
        return "untraced"
    if "replay=Valid" in t:
        return "VALID"
    if "bound rows" in t or "replay" in t:
        return "bound-uncertified"
    if "references a stack slot" in t:
        return "S"
    m = ROW.search(t)
    if m:
        return "R-flags" if "reads flags" in m.group(2) else "R"
    if "has no machine block" in t:
        return "B3"
    if "do not correspond" in t:
        return "B"
    if "no observable" in t or "a call or an incoming-memory access" in t:
        return "OD115"
    return "other"


OPND = re.compile(r"(SibMemAddr \{ base: (?P<sb>[^,]*?(?:\{[^}]*\}\))?), index: (?P<si>[^,]*?(?:\{[^}]*\}\))?), scale: (?P<sc>\d+), disp: (?P<sd>-?\d+) \})"
                  r"|(MemAddr \{ base: (?P<mb>[^,]*?(?:\{[^}]*\}\))?), disp: (?P<md>-?\d+) \})"
                  r"|(VReg\(VReg \{ id: \d+, class: (?P<vc>\w+) \}\))"
                  r"|(PReg\((?P<pr>[^)]*)\))"
                  r"|(Imm\((?P<im>-?\d+)\))")


def kind(s):
    if s is None:
        return None
    if s.startswith("VReg"):
        return "VReg"
    if s.startswith("PReg"):
        return "PReg"
    if s.startswith("StackSlot"):
        return "StackSlot"
    return s.split("(")[0]


def parse_row(detail):
    """Opcode, operand shape and flags of a machine-row refusal's detail."""
    m = re.match(r"(\w+) with operands \[(.*)\] (?:carries|and) flags InstFlags\(([^)]*)\)", detail)
    if not m:
        return dict(opcode=detail.split()[0], detail=detail)
    op, ops, flags = m.group(1), m.group(2), m.group(3)
    shape = dict(opcode=op, flags=flags, operands=[])
    for o in OPND.finditer(ops):
        if o.group("sc"):
            shape["operands"].append(dict(k="sib", base=kind(o.group("sb")), index=kind(o.group("si")),
                                          scale=int(o.group("sc")), disp=int(o.group("sd"))))
        elif o.group("md") is not None:
            shape["operands"].append(dict(k="mem", base=kind(o.group("mb")), disp=int(o.group("md"))))
        elif o.group("vc"):
            shape["operands"].append(dict(k="reg", cls=o.group("vc")))
        elif o.group("pr"):
            shape["operands"].append(dict(k="preg", reg=o.group("pr")))
        elif o.group("im") is not None:
            shape["operands"].append(dict(k="imm", v=int(o.group("im"))))
    return shape
