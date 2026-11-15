#!/usr/bin/env python3
"""O0 forms of the SIB address sites of the S25 roots' functions.

At O0 the selector emits an indexed access as `lea b, [slot]` (or a register
base), `LeaSib c, [b + i*s + d]`, then a base-only access through `c`. The O2
SIB fold rewrites exactly that site, so the O0 `lea (base,index,scale)` of the
same function tells, per site, the scale, whether the base is a private stack
address (last def of the base register is `lea -N(%rbp)`, through at most two
register copies) and whether the index is a constant (last def `mov $k` or a
zeroing xor). Jump-table dispatch loads (`mov (%b,%i,8)`) are listed apart.

Usage: o0_sib_sites.py <O0 obj-dir> <s25_roots.jsonl> <out.json>"""
import subprocess, re, sys, json, os, glob, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import census_lib as L

objdir, roots, out = sys.argv[1], sys.argv[2], sys.argv[3]
want = {}
for l in open(roots):
    r = json.loads(l)
    if r["cls"] in ("S", "R") and r["fn"]:
        want[L.key(r["fn"])] = r["symbol"]

INS = re.compile(r"^\s*([0-9a-f]+):\s+(\w+)\s*(.*)$")
SIB = re.compile(r"(-?0x[0-9a-f]+|-?\d+)?\(%(\w+),%(\w+)(?:,(\d))?\)")
R64 = {"eax": "rax", "ebx": "rbx", "ecx": "rcx", "edx": "rdx", "esi": "rsi", "edi": "rdi", "ebp": "rbp",
       "esp": "rsp"}
for n in range(8, 16):
    R64[f"r{n}d"] = f"r{n}"


def root(reg):
    return R64.get(reg, reg)


def dests(op, args):
    parts = [a.strip() for a in re.split(r",(?![^()]*\))", args)]
    if not parts or not parts[-1].startswith("%"):
        return None, parts
    return root(parts[-1][1:]), parts


def origin(insts, i, reg, depth=0):
    """Classify the last def of `reg` before insts[i]: slot / const / copy-of / other."""
    for j in range(i - 1, max(-1, i - 40), -1):
        op, args = insts[j]
        if op.startswith("call"):
            if reg in ("rbx", "rbp", "r12", "r13", "r14", "r15"):
                continue
            return "call"
        d, parts = dests(op, args)
        if d != reg:
            continue
        src = parts[0] if parts else ""
        if op.startswith("lea") and re.match(r"^-?(0x[0-9a-f]+|\d+)?\(%rbp\)$", src):
            return "slot"
        if op.startswith("lea") and re.match(r"^-?(0x[0-9a-f]+|\d+)?\(%rsp\)$", src):
            return "slot"
        if op.startswith("mov") and src.startswith("$"):
            return "const" if not VALUES else "const" + src
        if op.startswith("xor") and len(parts) == 2 and root(parts[0].lstrip("%")) == reg:
            return "const"
        if op in ("movq", "movl") and src.startswith("%") and depth < 2:
            return origin(insts, j, root(src[1:]), depth + 1)
        return "other"
    return "unknown"


VALUES = os.environ.get("S25_CONST_VALUES") == "1"
res = {}
files = sorted(glob.glob(os.path.join(objdir, "*.o")))
for i in range(0, len(files), 200):
    p = subprocess.run(["objdump", "-d", "--no-show-raw-insn"] + files[i:i + 200], capture_output=True, text=True)
    fn, insts = None, []

    def flush():
        if fn is None:
            return
        k = L.key(fn)
        if k not in want:
            return
        sites = collections.Counter()
        for idx, (op, args) in enumerate(insts):
            if op.startswith("nop"):
                continue
            # Variable-index private address at O0: `add %x, %y` with one side a slot address.
            if op == "addq" and re.match(r"^%\w+,\s*%\w+$", args.strip()):
                a, b = [root(x.strip()[1:]) for x in args.split(",")]
                oa, ob = origin(insts, idx, a), origin(insts, idx, b)
                if "slot" in (oa, ob):
                    other = ob if oa == "slot" else oa
                    sites[f"addrr slot+index index={other}"] += 1
            for m in SIB.finditer(args):
                base, index, scale = root(m.group(2)), root(m.group(3)), int(m.group(4) or 1)
                kind = "lea" if op.startswith("lea") else ("load" if args.strip().startswith(m.group(0)) else "store")
                b = origin(insts, idx, base)
                x = origin(insts, idx, index)
                sites[f"{kind} {op} s{scale} base={b} index={x}"] += 1
        res[want[k]] = dict(sites)

    for line in p.stdout.splitlines():
        m = re.match(r"^[0-9a-f]+ <(.+)>:$", line)
        if m:
            flush()
            fn, insts = m.group(1), []
            continue
        m = INS.match(line)
        if fn and m:
            insts.append((m.group(2), m.group(3)))
    flush()
json.dump(res, open(out, "w"), indent=0)
print(len(want), "S/R root functions;", len(res), "found in O0 objects")
