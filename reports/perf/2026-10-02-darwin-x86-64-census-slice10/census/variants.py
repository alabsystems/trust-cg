#!/usr/bin/env python3
"""Spelling experiments for the slice-10 theorems the qualification AY/Clean pair does
not certify: write variant queries of the dumped canonical ones (QDUMP) into OUT,
each a satisfiability-preserving respelling of the same theorem, for replay_dir.py.
usage: variants.py <qdump dir> <out dir>"""
import os
import re
import sys

src, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)


def read(name):
    return open(os.path.join(src, name + ".smt2")).read()


def write(name, text):
    open(os.path.join(out, name + ".smt2"), "w").write(text)


# Shifts by CL: the machine count without the CL extract (mathematically equal:
# the mask is below 256), or both counts as the low log2(width) bits.
for shape, bits in [("ShrU64", 64), ("SarI32", 32), ("ShlChecked", 32), ("SarI16", 32)]:
    q = read(shape)
    mask = bits - 1
    a = re.sub(r"\(bvand \(\(_ zero_extend (\d+)\) \(\(_ extract 7 0\) (\w+)\)\) \(_ bv%d (\d+)\)\)" % mask,
               lambda m: f"(bvand ((_ extract {int(m.group(3)) - 1} 0) {m.group(2)}) (_ bv{mask} {m.group(3)}))"
               if int(m.group(3)) < 64 else f"(bvand {m.group(2)} (_ bv{mask} 64))", q)
    write(f"{shape}__count_no_cl_extract", a)
    k = mask.bit_length()
    b = re.sub(r"\(bvand (\S+|\([^()]*\)) \(_ bv%d (\d+)\)\)" % mask,
               lambda m: f"((_ zero_extend {int(m.group(2)) - k}) ((_ extract {k - 1} 0) {m.group(1)}))", a)
    write(f"{shape}__count_low_bits", b)

# Popcount: narrow accumulators (each bit zero-extended to the count's own
# width, the sum zero-extended once), and a balanced tree of adds.
for shape, bits in [("CountU32", 32), ("CountU64", 64)]:
    q = read(shape)
    k = bits.bit_length()

    def narrow(m):
        term = m.group(0)
        operands = re.findall(r"\(\(_ zero_extend %d\) \(\(_ extract (\d+) \1\) (\w+)\)\)" % (bits - 1), term)
        if len(operands) != bits:
            return term
        var = operands[0][1]
        leaves = [f"((_ zero_extend {k - 1}) ((_ extract {i} {i}) {var}))" for i in range(bits)]
        while len(leaves) > 1:
            leaves = [f"(bvadd {leaves[i]} {leaves[i + 1]})" if i + 1 < len(leaves) else leaves[i]
                      for i in range(0, len(leaves), 2)]
        return f"((_ zero_extend {bits - k}) {leaves[0]})"

    # the count_ones term: the outermost bvadd chain of bits-1 adds.
    pattern = re.compile(r"\(bvadd " * (bits - 1) + r"[^=]*?" + r"\)" * 1)
    text = q
    start = text.find("(bvadd " * (bits - 1))
    while start != -1:
        depth, i = 0, start
        while True:
            if text[i] == "(":
                depth += 1
            elif text[i] == ")":
                depth -= 1
                if depth == 0:
                    break
            i += 1
        term = text[start:i + 1]
        replaced = narrow(re.match(r".*", term, re.S))
        text = text[:start] + replaced + text[i + 1:]
        start = text.find("(bvadd " * (bits - 1), start + len(replaced))
    write(f"{shape}__narrow_tree", text)

# Unsigned multiply: the source's overflow spelled as the machine's (the high
# half of the product is not zero), the same predicate.
for shape in ["MulU64", "MulPanics"]:
    q = read(shape)
    a = re.sub(r"\(not \(= \(\(_ zero_extend 64\) \(\(_ extract 63 0\) (\(bvmul \(\(_ zero_extend 64\) (\w+)\) \(\(_ zero_extend 64\) (\w+)\)\))\)\) \1\)\)",
               r"(not (= ((_ extract 127 64) \1) (_ bv0 64)))", q)
    write(f"{shape}__high_half", a)
print(sorted(os.listdir(out)))
