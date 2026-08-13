#!/usr/bin/env python3
"""Generate large-function Rust programs for compile-time SCALING measurement.

WHY THIS EXISTS

`benchmarks/beat-llvm` is the correctness-and-runtime corpus; its largest
program is ~30 lines. Every compile-time figure derived from it therefore
describes a regime no real crate occupies, and it is structurally incapable of
seeing superlinear behaviour in the backend. Three separate O(n^2) sites
(scheduler ready-set, scheduler physical-register pairing, and whole-function
reaching-defs per recognition site) all sat undetected behind it while the
geomean read a healthy 1.06x.

This generator produces the missing axis: the SAME shape at growing sizes, so a
ratio that climbs with N is visible as an algorithmic defect rather than noise.

SHAPES

Deliberately diverse, because a single shape flatters whichever passes it misses.
`mul_chain` in particular is close to `mul-shift-reduce`'s worst case, so a
finding measured only there would overstate the general picture.

  mul_chain    dependent multiply-by-constant chain (long critical path,
               maximal constant-recognition pressure)
  ilp_add      independent adds (wide ready-set, exercises scheduler selection
               rather than its dependence tracking)
  branchy      a long if/else ladder (many small blocks -> CFG-heavy dataflow)
  many_fns     many small functions (per-function fixed costs, not per-block)
  array_loop   loops over a fixed array (memory dependencies + bounds work)

Each program is a self-contained `main` that exits with a value derived from its
computation, so the runner can compare exit status against LLVM and reject a
build that silently produced nothing.

Author: Andrew Yates · Copyright 2026 Andrew Yates · License: Apache-2.0
"""
import sys, os

def mul_chain(n):
    body = "\n".join(
        f"    let v{i} = v{i-1}.wrapping_mul(6364136223846793005).wrapping_add({i});"
        for i in range(1, n))
    return (f"use std::hint::black_box as bb;\nfn main() {{\n"
            f"    let v0: u64 = bb(1);\n{body}\n"
            f"    std::process::exit((v{n-1} % 126) as i32);\n}}\n")

def ilp_add(n):
    body = "\n".join(f"    let v{i} = base.wrapping_add({i * 7});" for i in range(n))
    acc = " ^ ".join(f"v{i}" for i in range(n))
    return (f"use std::hint::black_box as bb;\nfn main() {{\n"
            f"    let base: u64 = bb(3);\n{body}\n"
            f"    let acc = {acc};\n"
            f"    std::process::exit((acc % 126) as i32);\n}}\n")

def branchy(n):
    arms = "\n".join(
        f"    if x % {i + 2} == 0 {{ acc = acc.wrapping_add({i}); }} "
        f"else {{ acc = acc.wrapping_mul(3).wrapping_add({i}); }}"
        for i in range(n))
    return (f"use std::hint::black_box as bb;\nfn main() {{\n"
            f"    let x: u64 = bb(97);\n    let mut acc: u64 = 0;\n{arms}\n"
            f"    std::process::exit((acc % 126) as i32);\n}}\n")

def many_fns(n):
    fns = "\n".join(
        f"#[inline(never)] fn f{i}(x: u64) -> u64 {{ "
        f"let mut a = x; let mut j = 0u64; "
        f"while j < 4 {{ a = a.wrapping_mul(6364136223846793005).wrapping_add(j + {i}); j += 1; }} a }}"
        for i in range(n))
    calls = "".join(f"a = a.wrapping_add(f{i}(a));" for i in range(n))
    return (f"use std::hint::black_box as bb;\n{fns}\nfn main() {{\n"
            f"    let mut a: u64 = bb(1);\n    {calls}\n"
            f"    std::process::exit((a % 126) as i32);\n}}\n")

def array_loop(n):
    loops = "\n".join(
        f"    for i in 0..buf.len() {{ buf[i] = buf[i].wrapping_mul({i * 2 + 3}).wrapping_add(i as u64); }}"
        for i in range(n))
    return (f"use std::hint::black_box as bb;\nfn main() {{\n"
            f"    let mut buf = [0u64; 32];\n"
            f"    for i in 0..buf.len() {{ buf[i] = bb(i as u64); }}\n{loops}\n"
            f"    let mut acc = 0u64;\n"
            f"    for i in 0..buf.len() {{ acc = acc.wrapping_add(buf[i]); }}\n"
            f"    std::process::exit((acc % 126) as i32);\n}}\n")

SHAPES = {"mul_chain": mul_chain, "ilp_add": ilp_add, "branchy": branchy,
          "many_fns": many_fns, "array_loop": array_loop}

if __name__ == "__main__":
    if len(sys.argv) != 4:
        sys.exit(f"usage: {sys.argv[0]} <shape> <n> <outfile>\n"
                 f"shapes: {', '.join(SHAPES)}")
    shape, n, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    if shape not in SHAPES:
        sys.exit(f"unknown shape {shape!r}; known: {', '.join(SHAPES)}")
    os.makedirs(os.path.dirname(out) or ".", exist_ok=True)
    with open(out, "w") as f:
        f.write(SHAPES[shape](n))
