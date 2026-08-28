#!/usr/bin/env python3
"""Generate compile-time SCALING probes.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0

WHY: every other gate in this repo compiles SMALL programs. The 18-program
beat-llvm corpus averages ~120ms and its functions have tens of blocks, so a
defect that is superlinear in program size is invisible to all of them. Two have
been found by hand and neither was caught by any gate:

  * trust-ir's `validate::compute_dominators` is O(N^3) in basic-block count
    (2951us -> 5.88s from 418 to 1618 blocks)
  * `run_extended_loop_rotation` ran three whole-function scans per candidate
    loop per driver iteration (16.7s of a 19.03s compile against LLVM's 0.48s)

Each shape below grows one dimension while holding the others fixed, so a
regression names its own cause.
"""
import sys

def blocks(n: int) -> str:
    """One function, N sequential CALLS -> N+1 basic blocks (calls terminate
    blocks in MIR). Stresses anything per-block or per-dominator."""
    out = ["use std::hint::black_box as bb;",
           "#[inline(never)] fn h(a: u64) -> u64 { a.wrapping_mul(31).wrapping_add(7) }",
           "fn main() { let mut t = 0u64;"]
    out += [f"    t = t.wrapping_add(h(bb({i}u64)));" for i in range(n)]
    out.append("    std::process::exit((t % 251) as i32); }")
    return "\n".join(out)

def loops(n: int) -> str:
    """One function, N independent LOOPS. Stresses loop analyses and any
    per-loop driver that recomputes whole-function state."""
    out = ["use std::hint::black_box as bb;", "const N: usize = 512;",
           "fn main() { let reps = bb(2u32); let mut acc = 0u64;"]
    for k in range(n):
        out.append(f"    {{ let mut a = [0u8; N]; let mut r = 0u32;")
        out.append(f"      while r < reps {{ let v = (r as u8) | {(k % 250) + 1}; let mut i = 0usize;")
        out.append(f"        while i < N {{ a[i] = v; i += 1; }}")
        out.append(f"        acc = acc.wrapping_add(a[bb(r as usize) % N] as u64); r += 1; }} }}")
    out.append("    std::process::exit((acc % 251) as i32); }")
    return "\n".join(out)

def funcs(n: int) -> str:
    """N separate FUNCTIONS, each small, with a tiny main. Stresses per-function
    and per-module cost without growing any single function."""
    out = ["use std::hint::black_box as bb;"]
    for i in range(n):
        out.append(f"#[no_mangle] pub extern \"C\" fn g{i}(a: u64) -> u64 {{"
                   f" let mut s = a; let mut j = 0u64;"
                   f" while j < 4 {{ s = s.wrapping_mul(31).wrapping_add(j ^ {i}); j += 1; }} s }}")
    out.append("fn main() { std::process::exit((unsafe { g0(bb(3)) } % 251) as i32); }")
    return "\n".join(out)

def arraysize(n: int) -> str:
    """ONE small function whose stack array grows to N bytes. Block count,
    instruction count and loop count are all FIXED — only the data size moves.

    Lowering has an O(array-size) component (5.2ms at N=256 -> 28.3ms at
    N=65536) that produces CONSTANT-size code, so it is pure compile-time work
    on an intermediate that is then collapsed into the array-fill helper. Cheap
    to keep honest, and no other shape here varies this dimension."""
    return f"""use std::hint::black_box as bb;
const N: usize = {n};
fn main() {{
    let mut a = [0u8; N];
    let mut acc: u64 = 0;
    let mut r = 0u32;
    while r < bb(3u32) {{
        let v = (r as u8) | 1;
        let mut i = 0usize;
        while i < N {{ a[i] = v; i += 1; }}
        acc = acc.wrapping_add(a[bb(r as usize) % N] as u64);
        r += 1;
    }}
    std::process::exit((acc % 251) as i32);
}}"""

SHAPES = {"blocks": blocks, "loops": loops, "funcs": funcs, "arraysize": arraysize}

if __name__ == "__main__":
    shape, n = sys.argv[1], int(sys.argv[2])
    print(SHAPES[shape](n))
