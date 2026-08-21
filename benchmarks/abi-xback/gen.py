#!/usr/bin/env python3
"""Generate a caller/callee pair for a cross-backend ABI differential."""

import random
import sys

INT_TYPES = [
    ("u8", 0, 255),
    ("i8", -128, 127),
    ("u16", 0, 65535),
    ("i16", -32768, 32767),
    ("u32", 0, 4_000_000),
    ("i32", -2_000_000, 2_000_000),
    ("u64", 0, 9_000_000),
    ("i64", -9_000_000, 9_000_000),
]
FLOAT_TYPES = ["f32", "f64"]


def main() -> int:
    seed = int(sys.argv[1])
    which = sys.argv[2]
    rng = random.Random(seed)

    params = []
    values = []
    for _ in range(rng.randrange(9, 21)):
        if rng.random() < 0.25:
            ty = rng.choice(FLOAT_TYPES)
            value = rng.randrange(-1000, 1000)
            params.append(ty)
            values.append(f"{value}.0{ty}")
        else:
            ty, low, high = rng.choice(INT_TYPES)
            value = rng.randrange(low, high + 1)
            params.append(ty)
            values.append(f"{value}{ty}")

    signature = ", ".join(f"p{i}: {ty}" for i, ty in enumerate(params))
    body = ["    let mut acc: u64 = 0;"]
    for i in range(len(params)):
        body.append(
            f"    acc = acc.wrapping_mul(31).wrapping_add(p{i} as i64 as u64);"
        )
    body.append("    acc")

    if which == "callee":
        print("#[no_mangle]")
        print(f'pub extern "C" fn xabi({signature}) -> u64 {{')
        print("\n".join(body))
        print("}")
    elif which == "caller":
        print(f'extern "C" {{ fn xabi({signature}) -> u64; }}')
        print("use std::hint::black_box as bb;")
        print("fn main() {")
        args = ", ".join(f"bb({value})" for value in values)
        print(f"    let v = unsafe {{ xabi({args}) }};")
        print("    std::process::exit((v % 251) as i32);")
        print("}")
    else:
        raise ValueError(f"expected callee or caller, got {which!r}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
