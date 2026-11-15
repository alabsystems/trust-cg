#!/usr/bin/env python3
"""Execute the x86-64 AOT inline-only fixture under the Unicorn x86-64 emulator.

This host (Apple Silicon, no Rosetta) has no x86-64 executor, so the x86-64
half of the inline-only evidence runs in an emulator: for each optimization
level, `examples/aot_inline_only_fast_path` compiles the same TrustIR module
for `x86_64-apple-darwin` twice with ONE compiler binary -- as is (the
inline-only body of `tcg_read` spliced into `sum`'s loop) and with
`TCG_NO_INLINE_ONLY_BODIES=1` (every read calls the linked definition) --
each object is linked by the host C driver with the C runtime that defines
`tcg_read` / `tcg_read_slow` (`cc -arch x86_64`, link only; nothing runs
natively), the linked image's segments are mapped into Unicorn, and `sum` is
entered directly for several iteration counts. Checked per run: the answer
(RAX) equals the closed-form reference computed here from the definition's
own semantics, and the runtime's call counters (read from the image's data
segment) show the linked definition called 0 times with the body spliced and
once per read without it, the remainder once per out-of-range read in both.

The Mach-O loader and calling harness follow
reports/perf/2026-09-28-x86-internal-multi-result/uc_multi_result.py.

Usage: uc_inline_only.py <aot_inline_only_fast_path binary> <out.tsv>
Requires: pip install unicorn (2.x); an Apple `cc` able to link x86_64.
"""
import os
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

from unicorn import Uc, UC_ARCH_X86, UC_MODE_64, UC_PROT_ALL
from unicorn import x86_const as X

PAGE = 0x1000
STACK_TOP = 0x7FFF_0000
STACK_SIZE = 0x10_0000
DATA_BASE = 0x6000_0000
SENTINEL = 0x5000_0000
TRIPLE = "x86_64-apple-darwin"
TABLE = [5, 10, 20, 30, 40, 50]
COUNTS = [0, 1, 5, 7, 8, 13, 1000]


def align_down(x):
    return x & ~(PAGE - 1)


def align_up(x):
    return (x + PAGE - 1) & ~(PAGE - 1)


def macho_segments(path):
    data = Path(path).read_bytes()
    magic, _cpu, _sub, _ftype, ncmds, _size, _flags, _res = struct.unpack_from("<IiiIIIII", data, 0)
    assert magic == 0xFEEDFACF, "not a 64-bit Mach-O"
    off = 32
    segs = []
    for _ in range(ncmds):
        cmd, cmdsize = struct.unpack_from("<II", data, off)
        if cmd == 0x19:  # LC_SEGMENT_64
            segname = data[off + 8:off + 24].rstrip(b"\0").decode()
            vmaddr, vmsize, fileoff, filesize = struct.unpack_from("<QQQQ", data, off + 24)
            if segname != "__PAGEZERO" and vmsize:
                segs.append((segname, vmaddr, vmsize, data[fileoff:fileoff + filesize]))
        off += cmdsize
    return segs


def symbols(path):
    out = subprocess.run(["nm", str(path)], check=True, capture_output=True, text=True).stdout
    table = {}
    for line in out.splitlines():
        parts = line.split()
        if len(parts) == 3 and parts[1].lower() in ("t", "b", "d", "s"):
            table[parts[2].lstrip("_")] = int(parts[0], 16)
    return table


def read_ref(index):
    return TABLE[1 + index] if index < TABLE[0] else -1000 - index


def reference(n):
    return sum(read_ref(i & 7) for i in range(n))


def run_image(image, n):
    uc = Uc(UC_ARCH_X86, UC_MODE_64)
    for _name, vmaddr, vmsize, content in macho_segments(image):
        base = align_down(vmaddr)
        uc.mem_map(base, align_up(vmaddr + vmsize) - base, UC_PROT_ALL)
        uc.mem_write(vmaddr, content)
    uc.mem_map(STACK_TOP - STACK_SIZE, STACK_SIZE, UC_PROT_ALL)
    uc.mem_map(DATA_BASE, 0x1_0000, UC_PROT_ALL)
    uc.mem_map(SENTINEL, PAGE, UC_PROT_ALL)
    uc.mem_write(SENTINEL, b"\xcc" * PAGE)
    sym = symbols(image)
    uc.mem_write(DATA_BASE, b"".join(struct.pack("<q", v) for v in TABLE))
    for counter in ("definition_calls", "slow_calls"):
        uc.mem_write(sym[counter], b"\0" * 8)
    uc.reg_write(X.UC_X86_REG_RDI, DATA_BASE)
    uc.reg_write(X.UC_X86_REG_RSI, n)
    rsp = STACK_TOP - 0x1000 - 8
    uc.mem_write(rsp, struct.pack("<Q", SENTINEL))
    uc.reg_write(X.UC_X86_REG_RSP, rsp)
    uc.emu_start(sym["sum"], SENTINEL, count=50_000_000)
    assert uc.reg_read(X.UC_X86_REG_RIP) == SENTINEL, "did not return"
    answer = struct.unpack("<q", struct.pack("<Q", uc.reg_read(X.UC_X86_REG_RAX)))[0]
    counters = [struct.unpack("<Q", uc.mem_read(sym[c], 8))[0]
                for c in ("definition_calls", "slow_calls")]
    return answer, counters[0], counters[1]


def main(example, out_tsv):
    rows = ["opt\tarm\tspliced\tn\tanswer\treference\tdefinition_calls\tslow_calls\tobject_sha256"]
    failures = 0
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        runtime = tmp / "runtime.c"
        for opt in ("0", "1", "2", "3"):
            for arm in ("on", "killed"):
                obj = tmp / f"sum_O{opt}_{arm}.o"
                env = dict(os.environ)
                env.pop("TCG_NO_INLINE_ONLY_BODIES", None)
                if arm == "killed":
                    env["TCG_NO_INLINE_ONLY_BODIES"] = "1"
                printed = subprocess.run(
                    [example, str(obj), opt, TRIPLE, "--runtime", str(runtime)],
                    check=True, capture_output=True, text=True, env=env).stdout
                spliced = 'spliced=[("tcg_read", 1)]' in printed
                sha = subprocess.run(["shasum", "-a", "256", str(obj)], check=True,
                                     capture_output=True, text=True).stdout.split()[0]
                image = tmp / f"image_O{opt}_{arm}"
                subprocess.run(["cc", "-arch", "x86_64", "-O0", "-o", str(image),
                                str(runtime), str(obj)], check=True)
                for n in COUNTS:
                    answer, definition_calls, slow_calls = run_image(image, n)
                    expected = reference(n)
                    slow_expected = sum(1 for i in range(n) if (i & 7) >= TABLE[0])
                    ok = (answer == expected and slow_calls == slow_expected
                          and definition_calls == (0 if spliced else n)
                          and spliced == (arm == "on" and opt != "0"))
                    failures += 0 if ok else 1
                    rows.append(f"O{opt}\t{arm}\t{spliced}\t{n}\t{answer}\t{expected}\t"
                                f"{definition_calls}\t{slow_calls}\t{sha}")
    Path(out_tsv).write_text("\n".join(rows) + "\n")
    print("\n".join(rows))
    print(f"runs={len(rows) - 1} failures={failures}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1], sys.argv[2]))
