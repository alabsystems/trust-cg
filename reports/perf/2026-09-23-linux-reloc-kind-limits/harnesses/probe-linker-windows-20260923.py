#!/usr/bin/env python3
"""Probe the host linkers' overflow checks at both edges of the psABI window
of the checked AArch64 relocation kinds trust-cg emits.

Usage: probe_windows.py OUT_DIR

Each case assembles a small GNU-as source, links it with GNU ld (bfd), gold
and lld, and records the exit status and the first diagnostic lines in
OUT_DIR/results.json. The value X each relocation resolves to is fixed by
--defsym, --section-start or a .tbss pad, so each edge value is exact. When a
link accepts a value the psABI puts outside the window, the relocated
instruction and the section table of the written image are recorded too.
.text is pinned with --section-start in every placed case: without it, gold
2.42 aborts with an internal error in set_segment_offsets, and lld lays
.text out after a placed .got. gold still aborts (set_offset) on every
-shared link with a placed .got, in or out of the window.

This is linker-behaviour evidence for these inputs, not a proof of any
window.
"""

from __future__ import annotations

import json
import os
import pathlib
import subprocess
import sys

OUT = pathlib.Path(sys.argv[1]).resolve()
OUT.mkdir(parents=True, exist_ok=True)
LLD = os.path.expanduser("~/.local/bin/ld.lld")
# lld refuses a section below its default image base and relro sections that
# a placement splits; neither changes which values it checks.
LINKERS = {
    "bfd": ["ld.bfd"],
    "gold": ["ld.gold"],
    "lld": [LLD, "-z", "norelro", "--image-base=0x10000"],
}
PLACEMENT_LINKERS = ("bfd", "gold", "lld")

TEXT_BASE = 0x100000
DATA_BASE = 0x10000000
GIB = 1 << 30
MASK = (1 << 64) - 1

SOURCES = {
    "abs32": """    .text
    .globl _start
_start:
    ret
    .data
    .p2align 2
slot:
    .word far_sym
""",
    "prel32": """    .text
    .globl _start
_start:
    ret
    .data
    .p2align 2
slot:
    .word far_sym - .
""",
    "adrp": """    .text
    .globl _start
_start:
    adrp x0, far_sym
    ret
""",
    # TPREL(v) = 16 (TCB, p_align 1) + PAD: .tbss holds PAD bytes, then v.
    "tlsle": """    .text
    .globl _start
_start:
    mrs x0, tpidr_el0
    add x0, x0, #:tprel_hi12:v, lsl #12
    add x0, x0, #:tprel_lo12_nc:v
    ret
    .section .tbss,"awT",@nobits
    .p2align 0
pad:
    .zero PAD
    .globl v
v:
    .zero 1
""",
    # GOT-indirect address of a preemptible data symbol (-shared keeps it).
    "gotpage": """    .text
    .globl get
    .type get,%function
get:
    adrp x0, :got:dv
    ldr x0, [x0, #:got_lo12:dv]
    ret
    .data
    .globl dv
    .type dv,%object
    .p2align 3
dv:
    .xword 7
""",
    # Initial-exec TLS through its GOT slot (-shared, DF_STATIC_TLS).
    "tlsie": """    .text
    .globl get
    .type get,%function
get:
    adrp x0, :gottprel:iv
    ldr x0, [x0, #:gottprel_lo12:iv]
    mrs x1, tpidr_el0
    add x0, x1, x0
    ret
    .section .tbss,"awT",@nobits
    .globl iv
    .type iv,%object
    .p2align 3
iv:
    .zero 8
""",
    # General-dynamic TLS descriptor access to a preemptible thread-local,
    # kept as TLSDESC in a -shared link.
    "tlsdesc": """    .text
    .globl get
    .type get,%function
get:
    stp x29, x30, [sp, #-16]!
    adrp x0, :tlsdesc:tv
    ldr x1, [x0, #:tlsdesc_lo12:tv]
    add x0, x0, #:tlsdesc_lo12:tv
    .tlsdesccall tv
    blr x1
    mrs x1, tpidr_el0
    add x0, x1, x0
    ldp x29, x30, [sp], #16
    ret
    .section .tbss,"awT",@nobits
    .globl tv
    .type tv,%object
    .p2align 3
tv:
    .zero 8
""",
}


def run(argv: list[str], cwd: pathlib.Path) -> dict:
    proc = subprocess.run(argv, cwd=cwd, capture_output=True, text=True, timeout=120)
    lines = [line for line in (proc.stderr + proc.stdout).splitlines() if line.strip()]
    return {"argv": argv, "status": proc.returncode, "diagnostic": lines[:4]}


def assemble(name: str, source: str) -> pathlib.Path:
    src = OUT / f"{name}.s"
    obj = OUT / f"{name}.o"
    src.write_text(source)
    result = run(["as", src.name, "-o", obj.name], OUT)
    assert result["status"] == 0, result
    return obj


def tool_versions() -> dict:
    versions = {}
    for name, argv in [("as", ["as", "--version"]), ("bfd", ["ld.bfd", "--version"]),
                       ("gold", ["ld.gold", "--version"]), ("lld", [LLD, "--version"])]:
        versions[name] = subprocess.run(argv, capture_output=True, text=True).stdout.splitlines()[0]
    return versions


def main() -> int:
    cases = []

    def case(kind, value, in_window, obj, extra, linkers, shared=False):
        for linker in linkers:
            output = OUT / f"{obj.stem}-{linker}-{value & MASK:x}.out"
            argv = list(LINKERS[linker]) + (["-shared"] if shared else ["-e", "_start"])
            argv += extra + [obj.name, "-o", output.name]
            result = run(argv, OUT)
            if output.exists():
                if not in_window:
                    dis = subprocess.run(["objdump", "-d", "--no-show-raw-insn", output.name],
                                         cwd=OUT, capture_output=True, text=True, timeout=60).stdout
                    sections = subprocess.run(["readelf", "-rSW", output.name], cwd=OUT,
                                              capture_output=True, text=True, timeout=60).stdout
                    result["accepted_image"] = {
                        "adrp_lines": [l.strip() for l in dis.splitlines() if "adrp" in l][:4],
                        "readelf_lines": [l.strip() for l in sections.splitlines()
                                          if "R_AARCH64" in l or ".got" in l or " .text " in l
                                          or " .data " in l][:12],
                    }
                output.unlink()
            cases.append({"relocation": f"R_AARCH64_{kind}", "linker": linker, "x": value,
                          "psabi_in_window": in_window, **result})

    placed = [f"--section-start=.text={TEXT_BASE:#x}"]

    abs32 = assemble("abs32", SOURCES["abs32"])
    for x, ok in [(2**32 - 1, True), (2**32, False), (-2**31, True), (-2**31 - 1, False)]:
        case("ABS32", x, ok, abs32, placed + [f"--defsym=far_sym={x & MASK:#x}",
                                             f"--section-start=.data={DATA_BASE:#x}"],
             PLACEMENT_LINKERS)

    prel32 = assemble("prel32", SOURCES["prel32"])
    # aaelf64 2026Q2 and later: -2^31 <= X < 2^31 (earlier releases: < 2^32).
    for x, ok in [(2**31 - 1, True), (2**31, False), (2**32 - 1, False), (-2**31, True),
                  (-2**31 - 1, False)]:
        case("PREL32", x, ok, prel32, placed + [f"--defsym=far_sym={(DATA_BASE + x) & MASK:#x}",
                                               f"--section-start=.data={DATA_BASE:#x}"],
             PLACEMENT_LINKERS)

    # X = Page(S) - Page(P); P is _start at the start of .text.
    adrp = assemble("adrp", SOURCES["adrp"])
    for text, x, ok in [(TEXT_BASE, 4 * GIB - 4096, True), (TEXT_BASE, 4 * GIB, False),
                        (TEXT_BASE + 4 * GIB, -4 * GIB, True),
                        (TEXT_BASE + 4 * GIB, -4 * GIB - 4096, False)]:
        case("ADR_PREL_PG_HI21", x, ok, adrp,
             [f"--section-start=.text={text:#x}", f"--defsym=far_sym={text + x:#x}"],
             PLACEMENT_LINKERS)

    # TPREL(v) = align_up(16, p_align = 1) + PAD = 16 + PAD.
    for x, ok in [(2**24 - 1, True), (2**24, False)]:
        obj = assemble(f"tlsle-{x:x}", SOURCES["tlsle"].replace("PAD", str(x - 16)))
        case("TLSLE_ADD_TPREL_HI12", x, ok, obj, [], ("bfd", "gold", "lld"))

    # The GOT and .got.plt are placed at GOT_BASE and .text at TEXT_BASE, so
    # the page delta is about GOT_BASE.
    for name, kind in [("gotpage", "ADR_GOT_PAGE"), ("tlsie", "TLSIE_ADR_GOTTPREL_PAGE21"),
                       ("tlsdesc", "TLSDESC_ADR_PAGE21")]:
        obj = assemble(name, SOURCES[name])
        for got_base, ok in [(2 * GIB, True), (8 * GIB, False)]:
            extra = placed + [f"--section-start=.got={got_base:#x}",
                              f"--section-start=.got.plt={got_base + 0x10000:#x}"]
            case(kind, got_base, ok, obj, extra, PLACEMENT_LINKERS, shared=True)

    report = {"tools": tool_versions(), "cases": cases}
    (OUT / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    for row in cases:
        verdict = "linked" if row["status"] == 0 else "refused"
        silent = " (accepted outside the window)" if row["status"] == 0 and not row["psabi_in_window"] else ""
        print(f"{row['relocation']:38} {row['linker']:5} X={row['x']:>12} "
              f"in_window={row['psabi_in_window']!s:5} -> {verdict}{silent}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
