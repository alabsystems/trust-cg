#!/usr/bin/env python3
"""Probe GNU ld 2.42 (and LLD 22 for recognition) on every aaelf64 relocation
whose operation names a GOT slot (Linux AArch64, 2026-09-23).

For each kind an object is assembled from a one-instruction function that
carries it; where GNU as 2.42 has no syntax for the kind, a stand-in
relocation of the same instruction form is assembled and its type is
patched to the kind (the record says which). Each object is linked with
`cc -shared -nostdlib` by GNU ld with the default layout ("near") and with
`.got` placed out of the kind's window ("far": 8 GiB for the page, data-word
and GOT-base kinds, 16 MiB for the load-literal and ADR kinds). LLD is run
on the default layout only, to record which kinds it recognizes. Three
GOT-base overflow probes follow: LD64_GOTPAGE_LO15 and LD64_GOTOFF_LO15 with
5,000 GOT slots, and TLSDESC_OFF_G1 with .got.plt placed 8 GiB from .got.

Usage: probe-got-kinds-20260923.py WORK OUT_JSON
"""

from __future__ import annotations

import json
import os
import struct
import subprocess
import sys
from pathlib import Path

WORK = Path(sys.argv[1]).resolve()
OUT = Path(sys.argv[2]).resolve()
WORK.mkdir(parents=True, exist_ok=True)
LLD_DIR = os.path.expanduser("~/.local/bin")


def patch_types(obj: Path, mapping: dict[int, int]) -> int:
    """Rewrite the type of every SHT_RELA entry of `obj` found in `mapping`."""
    data = bytearray(obj.read_bytes())
    (shoff,) = struct.unpack_from("<Q", data, 40)
    shentsize, shnum = struct.unpack_from("<HH", data, 58)
    count = 0
    for index in range(shnum):
        header = shoff + index * shentsize
        (kind,) = struct.unpack_from("<I", data, header + 4)
        if kind != 4:
            continue
        offset, size = struct.unpack_from("<QQ", data, header + 24)
        for entry in range(offset, offset + size, 24):
            (info,) = struct.unpack_from("<Q", data, entry + 8)
            if info & 0xFFFFFFFF in mapping:
                struct.pack_into("<Q", data, entry + 8, (info & ~0xFFFFFFFF) | mapping[info & 0xFFFFFFFF])
                count += 1
    obj.write_bytes(bytes(data))
    return count


TEMPLATE = """\t.text
\t.globl f
\t.type f, %function
f:
{ins}
\tret
\t.size f, .-f
\t.section .tdata,"awT",%progbits
\t.globl tv
\t.type tv, %object
\t.size tv, 4
tv:\t.word 42
\t.data
\t.globl dv
\t.type dv, %object
\t.size dv, 8
dv:\t.xword 7
"""

# code, name, class, instruction, stand-in type (None: GNU as emits the kind).
KINDS = [
    (300, "R_AARCH64_MOVW_GOTOFF_G0", "got-base", "\tmovz x0, #:gotoff_g1:dv", 302),
    (301, "R_AARCH64_MOVW_GOTOFF_G0_NC", "got-base", "\tmovk x0, #:gotoff_g0_nc:dv", None),
    (302, "R_AARCH64_MOVW_GOTOFF_G1", "got-base", "\tmovz x0, #:gotoff_g1:dv", None),
    (303, "R_AARCH64_MOVW_GOTOFF_G1_NC", "got-base", "\tmovk x0, #:gotoff_g0_nc:dv", 301),
    (304, "R_AARCH64_MOVW_GOTOFF_G2", "got-base", "\tmovz x0, #:gotoff_g1:dv", 302),
    (305, "R_AARCH64_MOVW_GOTOFF_G2_NC", "got-base", "\tmovk x0, #:gotoff_g0_nc:dv", 301),
    (306, "R_AARCH64_MOVW_GOTOFF_G3", "got-base", "\tmovz x0, #:gotoff_g1:dv", 302),
    (309, "R_AARCH64_GOT_LD_PREL19", "load-literal", "\tldr x0, :got:dv", None),
    (310, "R_AARCH64_LD64_GOTOFF_LO15", "got-base", "\tldr x0, [x28, #:gotoff_lo15:dv]", None),
    (311, "R_AARCH64_ADR_GOT_PAGE", "page", "\tadrp x0, :got:dv", None),
    (312, "R_AARCH64_LD64_GOT_LO12_NC", "low-bits", "\tldr x0, [x0, #:got_lo12:dv]", None),
    (313, "R_AARCH64_LD64_GOTPAGE_LO15", "got-base", "\tldr x0, [x28, #:gotpage_lo15:dv]", None),
    (315, "R_AARCH64_GOTPCREL32", "data-word", "\t.word dv - .", 261),
    (512, "R_AARCH64_TLSGD_ADR_PREL21", "adr", "\tadr x0, :tlsgd:tv", None),
    (513, "R_AARCH64_TLSGD_ADR_PAGE21", "page", "\tadrp x0, :tlsgd:tv", None),
    (514, "R_AARCH64_TLSGD_ADD_LO12_NC", "low-bits", "\tadd x0, x0, #:tlsgd_lo12:tv", None),
    (515, "R_AARCH64_TLSGD_MOVW_G1", "got-base", "\tmovz x0, #:tlsgd_g1:tv", None),
    (516, "R_AARCH64_TLSGD_MOVW_G0_NC", "got-base", "\tmovk x0, #:tlsgd_g0_nc:tv", None),
    (517, "R_AARCH64_TLSLD_ADR_PREL21", "adr", "\tadr x0, :tlsldm:tv", None),
    (518, "R_AARCH64_TLSLD_ADR_PAGE21", "page", "\tadrp x0, :tlsldm:tv", None),
    (519, "R_AARCH64_TLSLD_ADD_LO12_NC", "low-bits", "\tadd x0, x0, #:tlsldm_lo12_nc:tv", None),
    (520, "R_AARCH64_TLSLD_MOVW_G1", "got-base", "\tmovz x0, #:tlsgd_g1:tv", 515),
    (521, "R_AARCH64_TLSLD_MOVW_G0_NC", "got-base", "\tmovk x0, #:tlsgd_g0_nc:tv", 516),
    (522, "R_AARCH64_TLSLD_LD_PREL19", "load-literal", "\tldr x0, :gottprel:tv", 543),
    (539, "R_AARCH64_TLSIE_MOVW_GOTTPREL_G1", "got-base", "\tmovz x0, #:gottprel_g1:tv", None),
    (540, "R_AARCH64_TLSIE_MOVW_GOTTPREL_G0_NC", "got-base", "\tmovk x0, #:gottprel_g0_nc:tv", None),
    (541, "R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21", "page", "\tadrp x0, :gottprel:tv", None),
    (542, "R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC", "low-bits", "\tldr x0, [x0, #:gottprel_lo12:tv]", None),
    (543, "R_AARCH64_TLSIE_LD_GOTTPREL_PREL19", "load-literal", "\tldr x0, :gottprel:tv", None),
    (560, "R_AARCH64_TLSDESC_LD_PREL19", "load-literal", "\tldr x1, :tlsdesc:tv", None),
    (561, "R_AARCH64_TLSDESC_ADR_PREL21", "adr", "\tadr x0, :tlsdesc:tv", None),
    (562, "R_AARCH64_TLSDESC_ADR_PAGE21", "page", "\tadrp x0, :tlsdesc:tv", None),
    (563, "R_AARCH64_TLSDESC_LD64_LO12", "low-bits", "\tldr x1, [x0, #:tlsdesc_lo12:tv]", None),
    (564, "R_AARCH64_TLSDESC_ADD_LO12", "low-bits", "\tadd x0, x0, #:tlsdesc_lo12:tv", None),
    (565, "R_AARCH64_TLSDESC_OFF_G1", "got-base", "\tmovz x0, #:tlsdesc_off_g1:tv", None),
    (566, "R_AARCH64_TLSDESC_OFF_G0_NC", "got-base", "\tmovk x0, #:tlsdesc_off_g0_nc:tv", None),
    (581, "R_AARCH64_AUTH_MOVW_GOTOFF_G0", "got-base", "\tmovz x0, #:gotoff_g1:dv", 302),
    (582, "R_AARCH64_AUTH_MOVW_GOTOFF_G0_NC", "got-base", "\tmovk x0, #:gotoff_g0_nc:dv", 301),
    (583, "R_AARCH64_AUTH_MOVW_GOTOFF_G1", "got-base", "\tmovz x0, #:gotoff_g1:dv", 302),
    (584, "R_AARCH64_AUTH_MOVW_GOTOFF_G1_NC", "got-base", "\tmovk x0, #:gotoff_g0_nc:dv", 301),
    (585, "R_AARCH64_AUTH_MOVW_GOTOFF_G2", "got-base", "\tmovz x0, #:gotoff_g1:dv", 302),
    (586, "R_AARCH64_AUTH_MOVW_GOTOFF_G2_NC", "got-base", "\tmovk x0, #:gotoff_g0_nc:dv", 301),
    (587, "R_AARCH64_AUTH_MOVW_GOTOFF_G3", "got-base", "\tmovz x0, #:gotoff_g1:dv", 302),
    (588, "R_AARCH64_AUTH_GOT_LD_PREL19", "load-literal", "\tldr x0, :got:dv", 309),
    (589, "R_AARCH64_AUTH_LD64_GOTOFF_LO15", "got-base", "\tldr x0, [x28, #:gotoff_lo15:dv]", 310),
    (590, "R_AARCH64_AUTH_ADR_GOT_PAGE", "page", "\tadrp x0, :got:dv", 311),
    (591, "R_AARCH64_AUTH_LD64_GOT_LO12_NC", "low-bits", "\tldr x0, [x0, #:got_lo12:dv]", 312),
    (592, "R_AARCH64_AUTH_LD64_GOTPAGE_LO15", "got-base", "\tldr x0, [x28, #:gotpage_lo15:dv]", 313),
    (593, "R_AARCH64_AUTH_GOT_ADD_LO12_NC", "low-bits", "\tadd x0, x0, #:lo12:dv", 277),
    (594, "R_AARCH64_AUTH_GOT_ADR_PREL_LO21", "adr", "\tadr x0, dv", 274),
    (595, "R_AARCH64_AUTH_TLSDESC_ADR_PAGE21", "page", "\tadrp x0, :tlsdesc:tv", 562),
    (596, "R_AARCH64_AUTH_TLSDESC_LD64_LO12", "low-bits", "\tldr x1, [x0, #:tlsdesc_lo12:tv]", 563),
    (597, "R_AARCH64_AUTH_TLSDESC_ADD_LO12", "low-bits", "\tadd x0, x0, #:tlsdesc_lo12:tv", 564),
]
FAR = {
    "page": 0x2_0000_0000,
    "data-word": 0x2_0000_0000,
    "got-base": 0x2_0000_0000,
    "low-bits": 0x2_0000_0000,
    "load-literal": 0x100_0000,
    "adr": 0x100_0000,
}


def run(argv: list[str]) -> tuple[int, str]:
    completed = subprocess.run(argv, cwd=WORK, capture_output=True, text=True, timeout=120)
    return completed.returncode, (completed.stdout + completed.stderr).strip()


def link(obj: Path, output: str, extra: list[str]) -> dict:
    code, text = run(["cc", "-shared", "-nostdlib", "-Wl,-z,noexecstack", "-o", output, obj.name, *extra])
    return {"exit": code, "output": text[-800:]}


def main() -> int:
    rows = []
    for code, name, klass, instruction, standin in KINDS:
        base = WORK / f"k{code}"
        base.with_suffix(".s").write_text(TEMPLATE.format(ins=instruction))
        exit_code, text = run(["as", "-o", f"k{code}.o", f"k{code}.s"])
        row = {"code": code, "name": name, "class": klass, "instruction": instruction.strip()}
        if exit_code != 0:
            row["assembled"] = False
            row["as"] = text
            rows.append(row)
            continue
        row["assembled"] = True
        if standin is not None:
            row["stand_in"] = standin
            row["patched"] = patch_types(base.with_suffix(".o"), {standin: code})
        exit_code, text = run(["readelf", "-rW", f"k{code}.o"])
        row["readelf"] = [line.split()[2] for line in text.splitlines() if line[:1] == "0" and len(line.split()) > 2]
        row["gnu_ld_near"] = link(base.with_suffix(".o"), f"libk{code}_near.so", [])
        row["gnu_ld_far"] = link(
            base.with_suffix(".o"), f"libk{code}_far.so", [f"-Wl,--section-start=.got={FAR[klass]:#x}"]
        )
        row["far_got"] = hex(FAR[klass])
        row["lld_near"] = link(base.with_suffix(".o"), f"libk{code}_lld.so", ["-fuse-ld=lld", f"-B{LLD_DIR}"])
        rows.append(row)
        print(
            f"{code} {name:40} {klass:12} gnu-ld near {row['gnu_ld_near']['exit']} far "
            f"{row['gnu_ld_far']['exit']}  lld near {row['lld_near']['exit']}",
            flush=True,
        )

    # GOT-base overflow probes.
    overflow = []
    for name, instruction, count in (
        ("LD64_GOTPAGE_LO15", "ldr x0, [x28, #:gotpage_lo15:d{i}]", 5000),
        ("LD64_GOTOFF_LO15", "ldr x0, [x28, #:gotoff_lo15:d{i}]", 5000),
    ):
        source = ["\t.text", "\t.globl f", "f:"]
        source += ["\t" + instruction.format(i=i) for i in range(count)] + ["\tret", "\t.data"]
        for i in range(count):
            source += [f"\t.globl d{i}", f"d{i}:\t.xword {i}"]
        (WORK / f"{name}.s").write_text("\n".join(source) + "\n")
        run(["as", "-o", f"{name}.o", f"{name}.s"])
        result = link(WORK / f"{name}.o", f"lib{name}.so", [])
        overflow.append({"name": name, "slots": count, **result})
    result = link(WORK / "k565.o", "libk565_gotplt_far.so", ["-Wl,--section-start=.got.plt=0x200010000"])
    overflow.append({"name": "TLSDESC_OFF_G1", "placement": ".got.plt at 0x200010000", **result})
    for entry in overflow:
        print(f"overflow {entry['name']}: exit {entry['exit']}", flush=True)
    OUT.write_text(json.dumps({"kinds": rows, "got_base_overflow": overflow}, indent=1) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
