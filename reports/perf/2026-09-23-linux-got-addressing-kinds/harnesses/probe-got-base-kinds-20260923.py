#!/usr/bin/env python3
"""Probe GNU ld 2.42, gold 2.42 and LLD 22 on every aaelf64 GOT-base
relocation (a GOT slot measured from the GOT base) on Linux AArch64,
2026-09-23 (the L02-P10 GOT-base repair).

For each of the 26 aaelf64 GOT-base kinds (and the two GOT-relative data
relocations GOTREL64/GOTREL32, which name no slot) an object is assembled
from one instruction that carries it; where GNU as 2.42 has no syntax for the
kind a stand-in relocation of the same instruction form is assembled and its
type patched (the record says which). Each object is linked with
`cc -shared -nostdlib` by each linker ("near": default layout).

The GOT base each linker uses is read back from its near LD64_GOTPAGE_LO15 and
LD64_GOTOFF_LO15 libraries, PIEs and static PIEs: the slot (`R_AARCH64_GLOB_DAT`
target, or the `RELATIVE` whose addend is the symbol) minus the offset the
linker wrote, against `_GLOBAL_OFFSET_TABLE_` in `.symtab` and the start of
`.got`. The verifier's `gb.o` shape (6,000 slots through ADR_GOT_PAGE, then
one LD64_GOTPAGE_LO15 load of `dv_last`) is linked by each linker: gold defines
`_GLOBAL_OFFSET_TABLE_` inside `.got` there. The LO15 forms against an IFUNC
show where each linker puts its GOT slot (LLD: `.got.plt`).

"Far" probes put slots outside each checked form's window where a layout can:
the LO15 forms with 6,000 slots (48 KiB), every slot addressed through the
probed kind so some slot is out of the window whatever order the linker
chooses; the MOVW G0 forms with 10,000 slots (80 KiB); TLSDESC_OFF_G1 with
.got.plt 8 GiB from .got (GNU ld keeps descriptor slots in .got.plt); and the
MOVW_GOTOFF_G1 forms against an IFUNC in a static position-dependent program
with .got.plt 8 GiB away (GNU ld gives the IFUNC's GOT reference its PLT
slot there). Each linked far library has every written field decoded and
compared with the value the psABI operation gives from the linker's own GOT
base (`_GLOBAL_OFFSET_TABLE_`) and each slot: "truncated" means the linker
exited 0 and wrote a value that is not X.

Usage: probe-got-base-kinds-20260923.py WORK OUT_JSON
"""

from __future__ import annotations

import json
import os
import re
import struct
import subprocess
import sys
from pathlib import Path

WORK = Path(sys.argv[1]).resolve()
OUT = Path(sys.argv[2]).resolve()
WORK.mkdir(parents=True, exist_ok=True)
LLD_DIR = os.path.expanduser("~/.local/bin")
LINKERS = {
    "gnu-ld": ["-fuse-ld=bfd"],
    "gold": ["-fuse-ld=gold"],
    "lld": ["-fuse-ld=lld", f"-B{LLD_DIR}"],
}
R_AARCH64_GLOB_DAT = 1025
R_AARCH64_IRELATIVE = 1032
R_AARCH64_TLSDESC = 1031


def run(argv: list[str], cwd: Path = WORK) -> tuple[int, str]:
    completed = subprocess.run(argv, cwd=cwd, capture_output=True, text=True, timeout=300)
    return completed.returncode, (completed.stdout + completed.stderr).strip()


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


class Image:
    """The sections, symbols and dynamic relocations of a linked ELF64 image."""

    def __init__(self, path: Path):
        self.data = path.read_bytes()
        d = self.data
        (shoff,) = struct.unpack_from("<Q", d, 40)
        shentsize, shnum, shstrndx = struct.unpack_from("<HHH", d, 58)
        headers = []
        for i in range(shnum):
            at = shoff + i * shentsize
            name, kind, flags, addr, off, size, link, info, align, entsize = struct.unpack_from(
                "<IIQQQQIIQQ", d, at
            )
            headers.append([name, kind, flags, addr, off, size, link, entsize])
        strtab = headers[shstrndx]
        names = d[strtab[4] : strtab[4] + strtab[5]]

        def cstr(table: bytes, at: int) -> str:
            return table[at : table.index(b"\0", at)].decode()

        self.sections = []
        for h in headers:
            self.sections.append(
                {"name": cstr(names, h[0]), "kind": h[1], "flags": h[2], "address": h[3], "offset": h[4], "size": h[5], "link": h[6]}
            )
        self.symbols: dict[str, list[int]] = {}
        self.dynsyms: list[str] = []
        for s in self.sections:
            if s["kind"] in (2, 11):
                strings = self.sections[s["link"]]
                table = d[strings["offset"] : strings["offset"] + strings["size"]]
                for at in range(s["offset"], s["offset"] + s["size"], 24):
                    st_name, info, other, shndx, value, size = struct.unpack_from("<IBBHQQ", d, at)
                    name = cstr(table, st_name)
                    if s["kind"] == 11:
                        self.dynsyms.append(name)
                    elif shndx != 0 and name:
                        self.symbols.setdefault(name, []).append(value)
        self.relocations = []  # (offset, type, symbol name)
        for s in self.sections:
            if s["kind"] == 4 and s["flags"] & 2:
                for at in range(s["offset"], s["offset"] + s["size"], 24):
                    r_offset, r_info, addend = struct.unpack_from("<QQq", d, at)
                    symbol = self.dynsyms[r_info >> 32] if (r_info >> 32) and s["link"] and self.sections[s["link"]]["kind"] == 11 else ""
                    self.relocations.append((r_offset, r_info & 0xFFFFFFFF, symbol, addend))

    def section(self, name: str):
        return next((s for s in self.sections if s["name"] == name), None)

    def word(self, address: int) -> int:
        for s in self.sections:
            if s["kind"] != 8 and s["address"] <= address < s["address"] + s["size"] and s["flags"] & 2:
                (value,) = struct.unpack_from("<I", self.data, s["offset"] + address - s["address"])
                return value
        raise KeyError(hex(address))

    def qword(self, address: int) -> int | None:
        for s in self.sections:
            if s["kind"] != 8 and s["address"] <= address and address + 8 <= s["address"] + s["size"] and s["flags"] & 2:
                (value,) = struct.unpack_from("<Q", self.data, s["offset"] + address - s["address"])
                return value
        return None

    def section_of(self, address: int) -> str | None:
        for s in self.sections:
            if s["flags"] & 2 and s["address"] <= address < s["address"] + s["size"]:
                return s["name"]
        return None

    def symbol(self, name: str) -> int | None:
        values = sorted(set(self.symbols.get(name, [])))
        return values[0] if len(values) == 1 else None

    def slot(self, symbol: str, kinds: tuple[int, ...] = (R_AARCH64_GLOB_DAT,)) -> int | None:
        found = [r[0] for r in self.relocations if r[1] in kinds and r[2] == symbol]
        return found[0] if len(found) == 1 else None


def ldst_offset(word: int) -> int:
    """The byte offset of a 64-bit LDR (unsigned offset): imm12 scaled by 8."""
    return ((word >> 10) & 0xFFF) * 8


def movw_value(word: int) -> int:
    """The value a MOVZ/MOVN/MOVK writes into its halfword (MOVN inverted)."""
    imm16 = (word >> 5) & 0xFFFF
    hw = (word >> 21) & 3
    opc = (word >> 29) & 3
    if opc == 0:  # MOVN
        return ~(imm16 << (16 * hw))
    return imm16 << (16 * hw)


def first_error(text: str) -> str:
    lines = [line for line in text.splitlines() if not line.startswith("collect2:")]
    for line in lines:
        if "error" in line or "internal" in line or "truncated" in line or "unknown" in line or "unsupported" in line:
            return line.strip()[:300]
    return lines[0].strip()[:300] if lines else ""


def classify(code: int, text: str) -> str:
    if code == 0:
        return "links"
    if "unknown relocation" in text or "unsupported reloc" in text or "unexpected reloc" in text or "unrecognized reloc" in text:
        return "does not recognize"
    if "internal error" in text:
        return "internal error"
    if "truncated to fit" in text or "out of range" in text:
        return "refuses (out of range)"
    return "refuses (other)"


TEMPLATE = """\t.text
\t.globl f
\t.type f, %function
f:
\tadrp x28, _GLOBAL_OFFSET_TABLE_
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

# code, name, window ("lo15-page", "lo15", "g0", "g1", "g2", "none"), instruction, stand-in type.
KINDS = [
    (300, "R_AARCH64_MOVW_GOTOFF_G0", "g0", "\tmovz x0, #:gotoff_g1:dv", 302),
    (301, "R_AARCH64_MOVW_GOTOFF_G0_NC", "none", "\tmovk x0, #:gotoff_g0_nc:dv", None),
    (302, "R_AARCH64_MOVW_GOTOFF_G1", "g1", "\tmovz x0, #:gotoff_g1:dv", None),
    (303, "R_AARCH64_MOVW_GOTOFF_G1_NC", "none", "\tmovk x0, #:gotoff_g0_nc:dv", 301),
    (304, "R_AARCH64_MOVW_GOTOFF_G2", "g2", "\tmovz x0, #:gotoff_g1:dv", 302),
    (305, "R_AARCH64_MOVW_GOTOFF_G2_NC", "none", "\tmovk x0, #:gotoff_g0_nc:dv", 301),
    (306, "R_AARCH64_MOVW_GOTOFF_G3", "none", "\tmovz x0, #:gotoff_g1:dv", 302),
    (310, "R_AARCH64_LD64_GOTOFF_LO15", "lo15", "\tldr x0, [x28, #:gotoff_lo15:dv]", None),
    (313, "R_AARCH64_LD64_GOTPAGE_LO15", "lo15-page", "\tldr x0, [x28, #:gotpage_lo15:dv]", None),
    (515, "R_AARCH64_TLSGD_MOVW_G1", "g1", "\tmovz x0, #:tlsgd_g1:tv", None),
    (516, "R_AARCH64_TLSGD_MOVW_G0_NC", "none", "\tmovk x0, #:tlsgd_g0_nc:tv", None),
    (520, "R_AARCH64_TLSLD_MOVW_G1", "g1", "\tmovz x0, #:tlsgd_g1:tv", 515),
    (521, "R_AARCH64_TLSLD_MOVW_G0_NC", "none", "\tmovk x0, #:tlsgd_g0_nc:tv", 516),
    (539, "R_AARCH64_TLSIE_MOVW_GOTTPREL_G1", "g1", "\tmovz x0, #:gottprel_g1:tv", None),
    (540, "R_AARCH64_TLSIE_MOVW_GOTTPREL_G0_NC", "none", "\tmovk x0, #:gottprel_g0_nc:tv", None),
    (565, "R_AARCH64_TLSDESC_OFF_G1", "g1", "\tmovz x0, #:tlsdesc_off_g1:tv", None),
    (566, "R_AARCH64_TLSDESC_OFF_G0_NC", "none", "\tmovk x0, #:tlsdesc_off_g0_nc:tv", None),
    (581, "R_AARCH64_AUTH_MOVW_GOTOFF_G0", "g0", "\tmovz x0, #:gotoff_g1:dv", 302),
    (582, "R_AARCH64_AUTH_MOVW_GOTOFF_G0_NC", "none", "\tmovk x0, #:gotoff_g0_nc:dv", 301),
    (583, "R_AARCH64_AUTH_MOVW_GOTOFF_G1", "g1", "\tmovz x0, #:gotoff_g1:dv", 302),
    (584, "R_AARCH64_AUTH_MOVW_GOTOFF_G1_NC", "none", "\tmovk x0, #:gotoff_g0_nc:dv", 301),
    (585, "R_AARCH64_AUTH_MOVW_GOTOFF_G2", "g2", "\tmovz x0, #:gotoff_g1:dv", 302),
    (586, "R_AARCH64_AUTH_MOVW_GOTOFF_G2_NC", "none", "\tmovk x0, #:gotoff_g0_nc:dv", 301),
    (587, "R_AARCH64_AUTH_MOVW_GOTOFF_G3", "none", "\tmovz x0, #:gotoff_g1:dv", 302),
    (589, "R_AARCH64_AUTH_LD64_GOTOFF_LO15", "lo15", "\tldr x0, [x28, #:gotoff_lo15:dv]", 310),
    (592, "R_AARCH64_AUTH_LD64_GOTPAGE_LO15", "lo15-page", "\tldr x0, [x28, #:gotpage_lo15:dv]", 313),
    # GOT-relative data relocations: S + A - GOT, no slot.
    (307, "R_AARCH64_GOTREL64", "data64", "\t.xword dv", 257),
    (308, "R_AARCH64_GOTREL32", "data32", "\t.word dv", 258),
]


def link(obj: str, output: str, linker: str, extra: list[str], shape: list[str] | None = None) -> dict:
    argv = ["cc", *(shape or ["-shared"]), "-nostdlib", "-Wl,-z,noexecstack", *LINKERS[linker], "-o", output, obj, *extra]
    code, text = run(argv)
    home = os.path.expanduser("~")
    shown = [a.replace(home, "$HOME") for a in argv]
    return {"argv": shown, "exit": code, "class": classify(code, text), "first_error": first_error(text) if code else "", "output": text[-1500:].replace(home, "$HOME")}


def assemble(name: str, source: str, standin: int | None, code: int) -> dict:
    (WORK / f"{name}.s").write_text(source)
    exit_code, text = run(["as", "-o", f"{name}.o", f"{name}.s"])
    row = {"assembled": exit_code == 0, "as": text}
    if exit_code == 0 and standin is not None:
        row["stand_in"] = standin
        row["patched"] = patch_types(WORK / f"{name}.o", {standin: code})
    _, text = run(["readelf", "-rW", f"{name}.o"])
    row["types"] = sorted({line.split()[2] for line in text.splitlines() if line[:1] == "0" and len(line.split()) > 2})
    return row


def near_probes() -> list[dict]:
    rows = []
    for code, name, window, instruction, standin in KINDS:
        if window.startswith("data"):
            source = f"\t.data\n\t.globl dv\ndv:\t.xword 7\nw:\n{instruction}\n"
        else:
            source = TEMPLATE.format(ins=instruction)
        row = {"code": code, "name": name, "window": window, "instruction": instruction.strip()}
        row.update(assemble(f"k{code}", source, standin, code))
        if not row["assembled"]:
            rows.append(row)
            continue
        row["near"] = {}
        for linker in LINKERS:
            row["near"][linker] = link(f"k{code}.o", f"libk{code}_{linker}.so", linker, [])
        rows.append(row)
        print(f"{code} {name:38} " + "  ".join(f"{l}: {row['near'][l]['class']}" for l in LINKERS), flush=True)
    return rows


def base_probes() -> list[dict]:
    """Which GOT base each linker measures LD64_GOTPAGE_LO15/GOTOFF_LO15 from."""
    rows = []
    for code, kind in ((313, "gotpage"), (310, "gotoff")):
        for linker in LINKERS:
            for shape in (["-shared"], ["-pie"], ["-static-pie"]):
                output = f"base_{kind}_{linker}_{shape[0][1:]}"
                result = link(f"k{code}.o", output, linker, [], shape)
                row = {"code": code, "linker": linker, "shape": shape[0], "exit": result["exit"], "class": result["class"], "first_error": result["first_error"]}
                if result["exit"] == 0:
                    image = Image(WORK / output)
                    row.update(read_base(image, code, "dv"))
                rows.append(row)
    # gold with 6,000 slots: _GLOBAL_OFFSET_TABLE_ is not the start of .got.
    return rows


def read_base(image: Image, code: int, symbol: str, index: int = 0) -> dict:
    got = image.section(".got")
    base = image.symbol("_GLOBAL_OFFSET_TABLE_")
    f = image.symbol("f")
    slot = image.slot(symbol)
    if slot is None:
        # A PIE or static PIE binds `dv` itself: its slot is the RELATIVE whose addend is `dv`.
        dv = image.symbol(symbol)
        found = [r[0] for r in image.relocations if r[1] == 1027 and r[3] == dv]
        slot = found[0] if len(found) == 1 else None
    word = image.word(f + 4 + 4 * index)
    written = ldst_offset(word)
    row = {
        "got_start": hex(got["address"]) if got else None,
        "got_end": hex(got["address"] + got["size"]) if got else None,
        "_GLOBAL_OFFSET_TABLE_": hex(base) if base is not None else None,
        "slot": hex(slot) if slot is not None else None,
        "written": written,
    }
    if slot is not None:
        origin = slot - written
        row["implied_origin"] = hex(origin)
        if base is not None:
            expected = (base & ~0xFFF) if code in (313, 592) else base
            row["origin_is_symbol"] = origin == expected
        if got is not None:
            start = (got["address"] & ~0xFFF) if code in (313, 592) else got["address"]
            row["origin_is_got_start"] = origin == start
    return row


def many(code: int, standin: int | None, instruction: str, count: int, name: str) -> Path:
    source = ["\t.text", "\t.globl f", "\t.type f, %function", "f:", "\tadrp x28, _GLOBAL_OFFSET_TABLE_"]
    source += ["\t" + instruction.format(i=i) for i in range(count)]
    source += ["\tret", "\t.size f, .-f", "\t.data"]
    for i in range(count):
        source += [f"\t.globl d{i}", f"\t.type d{i}, %object", f"\t.size d{i}, 8", f"d{i}:\t.xword {i}"]
    (WORK / f"{name}.s").write_text("\n".join(source) + "\n")
    run(["as", "-o", f"{name}.o", f"{name}.s"])
    if standin is not None:
        patch_types(WORK / f"{name}.o", {standin: code})
    return WORK / f"{name}.o"


def far_probes() -> list[dict]:
    rows = []
    # LO15 forms: 6,000 slots, every one through the kind.
    for code, standin, instruction, page in (
        (313, None, "ldr x0, [x28, #:gotpage_lo15:d{i}]", True),
        (310, None, "ldr x0, [x28, #:gotoff_lo15:d{i}]", False),
        (592, 313, "ldr x0, [x28, #:gotpage_lo15:d{i}]", True),
        (589, 310, "ldr x0, [x28, #:gotoff_lo15:d{i}]", False),
    ):
        name = f"far{code}"
        many(code, standin, instruction, 6000, name)
        for linker in LINKERS:
            output = f"lib{name}_{linker}.so"
            result = link(f"{name}.o", output, linker, [])
            row = {"code": code, "layout": "6,000 slots, every one through the kind", "linker": linker, "exit": result["exit"], "class": result["class"], "first_error": result["first_error"]}
            if result["exit"] == 0:
                image = Image(WORK / output)
                base = image.symbol("_GLOBAL_OFFSET_TABLE_")
                f = image.symbol("f")
                origin = (base & ~0xFFF) if page else base
                truncated, out_of_window, examples = 0, 0, []
                for i in range(6000):
                    slot = image.slot(f"d{i}")
                    x = slot - origin
                    written = ldst_offset(image.word(f + 4 + 4 * i))
                    if not (0 <= x <= 32760):
                        out_of_window += 1
                    if written != x:
                        truncated += 1
                        if len(examples) < 3:
                            examples.append({"symbol": f"d{i}", "slot": hex(slot), "X": x, "written": written, "X_and_0x7ff8": x & 0x7FF8})
                got = image.section(".got")
                row.update({
                    "_GLOBAL_OFFSET_TABLE_": hex(base),
                    "got": [hex(got["address"]), hex(got["address"] + got["size"])],
                    "slots_out_of_window": out_of_window,
                    "written_not_X": truncated,
                    "examples": examples,
                })
                row["class"] = "links, value truncated" if truncated else "links, every value right"
            rows.append(row)
            print(f"far {code} {linker}: {row['class']} {row.get('written_not_X', '')}", flush=True)
    # MOVW G0 forms: 10,000 slots.
    for code in (300, 581):
        name = f"far{code}"
        many(code, 302, "movz x0, #:gotoff_g1:d{i}", 10000, name)
        for linker in LINKERS:
            result = link(f"{name}.o", f"lib{name}_{linker}.so", linker, [])
            rows.append({"code": code, "layout": "10,000 slots", "linker": linker, "exit": result["exit"], "class": result["class"], "first_error": result["first_error"]})
            print(f"far {code} {linker}: {result['class']}", flush=True)
    # TLSDESC_OFF_G1: descriptor slots in .got.plt, placed 8 GiB from .got.
    for linker in LINKERS:
        result = link("k565.o", f"libfar565_{linker}.so", linker, ["-Wl,--section-start=.got.plt=0x200010000"])
        row = {"code": 565, "layout": ".got.plt at 0x200010000", "linker": linker, "exit": result["exit"], "class": result["class"], "first_error": result["first_error"]}
        if result["exit"] == 0:
            image = Image(WORK / f"libfar565_{linker}.so")
            base = image.symbol("_GLOBAL_OFFSET_TABLE_")
            slot = image.slot("tv", (R_AARCH64_TLSDESC,))
            row.update({"_GLOBAL_OFFSET_TABLE_": base and hex(base), "slot": slot and hex(slot)})
            if base is not None and slot is not None:
                x = slot - base
                written = movw_value(image.word(image.symbol("f") + 4))
                row.update({"X": x, "written": written & 0xFFFF_FFFF_FFFF_FFFF})
                if not (-(1 << 32) <= x < (1 << 32)):
                    row["class"] = "links, value truncated"
        rows.append(row)
        print(f"far 565 {linker}: {row['class']}", flush=True)
    # MOVW_GOTOFF_G1 (and its PAuth form) against an IFUNC in a static
    # position-dependent program, .got.plt 8 GiB away.
    ifunc = (
        "\t.text\n\t.globl _start\n\t.type _start, %function\n_start:\n\tadrp x28, _GLOBAL_OFFSET_TABLE_\n"
        "\tmovz x0, #:gotoff_g1:myfunc\n\tmovk x0, #:gotoff_g0_nc:myfunc\n\tmov x8, #93\n\tsvc #0\n"
        "\t.size _start, .-_start\n\t.globl myfunc\n\t.type myfunc, %gnu_indirect_function\nmyfunc:\n\tadr x0, impl\n\tret\nimpl:\n\tmov x0, #42\n\tret\n"
    )
    for code, standin in ((302, None), (583, 302)):
        name = f"ifunc{code}"
        assemble(name, ifunc, standin, code)
        for linker in LINKERS:
            output = f"{name}_{linker}"
            result = link(f"{name}.o", output, linker, ["-Wl,--section-start=.got.plt=0x200000000"], ["-static", "-no-pie"])
            row = {"code": code, "layout": "IFUNC, static, .got.plt at 0x200000000", "linker": linker, "exit": result["exit"], "class": result["class"], "first_error": result["first_error"]}
            if result["exit"] == 0:
                image = Image(WORK / output)
                base = image.symbol("_GLOBAL_OFFSET_TABLE_")
                slots = [r[0] for r in image.relocations if r[1] == R_AARCH64_IRELATIVE]
                row.update({"_GLOBAL_OFFSET_TABLE_": base and hex(base), "irelative_slots": [hex(s) for s in slots]})
                if base is not None and len(slots) == 1:
                    x = slots[0] - base
                    row["X"] = x
                    if not (-(1 << 32) <= x < (1 << 32)):
                        row["class"] = "links, value truncated"
                    else:
                        row["class"] = "links, slot within the window"
            rows.append(row)
            print(f"far {code} ifunc {linker}: {row['class']}", flush=True)
    return rows


def verifier_shape() -> list[dict]:
    """The verifier's gb.o shape: 6,000 slots loaded through ADR_GOT_PAGE, then
    one LD64_GOTPAGE_LO15 load of dv_last, linked -shared -nostdlib by each
    linker: where each puts _GLOBAL_OFFSET_TABLE_ and dv_last's slot, and what
    it writes (gold defines the symbol inside .got here)."""
    source = ["\t.text", "\t.globl touch", "\t.type touch, %function", "touch:"]
    for i in range(6000):
        source += [f"\tadrp x1, :got:dv_{i}", f"\tldr x1, [x1, #:got_lo12:dv_{i}]"]
    source += ["\tret", "\t.size touch, .-touch", "\t.globl f_gb", "\t.type f_gb, %function", "f_gb:",
               "\tadrp x28, _GLOBAL_OFFSET_TABLE_", "\tldr x0, [x28, #:gotpage_lo15:dv_last]", "\tldr x0, [x0]",
               "\tret", "\t.size f_gb, .-f_gb", "\t.data"]
    for i in range(6000):
        source += [f"\t.globl dv_{i}", f"dv_{i}:", f"\t.xword {i}"]
    source += ["\t.globl dv_last", "dv_last:", "\t.xword 4242"]
    (WORK / "gbshape.s").write_text("\n".join(source) + "\n")
    run(["as", "-o", "gbshape.o", "gbshape.s"])
    rows = []
    for linker in LINKERS:
        output = f"libgbshape_{linker}.so"
        result = link("gbshape.o", output, linker, [])
        row = {"linker": linker, "exit": result["exit"], "class": result["class"], "first_error": result["first_error"]}
        if result["exit"] == 0:
            image = Image(WORK / output)
            got = image.section(".got")
            base = image.symbol("_GLOBAL_OFFSET_TABLE_")
            slot = image.slot("dv_last")
            written = ldst_offset(image.word(image.symbol("f_gb") + 4))
            x = slot - (base & ~0xFFF)
            row.update({
                "got": [hex(got["address"]), hex(got["address"] + got["size"])],
                "_GLOBAL_OFFSET_TABLE_": hex(base),
                "symbol_offset_in_got": base - got["address"],
                "dv_last_slot": hex(slot),
                "X": x,
                "written": written,
                "class": "links, value right" if written == x else "links, value truncated",
            })
        rows.append(row)
        print(f"verifier shape {linker}: {row['class']}", flush=True)
    return rows


def ifunc_probes() -> list[dict]:
    """LD64_GOTPAGE_LO15 and LD64_GOTOFF_LO15 against an IFUNC (and a data
    word) with the default layout: where each linker puts the IFUNC's GOT slot
    relative to _GLOBAL_OFFSET_TABLE_, and what it writes."""
    source = (
        "\t.text\n\t.globl _start\n\t.type _start, %function\n_start:\n\tadrp x28, _GLOBAL_OFFSET_TABLE_\n"
        "\tldr x0, [x28, #:{kind}:myfunc]\n\tmov x8, #93\n\tsvc #0\n\t.size _start, .-_start\n"
        "\t.globl myfunc\n\t.type myfunc, %gnu_indirect_function\nmyfunc:\n\tadr x0, impl\n\tret\nimpl:\n\tmov x0, #42\n\tret\n"
    )
    rows = []
    for code, kind in ((313, "gotpage_lo15"), (310, "gotoff_lo15")):
        (WORK / f"if{code}.s").write_text(source.format(kind=kind))
        run(["as", "-o", f"if{code}.o", f"if{code}.s"])
        for linker in LINKERS:
            for shape in (["-static", "-no-pie"], ["-static-pie"], ["-shared"]):
                output = f"if{code}_{linker}_{shape[0][1:]}"
                result = link(f"if{code}.o", output, linker, [], shape)
                row = {"code": code, "linker": linker, "shape": " ".join(shape), "exit": result["exit"], "class": result["class"], "first_error": result["first_error"]}
                if result["exit"] == 0:
                    image = Image(WORK / output)
                    base = image.symbol("_GLOBAL_OFFSET_TABLE_")
                    slots = [r[0] for r in image.relocations if r[1] == R_AARCH64_IRELATIVE] or [
                        r[0] for r in image.relocations if r[1] == R_AARCH64_GLOB_DAT and r[2] == "myfunc"
                    ]
                    written = ldst_offset(image.word(image.symbol("_start") + 4))
                    got, gotplt = image.section(".got"), image.section(".got.plt")
                    row.update({
                        "_GLOBAL_OFFSET_TABLE_": base and hex(base),
                        "got": got and hex(got["address"]),
                        "got_plt": gotplt and hex(gotplt["address"]),
                        "ifunc_slot": [hex(s) for s in slots],
                        "written": written,
                    })
                    if base is not None:
                        origin = (base & ~0xFFF) if code == 313 else base
                        implied = origin + written
                        row["addressed"] = hex(implied)
                        row["addressed_section"] = image.section_of(implied)
                        word = image.qword(implied)
                        row["addressed_word"] = None if word is None else hex(word)
                        if implied in slots:
                            row["X"] = implied - origin
                            row["class"] = "links, value right (the IFUNC's relocated slot)"
                        elif len(slots) == 1 and not (0 <= slots[0] - origin <= 32760) and (slots[0] - origin) & 0x7FF8 == written:
                            row["X"] = slots[0] - origin
                            row["class"] = "links, value truncated"
                        else:
                            row["class"] = "links, addresses a word no IRELATIVE or GLOB_DAT names (a statically filled slot)"
                rows.append(row)
                print(f"ifunc {code} {linker} {' '.join(shape)}: {row['class']}", flush=True)
    return rows


def main() -> int:
    versions = {}
    for linker in LINKERS:
        _, text = run(["cc", *LINKERS[linker], "-Wl,--version", "-nostdlib", "-o", "/dev/null"])
        versions[linker] = text.splitlines()[0] if text else ""
    near = near_probes()
    bases = base_probes()
    far = far_probes()
    result = {
        "versions": versions,
        "near": near,
        "base": bases,
        "verifier_shape": verifier_shape(),
        "ifunc": ifunc_probes(),
        "far": far,
    }
    OUT.write_text(json.dumps(result, indent=1) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
