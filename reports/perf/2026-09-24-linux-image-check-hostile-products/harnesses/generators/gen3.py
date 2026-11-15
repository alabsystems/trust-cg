#!/usr/bin/env python3
"""Round-3 hostile images (built on mkelf2.py's helpers)."""
import struct, sys, os
_lib = open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "mkelf2.py")).read()
exec(_lib[:_lib.index("kind, path, args")])

GAP = (5 << 28) + 12345  # 1.25 GiB + change: the production sparse path


def names_gap(path, relocs, name_len, dynamics=1, gap=GAP):
    """ET_EXEC, no section headers: `dynamics` PT_DYNAMIC headers naming one
    .dynamic whose DT_JMPREL holds `relocs` JUMP_SLOT relocations against
    symbol 1 (a `name_len`-byte name), plus a far PT_LOAD `gap` bytes into
    the file (a sparse hole), so the file is read piecewise."""
    phnum = dynamics + 2
    base = (64 + 56 * phnum + 0xfff) // 0x1000 * 0x1000
    strtab = b"\0" + b"A" * name_len + b"\0"
    symtab = bytes(24) + struct.pack("<IBBHQQ", 1, 0x12, 0, 0, 0, 0)
    one = struct.pack("<QQq", 0x400000 + base, (1 << 32) | R_JUMP_SLOT, 0)
    str_off = base
    sym_off = (str_off + len(strtab) + 15) // 16 * 16
    rela_off = sym_off + len(symtab)
    rela_len = 24 * relocs
    dyn_off = (rela_off + rela_len + 15) // 16 * 16
    va = lambda off: 0x400000 + off
    dynamic = dyn([(DT_STRTAB, va(str_off)), (DT_STRSZ, len(strtab)), (DT_SYMTAB, va(sym_off)),
                   (DT_SYMENT, 24), (DT_JMPREL, va(rela_off)), (DT_PLTRELSZ, rela_len),
                   (DT_PLTREL, DT_RELA), (DT_NULL, 0)])
    length = dyn_off + len(dynamic)
    far_off = length + gap
    phs = [phdr(PT_LOAD, 6, 0, 0x400000, length, length)]
    phs += [phdr(PT_DYNAMIC, 6, dyn_off, va(dyn_off), len(dynamic), len(dynamic))] * dynamics
    phs += [phdr(PT_LOAD, 5, far_off, 0x40_0000_0000, 0x40, 0x40)]
    with open(path, "wb") as f:
        f.write(ehdr(2, phnum, 0, 0, 0))
        f.write(b"".join(phs))
        f.seek(str_off); f.write(strtab)
        f.seek(sym_off); f.write(symtab)
        f.seek(rela_off)
        chunk = one * 65536
        left = relocs
        while left:
            n = min(left, 65536)
            f.write(chunk if n == 65536 else one * n)
            left -= n
        f.seek(dyn_off); f.write(dynamic)
        f.seek(far_off); f.write(b"\x1f\x20\x03\xd5" * 16)
    print("bytes", far_off + 64, "names", relocs * name_len)


def relanone1(path, entries, gap=0):
    """ET_EXEC: one allocated SHT_RELA of `entries` R_AARCH64_NONE entries
    (a hole of zeros), optionally with a far hole after it."""
    table_off = 0x10000
    table_len = 24 * entries
    names = b"\0.text\0.rela.x\0.shstrtab\0"
    names_off = table_off + table_len + gap
    shoff = (names_off + len(names) + 63) // 64 * 64
    secs = [bytes(64), shdr(1, SHT_PROGBITS, SHF_ALLOC | SHF_EXECINSTR, 0x401000, 0x1000, 0x40),
            shdr(7, SHT_RELA, SHF_ALLOC, 0x500000, table_off, table_len, 0, 24),
            shdr(15, SHT_STRTAB, 0, 0, names_off, len(names))]
    with open(path, "wb") as f:
        f.write(ehdr(2, 1, shoff, len(secs), len(secs) - 1))
        f.write(phdr(PT_LOAD, 5, 0, 0x400000, 0x2000, 0x2000))
        f.seek(0x1000); f.write(b"\x1f\x20\x03\xd5" * 16)
        f.seek(names_off); f.write(names)
        f.seek(shoff); f.write(b"".join(secs))
    print("bytes", shoff + 64 * len(secs), "entries", entries)


def strscan(path, symbols, strtab_len):
    """ET_EXEC with a .symtab of `symbols` defined entries, each named at
    offset 0 of a `strtab_len`-byte .strtab that holds no NUL byte."""
    SHT_SYMTAB = 2
    text_off = 0x1000
    str_off = 0x2000
    sym_off = (str_off + strtab_len + 63) // 64 * 64
    sym = struct.pack("<IBBHQQ", 0, 0x12, 0, 1, 0x401000, 4)
    names = b"\0.text\0.strtab\0.symtab\0.shstrtab\0"
    idx = lambda n: names.index(n.encode() + b"\0")
    names_off = sym_off + 24 * (symbols + 1)
    shoff = (names_off + len(names) + 63) // 64 * 64
    secs = [bytes(64),
            shdr(idx(".text"), SHT_PROGBITS, SHF_ALLOC | SHF_EXECINSTR, 0x401000, text_off, 0x40),
            shdr(idx(".strtab"), SHT_STRTAB, 0, 0, str_off, strtab_len),
            shdr(idx(".symtab"), SHT_SYMTAB, 0, 0, sym_off, 24 * (symbols + 1), 2, 24),
            shdr(idx(".shstrtab"), SHT_STRTAB, 0, 0, names_off, len(names))]
    with open(path, "wb") as f:
        f.write(ehdr(2, 1, shoff, len(secs), len(secs) - 1))
        f.write(phdr(PT_LOAD, 5, 0, 0x400000, 0x2000, 0x2000))
        f.seek(text_off); f.write(b"\x1f\x20\x03\xd5" * 16)
        f.seek(str_off)
        block = b"A" * (1 << 20)
        left = strtab_len
        while left:
            n = min(left, 1 << 20)
            f.write(block[:n]); left -= n
        f.seek(sym_off); f.write(bytes(24) + sym * symbols)
        f.seek(names_off); f.write(names)
        f.seek(shoff); f.write(b"".join(secs))
    print("bytes", shoff + 64 * len(secs), "scan bytes", symbols * strtab_len)


def ehspans(path, n):
    """ET_EXEC with `n` 16-byte executable sections 32 bytes apart (no PF_X
    PT_LOAD, so they stay `n` spans) and an .eh_frame of one zR CIE and `n`
    FDEs, one per section: every FDE's alias search walks every span."""
    import array
    base = 0x1000_0000
    eh_addr = 0x8000_0000
    eh_off = 0x1000
    cie = bytes([0, 0, 0, 0, 1]) + b"zR\0" + bytes([4, 0x78, 30, 1, 0x1b, 0x0c, 31, 0])
    cie += bytes((-len(cie)) % 4)
    cie = struct.pack("<I", len(cie)) + cie
    body = bytearray(cie)
    for i in range(n):
        at = eh_addr + len(body)
        field = at + 8
        target = base + 32 * i
        body += struct.pack("<IIiIB", 17, at + 4 - eh_addr, (target - field), 16, 0)
        body += bytes((-len(body)) % 4)
    # fix lengths: each record is 4 + 17 -> padded to 4+20
    body = bytearray(cie)
    for i in range(n):
        at = eh_addr + len(body)
        field = at + 8
        target = base + 32 * i
        rec = struct.pack("<IiIB", at + 4 - eh_addr, (target - field), 16, 0) + bytes(3)
        body += struct.pack("<I", len(rec)) + rec
    body += bytes(4)
    names = b"\0.text\0.eh_frame\0.shstrtab\0"
    names_off = eh_off + len(body)
    shoff = (names_off + len(names) + 63) // 64 * 64
    count = n + 3
    sec0 = shdr(0, 0, 0, 0, 0, count if count >= 0xff00 else 0, count - 1 if count >= 0xff00 else 0)
    secs = [sec0]
    text = [shdr(1, SHT_PROGBITS, SHF_ALLOC | SHF_EXECINSTR, base + 32 * i, 0x40, 16) for i in range(n)]
    secs += text
    secs.append(shdr(7, SHT_PROGBITS, SHF_ALLOC, eh_addr, eh_off, len(body)))
    secs.append(shdr(17, SHT_STRTAB, 0, 0, names_off, len(names)))
    shnum = 0 if count >= 0xff00 else count
    shstrndx = 0xffff if count >= 0xff00 else count - 1
    with open(path, "wb") as f:
        f.write(ehdr(2, 1, shoff, shnum, shstrndx))
        f.write(phdr(PT_LOAD, 4, 0, 0x400000, 0x1000, 0x1000))
        f.seek(eh_off); f.write(body)
        f.seek(names_off); f.write(names)
        f.seek(shoff); f.write(b"".join(secs))
    print("bytes", shoff + 64 * len(secs), "sections", n, "fdes", n)


def ehgroups(path, n):
    """ET_DYN, PT_GNU_EH_FRAME: `n` pcs each begun by two FDEs (16 bytes and
    zero bytes), and a sorted .eh_frame_hdr table with one entry per pc
    naming the wide FDE: each group's table lookup scans the table."""
    PT_GNU_EH_FRAME = 0x6474E550
    text = 0x4000_0000
    hdr_addr = 0x1000
    table_len = 12 + 8 * n
    eh_addr = (hdr_addr + table_len + 15) // 16 * 16
    cie = bytes([0, 0, 0, 0, 1]) + b"zR\0" + bytes([4, 0x78, 30, 1, 0x1b, 0x0c, 31, 0])
    cie += bytes((-len(cie)) % 4)
    cie = struct.pack("<I", len(cie)) + cie
    body = bytearray(cie)
    wide = []
    for i in range(n):
        pc = text + 16 * i
        for rng in (16, 0):
            at = eh_addr + len(body)
            rec = struct.pack("<IiIB", at + 4 - eh_addr, pc - (at + 8), rng, 0) + bytes(3)
            if rng:
                wide.append((pc, at))
            body += struct.pack("<I", len(rec)) + rec
    body += bytes(4)
    hdr = bytearray([1, 0x1b, 0x03, 0x3b])
    hdr += struct.pack("<i", eh_addr - (hdr_addr + 4))
    hdr += struct.pack("<I", n)
    for pc, fde in wide:
        hdr += struct.pack("<ii", pc - hdr_addr, fde - hdr_addr)
    names = b"\0.text\0.eh_frame\0.eh_frame_hdr\0.shstrtab\0"
    idx = lambda s: names.index(s.encode() + b"\0")
    names_off = eh_addr + len(body)
    shoff = (names_off + len(names) + 63) // 64 * 64
    end = shoff + 64 * 5
    secs = [bytes(64),
            shdr(idx(".text"), SHT_PROGBITS, SHF_ALLOC | SHF_EXECINSTR, text, 0x40, 16 * n),
            shdr(idx(".eh_frame_hdr"), SHT_PROGBITS, SHF_ALLOC, hdr_addr, hdr_addr, len(hdr)),
            shdr(idx(".eh_frame"), SHT_PROGBITS, SHF_ALLOC, eh_addr, eh_addr, len(body)),
            shdr(idx(".shstrtab"), SHT_STRTAB, 0, 0, names_off, len(names))]
    phs = [phdr(PT_LOAD, 4, 0, 0, end, end),
           phdr(PT_LOAD, 5, 0x40, text, 0, 16 * n),
           phdr(PT_GNU_EH_FRAME, 4, hdr_addr, hdr_addr, len(hdr), len(hdr))]
    with open(path, "wb") as f:
        f.write(ehdr(3, len(phs), shoff, len(secs), len(secs) - 1))
        f.write(b"".join(phs))
        f.seek(hdr_addr); f.write(hdr)
        f.seek(eh_addr); f.write(body)
        f.seek(names_off); f.write(names)
        f.seek(shoff); f.write(b"".join(secs))
    print("bytes", end, "groups", n, "fdes", 2 * n)


kind, path, args = sys.argv[1], sys.argv[2], [int(a) for a in sys.argv[3:]]
{"names_gap": names_gap, "relanone1": relanone1, "jumpslots": jumpslots,
 "relanone": relanone, "pltfar": pltfar, "strscan": strscan, "ehspans": ehspans, "ehgroups": ehgroups}[kind](path, *args)
