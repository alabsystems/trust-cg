#!/usr/bin/env python3
"""Second-round read-back probes: ELF64 AArch64 images for the caps and
PT_DYNAMIC duplication."""
import struct, sys

PT_LOAD, PT_DYNAMIC = 1, 2
SHT_PROGBITS, SHT_STRTAB, SHT_RELA, SHT_DYNAMIC, SHT_RELR = 1, 3, 4, 6, 19
SHF_WRITE, SHF_ALLOC, SHF_EXECINSTR = 1, 2, 4
R_JUMP_SLOT, R_RELATIVE = 1026, 1027
DT_NULL, DT_PLTRELSZ, DT_PLTGOT, DT_STRTAB, DT_SYMTAB, DT_RELA = 0, 2, 3, 5, 6, 7
DT_STRSZ, DT_SYMENT, DT_PLTREL, DT_DEBUG, DT_JMPREL = 10, 11, 20, 21, 23
DT_RELRSZ, DT_RELR, DT_RELRENT = 35, 36, 37


def ehdr(e_type, phnum, shoff, shnum, shstrndx):
    h = b"\x7fELF" + bytes([2, 1, 1, 0]) + bytes(8)
    h += struct.pack("<HHIQQQIHHHHHH", e_type, 183, 1, 0x400000, 64 if phnum else 0,
                     shoff, 0, 64, 56, phnum, 64, shnum, shstrndx)
    return h


def phdr(t, fl, off, va, fs, ms):
    return struct.pack("<IIQQQQQQ", t, fl, off, va, va, fs, ms, 0x1000)


def shdr(name, t, fl, addr, off, size, link=0, ent=0):
    return struct.pack("<IIQQQQIIQQ", name, t, fl, addr, off, size, link, 0, 8, ent)


def dyn(entries):
    return b"".join(struct.pack("<QQ", t, v) for t, v in entries)


def pltfar(path, words):
    """ET_EXEC with a PLT (.plt at 0x401000, R_AARCH64_JUMP_SLOT slot in
    .got.plt 8 GiB away) and a packed .relr.dyn of one address and `words`
    all-ones bitmaps (63 targets each): 1 + 63 * words targets. No .eh_frame."""
    got = 0x2_0040_2000
    rw_off = 0x2000
    dyn_off, rela_off, relr_off = 0x2100, 0x2400, 0x3000
    relr = struct.pack("<Q", got + 0x10_0000) + struct.pack("<Q", (1 << 64) - 1) * words
    end = relr_off + len(relr)
    dynamic = dyn([(DT_JMPREL, got + (rela_off - rw_off)), (DT_PLTRELSZ, 24), (DT_PLTREL, DT_RELA),
                   (DT_PLTGOT, got), (DT_RELR, got + (relr_off - rw_off)),
                   (DT_RELRSZ, len(relr)), (DT_RELRENT, 8), (DT_NULL, 0)])
    names = b"\0.plt\0.got.plt\0.dynamic\0.rela.plt\0.relr.dyn\0.shstrtab\0"
    idx = lambda n: names.index(n.encode() + b"\0")
    names_off = (end + 15) // 16 * 16
    shoff = (names_off + len(names) + 63) // 64 * 64
    rw_size = end - rw_off
    secs = [bytes(64),
            shdr(idx(".plt"), SHT_PROGBITS, SHF_ALLOC | SHF_EXECINSTR, 0x401000, 0x1000, 0x20),
            shdr(idx(".got.plt"), SHT_PROGBITS, SHF_ALLOC | SHF_WRITE, got, rw_off, 0x20),
            shdr(idx(".dynamic"), SHT_DYNAMIC, SHF_ALLOC | SHF_WRITE, got + 0x100, dyn_off, len(dynamic), 0, 16),
            shdr(idx(".rela.plt"), SHT_RELA, SHF_ALLOC, got + 0x400, rela_off, 24, 0, 24),
            shdr(idx(".relr.dyn"), SHT_RELR, SHF_ALLOC, got + 0x1000, relr_off, len(relr), 0, 8),
            shdr(idx(".shstrtab"), SHT_STRTAB, 0, 0, names_off, len(names))]
    phs = [phdr(PT_LOAD, 5, 0, 0x400000, 0x2000, 0x2000),
           phdr(PT_LOAD, 6, rw_off, got, rw_size, rw_size + 0x4000_0000),
           phdr(PT_DYNAMIC, 6, dyn_off, got + 0x100, len(dynamic), len(dynamic))]
    buf = bytearray(shoff + 64 * len(secs))
    buf[0:64] = ehdr(2, len(phs), shoff, len(secs), len(secs) - 1)
    buf[64:64 + 56 * len(phs)] = b"".join(phs)
    buf[0x1000:0x1020] = b"\x1f\x20\x03\xd5" * 8
    buf[dyn_off:dyn_off + len(dynamic)] = dynamic
    buf[rela_off:rela_off + 24] = struct.pack("<QQq", got + 0x18, R_JUMP_SLOT, 0)
    buf[relr_off:end] = relr
    buf[names_off:names_off + len(names)] = names
    buf[shoff:] = b"".join(secs)
    open(path, "wb").write(buf)
    print("targets", 1 + 63 * words, "bytes", len(buf))


def dyndup_tags(path, copies, entries):
    """ET_EXEC, no section headers: `copies` PT_DYNAMIC headers naming one
    .dynamic of `entries` DT_DEBUG tags and no DT_NULL."""
    phnum = copies + 1
    dyn_off = (64 + 56 * phnum + 0xfff) // 0x1000 * 0x1000
    dynamic = dyn([(DT_DEBUG, 0)] * entries)
    length = dyn_off + len(dynamic)
    phs = [phdr(PT_LOAD, 4, 0, 0x400000, length, length)]
    phs += [phdr(PT_DYNAMIC, 6, dyn_off, 0x400000 + dyn_off, len(dynamic), len(dynamic))] * copies
    with open(path, "wb") as f:
        f.write(ehdr(2, phnum, 0, 0, 0))
        f.write(b"".join(phs))
        f.seek(dyn_off)
        f.write(dynamic)
    print("bytes", length)


def dyndup_names(path, copies, relocs, name_len):
    """ET_EXEC, no section headers: `copies` PT_DYNAMIC headers naming one
    .dynamic whose DT_JMPREL holds `relocs` R_AARCH64_JUMP_SLOT relocations
    against symbol 1, named with `name_len` bytes."""
    phnum = copies + 1
    base = (64 + 56 * phnum + 0xfff) // 0x1000 * 0x1000
    strtab = b"\0" + b"A" * name_len + b"\0"
    symtab = bytes(24) + struct.pack("<IBBHQQ", 1, 0x12, 0, 0, 0, 0)
    rela = struct.pack("<QQq", 0x400000 + base, (1 << 32) | R_JUMP_SLOT, 0) * relocs
    str_off = base
    sym_off = (str_off + len(strtab) + 15) // 16 * 16
    rela_off = sym_off + len(symtab)
    dyn_off = (rela_off + len(rela) + 15) // 16 * 16
    va = lambda off: 0x400000 + off
    dynamic = dyn([(DT_STRTAB, va(str_off)), (DT_STRSZ, len(strtab)), (DT_SYMTAB, va(sym_off)),
                   (DT_SYMENT, 24), (DT_JMPREL, va(rela_off)), (DT_PLTRELSZ, len(rela)),
                   (DT_PLTREL, DT_RELA), (DT_NULL, 0)])
    length = dyn_off + len(dynamic)
    phs = [phdr(PT_LOAD, 6, 0, 0x400000, length, length)]
    phs += [phdr(PT_DYNAMIC, 6, dyn_off, va(dyn_off), len(dynamic), len(dynamic))] * copies
    with open(path, "wb") as f:
        f.write(ehdr(2, phnum, 0, 0, 0))
        f.write(b"".join(phs))
        f.seek(str_off); f.write(strtab)
        f.seek(sym_off); f.write(symtab)
        f.seek(rela_off); f.write(rela)
        f.seek(dyn_off); f.write(dynamic)
    print("bytes", length, "names per segment", relocs * name_len, "total", copies * relocs * name_len)


def relanone(path, headers, entries):
    """ET_EXEC: `headers` allocated SHT_RELA section headers, each at a
    distinct offset 24 bytes apart, each `entries` Elf64_Rela long, over a
    table of zeros (R_AARCH64_NONE, which the check skips uncounted)."""
    table_off = 0x10000
    table_len = 24 * (entries + headers)
    names = b"\0.text\0.rela.x\0.shstrtab\0"
    names_off = table_off + table_len
    shoff = (names_off + len(names) + 63) // 64 * 64
    secs = [bytes(64), shdr(1, SHT_PROGBITS, SHF_ALLOC | SHF_EXECINSTR, 0x401000, 0x1000, 0x40)]
    secs += [shdr(7, SHT_RELA, SHF_ALLOC, 0x500000, table_off + 24 * k, 24 * entries, 0, 24)
             for k in range(headers)]
    secs.append(shdr(15, SHT_STRTAB, 0, 0, names_off, len(names)))
    with open(path, "wb") as f:
        f.write(ehdr(2, 1, shoff, len(secs), len(secs) - 1))
        f.write(phdr(PT_LOAD, 5, 0, 0x400000, 0x2000, 0x2000))
        f.seek(0x1000); f.write(b"\x1f\x20\x03\xd5" * 16)
        f.seek(names_off); f.write(names)
        f.seek(shoff); f.write(b"".join(secs))
    print("bytes", shoff + 64 * len(secs), "iterations", headers * entries)


def jumpslots(path, slots):
    """ET_EXEC with .plt at 0x401000 and `slots` R_AARCH64_JUMP_SLOT slots
    in .got.plt 8 GiB away: the PLT refusal compares every slot with every
    slot."""
    got = 0x2_0040_2000
    rw_off = 0x2000
    got_size = 24 + 8 * slots
    dyn_off = rw_off + (got_size + 15) // 16 * 16
    rela_off = dyn_off + 0x100
    rela = b"".join(struct.pack("<QQq", got + 24 + 8 * i, R_JUMP_SLOT, 0) for i in range(slots))
    end = rela_off + len(rela)
    va = lambda off: got + (off - rw_off)
    dynamic = dyn([(DT_JMPREL, va(rela_off)), (DT_PLTRELSZ, len(rela)), (DT_PLTREL, DT_RELA),
                   (DT_PLTGOT, got), (DT_NULL, 0)])
    names = b"\0.plt\0.got.plt\0.dynamic\0.shstrtab\0"
    idx = lambda n: names.index(n.encode() + b"\0")
    names_off = (end + 15) // 16 * 16
    shoff = (names_off + len(names) + 63) // 64 * 64
    secs = [bytes(64),
            shdr(idx(".plt"), SHT_PROGBITS, SHF_ALLOC | SHF_EXECINSTR, 0x401000, 0x1000, 0x20),
            shdr(idx(".got.plt"), SHT_PROGBITS, SHF_ALLOC | SHF_WRITE, got, rw_off, got_size),
            shdr(idx(".dynamic"), SHT_DYNAMIC, SHF_ALLOC | SHF_WRITE, va(dyn_off), dyn_off, len(dynamic), 0, 16),
            shdr(idx(".shstrtab"), SHT_STRTAB, 0, 0, names_off, len(names))]
    phs = [phdr(PT_LOAD, 5, 0, 0x400000, 0x2000, 0x2000),
           phdr(PT_LOAD, 6, rw_off, got, end - rw_off, end - rw_off),
           phdr(PT_DYNAMIC, 6, dyn_off, va(dyn_off), len(dynamic), len(dynamic))]
    buf = bytearray(shoff + 64 * len(secs))
    buf[0:64] = ehdr(2, len(phs), shoff, len(secs), len(secs) - 1)
    buf[64:64 + 56 * len(phs)] = b"".join(phs)
    buf[0x1000:0x1020] = b"\x1f\x20\x03\xd5" * 8
    buf[dyn_off:dyn_off + len(dynamic)] = dynamic
    buf[rela_off:end] = rela
    buf[names_off:names_off + len(names)] = names
    buf[shoff:] = b"".join(secs)
    open(path, "wb").write(buf)
    print("bytes", len(buf))


kind, path, args = sys.argv[1], sys.argv[2], [int(a) for a in sys.argv[3:]]
{"pltfar": pltfar, "dyndup-tags": dyndup_tags, "dyndup-names": dyndup_names,
 "relanone": relanone, "jumpslots": jumpslots}[kind](path, *args)
