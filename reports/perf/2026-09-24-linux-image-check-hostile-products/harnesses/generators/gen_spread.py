#!/usr/bin/env python3
"""ehspans with its executable sections spread 4 GiB + 4 KiB apart: every
FDE describes section 0, so no alias exists and each FDE's search has to
cover every span (the window fast path cannot apply)."""
import struct, sys, os
_lib = open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "mkelf2.py")).read()
exec(_lib[:_lib.index("kind, path, args")])

def ehspread(path, n):
    base = 0x1000_0000
    step = (1 << 32) + 0x1000
    eh_addr = 0x8000_0000
    eh_off = 0x1000
    cie = bytes([0, 0, 0, 0, 1]) + b"zR\0" + bytes([4, 0x78, 30, 1, 0x1b, 0x0c, 31, 0])
    cie += bytes((-len(cie)) % 4)
    cie = struct.pack("<I", len(cie)) + cie
    body = bytearray(cie)
    for i in range(n):
        at = eh_addr + len(body)
        rec = struct.pack("<IiIB", at + 4 - eh_addr, base - (at + 8), 16, 0) + bytes(3)
        body += struct.pack("<I", len(rec)) + rec
    body += bytes(4)
    names = b"\0.text\0.eh_frame\0.shstrtab\0"
    names_off = eh_off + len(body)
    shoff = (names_off + len(names) + 63) // 64 * 64
    count = n + 3
    sec0 = shdr(0, 0, 0, 0, 0, count if count >= 0xff00 else 0, count - 1 if count >= 0xff00 else 0)
    secs = [sec0]
    secs += [shdr(1, SHT_PROGBITS, SHF_ALLOC | SHF_EXECINSTR, base + step * i, 0x40, 16) for i in range(n)]
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

ehspread(sys.argv[1], int(sys.argv[2]))
