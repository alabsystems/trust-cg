#!/usr/bin/env python3
"""gen_hdrzeros.py OUT n_headers zero_bytes: ET_EXEC without PT_GNU_EH_FRAME
whose n allocated PROGBITS section headers are all named .eh_frame_hdr and
all name the same zero_bytes zeros (sparse)."""
import struct, sys
_lib = open("/tmp/claude-1000/-home-ayates-trust-cg/5c614a35-bd1c-42d4-a526-64c88f7a04db/scratchpad/mkelf2.py").read()
exec(_lib[:_lib.index("kind, path, args")])
path, n, size = sys.argv[1], int(sys.argv[2]), int(sys.argv[3], 0)
zeros_off = 0x2000
names = b"\0.text\0.eh_frame_hdr\0.shstrtab\0"
names_off = zeros_off + size
shoff = (names_off + len(names) + 63) // 64 * 64
count = n + 3
sec0 = shdr(0, 0, 0, 0, 0, count if count >= 0xff00 else 0, count - 1 if count >= 0xff00 else 0)
secs = [sec0, shdr(1, SHT_PROGBITS, SHF_ALLOC | SHF_EXECINSTR, 0x401000, 0x1000, 0x20)]
secs += [shdr(7, SHT_PROGBITS, SHF_ALLOC, 0x10_0000_0000, zeros_off, size) for _ in range(n)]
secs.append(shdr(21, SHT_STRTAB, 0, 0, names_off, len(names)))
shnum = 0 if count >= 0xff00 else count
shstrndx = 0xffff if count >= 0xff00 else count - 1
with open(path, "wb") as f:
    f.write(ehdr(2, 1, shoff, shnum, shstrndx))
    f.write(phdr(PT_LOAD, 5, 0, 0x400000, 0x2000, 0x2000))
    f.seek(0x1000); f.write(b"\x1f\x20\x03\xd5" * 8)
    f.seek(names_off); f.write(names)
    f.seek(shoff); f.write(b"".join(secs))
print("bytes", shoff + 64 * len(secs), "headers", n, "zeros", size)
