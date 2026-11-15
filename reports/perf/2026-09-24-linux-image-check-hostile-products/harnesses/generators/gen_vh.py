#!/usr/bin/env python3
"""gen_vh.py OUT BIG ORDER: ET_EXEC AArch64, no PT_GNU_EH_FRAME, one real FDE,
section order ORDER (comma list: R = the real .eh_frame_hdr, a number = a
zero-filled .eh_frame_hdr placeholder of that many bytes, all naming the same
zeros in a hole). BIG=1 puts the zeros and the section headers past 1 GiB."""
import struct, sys
out, big, order = sys.argv[1], int(sys.argv[2]), sys.argv[3].split(',')
SHT_PROGBITS, SHT_STRTAB, SHF_ALLOC, SHF_EXECINSTR = 1, 3, 2, 4
def ehdr(phnum, shoff, shnum, shstrndx):
    h = b"\x7fELF" + bytes([2, 1, 1, 0]) + bytes(8)
    return h + struct.pack("<HHIQQQIHHHHHH", 2, 183, 1, 0x401000, 64, shoff, 0, 64, 56, phnum, 64, shnum, shstrndx)
def phdr(t, fl, off, va, fs, ms):
    return struct.pack("<IIQQQQQQ", t, fl, off, va, va, fs, ms, 0x1000)
def shdr(name, t, fl, addr, off, size):
    return struct.pack("<IIQQQQIIQQ", name, t, fl, addr, off, size, 0, 0, 8, 0)
def pcrel4(field, target):
    return struct.pack("<I", (target - field) & 0xffffffff)
text, eh, hdr = 0x401000, 0x402000, 0x402800
# .eh_frame: CIE zR (pcrel|sdata4), FDE for text..text+0x20, terminator.
def record(body):
    body = body + bytes((-len(body)) % 4)
    return struct.pack("<I", len(body)) + body
cie = record(bytes([0, 0, 0, 0, 1]) + b"zR\0" + bytes([4, 0x78, 30, 1, 0x1b, 0x0c, 31, 0]))
fde_at = eh + len(cie)
fde_body = struct.pack("<I", fde_at + 4 - eh) + pcrel4(fde_at + 8, text) + struct.pack("<I", 0x20) + b"\0"
frame = cie + record(fde_body) + bytes(4)
table = bytes([1, 0x1b, 0x03, 0x3b]) + pcrel4(hdr + 4, eh) + struct.pack("<I", 1)
table += struct.pack("<I", (text - hdr) & 0xffffffff) + struct.pack("<I", (fde_at - hdr) & 0xffffffff)
zeros_off = (0x4000_1000 if big else 0x4000)
sizes = [int(x, 0) for x in order if x != 'R']
zsize = max(sizes) if sizes else 0
names = b"\0.text\0.eh_frame\0.eh_frame_hdr\0.shstrtab\0"
n_text, n_eh, n_hdr, n_str = 1, 7, 17, 31
names_off = zeros_off + zsize
shoff = (names_off + len(names) + 63) // 64 * 64
secs = [bytes(64), shdr(n_text, SHT_PROGBITS, SHF_ALLOC | SHF_EXECINSTR, text, 0x1000, 0x100),
        shdr(n_eh, SHT_PROGBITS, SHF_ALLOC, eh, 0x2000, len(frame))]
for index, item in enumerate(order):
    if item == 'R':
        secs.append(shdr(n_hdr, SHT_PROGBITS, SHF_ALLOC, hdr, 0x2800, len(table)))
    else:
        secs.append(shdr(n_hdr, SHT_PROGBITS, SHF_ALLOC, 0x10_0000_0000 + (index << 26), zeros_off, int(item, 0)))
secs.append(shdr(n_str, SHT_STRTAB, 0, 0, names_off, len(names)))
phs = [phdr(1, 5, 0, 0x400000, 0x2000, 0x2000), phdr(1, 4, 0x2000, eh, 0x1000, 0x1000)]
with open(out, "wb") as f:
    f.write(ehdr(len(phs), shoff, len(secs), len(secs) - 1))
    f.write(b"".join(phs))
    f.seek(0x1000); f.write(b"\x1f\x20\x03\xd5" * 64)
    f.seek(0x2000); f.write(frame)
    f.seek(0x2800); f.write(table)
    f.seek(names_off); f.write(names)
    f.seek(shoff); f.write(b"".join(secs))
print("bytes", shoff + 64 * len(secs), "order", ",".join(order))
