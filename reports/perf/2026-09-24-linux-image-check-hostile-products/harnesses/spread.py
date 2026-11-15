#!/usr/bin/env python3
"""For each host ELF64 little-endian image: the extent of its allocated
memory (every PT_LOAD's p_vaddr..p_vaddr+p_memsz and every SHF_ALLOC
section's sh_addr..sh_addr+sh_size). A 4-byte .eh_frame pointer that
resolves inside that memory, searched in spans inside it, takes the
window fast path of eh_wrap_alias when the extent is at most 2^32."""
import struct, sys, collections
rows = []
for path in sys.stdin.read().split('\n'):
    if not path:
        continue
    try:
        with open(path, 'rb') as f:
            head = f.read(64)
            if len(head) < 64 or head[:4] != b'\x7fELF' or head[4] != 2 or head[5] != 1:
                rows.append((path, 'not-elf64le', None)); continue
            e_phoff, e_shoff = struct.unpack_from('<QQ', head, 32)
            e_phentsize, e_phnum, e_shentsize, e_shnum = struct.unpack_from('<HHHH', head, 54)
            spans = []
            f.seek(e_phoff); ph = f.read(e_phentsize * e_phnum)
            for i in range(e_phnum):
                p_type, _, _, vaddr, _, _, memsz, _ = struct.unpack_from('<IIQQQQQQ', ph, i * e_phentsize)
                if p_type == 1 and memsz:
                    spans.append((vaddr, vaddr + memsz))
            if e_shoff and e_shentsize == 64:
                f.seek(e_shoff); first = f.read(64)
                count = e_shnum or (struct.unpack_from('<Q', first, 32)[0] if len(first) == 64 else 0)
                f.seek(e_shoff); sh = f.read(64 * count)
                for i in range(len(sh) // 64):
                    _, sh_type, flags, addr, _, size = struct.unpack_from('<IIQQQQ', sh, 64 * i)
                    if flags & 2 and size:
                        spans.append((addr, addr + size))
            if not spans:
                rows.append((path, 'no-alloc', None)); continue
            lo = min(s[0] for s in spans); hi = max(s[1] for s in spans)
            rows.append((path, 'ok', hi - lo))
    except OSError as e:
        rows.append((path, 'unreadable', None))
kinds = collections.Counter(r[1] for r in rows)
ok = [r for r in rows if r[1] == 'ok']
within = [r for r in ok if r[2] <= 1 << 32]
print('images', len(rows), dict(kinds))
print('allocated extent <= 2^32:', len(within), 'of', len(ok))
for r in sorted(ok, key=lambda r: -r[2])[:5]:
    print('largest extent %#x %s' % (r[2], r[0]))
