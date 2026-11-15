#!/usr/bin/env python3
"""Scan ELF executables and shared objects for non-allocated sections that are placed or writable (2026-09-23).

The L02-P10 second repair counts a non-allocated section as a possible GOT
slot region when it has a nonzero sh_addr or SHF_WRITE. This scan counts,
under each ROOT, the regular (non-symlink) ELF64 little-endian ET_EXEC and
ET_DYN files and lists every such section it finds. It reads section
headers only; it says nothing about images that are not on this host.

Usage: scan-non-allocated-sections-20260923.py ROOT [ROOT ...]
"""

import os
import struct
import sys

SHF_WRITE, SHF_ALLOC = 0x1, 0x2


def scan(path):
    try:
        with open(path, "rb") as handle:
            data = handle.read()
    except OSError:
        return None
    if data[:6] != b"\x7fELF\x02\x01" or struct.unpack_from("<H", data, 16)[0] not in (2, 3):
        return None
    shoff, = struct.unpack_from("<Q", data, 40)
    shentsize, shnum, shstrndx = struct.unpack_from("<HHH", data, 58)
    if shoff == 0 or shnum == 0:
        return "no-section-headers", []
    try:
        names_offset, names_size = struct.unpack_from("<QQ", data, shoff + shstrndx * shentsize + 24)
        names = data[names_offset:names_offset + names_size]
        found = []
        for index in range(shnum):
            name, kind, flags, address, _, size = struct.unpack_from("<IIQQQQ", data, shoff + index * shentsize)
            if not flags & SHF_ALLOC and (address != 0 or flags & SHF_WRITE) and size != 0:
                found.append((names[name:names.index(b"\0", name)].decode(errors="replace"), hex(address),
                              hex(flags), kind))
        return "sections", found
    except (struct.error, ValueError) as error:
        return "unreadable", [str(error)]


def main():
    counts = {"sections": 0, "no-section-headers": 0, "unreadable": 0}
    hits = []
    for root in sys.argv[1:]:
        for directory, _, files in os.walk(root):
            for name in files:
                path = os.path.join(directory, name)
                if os.path.islink(path) or not os.path.isfile(path):
                    continue
                result = scan(path)
                if result is None:
                    continue
                state, found = result
                counts[state] += 1
                if found:
                    hits.append((path, state, found))
    print("roots:", " ".join(sys.argv[1:]))
    print("ELF64 ET_EXEC/ET_DYN images:", sum(counts.values()), counts)
    print("images with a non-allocated section at a nonzero address or with SHF_WRITE:",
          sum(1 for _, state, _ in hits if state == "sections"))
    for path, state, found in hits:
        print(path, state, found)
    return 0


if __name__ == "__main__":
    sys.exit(main())
