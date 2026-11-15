#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows (path relative to ~/tcg-scratch, bytes, sha256).

A directory's row is its total bytes over every file beneath it and the
SHA-256 of its manifest: one line `<sha256>  <relative path>` per file,
sorted by path, newline-terminated."""
import hashlib
import os
import sys

H = os.path.expanduser('~/tcg-scratch')
FILES = [line.split('\t', 1) for line in sys.stdin.read().splitlines() if line.strip()]


def sha(path):
    digest = hashlib.sha256()
    with open(path, 'rb') as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b''):
            digest.update(chunk)
    return digest.hexdigest()


for rel, what in FILES:
    path = os.path.join(H, rel)
    if os.path.isdir(path):
        rows = []
        total = 0
        for root, _, names in os.walk(path):
            for name in names:
                full = os.path.join(root, name)
                rows.append((os.path.relpath(full, path), sha(full)))
                total += os.path.getsize(full)
        rows.sort()
        manifest = ''.join(f'{digest}  {name}\n' for name, digest in rows)
        print(f'| `{rel}` ({what}) ({len(rows)} files) | {total} | '
              f'`{hashlib.sha256(manifest.encode()).hexdigest()}` (manifest) |')
    else:
        print(f'| `{rel}` ({what}) | {os.path.getsize(path)} | `{sha(path)}` |')
