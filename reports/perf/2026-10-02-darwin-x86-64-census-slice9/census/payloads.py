#!/usr/bin/env python3
"""SHA-256 of each slice-9 payload (a file, or for a directory the SHA-256 of
its sorted `<sha256>  <relative path>` listing) as Markdown table rows."""
import hashlib
import os
import sys

H = os.path.expanduser('~')


def file_hash(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def tree_hash(path):
    lines = []
    count = 0
    for root, _, files in os.walk(path):
        for name in files:
            full = os.path.join(root, name)
            lines.append(f'{file_hash(full)}  {os.path.relpath(full, path)}')
            count += 1
    lines.sort()
    return hashlib.sha256('\n'.join(lines).encode()).hexdigest(), count


for arg in sys.argv[1:]:
    path, _, what = arg.partition('=')
    shown = path.replace(H, '~')
    if os.path.isdir(path):
        digest, count = tree_hash(path)
        print(f'| `{shown}/` ({count} files, listing digest) | `{digest}` | {what} |')
    elif os.path.exists(path):
        print(f'| `{shown}` | `{file_hash(path)}` | {what} |')
    else:
        print(f'| `{shown}` | MISSING | {what} |')
