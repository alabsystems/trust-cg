#!/usr/bin/env python3
"""Merge repeated extern DECLARATIONS in a frozen `--mir-emit-closure` trust-ir text
fixture, exactly as trust-ir's fixed frontend now emits them (trust-ir d8f5a279,
`ClosureWiring::shared_externs`: one 0-block declaration per link-time symbol across the
whole closure; every later member reuses the first member's declaration).

Why this exists: since binary v41 `Function::name` is the link-time symbol and
`validate_module` refuses a repeated one (`DuplicateFunctionSymbol`). The frozen kernel
fixtures were emitted by an earlier frontend that re-declared each extern once per
closure member (twelve `drop_glue<Expr>` declarations in one module). They cannot be
byte re-minted: the compiler they were minted against (`fixture_toolchain.rs`) is not
available, and a fresh emit by today's frontend is a different generation whose ABI the
tests' hand-written shims do not bind (measured 2026-09-15: fresh re-mint -> 7 of 8
`e2e_defeq_cache` tests fail at the shim binding; this transformation -> 8 of 8 pass).

What it does, and nothing else: keeps every function DEFINITION and the FIRST declaration
of each symbol, drops later 0-block declarations of an already-declared symbol, and
renumbers every `@func.N` reference. Bodies, types, functy table and all other rows are
untouched byte-for-byte. Idempotent. Usage:
    dedup_frozen_declarations.py FIXTURE.tir [FIXTURE.tir ...]     (in place)
    dedup_frozen_declarations.py --check FIXTURE.tir ...             (exit 1 if any repeat)
"""
import re, sys

FN_RE = re.compile(r'^fn @([^(]+)\(')

def dedup(text):
    lines = text.split('\n')
    fns = []  # (start, end, name, is_decl)
    i = 0
    while i < len(lines):
        m = FN_RE.match(lines[i])
        if not m:
            i += 1
            continue
        j = i + 1
        while j < len(lines) and not FN_RE.match(lines[j]):
            j += 1
        body = lines[i + 1:j]
        first = next((l for l in body if l.strip()), '')
        is_decl = first.strip() == '}' and not any(l.startswith('bb') for l in body)
        fns.append((i, j, m.group(1), is_decl))
        i = j
    first_by_name, remap, keep, dropped = {}, {}, set(), 0
    new_index = 0
    for idx, (_, _, name, is_decl) in enumerate(fns):
        prev = first_by_name.get(name)
        if is_decl and prev is not None and fns[prev][3]:
            remap[idx] = remap[prev]
            dropped += 1
            continue
        if prev is None:
            first_by_name[name] = idx
        remap[idx] = new_index
        new_index += 1
        keep.add(idx)
    out, last = [], 0
    for idx, (s, e, _, _) in enumerate(fns):
        out.extend(lines[last:s])
        if idx in keep:
            out.extend(lines[s:e])
        last = e
    out.extend(lines[last:])
    text = '\n'.join(out)
    text = re.sub(r'@func\.(\d+)', lambda m: '@func.%d' % remap[int(m.group(1))], text)
    return text, len(fns), new_index, dropped

def main(argv):
    check = argv and argv[0] == '--check'
    paths = argv[1:] if check else argv
    bad = 0
    for p in paths:
        raw = open(p, 'rb').read().decode('utf-8', 'surrogateescape')
        new, before, after, dropped = dedup(raw)
        if check:
            if dropped:
                print(f'{p}: {dropped} repeated declaration(s)'); bad += 1
            continue
        if dropped:
            open(p, 'wb').write(new.encode('utf-8', 'surrogateescape'))
        print(f'{p}: {before} fn rows -> {after} ({dropped} repeated declarations merged)')
    return 1 if bad else 0

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
