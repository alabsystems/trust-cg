#!/usr/bin/env python3
"""Apply dedup_frozen_declarations to every trust-ir module EMBEDDED verbatim in a test
source (`const X: &str = r##"; TrustIr text format v1 ... "##;`). Same transformation,
same reason; only the module text inside the raw string changes."""
import re, sys, importlib.util
spec = importlib.util.spec_from_file_location('d', __file__.replace('dedup_inline_modules.py', 'dedup_frozen_declarations.py'))
d = importlib.util.module_from_spec(spec); spec.loader.exec_module(d)
RAW = re.compile(r'(r(#+)")(; TrustIr text format v1\n.*?)("\2)', re.S)
for p in sys.argv[1:]:
    src = open(p, encoding='utf-8', errors='surrogateescape').read()
    total = 0
    def sub(m):
        global total
        new, before, after, dropped = d.dedup(m.group(3)); total += dropped
        return m.group(1) + new + m.group(4)
    out = RAW.sub(sub, src)
    if total:
        open(p, 'w', encoding='utf-8', errors='surrogateescape').write(out)
    print(f'{p}: {len(RAW.findall(src))} embedded module(s), {total} repeated declarations merged')
