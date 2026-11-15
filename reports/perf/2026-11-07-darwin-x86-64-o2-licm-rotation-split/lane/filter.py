"""filter.py <needle>: stdin -> stdout, dropping x86-peephole[entry] dumps of every function
whose header does not contain needle (all other lines pass through)."""
import sys
needle = sys.argv[1]; keep = False; inpeep = False
for line in sys.stdin:
    if line.startswith('x86-peephole[entry]:'):
        inpeep = True; keep = needle in line
        if keep: sys.stdout.write(line)
        continue
    if inpeep and line.startswith('  '):
        if keep: sys.stdout.write(line)
        continue
    inpeep = False
    sys.stdout.write(line)
