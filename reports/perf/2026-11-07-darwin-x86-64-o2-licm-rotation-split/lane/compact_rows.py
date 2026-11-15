"""compact_rows.py <trace.log> <fn-substring> [occurrence=1]: print the k-th
x86-peephole[entry] dump of a function with compact operand spelling."""
import sys, re
path, needle = sys.argv[1], sys.argv[2]
occ = int(sys.argv[3]) if len(sys.argv) > 3 else 1
lines = open(path).read().split('\n')
starts = [i for i, l in enumerate(lines) if l.startswith('x86-peephole[entry]:') and needle in l]
i = starts[occ - 1]
out = [lines[i]]
for l in lines[i + 1:]:
    if not l.startswith('  '):
        break
    s = l
    s = re.sub(r'VReg\(VReg \{ id: (\d+), class: (\w+) \}\)', lambda m: 'v' + m.group(1) + ('' if m.group(2) == 'Gpr64' else ':' + m.group(2)), s)
    s = re.sub(r'PReg\(X86PReg\(\d+:(\w+)\)\)', r'%\1', s)
    s = re.sub(r'MemAddr \{ base: StackSlot\((\d+)\), disp: (-?\d+) \}', r'[slot\1+\2]', s)
    s = re.sub(r'MemAddr \{ base: (v\d+(?::\w+)?), disp: (-?\d+) \}', r'[\1+\2]', s)
    s = re.sub(r'Imm\((-?\d+)\)', r'#\1', s)
    out.append(s)
print('\n'.join(out))
