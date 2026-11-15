#!/usr/bin/env python3
"""Histogram of the stack-slot scan's named rows (slice 25.0) in a Darwin core
census: for each function whose last [TCG-X86-BODY-TRACE] line is the scan's
refusal, the first offending row the refusal names (`block B row r, Op with
operands [..] (n such rows)`), parsed from its Debug operands into opcode,
where the slot appears, base kind, index kind, scale, displacement and the
other operands' kinds; whether the refusal is stated over a merged-chain
quotient (the OverQuotient suffix, OD-226); and how many failed roots name the
function.

Index constant-ness at O2. The census payloads carry no defining row of the
index register: the trace names one row, a refused body dumps no query
(x86-body-dump writes only the query of a built theorem; the script checks
the dump directory), and the failed-root and typed-refusal records carry only
the emitted opcode inventory. So every register index is "undecided" at O2;
only an index that is itself an immediate would be decided. As a separate,
labelled cross-reference (not O2 evidence), the O0 object of the same
function is read by the slice-25 design's o0_sib_sites.py (a heuristic over
O0 disassembly: the last definition of an O0 `lea (b,i,s)` index register is
a `mov $k` or a zeroing `xor`), whose JSON this script reads when given.

usage: s_histogram.py <census dir> <dump dir> <out.md> <out.tsv> [<o0 sites json>]
"""
import collections
import json
import os
import re
import sys

run, dump, out_md, out_tsv = sys.argv[1:5]
o0_path = sys.argv[5] if len(sys.argv) > 5 else None

PAT = re.compile(r'^\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)$')
S_PREFIX = 'a row that references a stack slot outside a modelled `[slot + disp]` operand'
# The slice-25 production text names the scaled-index base after `operand`;
# the S25.0 diagnostic's did not, and both match.
DETAIL = re.compile(
    re.escape(S_PREFIX)
    + r'(?: or scaled-index base)?: block Block\((?P<block>\d+)\) row (?P<row>\d+|\(not laid out\) index \d+), '
    r'(?P<op>\w+) with operands (?P<operands>\[.*?\]) \((?P<count>\d+) such rows?\)'
    r'(?P<rest>.*)$')
QUOTIENT = ' (over the merged-chain quotient: chains '
FN_IN_MSG = re.compile(r'non_verified proof entry \S+ in (\S+?): ')


# ---- a parser for Rust's derived Debug text --------------------------------
TOKEN = re.compile(r'\s*(?:(?P<str>"(?:[^"\\]|\\.)*")|(?P<num>-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?)'
                   r'|(?P<id>-?[A-Za-z_][A-Za-z0-9_]*)|(?P<p>[{}()\[\],:]))')


def tokens(text):
    # X86PReg's Debug is `X86PReg(4:rsp)`; read it as the tuple `X86PReg("rsp")`.
    text = re.sub(r'X86PReg\((\d+):(\w+)\)', r'X86PReg("\2")', text)
    pos, out = 0, []
    while pos < len(text):
        if text[pos:].strip() == '':
            break
        m = TOKEN.match(text, pos)
        if not m:
            raise ValueError(f'cannot tokenize at {text[pos:pos + 40]!r}')
        pos = m.end()
        kind = m.lastgroup
        out.append((kind, m.group(kind)))
    return out


class Parser:
    def __init__(self, text):
        self.t = tokens(text)
        self.i = 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else (None, None)

    def take(self, want=None):
        tok = self.peek()
        if want is not None and tok[1] != want:
            raise ValueError(f'expected {want!r}, got {tok!r}')
        self.i += 1
        return tok

    def value(self):
        kind, text = self.take()
        if kind == 'str':
            return json.loads(text)
        if kind == 'num':
            return float(text) if any(c in text for c in '.eE') else int(text)
        if text == '[':
            items = []
            while self.peek()[1] != ']':
                items.append(self.value())
                if self.peek()[1] == ',':
                    self.take(',')
            self.take(']')
            return items
        if kind == 'id':
            nxt = self.peek()[1]
            if nxt == '{':
                self.take('{')
                node = {'_': text}
                while self.peek()[1] != '}':
                    name = self.take()[1]
                    self.take(':')
                    node[name] = self.value()
                    if self.peek()[1] == ',':
                        self.take(',')
                self.take('}')
                return node
            if nxt == '(':
                self.take('(')
                node = {'_': text}
                n = 0
                while self.peek()[1] != ')':
                    node[str(n)] = self.value()
                    n += 1
                    if self.peek()[1] == ',':
                        self.take(',')
                self.take(')')
                return node
            return text
        raise ValueError(f'unexpected token {text!r}')


def parse(text):
    p = Parser(text)
    v = p.value()
    if p.i != len(p.t):
        raise ValueError('trailing tokens')
    return v


def kind(op):
    """`VReg:Gpr64`, `PReg:rsp`, `StackSlot`, `Imm`, ... of one operand."""
    if not isinstance(op, dict):
        return repr(op)
    name = op['_']
    if name == 'VReg':
        return f"VReg:{op['0']['class']}"
    if name == 'PReg':
        return f"PReg:{op['0']['0']}"
    return name


def mentions_slot(op):
    if not isinstance(op, dict):
        return False
    if op['_'] == 'StackSlot':
        return True
    return any(mentions_slot(v) for k, v in op.items() if k != '_')


def slot_position(op):
    if op['_'] == 'StackSlot':
        return 'bare StackSlot operand'
    if op['_'] == 'MemAddr':
        return 'MemAddr base' if mentions_slot(op['base']) else 'MemAddr (nested)'
    if op['_'] == 'SibMemAddr':
        where = [w for w in ('base', 'index') if mentions_slot(op[w])]
        return 'SIB ' + '+'.join(where)
    return f"{op['_']} (nested)"


# ---- the census -------------------------------------------------------------
last, any_merged = {}, set()
for line in open(f'{run}/stderr.log', errors='replace'):
    m = PAT.match(line.rstrip('\n'))
    if m:
        last[m.group(1)] = m.group(2)
        if m.group(2).startswith('merged chains='):
            any_merged.add(m.group(1))
roots_of = collections.defaultdict(list)
inventory = {}
INV = re.compile(r'uncovered non-pseudo opcode\(s\) across \d+ distinct opcode\(s\) \[([^\]]*)\]')
for line in open(f'{run}/failed_roots.jsonl'):
    if line.strip():
        r = json.loads(line)
        m = FN_IN_MSG.search(r.get('message', ''))
        if m:
            roots_of[m.group(1)].append(r['symbol'])
            inv = INV.search(r.get('message', ''))
            if inv:
                inventory[m.group(1)] = sorted(
                    x.strip().replace('x86_64::', '') for x in inv.group(1).split(','))
dumped = set(os.listdir(dump)) if os.path.isdir(dump) else set()
o0 = json.load(open(o0_path)) if o0_path else None


def dump_name(fn):
    return fn.replace('.', '-') + '.smt2'


rows, unparsed = [], []
for fn, text in sorted(last.items()):
    if S_PREFIX not in text:
        continue
    m = DETAIL.search(text)
    if not m:
        unparsed.append((fn, 'no detail', text[:300]))
        continue
    try:
        operands = parse(m.group('operands'))
    except ValueError as e:
        unparsed.append((fn, f'operands: {e}', m.group('operands')[:300]))
        continue
    slot_ops = [o for o in operands if mentions_slot(o)]
    mem = next((o for o in operands if isinstance(o, dict) and o['_'] in ('SibMemAddr', 'MemAddr')), None)
    others = [kind(o) for o in operands if o is not mem]
    rec = {
        'fn': fn,
        'roots': len(roots_of.get(fn, [])),
        'symbols': roots_of.get(fn, []),
        'block': int(m.group('block')),
        'row': m.group('row'),
        'laid_out': not m.group('row').startswith('('),
        'opcode': m.group('op'),
        'count': int(m.group('count')),
        'quotient': m.group('rest').startswith(QUOTIENT),
        'rest_other': m.group('rest') and not m.group('rest').startswith(QUOTIENT),
        'merged_line': fn in any_merged,
        'slot_position': ' / '.join(slot_position(o) for o in slot_ops) or '(none parsed)',
        'mem': mem['_'] if mem else '(no memory operand)',
        'base': kind(mem['base']) if mem else '-',
        'index': kind(mem['index']) if mem and mem['_'] == 'SibMemAddr' else '-',
        'scale': mem['scale'] if mem and mem['_'] == 'SibMemAddr' else '-',
        'disp': mem['disp'] if mem else '-',
        'others': ', '.join(others) or '-',
        'dumped_query': dump_name(fn) in dumped,
        'inv_sib': '+'.join(f'`{x}`' for x in inventory.get(fn, []) if x.endswith('Sib')) or
                   ('(no inventory)' if fn not in inventory else '(none)'),
        'operands': m.group('operands'),
    }
    if mem and mem['_'] == 'SibMemAddr':
        rec['index_const_o2'] = 'constant (immediate index)' if rec['index'] == 'Imm' else 'undecided'
    else:
        rec['index_const_o2'] = '- (no index)'
    if o0 is not None:
        sym_sites = [o0.get(s) for s in rec['symbols']]
        sym_sites = [s for s in sym_sites if s is not None]
        if not rec['symbols']:
            rec['o0'] = 'no root symbol'
        elif not sym_sites:
            rec['o0'] = 'no O0 object'
        else:
            sites = sym_sites[0]
            ci = sorted({k.split()[2] for k in sites if k.startswith('lea') and 'base=slot index=const' in k})
            vi = any(k.startswith('addrr') and 'index=const' not in k for k in sites)
            rec['o0'] = ('CI ' + ','.join(ci) if ci else 'no CI') + (' + VI' if vi else '')
            rec['o0_scale_match'] = ('n/a (no SIB index)' if rec['scale'] == '-'
                                     else 'yes' if f"s{rec['scale']}" in ci else 'no')
    rows.append(rec)

with open(out_tsv, 'w') as tsv:
    cols = ['fn', 'roots', 'opcode', 'slot_position', 'mem', 'base', 'index', 'scale', 'disp',
            'others', 'count', 'block', 'row', 'quotient', 'index_const_o2', 'o0', 'inv_sib',
            'operands']
    tsv.write('\t'.join(cols) + '\n')
    for r in rows:
        tsv.write('\t'.join(str(r.get(c, '')) for c in cols) + '\n')


def table(title, key, note=None):
    fns = collections.Counter(key(r) for r in rows)
    rts = collections.Counter()
    for r in rows:
        rts[key(r)] += r['roots']
    lines = [f'### {title}', '']
    if note:
        lines += [note, '']
    lines += ['| value | functions | roots |', '| --- | ---: | ---: |']
    for k, n in sorted(fns.items(), key=lambda kv: (-kv[1], str(kv[0]))):
        lines.append(f'| {k} | {n} | {rts[k]} |')
    lines.append(f'| total | {sum(fns.values())} | {sum(rts.values())} |')
    return lines + ['']


def shape(r):
    if r['mem'] == 'SibMemAddr':
        return f"`{r['opcode']}` {r['others']} [{r['base']} + {r['index']}*{r['scale']} + {r['disp']}]"
    if r['mem'] == 'MemAddr':
        return f"`{r['opcode']}` {r['others']} [{r['base']} + {r['disp']}]"
    return f"`{r['opcode']}` {r['others']}"


n_roots = sum(r['roots'] for r in rows)
md = [
    '# Slice 25.0 diagnostic census: the stack-slot scan\'s named rows (O2)',
    '',
    f'- Census: `{run}`; produced by `{os.path.abspath(sys.argv[0])}`'
    f' (`s_histogram.py {" ".join(sys.argv[1:])}`).',
    f'- Functions whose last trace line is the scan\'s refusal: **{len(rows) + len(unparsed)}**'
    f' ({len(unparsed)} not parsed); failed roots naming them: **{n_roots}**.',
    f'- Each function is counted once, by the FIRST offending row the refusal names (layout order);'
    f' "roots" sums the failed roots that name the function.',
    f'- Inside a merged-chain quotient (OverQuotient-wrapped refusal): '
    f'**{sum(r["quotient"] for r in rows)}** functions / {sum(r["roots"] for r in rows if r["quotient"])} roots;'
    f' not: **{sum(not r["quotient"] for r in rows)}** / {sum(r["roots"] for r in rows if not r["quotient"])}.',
    f'- Functions with a `merged chains=` trace line: {sum(r["merged_line"] for r in rows)};'
    f' named rows not laid out (`(not laid out) index i`): {sum(not r["laid_out"] for r in rows)};'
    f' refusals with an unexpected suffix: {sum(bool(r["rest_other"]) for r in rows)}.',
    f'- S functions with a dumped query in `{dump}`: {sum(r["dumped_query"] for r in rows)}'
    f' (the dump holds {len(dumped)} queries in all).',
    '',
]
md += table('Opcode of the named row', lambda r: f"`{r['opcode']}`")
md += table('Where the slot appears', lambda r: r['slot_position'])
md += table('Memory operand, base kind', lambda r: f"{r['mem']} base {r['base']}")
md += table('Index kind (SIB rows)', lambda r: r['index'])
md += table('Scale (SIB rows)', lambda r: r['scale'])
md += table('Displacement', lambda r: r['disp'])
md += table('Other operands (destination or stored value)', lambda r: r['others'])
md += table('Full shape', shape)
md += table('SIB opcodes of the function\'s emitted opcode inventory (its PROOF-465 record)',
            lambda r: r['inv_sib'],
            note='The refusal names only the first offending row; the failed-root record lists every '
                 'distinct uncovered opcode the function emits, so it bounds what the other rows are.')
md += table('Opcode by quotient', lambda r: f"`{r['opcode']}` {'over a quotient' if r['quotient'] else 'not over a quotient'}")
md += table('Offending rows per function (the refusal\'s count)',
            lambda r: r['count'] if r['count'] <= 4 else ('5-9' if r['count'] < 10 else '10+'))
md += table('Index constant at O2', lambda r: r['index_const_o2'],
            note='The O2 payloads carry no defining row of a register index (module docstring), so '
                 'a register index is undecided at O2.')
if o0 is not None:
    md += table('Cross-reference, NOT O2 evidence: the same function\'s O0 slot-address sites',
                lambda r: r.get('o0', '-'),
                note=f'From `{o0_path}` (o0_sib_sites.py over the O0 census objects): `CI sK` = an O0 '
                     '`lea (b,i,K)` whose base is a private stack address and whose index\'s last '
                     'definition is a `mov $k` or a zeroing `xor`; `VI` = an O0 `add` of a stack '
                     'address and a non-constant value. A heuristic over O0 machine code, not the O2 row.')
    md += table('Cross-reference: the named O2 row\'s scale is among the O0 constant-index scales',
                lambda r: r.get('o0_scale_match', f"n/a ({r.get('o0')})"))
if unparsed:
    md += ['### Not parsed', '']
    md += [f'- `{fn}`: {why}: `{t}`' for fn, why, t in unparsed] + ['']
open(out_md, 'w').write('\n'.join(md))
print('\n'.join(md))
sys.exit(1 if unparsed else 0)
