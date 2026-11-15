"""Check real ELF placement and relocations, independent of bridge IR types."""
from pathlib import Path
import json, re, struct, sys


def elf(path):
    data = path.read_bytes()
    assert data[:6] == b'\x7fELF\x02\x01'
    kind, machine = struct.unpack_from('<HH', data, 16)
    assert kind in (1, 2, 3) and machine == 183
    shoff = struct.unpack_from('<Q', data, 40)[0]
    shsize, shnum, names = struct.unpack_from('<HHH', data, 58)
    assert shsize == 64 and shnum and names < shnum
    sections = [struct.unpack_from('<IIQQQQIIQQ', data, shoff + i * shsize) for i in range(shnum)]
    def contents(section):
        return data[section[4]:section[4]+section[5]]
    def name(strings, offset):
        return strings[offset:strings.index(b'\0', offset)].decode()
    strings = contents(sections[names])
    section_names = [name(strings, s[0]) for s in sections]
    symbols = {}
    tables = {}
    for index, section in enumerate(sections):
        if section[1] != 2:
            continue
        strings = contents(sections[section[6]])
        table = []
        for at in range(section[4], section[4]+section[5], section[9]):
            n, info, other, shndx, value, size = struct.unpack_from('<IBBHQQ', data, at)
            row = dict(name=name(strings, n), info=info, other=other, shndx=shndx, value=value, size=size)
            table.append(row)
            if re.fullmatch(r'SA_(RO|RW|ZERO|TLS|TZ|REL|MID)_(16|64|256|4096)', row['name']) and shndx != 0:
                assert row['name'] not in symbols
                symbols[row['name']] = row
        tables[index] = table
    relocations = {}
    for section in sections:
        if section[1] != 4:
            continue
        table = tables.get(section[6])
        if table is None:
            continue
        for at in range(section[4], section[4]+section[5], section[9]):
            offset, info, addend = struct.unpack_from('<QQq', data, at)
            relocations[(section[7], offset)] = (info & 0xffffffff, table[info >> 32], addend)
    phoff = struct.unpack_from('<Q', data, 32)[0]
    phsize, phnum = struct.unpack_from('<HH', data, 54)
    headers = [struct.unpack_from('<IIQQQQQQ', data, phoff+i*phsize) for i in range(phnum)]
    return dict(path=str(path), kind=kind, data=data, sections=sections, names=section_names,
                symbols=symbols, relocations=relocations, headers=headers)


def audit(image):
    result = []
    for name, symbol in sorted(image['symbols'].items()):
        match = re.fullmatch(r'SA_(RO|RW|ZERO|TLS|TZ|REL|MID)_(16|64|256|4096)', name)
        assert match, name
        cls, alignment = match[1], int(match[2])
        align = 8 if cls == 'MID' else alignment
        section = image['sections'][symbol['shndx']]
        assert symbol['size'] == align, (name, symbol)
        assert section[8] >= align and section[8] % align == 0
        assert symbol['value'] % align == 0, (name, symbol)
        assert symbol['info'] & 15 == (6 if cls in ('TLS', 'TZ') else 1)
        assert bool(section[2] & 0x400) == (cls in ('TLS', 'TZ'))
        assert section[1] == (8 if cls in ('ZERO', 'TZ') else 1), (name, section)
        if cls == 'RO':
            assert not section[2] & 1
        elif cls in ('RW', 'ZERO', 'TLS', 'TZ'):
            assert section[2] & 1
        result.append(dict(name=name, section=image['names'][symbol['shndx']],
                           section_alignment=section[8], value=symbol['value'], size=symbol['size']))
        if image['kind'] != 1:
            continue
        if cls == 'MID':
            typ, target, addend = image['relocations'][(symbol['shndx'], symbol['value'])]
            assert typ == 257 and target['name'] == f'SA_RO_{alignment}' and addend == 8
        if cls == 'REL':
            for lane in range(2):
                typ, target, addend = image['relocations'][(symbol['shndx'], symbol['value']+lane*8)]
                assert typ == 257 and 0 < target['shndx'] < len(image['sections'])
                target_section = image['sections'][target['shndx']]
                offset = target['value'] + addend
                assert offset % alignment == 0 and target_section[8] >= alignment
                assert target_section[1] == 1 and not target_section[2] & 1
                start = target_section[4] + offset
                expected = struct.pack('<Q', (0x4000 if lane == 0 else 0x5000)+alignment)*(alignment//8)
                assert image['data'][start:start+alignment] == expected
    return result


executable = elf(Path(sys.argv[1]))
linked = audit(executable)
assert len(linked) == 28
rows = []
for filename in sys.argv[2:]:
    image = elf(Path(filename))
    assert image['kind'] == 1
    rows.extend(audit(image))
assert len(rows) == 28 and {r['name'] for r in rows} == {r['name'] for r in linked}
tls = [p for p in executable['headers'] if p[0] == 7]
assert len(tls) == 1 and tls[0][7] >= 4096
assert tls[0][2] % 4096 == 0 and tls[0][3] % 4096 == 0
print(json.dumps(dict(objects=rows, linked=linked, tls_program_header=tls[0], passed=True), indent=2))
