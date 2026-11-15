#!/usr/bin/env python3
"""Qualify whole-module AArch64 ELF DWARF parameters/variables (L03-P4), 2026-09-23.

usage: qualify-module-dwarf-20260923.py ROOT OUT

ROOT is a clean trust-cg checkout; OUT is a new directory outside it. The
test binaries are built first with the real tools on PATH, then the two
unchanged integration targets and the four `pipeline::tests::module_debug_*`
unit tests run with recording wrappers in front of cc, gdb and the LLVM
readers (PATH and TRUST_CG_LLVM_BIN). Every run goes through the Linux
floor's own process-group timeout and 16 GiB RSS ceiling. Source identity is
checked before and after. The wrappers forward exact arguments and add no
authority; the post-checks below only re-read what the tests' tools printed.
"""
from pathlib import Path
import hashlib, importlib.util, json, os, re, shutil, sys
from datetime import datetime, timezone

ROOT = Path(sys.argv[1]).resolve()
OUT = Path(sys.argv[2]).resolve()
assert not str(OUT).startswith(str(ROOT) + os.sep), 'OUT must be outside the source tree'
HERE = Path(__file__).resolve().parent
CAPTURE = HERE / 'capture-module-dwarf-tools-20260923.py'
HOME = Path.home()
PKG = HOME / '.local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23'
LEVELS = ['O0', 'O1', 'O2', 'O3']

OUT.mkdir()
for name in ['bin', 'calls', 'blobs', 'logs']:
    (OUT / name).mkdir()


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


tools = {}
for name in ['cc', 'gdb', 'llvm-dwarfdump', 'llvm-readelf', 'llvm-objdump']:
    # Keep argv[0]: llvm-readelf and llvm-readobj share a binary and select
    # their output mode from the invoked name.
    real = Path(shutil.which(name)).absolute()
    tools[name] = dict(path=str(real), resolved=str(real.resolve()), sha256=sha256(real))
    wrapper = OUT / 'bin' / name
    shutil.copyfile(CAPTURE, wrapper)
    wrapper.chmod(0o755)
(OUT / 'tools.json').write_text(json.dumps(tools, indent=2) + '\n')

SCRUB = ('RUSTFLAGS', 'RUSTC', 'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER', 'CARGO_ENCODED_RUSTFLAGS',
         'CARGO_BUILD_TARGET', 'CARGO_BUILD_RUSTC', 'CARGO_BUILD_RUSTC_WRAPPER',
         'CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER', 'CARGO_TARGET_DIR', 'TRUST_CG_KEEP_TEST_OBJECTS')
env = {k: v for k, v in os.environ.items()
       if not k.startswith(('TCG_', 'TRUST_CG_', 'AY_')) and k not in SCRUB}
real_path = ':'.join([str(PKG / 'bin'), str(HOME / '.rustup/toolchains/1.97.1-aarch64-unknown-linux-gnu/bin'),
                      str(HOME / '.cargo/bin'), str(HOME / '.local/bin'), '/usr/bin', '/bin'])
env.update(PATH=real_path, RUSTUP_TOOLCHAIN='1.97.1', CARGO_BUILD_JOBS='8', RUST_TEST_THREADS='1',
           RUST_MIN_STACK='16777216', CG_MODULE_DWARF_CAPTURE_ROOT=str(OUT))
os.environ.clear()
os.environ.update(env)
os.chdir(ROOT)

spec = importlib.util.spec_from_file_location('linux_floor', ROOT / 'scripts/check_linux_aarch64.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
provenance = gate.preflight()
assert not provenance['dirty'], provenance['git_status']

record = dict(
    scope='L03-P4 whole-module AArch64 DWARF parameters/variables: aarch64_elf_dwarf and '
          'e2e_aarch64_elf_debugger_linux unchanged from the commit, plus the four '
          'pipeline::tests::module_debug_* unit tests, with exact-argument tool forwarding and '
          'retained tool transcripts/inputs. Object and debugger evidence for these fixtures; '
          'not a proof that a described location holds its source value.',
    provenance=provenance, started=datetime.now(timezone.utc).isoformat(), tools=tools,
    environment={k: env[k] for k in ('PATH', 'RUSTUP_TOOLCHAIN', 'CARGO_BUILD_JOBS', 'RUST_TEST_THREADS',
                                     'RUST_MIN_STACK')},
    max_rss_gib=16, timeout_seconds=1200, commands=[], complete=False)


def save():
    (OUT / 'results.json').write_text(json.dumps(record, indent=2) + '\n')


save()
CARGO = ['cargo', 'test', '--locked', '--offline', '--color', 'never', '-j', '8', '-p', 'trust-cg-codegen']

# 1. Build every binary with the real tools so no wrapped run compiles or links.
prebuild = CARGO + ['--lib', '--test', 'aarch64_elf_dwarf', '--test', 'e2e_aarch64_elf_debugger_linux', '--no-run']
row = gate.run_target(prebuild, OUT / 'logs' / 'prebuild.log', 1200, root=ROOT, max_rss_gib=16)
row = dict(label='prebuild', **row)
# A --no-run build prints no test suite, which the floor classifier requires;
# keep its verdict under its own name and judge the build by its exit status
# and RSS receipt.
row['test_classifier'] = dict(status=row.pop('status'), errors=row.pop('errors'))
row['status'] = 'built' if row['returncode'] == 0 and row['rss']['outcome'] == 'within' else 'fail'
record['commands'].append(row)
save()
assert row['status'] == 'built', row

# 2. The qualifying runs, wrapped.
os.environ['PATH'] = str(OUT / 'bin') + ':' + real_path
os.environ['TRUST_CG_LLVM_BIN'] = str(OUT / 'bin')
record['environment'].update(PATH_wrapped=os.environ['PATH'], TRUST_CG_LLVM_BIN=os.environ['TRUST_CG_LLVM_BIN'])
runs = [
    ('aarch64_elf_dwarf', CARGO + ['--test', 'aarch64_elf_dwarf', '--', '--nocapture', '--test-threads=1']),
    ('e2e_aarch64_elf_debugger_linux',
     CARGO + ['--test', 'e2e_aarch64_elf_debugger_linux', '--', '--nocapture', '--test-threads=1']),
    ('lib-module_debug', CARGO + ['--lib', 'pipeline::tests::module_debug_', '--', '--nocapture',
                                  '--test-threads=1']),
]
SUMMARY = re.compile(r'test result: (\w+)\. (\d+) passed; (\d+) failed; (\d+) ignored; (\d+) measured; '
                     r'(\d+) filtered out')
for label, command in runs:
    log = OUT / 'logs' / (label + '.log')
    row = dict(label=label, **gate.run_target(command, log, 1200, root=ROOT, max_rss_gib=16))
    text = log.read_text(errors='replace')
    row['recompiled'] = bool(re.search(r'^\s*Compiling ', text, re.MULTILINE))
    row['test_result_lines'] = [m.group(0) for m in SUMMARY.finditer(text)]
    if label == 'lib-module_debug':
        # A filtered unit-test run: the floor classifier refuses filters by
        # design, so require exactly the four named tests instead.
        names = sorted(re.findall(r'^test (pipeline::tests::module_debug_\w+) \.\.\. ok$', text, re.MULTILINE))
        summaries = list(SUMMARY.finditer(text))
        row['unit_tests'] = names
        row['status'] = 'pass' if (row['returncode'] == 0 and len(names) == 4 and len(summaries) == 1
                                   and summaries[0].group(1) == 'ok' and summaries[0].group(2) == '4'
                                   and summaries[0].group(3) == '0') else 'fail'
    record['commands'].append(row)
    save()
    print(json.dumps(dict(label=label, status=row['status'], results=row['test_result_lines'])), flush=True)
    assert row['status'] == 'pass', row
    assert not row['recompiled'], f'{label} recompiled under the wrappers'

# 3. Post-checks over the captured tool calls (re-reading the tests' own tool output).
calls = []
for folder in sorted((OUT / 'calls').iterdir()):
    request = json.loads((folder / 'request.json').read_text())
    result = json.loads((folder / 'result.json').read_text())
    result['folder'] = folder.name
    result['stdout'] = (folder / 'stdout').read_text(errors='replace')
    calls.append(result)
assert len(calls) == len(list((OUT / 'calls').glob('*/request.json')))


def basename(row):
    return Path(row['args'][-1]).name if row['args'] else ''


gdb = [row for row in calls if row['tool'] == 'gdb']
assert all(row['exit_code'] == 0 for row in gdb), [row['folder'] for row in gdb if row['exit_code']]
gdb_by_exe = {}
for row in gdb:
    gdb_by_exe.setdefault(basename(row), []).append(row)
assert set(gdb_by_exe) == {f'fixture_{lvl}' for lvl in LEVELS} | {f'module_{lvl}' for lvl in LEVELS}, sorted(gdb_by_exe)
assert all(len(gdb_by_exe[f'fixture_{lvl}']) == 1 for lvl in LEVELS)
assert all(len(gdb_by_exe[f'module_{lvl}']) == 2 for lvl in LEVELS)

# The module leg's values, as gdb printed them.
PROBE = re.compile(r'^trust-cg-probe (\w+)=(.*)$', re.MULTILINE)
module_values = {}
for lvl in LEVELS:
    live = [row for row in gdb_by_exe[f'module_{lvl}'] if '-ex' in row['args'] and 'run' in row['args']]
    assert len(live) == 1, lvl
    module_values[lvl] = dict(PROBE.findall(live[0]['stdout']))
    assert module_values[lvl].get('x') == '7', (lvl, module_values[lvl])

# llvm-dwarfdump --verify on every module object (ELF both layouts, Mach-O both layouts).
verify = {}
for row in calls:
    if row['tool'] == 'llvm-dwarfdump' and row['args'][:1] == ['--verify']:
        name = basename(row)
        if name.startswith(('module_', 'macho_module_', 'checker_', 'absent_', 'lines_only_')):
            verify[name] = row['exit_code'] == 0 and 'No errors.' in row['stdout']
expected_modules = {f'module_{lvl}_{order}.o' for lvl in LEVELS for order in ('fixture_first', 'leaf_first')}
expected_modules |= {f'macho_module_{lvl}_{order}.o' for lvl in LEVELS for order in ('fixture_first', 'leaf_first')}
expected_modules |= {f'lines_only_{lvl}_{order}.o' for lvl in LEVELS for order in ('fixture_first', 'leaf_first')}
assert expected_modules <= set(verify), sorted(expected_modules - set(verify))
assert all(verify[name] for name in expected_modules), {k: v for k, v in verify.items() if not v}


def dies(dump):
    """Per-subprogram (tag, name) DIEs and each ranged location, from --debug-info text."""
    subs, current, low, tag = {}, None, None, None
    for line in dump.splitlines():
        text = line.strip()
        m = re.match(r'0x[0-9a-f]+:\s+(DW_TAG_\w+)', text)
        if m:
            tag = m.group(1)
            if tag == 'DW_TAG_subprogram':
                current, low = None, None
            continue
        m = re.match(r'DW_AT_name\s+\("(.*)"\)', text)
        if m and tag == 'DW_TAG_subprogram' and current is None:
            current = m.group(1)
            subs[current] = dict(low=None, dies=[], ranges=[])
            continue
        m = re.match(r'DW_AT_low_pc\s+\((0x[0-9a-f]+)\)', text)
        if m and tag == 'DW_TAG_subprogram' and current and subs[current]['low'] is None:
            subs[current]['low'] = int(m.group(1), 16)
            continue
        if m and tag == 'DW_TAG_subprogram':
            continue
        if current and tag in ('DW_TAG_formal_parameter', 'DW_TAG_variable'):
            m = re.match(r'DW_AT_name\s+\("(.*)"\)', text)
            if m:
                subs[current]['dies'].append((tag, m.group(1)))
                continue
            m = re.match(r'\[(0x[0-9a-f]+), (0x[0-9a-f]+)\): (.*)', text)
            if m:
                name = subs[current]['dies'][-1][1]
                subs[current]['ranges'].append((name, int(m.group(1), 16), int(m.group(2), 16), m.group(3)))
        if tag == 'DW_TAG_base_type':
            current = None
    return subs


info = {}
for row in calls:
    # Only the plain two-argument dump; `--debug-info -v` prints forms too.
    if row['tool'] == 'llvm-dwarfdump' and len(row['args']) == 2 and row['args'][0] == '--debug-info' \
            and row['exit_code'] == 0:
        info.setdefault(basename(row), row['stdout'])
die_summary, parity = {}, {}
for lvl in LEVELS:
    for order in ('fixture_first', 'leaf_first'):
        name = f'module_{lvl}_{order}.o'
        subs = dies(info[name])
        die_summary[name] = {sub: dict(low=v['low'],
                                       formal_parameters=[n for t, n in v['dies'] if t == 'DW_TAG_formal_parameter'],
                                       variables=[n for t, n in v['dies'] if t == 'DW_TAG_variable'],
                                       ranged_entries=len(v['ranges']))
                             for sub, v in subs.items()}
        fixture = die_summary[name]['elf_debug_fixture']
        assert 'x' in fixture['formal_parameters'], (name, fixture)
        for local in ('acc', 'spill_probe', 'reg_probe', 'tail_const'):
            assert local in fixture['variables'], (name, local)
        assert die_summary[name]['elf_debug_leaf']['formal_parameters'] == ['arg0', 'arg1'], name
    # Observation (not an assertion): the leaf-first module's fixture ranges
    # versus the single-function object's, after removing the text offset.
    single = dies(info[f'single_{lvl}.o'])['elf_debug_fixture']
    moved = dies(info[f'module_{lvl}_leaf_first.o'])['elf_debug_fixture']
    rebased = [(n, s - moved['low'], e - moved['low'], x) for n, s, e, x in moved['ranges']]
    parity[lvl] = dict(fixture_text_offset=moved['low'], single_ranges=len(single['ranges']),
                       module_ranges=len(rebased),
                       identical_after_rebasing=rebased == [(n, s - single['low'], e - single['low'], x)
                                                            for n, s, e, x in single['ranges']])

# The legacy lines-only module entry (the Compiler/CLI -g description):
# both subprograms, no parameter or variable DIE, in both orders.
lines_only = {}
for lvl in LEVELS:
    for order in ('fixture_first', 'leaf_first'):
        name = f'lines_only_{lvl}_{order}.o'
        dump = info[name]
        subs = dies(dump)
        assert {'elf_debug_fixture', 'elf_debug_leaf'} <= set(subs), (name, sorted(subs))
        assert 'DW_TAG_formal_parameter' not in dump and 'DW_TAG_variable' not in dump, name
        lines_only[name] = {sub: dict(low=v['low'], dies=len(v['dies'])) for sub, v in subs.items()}
        second = 'elf_debug_leaf' if order == 'fixture_first' else 'elf_debug_fixture'
        assert lines_only[name][second]['low'] > 0, (name, lines_only[name])

for name in ['llvm-dwarfdump', 'llvm-objdump', 'llvm-readelf', 'cc']:
    assert any(row['tool'] == name for row in calls), name
record['final_source'] = gate.source_provenance(provenance['tools']['git'])
record['source_unchanged'] = record['final_source']['source_fingerprint'] == provenance['source_fingerprint']
assert record['source_unchanged']
record.update(
    captured_calls=len(calls),
    calls_by_tool={tool: sum(1 for row in calls if row['tool'] == tool) for tool in sorted(tools)},
    nonzero_exit_calls=sorted(row['folder'] for row in calls if row['exit_code'] != 0),
    debugger_calls=len(gdb), module_gdb_values=module_values, module_verify=verify,
    module_dies=die_summary, lines_only_module_dies=lines_only,
    single_vs_module_parity_observation=parity,
    complete=True, passed=True, finished=datetime.now(timezone.utc).isoformat())
save()
print(json.dumps(dict(passed=True, calls=len(calls), debugger_calls=len(gdb), parity=parity)), flush=True)
