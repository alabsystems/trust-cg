#!/usr/bin/env python3
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates
# License: Apache-2.0
"""Drive `m145_x86_indirect_arg_xback.rs` outside the `targo test` harness.

That harness cannot dlopen a stage1-linked bridge under the pinned pack
compiler on every host, so this runs the SAME matrix with a `trustc` that can:
the callee source, the caller header, every `shapes()` row and every `CONTROLS`
entry are EXTRACTED from the test file, so what it measures is that file.

  m145_xback.py <bridge dylib> [opt levels...] [--only name,name] [--test FILE]
                [--trustc TRUSTC] [--no-controls] [--keep]

Matrix rows: all four rlib x bin combinations, each exit code compared with the
row's expected value (the LLVM x LLVM oracle is asserted too). A file whose
`const XBACK_CELLS: &str = "tcg-rlib";` restricts its rows to the two cells
with a bridge-compiled rlib runs only those (its rows would be undefined
behaviour in an LLVM-compiled rlib, so there is no LLVM x LLVM oracle; the
row's expected value is the oracle). Controls: the
LLVM x LLVM oracle must hold, the bridge-compiled rlib / bin must refuse with
every listed substring (or compile, when none is listed) at the control's
`refused_at` levels and compile at every other level, and every cell that
compiles must agree with the oracle. Exit status 1 on any failure.

`--trustc` (or `$TRUSTC`) defaults to the installed Trust package's `trustc`
on PATH. Needs an x86-64 or AArch64 host and that target's
`rust-std`; the matrix is built and run for the host's own architecture.
"""
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))


def take(flag, default=None):
    if flag in sys.argv:
        i = sys.argv.index(flag)
        value = sys.argv[i + 1]
        del sys.argv[i:i + 2]
        return value
    return default


def has(flag):
    if flag in sys.argv:
        sys.argv.remove(flag)
        return True
    return False


# The matrix runs NATIVELY: an x86-64 host measures x86-64, an AArch64 host
# AArch64 (the indirect argument lane covers both). A run qualifies only the
# host it ran on.
MACHINE = platform.machine()
if MACHINE in ('x86_64', 'AMD64'):
    ARCH = 'x86_64'
elif MACHINE in ('arm64', 'aarch64'):
    ARCH = 'aarch64'
else:
    sys.exit(f'm145_xback.py: needs an x86-64 or AArch64 host, not {MACHINE}')
TARGET = f'{ARCH}-apple-darwin' if platform.system() == 'Darwin' else f'{ARCH}-unknown-linux-gnu'
test = take('--test', os.path.join(HERE, os.pardir, 'm145_x86_indirect_arg_xback.rs'))
# The installed Trust package's trustc (never a stage of the Trust bootstrap
# build tree: it is exclusive and x.py deletes its compilers mid-build).
trustc = take('--trustc', os.environ.get('TRUSTC') or shutil.which('trustc') or 'trustc')
only = take('--only')
keep = has('--keep')
controls_on = not has('--no-controls')
if len(sys.argv) < 2:
    sys.exit(__doc__)
dylib = os.path.abspath(sys.argv[1])
opts = sys.argv[2:] or ['0', '2']

text = open(test).read()
callee = re.search(r'const CALLEE_SRC: &str = r#"(.*?)"#;', text, re.S).group(1)
hdr = re.search(r'const CALLER_HDR: &str = "(.*?)";', text, re.S).group(1)
hdr = hdr.replace('\\n\\\n    ', '\n').replace('\\n', '\n')
body = re.search(r'fn shapes\(\).*?vec!\[(.*?)\n    \]\n\}', text, re.S).group(1)
shapes = [(m.group(1), m.group(2), int(m.group(3))) for m in
          re.finditer(r'\(\s*"(\w+)",\s*r#"(.*?)"#,\s*(\d+),?\s*\)', body, re.S)]
# Every row carries exactly one raw-string body, so the extraction must find
# one shape per `r#"` (the file may be another matrix test, `--test`).
assert shapes and len(shapes) == body.count('r#"'), (len(shapes), body.count('r#"'))
STR = r'"((?:[^"\\]|\\.)*)"'
controls = [dict(name=m.group(1), lib=m.group(2), bin=m.group(3), oracle=int(m.group(4)),
                 lib_refusal=re.findall(STR, m.group(5)), bin_refusal=re.findall(STR, m.group(6)),
                 refused_at=re.findall(STR, m.group(7)),
                 bin_refusal_needs_llvm_rlib=m.group(8) == 'true')
            for m in re.finditer(
                r'Control \{\s*name: "(\w+)",\s*lib: r#"(.*?)"#,\s*bin: r#"(.*?)"#,\s*'
                r'oracle: (\d+),\s*lib_refusal: &\[(.*?)\],\s*bin_refusal: &\[(.*?)\],\s*'
                r'refused_at: &\[(.*?)\],\s*bin_refusal_needs_llvm_rlib: (true|false),\s*\}',
                text, re.S)]
assert len(controls) == text.count('    Control {'), (len(controls), text.count('    Control {'))
CELL_SETS = {
    'all': (('llvm', 'llvm'), ('llvm', 'tcg'), ('tcg', 'llvm'), ('tcg', 'tcg')),
    'tcg-rlib': (('tcg', 'llvm'), ('tcg', 'tcg')),
}
cell_set = re.search(r'const XBACK_CELLS: &str = "([\w-]+)";', text)
CELLS = CELL_SETS[cell_set.group(1) if cell_set else 'all']
RLIB_BACKENDS = [be for be in ('llvm', 'tcg') if any(rl == be for rl, _ in CELLS)]
if only:
    wanted = set(only.split(','))
    shapes = [s for s in shapes if s[0] in wanted]
    controls = [c for c in controls if c['name'] in wanted]

base = [trustc, '--edition=2021', '-Ztrust-verify=off', '--target', TARGET,
        '-Cpanic=abort', '-Coverflow-checks=off', '-Ccodegen-units=1']
tcg = [f'-Zcodegen-backend={dylib}', '-Ztrust-ir-cg-args=no-proof-certs']
env = dict(os.environ, RUSTC_BOOTSTRAP='1')
if platform.system() == 'Darwin':
    env.setdefault('MACOSX_DEPLOYMENT_TARGET', '13.0')
tmp = tempfile.mkdtemp(prefix='m145_')
failures, cells = [], 0


def run(cmd):
    r = subprocess.run(['nice'] + cmd, env=env, capture_output=True, text=True)
    return r.returncode, r.stderr


def why(err):
    keep_lines = [l for l in err.splitlines()
                  if 'TCG-' in l or l.startswith('error') or l.strip().startswith('- ')]
    return ' | '.join(keep_lines[:4])[:700]


def exit_code(path):
    return subprocess.run([path], capture_output=True).returncode


def compile_rlib(name, src, backend, opt):
    out = os.path.join(tmp, f'{name}_{backend}_O{opt}')
    os.makedirs(out, exist_ok=True)
    srcp = os.path.join(tmp, f'{name}.rs')
    open(srcp, 'w').write(src)
    crate = 'callee' if name == 'callee' else 'w'
    rc, err = run(base + (tcg if backend == 'tcg' else []) + [
        '--crate-type', 'rlib', '--crate-name', crate, f'-Copt-level={opt}',
        '--out-dir', out, srcp])
    return (os.path.join(out, f'lib{crate}.rlib'), '') if rc == 0 else (None, err)


def compile_bin(name, src, backend, opt, rlib, crate):
    srcp = os.path.join(tmp, f'{name}.rs')
    open(srcp, 'w').write(src + '\n')
    binp = os.path.join(tmp, f'{name}_{backend}_O{opt}')
    rc, err = run(base + (tcg if backend == 'tcg' else []) + [
        '--crate-type', 'bin', f'-Copt-level={opt}', '--extern', f'{crate}={rlib}',
        '-L', os.path.dirname(rlib), '-o', binp, srcp])
    return (binp, '') if rc == 0 else (None, err)


for opt in opts:
    rlibs = {}
    for be in RLIB_BACKENDS:
        rlibs[be], err = compile_rlib('callee', callee, be, opt)
        if rlibs[be] is None:
            failures.append(f'O{opt} callee rlib ({be}) COMPILE-ERROR: {why(err)}')
            print(failures[-1])
    for name, body_src, expected in shapes:
        row = []
        for rl_be, bin_be in CELLS:
            tag = f'{rl_be[0]}x{bin_be[0]}'
            if rlibs[rl_be] is None:
                row.append(f'{tag}=SKIP')
                continue
            binp, err = compile_bin(f'caller_{name}_{rl_be}', hdr + body_src, bin_be, opt,
                                    rlibs[rl_be], 'callee')
            label = f'O{opt} {name} rlib={rl_be} bin={bin_be}'
            if binp is None:
                failures.append(f'{label}: COMPILE-ERROR {why(err)}')
                row.append(f'{tag}=CE')
                continue
            code = exit_code(binp)
            cells += 1
            row.append(f'{tag}={code}')
            if code != expected:
                failures.append(f'{label}: exit {code}, expected {expected}' +
                                (' (ORACLE)' if (rl_be, bin_be) == ('llvm', 'llvm') else ''))
        print(f'O{opt} {name:24s} want={expected:3d} ' + ' '.join(row), flush=True)
    if not controls_on:
        continue
    for c in controls:
        name = c['name']
        row = []
        llvm_rlib, err = compile_rlib(f'{name}_lib', c['lib'], 'llvm', opt)
        if llvm_rlib is None:
            failures.append(f'O{opt} control {name}: LLVM rlib COMPILE-ERROR {why(err)}')
            print(failures[-1])
            continue
        oracle_bin, err = compile_bin(f'{name}_bin_ll', c['bin'], 'llvm', opt, llvm_rlib, 'w')
        if oracle_bin is None:
            failures.append(f'O{opt} control {name}: LLVM bin COMPILE-ERROR {why(err)}')
            print(failures[-1])
            continue
        oracle = exit_code(oracle_bin)
        cells += 1
        row.append(f'lxl={oracle}')
        if oracle != c['oracle']:
            failures.append(f'O{opt} control {name}: ORACLE exit {oracle}, expected {c["oracle"]}')

        def judge(label, artifact, err, needles):
            if needles:
                if artifact is not None:
                    failures.append(f'O{opt} control {name} {label}: compiled, expected a refusal '
                                    f'naming {needles}')
                    # Still run it (a bin), so the report shows what it computes.
                    return 'COMPILED', artifact
                missing = [n for n in needles if n not in err]
                if missing:
                    failures.append(f'O{opt} control {name} {label}: refused without {missing}: '
                                    f'{why(err)}')
                    return 'WRONG-REFUSAL', None
                return 'REFUSED', None
            if artifact is None:
                failures.append(f'O{opt} control {name} {label}: refused, expected to compile: '
                                f'{why(err)}')
                return 'CE', None
            return 'OK', artifact

        # The refusals apply only at the listed levels; elsewhere the control
        # must compile in every cell and agree with the oracle.
        refused_here = opt in c['refused_at']
        lib_needles = c['lib_refusal'] if refused_here else []
        bin_needles = c['bin_refusal'] if refused_here else []
        tcg_rlib, err = compile_rlib(f'{name}_lib', c['lib'], 'tcg', opt)
        verdict, tcg_rlib = judge('trust-cg rlib', tcg_rlib, err, lib_needles)
        row.append(f'rlib(tcg)={verdict}')
        cells_to_run = [('lxt', 'tcg', llvm_rlib)]
        if tcg_rlib is not None:
            cells_to_run += [('txl', 'llvm', tcg_rlib), ('txt', 'tcg', tcg_rlib)]
        for tag, bin_be, rlib in cells_to_run:
            binp, err = compile_bin(f'{name}_bin_{tag}', c['bin'], bin_be, opt, rlib, 'w')
            # A refusal to LINK a shared generic instance applies only against
            # the LLVM rlib: a bridge rlib exports no generic instance.
            linked_from_tcg = tag == 'txt'
            needles = (bin_needles if bin_be == 'tcg'
                       and not (c['bin_refusal_needs_llvm_rlib'] and linked_from_tcg) else [])
            verdict, binp = judge(tag, binp, err, needles)
            if binp is None:
                row.append(f'{tag}={verdict}')
                continue
            code = exit_code(binp)
            cells += 1
            row.append(f'{tag}={code}' if verdict == 'OK' else f'{tag}={verdict}:{code}')
            if code != oracle:
                failures.append(f'O{opt} control {name} {tag}: exit {code}, oracle {oracle}')
        print(f'O{opt} control {name:22s} want={c["oracle"]:3d} ' + ' '.join(row), flush=True)

print(f'cells built and run: {cells}; failures: {len(failures)}')
for f in failures:
    print('  FAIL', f)
if keep:
    print('kept', tmp)
else:
    shutil.rmtree(tmp, ignore_errors=True)
sys.exit(1 if failures else 0)
