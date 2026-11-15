#!/usr/bin/env python3
"""Print the LLVM x LLVM exit code of every row of an m145-format matrix file."""
import os, re, subprocess, sys, tempfile
TRUSTC = os.path.expanduser('trust/build/x86_64-apple-darwin/stage1/bin/trustc')
text = open(sys.argv[1]).read()
opt = sys.argv[2] if len(sys.argv) > 2 else '0'
callee = re.search(r'const CALLEE_SRC: &str = r#"(.*?)"#;', text, re.S).group(1)
hdr = re.search(r'const CALLER_HDR: &str = "(.*?)";', text, re.S).group(1)
hdr = hdr.replace('\\n\\\n    ', '\n').replace('\\n', '\n')
body = re.search(r'fn shapes\(\).*?vec!\[(.*?)\n    \]\n\}', text, re.S).group(1)
shapes = [(m.group(1), m.group(2)) for m in re.finditer(r'\(\s*"(\w+)",\s*r#"(.*?)"#,\s*(\d+),?\s*\)', body, re.S)]
env = dict(os.environ, RUSTC_BOOTSTRAP='1', MACOSX_DEPLOYMENT_TARGET='13.0')
base = [TRUSTC, '--edition=2021', '-Ztrust-verify=off', '--target', 'x86_64-apple-darwin',
        '-Cpanic=abort', '-Coverflow-checks=off', '-Ccodegen-units=1', f'-Copt-level={opt}']
with tempfile.TemporaryDirectory() as tmp:
    open(f'{tmp}/callee.rs', 'w').write(callee)
    subprocess.run(base + ['--crate-type', 'rlib', '--crate-name', 'callee', '--out-dir', tmp, f'{tmp}/callee.rs'], env=env, check=True)
    for name, src in shapes:
        open(f'{tmp}/{name}.rs', 'w').write(hdr + src + '\n')
        subprocess.run(base + ['--crate-type', 'bin', '--extern', f'callee={tmp}/libcallee.rlib', '-L', tmp, '-o', f'{tmp}/{name}', f'{tmp}/{name}.rs'], env=env, check=True)
        print(name, subprocess.run([f'{tmp}/{name}']).returncode)
