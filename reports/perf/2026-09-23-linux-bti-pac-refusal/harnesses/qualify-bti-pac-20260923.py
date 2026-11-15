#!/usr/bin/python3
"""Qualify the C-01 BTI/PAC link refusal on clean source and capture its evidence.

usage: qualify-bti-pac-20260923.py WORKTREE RUN

WORKTREE must be a clean checkout; RUN is a new directory outside it. With
PATH pinning the AY/Clean package and the rustup cargo, this script:

1. records the source identity (HEAD, tree, empty `git status --porcelain`)
   and the host (kernel, /proc/cpuinfo Features, glibc, GNU ld/readelf/cc
   versions and hashes, rustc/cargo versions);
2. builds the test targets, then runs `e2e_aarch64_elf_stack_zero_fill`
   (--show-output, one thread) with recording wrappers for `cc`, `readelf` and
   `getconf` first on PATH and TMPDIR inside RUN, so every native tool call
   and the BTI/PAC tests' objects and linked images are retained;
3. runs the link-driver unit tests, the CLI `link_options` target, the CLI
   refusal unit test and the whole codegen library suite without wrappers;
4. from a retained CG object, repeats the spec's direct listings
   (`readelf -n`, `cc -shared -Wl,-z,force-bti`, `readelf -lW`/`-n` of the
   output) and records them;
5. writes results.json: identities, every `test result:` line, the tests'
   `record:` lines and the per-call summary.

It fails (exit 1) when the tree is dirty or any target does not report
`test result: ok.`. It asserts nothing the tests do not; the BTI execution
outcome stays a record.
"""
from pathlib import Path
import hashlib, json, os, platform, re, shutil, stat, subprocess, sys, time

WORKTREE, RUN = (Path(arg).resolve() for arg in sys.argv[1:3])
HERE = Path(__file__).resolve().parent
RUN.mkdir(parents=True)
for sub in ('calls', 'blobs', 'logs', 'tmp', 'wrappers', 'direct'):
    (RUN / sub).mkdir()
BASE_ENV = dict(os.environ)


def sh(args, env=None, cwd=WORKTREE, check=True):
    result = subprocess.run(args, cwd=cwd, env=env or BASE_ENV, capture_output=True, text=True)
    if check and result.returncode != 0:
        raise SystemExit(f'{args}: exit {result.returncode}\n{result.stdout}\n{result.stderr}')
    return result


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def tool(name):
    found = shutil.which(name, path=BASE_ENV['PATH'])
    assert found, name
    return dict(path=found, resolved=str(Path(found).resolve()), sha256=sha256(found))


status = sh(['git', 'status', '--porcelain', '--untracked-files=all']).stdout
if status.strip():
    raise SystemExit(f'dirty worktree:\n{status}')
head = sh(['git', 'rev-parse', 'HEAD']).stdout.strip()
tree = sh(['git', 'rev-parse', 'HEAD^{tree}']).stdout.strip()

features = next(line for line in Path('/proc/cpuinfo').read_text().splitlines()
                if line.startswith('Features'))
ld = shutil.which('ld', path=BASE_ENV['PATH'])
host = dict(
    uname=' '.join(platform.uname()),
    cpuinfo_features=features,
    bti=' bti ' in f' {features.split(":", 1)[1]} ',
    glibc=sh(['getconf', 'GNU_LIBC_VERSION']).stdout.strip(),
    ldd=sh(['ldd', '--version']).stdout.splitlines()[0],
    ld=sh(['ld', '--version']).stdout.splitlines()[0],
    ld_path=ld, ld_resolved=str(Path(ld).resolve()), ld_sha256=sha256(ld),
    readelf=sh(['readelf', '--version']).stdout.splitlines()[0],
    cc=sh(['cc', '--version']).stdout.splitlines()[0],
    rustc=sh(['rustc', '-V']).stdout.strip(),
    cargo=sh(['cargo', '-V']).stdout.strip(),
    path=BASE_ENV['PATH'],
)
tools = {name: tool(name) for name in ('cc', 'readelf', 'getconf')}
(RUN / 'tools.json').write_text(json.dumps(tools, indent=2) + '\n')
wrapper = HERE / 'capture-bti-pac-tools-20260923.py'
for name in tools:
    dest = RUN / 'wrappers' / name
    shutil.copyfile(wrapper, dest)
    dest.chmod(dest.stat().st_mode | stat.S_IXUSR)

CARGO = ['cargo', 'test', '--locked', '--offline', '-j', '8']
runs = [
    ('e2e_aarch64_elf_stack_zero_fill', [*CARGO, '-p', 'trust-cg-codegen', '--test',
      'e2e_aarch64_elf_stack_zero_fill', '--', '--show-output', '--test-threads=1'], True),
    ('link_driver_unit', [*CARGO, '-p', 'trust-cg-codegen', '--lib', 'link_driver', '--',
      '--show-output'], False),
    ('cli_link_options', [*CARGO, '-p', 'trust-cg-cli', '--test', 'link_options', '--',
      '--show-output'], False),
    ('cli_refusal_unit', [*CARGO, '-p', 'trust-cg-cli', '--bin', 'trust-cg',
      'invalid_link_options_are_refused_by_name', '--', '--show-output'], False),
    ('codegen_lib', [*CARGO, '-p', 'trust-cg-codegen', '--lib'], False),
]
# Build every target first without wrappers so cargo's own `cc` link steps are
# not recorded as test calls.
for _, args, _ in runs:
    build = args[:args.index('--')] if '--' in args else args
    sh([*build, '--no-run'])

results = dict(source=dict(head=head, tree=tree, porcelain=''), host=host, runs={})
for label, args, wrapped in runs:
    env = dict(BASE_ENV)
    if wrapped:
        env.update(PATH=f"{RUN / 'wrappers'}:{BASE_ENV['PATH']}", TMPDIR=str(RUN / 'tmp'),
                   C01_CAPTURE_ROOT=str(RUN))
    started = time.time()
    result = subprocess.run(args, cwd=WORKTREE, env=env, capture_output=True, text=True)
    text = f'$ {" ".join(args)}\n{result.stdout}\n--- stderr ---\n{result.stderr}'
    (RUN / 'logs' / f'{label}.log').write_text(text)
    lines = re.findall(r'^test result: .*$', result.stdout, re.M)
    results['runs'][label] = dict(command=args, wrapped=wrapped, exit=result.returncode,
                                  seconds=round(time.time() - started, 1), test_results=lines,
                                  records=re.findall(r'^(?:record: |glibc |host linker ).*$',
                                                     result.stdout, re.M))
    if result.returncode != 0 or len(lines) != 1 or not lines[0].startswith('test result: ok.'):
        (RUN / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
        raise SystemExit(f'{label}: {lines} exit {result.returncode}')

calls = []
for folder in sorted((RUN / 'calls').iterdir()):
    record = json.loads((folder / 'result.json').read_text())
    stderr = (folder / 'stderr').read_text(errors='replace')
    stdout = (folder / 'stdout').read_text(errors='replace')
    calls.append(dict(call=folder.name, tool=record['tool'], args=record['args'],
                      exit=record['exit_code'],
                      force_bti_warnings=[line for line in stderr.splitlines() if 'force-bti' in line],
                      property_note='NT_GNU_PROPERTY_TYPE_0' in stdout if record['tool'] == 'readelf' else None,
                      snapshots_after=len(record['snapshots'].get('after', []))))
results['calls'] = calls

# Direct listings from one retained CG object (the O2 function object of the
# force-bti test), outside the test.
cg = next(Path(row['path']) for call in (RUN / 'calls').iterdir()
          for row in json.loads((call / 'result.json').read_text())['snapshots'].get('before', [])
          if row['path'].endswith('/cg-O2.o'))
cg_sha = sha256(RUN / 'blobs' / next(row['sha256'] for call in (RUN / 'calls').iterdir()
                for row in json.loads((call / 'result.json').read_text())['snapshots'].get('before', [])
                if row['path'].endswith('/cg-O2.o')))
direct = RUN / 'direct'
shutil.copyfile(RUN / 'blobs' / cg_sha, direct / 'cg-O2.o')
steps = [
    ('readelf-n-cg-O2.o', ['readelf', '-n', '-W', 'cg-O2.o']),
    ('readelf-SW-cg-O2.o', ['readelf', '-S', '-W', 'cg-O2.o']),
    ('cc-shared-force-bti', ['cc', '-shared', '-Wl,-z,force-bti', 'cg-O2.o', '-o', 'libbti.so']),
    ('readelf-lW-libbti.so', ['readelf', '-l', '-W', 'libbti.so']),
    ('readelf-n-libbti.so', ['readelf', '-n', '-W', 'libbti.so']),
    ('cc-shared-default', ['cc', '-shared', 'cg-O2.o', '-o', 'libdefault.so']),
    ('readelf-lW-libdefault.so', ['readelf', '-l', '-W', 'libdefault.so']),
    ('readelf-n-libdefault.so', ['readelf', '-n', '-W', 'libdefault.so']),
]
listings = {}
for label, args in steps:
    result = sh(args, cwd=direct)
    (direct / f'{label}.txt').write_text(f'$ {" ".join(args)}\n--- stdout ---\n{result.stdout}'
                                         f'--- stderr ---\n{result.stderr}--- exit {result.returncode}\n')
    listings[label] = dict(exit=result.returncode, stdout=result.stdout, stderr=result.stderr)
for image in ('libbti.so', 'libdefault.so'):
    (direct / image).unlink()
results['direct'] = dict(object=str(cg), object_sha256=cg_sha, steps=[
    dict(label=label, command=args) for label, args in steps])
results['direct_summary'] = dict(
    object_has_property_note='NT_GNU_PROPERTY_TYPE_0' in listings['readelf-n-cg-O2.o']['stdout'],
    forced_warning=[line for line in listings['cc-shared-force-bti']['stderr'].splitlines()
                    if 'force-bti' in line],
    forced_gnu_stack=[line.strip() for line in listings['readelf-lW-libbti.so']['stdout'].splitlines()
                      if 'GNU_STACK' in line],
    forced_property=[line.strip() for line in listings['readelf-n-libbti.so']['stdout'].splitlines()
                     if 'NT_GNU_PROPERTY_TYPE_0' in line or 'feature' in line],
    default_gnu_stack=[line.strip() for line in listings['readelf-lW-libdefault.so']['stdout'].splitlines()
                       if 'GNU_STACK' in line],
    default_property_note='NT_GNU_PROPERTY_TYPE_0' in listings['readelf-n-libdefault.so']['stdout'],
)
shutil.rmtree(RUN / 'tmp')
(RUN / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
after = sh(['git', 'status', '--porcelain', '--untracked-files=all']).stdout
if after.strip() or sh(['git', 'rev-parse', 'HEAD']).stdout.strip() != head:
    raise SystemExit(f'source changed during the run:\n{after}')
print(json.dumps({label: run['test_results'] for label, run in results['runs'].items()}, indent=2))
print(json.dumps(results['direct_summary'], indent=2))
