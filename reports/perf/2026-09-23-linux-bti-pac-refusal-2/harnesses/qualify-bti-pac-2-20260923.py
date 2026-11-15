#!/usr/bin/python3
"""Qualify the C-01 BTI/PAC link refusal (review repair) on clean source.

usage: qualify-bti-pac-2-20260923.py WORKTREE RUN LLD

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
4. from a retained CG object, repeats the direct listings (`readelf -n`,
   `cc -shared -Wl,-z,force-bti`, `readelf -lW`/`-n` of the output) and
   probes each refused keyword with GNU ld and with lld (LLD is the ld.lld
   whose directory is put first on PATH for `cc -fuse-ld=lld` only):
   `-z force-bti`, `-z pac-plt`, `-z bti-report=error|warning`, with
   `readelf -n`/`-d` of each output; links, runs and gdb-locates the fault of
   a C-only `-z pac-plt` executable; and runs the retained forced harness
   image and forced startfile image under gdb to record the fault PC;
5. writes results.json: identities, every `test result:` line, the tests'
   `record:` lines, the per-call summary (BTI warnings matched by the GNU ld
   or lld message text) and the probe summary.

It fails (exit 1) when the tree is dirty or any target does not report
`test result: ok.`. It asserts nothing the tests do not; the BTI execution
outcome stays a record.
"""
from pathlib import Path
import hashlib, json, os, platform, re, resource, shutil, stat, subprocess, sys, time

WORKTREE, RUN = (Path(arg).resolve() for arg in sys.argv[1:3])
LLD = Path(sys.argv[3]).absolute()
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
    gdb=sh(['gdb', '--version']).stdout.splitlines()[0],
    lld=dict(path=str(LLD), resolved=str(LLD.resolve()), sha256=sha256(LLD),
             version=sh([str(LLD), '--version']).stdout.strip()),
    path=BASE_ENV['PATH'],
)
tools = {name: tool(name) for name in ('cc', 'readelf', 'getconf')}
(RUN / 'tools.json').write_text(json.dumps(tools, indent=2) + '\n')
wrapper = HERE / 'capture-bti-pac-2-tools-20260923.py'
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

GNU_BTI = 'warning: BTI turned on by -z force-bti when all inputs do not have BTI in NOTE section'
LLD_BTI = '-z force-bti: file does not have GNU_PROPERTY_AARCH64_FEATURE_1_BTI property'


def bti_warnings(stderr):
    return [line for line in stderr.splitlines() if GNU_BTI in line or LLD_BTI in line]


calls = []
for folder in sorted((RUN / 'calls').iterdir()):
    record = json.loads((folder / 'result.json').read_text())
    stderr = (folder / 'stderr').read_text(errors='replace')
    stdout = (folder / 'stdout').read_text(errors='replace')
    calls.append(dict(call=folder.name, tool=record['tool'], args=record['args'],
                      exit=record['exit_code'],
                      force_bti_warnings=bti_warnings(stderr),
                      property_note='NT_GNU_PROPERTY_TYPE_0' in stdout if record['tool'] == 'readelf' else None,
                      snapshots_after=len(record['snapshots'].get('after', []))))
results['calls'] = calls

# Direct listings and linker probes from one retained CG object (the O2
# function object of the BTI link test), outside the test.
snapshots = [(row, stage) for call in (RUN / 'calls').iterdir()
             for stage, rows in json.loads((call / 'result.json').read_text())['snapshots'].items()
             for row in rows if 'sha256' in row]


def blob(suffix, stage):
    shas = {row['sha256'] for row, where in snapshots if where == stage and row['path'].endswith(suffix)}
    assert len(shas) == 1, (suffix, shas)
    sha = shas.pop()
    return sha, next(row['path'] for row, where in snapshots if row['sha256'] == sha)


cg_sha, cg = blob('/cg-O2.o', 'before')
direct = RUN / 'direct'
shutil.copyfile(RUN / 'blobs' / cg_sha, direct / 'cg-O2.o')
for name, suffix in (('cg-force-bti-O2', '/cg-force-bti-O2'),
                     ('startfile-force-bti', '/startfile-force-bti')):
    sha, _ = blob(suffix, 'after')
    shutil.copyfile(RUN / 'blobs' / sha, direct / name)
    (direct / name).chmod(0o755)
(direct / 'pac-main.c').write_text('#include <stdio.h>\nint main(void) { puts("pac-plt main"); return 0; }\n')
LLD_ENV = dict(BASE_ENV, PATH=f"{LLD.parent}:{BASE_ENV['PATH']}")
GDB = ['gdb', '-q', '-nx', '-batch', '-ex', 'run', '-ex', 'info symbol $pc', '-ex', 'x/2i $pc', '-ex', 'bt']
steps = [
    ('readelf-n-cg-O2.o', ['readelf', '-n', '-W', 'cg-O2.o'], None),
    ('readelf-SW-cg-O2.o', ['readelf', '-S', '-W', 'cg-O2.o'], None),
    ('cc-shared-force-bti', ['cc', '-shared', '-Wl,-z,force-bti', 'cg-O2.o', '-o', 'libbti.so'], None),
    ('readelf-lW-libbti.so', ['readelf', '-l', '-W', 'libbti.so'], None),
    ('readelf-n-libbti.so', ['readelf', '-n', '-W', 'libbti.so'], None),
    ('cc-shared-default', ['cc', '-shared', 'cg-O2.o', '-o', 'libdefault.so'], None),
    ('readelf-lW-libdefault.so', ['readelf', '-l', '-W', 'libdefault.so'], None),
    ('readelf-n-libdefault.so', ['readelf', '-n', '-W', 'libdefault.so'], None),
]
for linker, extra, env in (('gnu', [], None), ('lld', ['-fuse-ld=lld'], LLD_ENV)):
    for keyword in ('force-bti', 'pac-plt', 'bti-report=error', 'bti-report=warning'):
        out = f'{linker}-{keyword}.so'
        steps.append((f'{linker}-cc-shared-{keyword}',
                      ['cc', *extra, '-shared', f'-Wl,-z,{keyword}', 'cg-O2.o', '-o', out], env))
        steps.append((f'{linker}-readelf-n-{keyword}', ['readelf', '-n', '-W', out], None))
        steps.append((f'{linker}-readelf-d-{keyword}', ['readelf', '-d', '-W', out], None))
steps += [
    ('pac-cc-default', ['cc', '-O2', 'pac-main.c', '-o', 'pac-default'], None),
    ('pac-run-default', ['./pac-default'], None),
    ('pac-cc-pac-plt', ['cc', '-O2', '-Wl,-z,pac-plt', 'pac-main.c', '-o', 'pac-plt'], None),
    ('pac-readelf-n-pac-plt', ['readelf', '-n', '-W', 'pac-plt'], None),
    ('pac-readelf-d-pac-plt', ['readelf', '-d', '-W', 'pac-plt'], None),
    ('pac-run-pac-plt', ['./pac-plt'], None),
    ('pac-gdb-pac-plt', [*GDB, './pac-plt'], None),
    ('run-cg-force-bti-O2', ['./cg-force-bti-O2'], None),
    ('gdb-cg-force-bti-O2', [*GDB, './cg-force-bti-O2'], None),
    ('run-startfile-force-bti', ['./startfile-force-bti'], None),
    ('gdb-startfile-force-bti', [*GDB, './startfile-force-bti'], None),
]


def no_core():
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


listings = {}
for label, args, env in steps:
    result = subprocess.run(args, cwd=direct, env=env or BASE_ENV, capture_output=True, text=True,
                            preexec_fn=no_core, timeout=120)
    (direct / f'{label}.txt').write_text(f'$ {" ".join(args)}\n--- stdout ---\n{result.stdout}'
                                         f'--- stderr ---\n{result.stderr}--- exit {result.returncode}\n')
    listings[label] = dict(exit=result.returncode, stdout=result.stdout, stderr=result.stderr)
for path in list(direct.iterdir()):
    if path.suffix == '.so' or path.name in ('pac-default', 'pac-plt', 'cg-force-bti-O2',
                                              'startfile-force-bti', 'pac-main.c'):
        path.unlink()


def props(label):
    return [line.strip() for line in listings[label]['stdout'].splitlines()
            if 'NT_GNU_PROPERTY_TYPE_0' in line or 'feature' in line]


def gdb_fault(label):
    lines = listings[label]['stdout'].splitlines()
    return [line for line in lines if 'signal' in line or line.startswith('=>') or ' in section ' in line]


results['direct'] = dict(object=cg, object_sha256=cg_sha, lld=str(LLD),
                         steps=[dict(label=label, command=args, lld_path=env is not None)
                                for label, args, env in steps])
results['direct_summary'] = dict(
    object_has_property_note='NT_GNU_PROPERTY_TYPE_0' in listings['readelf-n-cg-O2.o']['stdout'],
    forced_warning=bti_warnings(listings['cc-shared-force-bti']['stderr']),
    forced_gnu_stack=[line.strip() for line in listings['readelf-lW-libbti.so']['stdout'].splitlines()
                      if 'GNU_STACK' in line],
    forced_property=props('readelf-n-libbti.so'),
    default_gnu_stack=[line.strip() for line in listings['readelf-lW-libdefault.so']['stdout'].splitlines()
                       if 'GNU_STACK' in line],
    default_property_note='NT_GNU_PROPERTY_TYPE_0' in listings['readelf-n-libdefault.so']['stdout'],
    keyword_probes={f'{linker} {keyword}': dict(
        link_exit=listings[f'{linker}-cc-shared-{keyword}']['exit'],
        link_stderr=listings[f'{linker}-cc-shared-{keyword}']['stderr'].splitlines(),
        property=props(f'{linker}-readelf-n-{keyword}'),
        pac_plt_tag=[line.strip() for line in listings[f'{linker}-readelf-d-{keyword}']['stdout'].splitlines()
                     if 'PAC_PLT' in line])
        for linker in ('gnu', 'lld')
        for keyword in ('force-bti', 'pac-plt', 'bti-report=error', 'bti-report=warning')},
    c_only_pac_plt=dict(
        default_run=dict(exit=listings['pac-run-default']['exit'], stdout=listings['pac-run-default']['stdout']),
        property=props('pac-readelf-n-pac-plt'),
        pac_plt_tag=[line.strip() for line in listings['pac-readelf-d-pac-plt']['stdout'].splitlines()
                     if 'PAC_PLT' in line],
        run=dict(exit=listings['pac-run-pac-plt']['exit'], stdout=listings['pac-run-pac-plt']['stdout']),
        gdb=gdb_fault('pac-gdb-pac-plt')),
    forced_harness_O2=dict(run=dict(exit=listings['run-cg-force-bti-O2']['exit'],
                                    stdout=listings['run-cg-force-bti-O2']['stdout']),
                           gdb=gdb_fault('gdb-cg-force-bti-O2')),
    startfile_forced=dict(run=dict(exit=listings['run-startfile-force-bti']['exit'],
                                   stdout=listings['run-startfile-force-bti']['stdout']),
                          gdb=gdb_fault('gdb-startfile-force-bti')),
)
shutil.rmtree(RUN / 'tmp')
(RUN / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
after = sh(['git', 'status', '--porcelain', '--untracked-files=all']).stdout
if after.strip() or sh(['git', 'rev-parse', 'HEAD']).stdout.strip() != head:
    raise SystemExit(f'source changed during the run:\n{after}')
print(json.dumps({label: run['test_results'] for label, run in results['runs'].items()}, indent=2))
print(json.dumps(results['direct_summary'], indent=2))
