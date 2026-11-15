#!/opt/homebrew/bin/python3
"""Copy this report's small raw records; never build, edit inputs or release caches."""
import hashlib
import json
from pathlib import Path
import re
import shutil
import stat
import sys

ROOT = Path('/private/tmp/trust-cg-prelude-cohort-20260916.8Xzp4n')
DEST = ROOT / 'source/reports/perf/2026-09-16-shared-prelude-cohort'
HEAD = 'c1b22c9b7ced09ad5285a5f3c8e0e153439b0f06'
TREE = '59becfad97be0ae00da95f3e14f07ec1a394d87c'
INPUT_BOOK_SHA = 'c09244065a988b7a4a15f3f80d0542bce16302bb7949ab60a2e4cc1e853f4908'
RESULTS = {'adoption': '3721203d58eb3e23a276a76db68a8ea596d625c1c517b517bd9ee00cf23758b6',
           'checks': '679e6c92e82896f48cb48606b0565a9ce4509184a370b5d8fdc1ff2818d8d0d2'}
CONTROLS = ['ADOPTION-PLAN.md', 'QUALIFICATION-PLAN.md', 'adopt_cohort.py', 'qualify_cohort.py', 'history.json']


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def record(path):
    info = path.lstat()
    require(stat.S_ISREG(info.st_mode), 'not a regular file: ' + str(path))
    with path.open('rb') as stream:
        digest = hashlib.file_digest(stream, 'sha256').hexdigest()
    return dict(sha256=digest, mode=stat.S_IMODE(info.st_mode), bytes=info.st_size)


def read(path):
    return json.loads(path.read_text())


def inputs():
    paths = []
    for directory, count in [('adoption', 16), ('checks', 173)]:
        selected = sorted((ROOT / directory).iterdir())
        require(len(selected) == count, 'raw membership changed: ' + directory)
        paths.extend(selected)
    paths.extend(ROOT / name for name in CONTROLS)
    book = {str(p.relative_to(ROOT)): record(p) for p in paths}
    digest = hashlib.sha256(json.dumps(book, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    require(len(book) == 194 and digest == INPUT_BOOK_SHA, 'frozen input book changed')
    return book


def authenticate(book):
    for directory, digest in RESULTS.items():
        require(book[directory + '/result.json']['sha256'] == digest, 'terminal result changed')
    adoption, result = read(ROOT / 'adoption/result.json'), read(ROOT / 'checks/result.json')
    require(adoption['status'] == 'transaction-passed-review-required' and adoption['exit'] == 0
            and adoption['inputs_unchanged'] and not adoption['bookend_errors'], 'adoption not qualified')
    require(result['status'] == 'tests-passed' and result['head'] == HEAD and result['tree'] == TREE
            and result['inputs_unchanged'] and not result['bookend_errors'], 'qualification not complete')
    require(not result['proof_required'] and not result['verified_compiler']
            and not result['performance_claim'] and not result['full_workspace_qualification'], 'scope changed')
    guard_log = (ROOT / 'adoption/bumper.log').read_text()
    actual = re.findall(r'^test (\S+) \.\.\. (ok|FAILED|ignored)$', guard_log, re.M)
    require([list(row) for row in actual] == adoption['actual'] and len(actual) == 4
            and all(outcome == 'ok' for _, outcome in actual), 'four actual guards changed')
    terminal = read(ROOT / 'adoption/bumper.exit.json')
    require(terminal['exit_code'] == 0 and terminal['log_sha256'] == book['adoption/bumper.log']['sha256'],
            'bumper exit/log changed')
    names = []
    for row in result['selections']:
        label = row['label']
        listed = [line[:-6] for line in (ROOT / 'checks' / (label + '-list.log')).read_text().splitlines()
                  if line.endswith(': test')]
        actual = re.findall(r'^test (\S+) \.\.\. (ok|FAILED|ignored)$',
                            (ROOT / 'checks' / (label + '.log')).read_text(), re.M)
        require(sorted(listed) == sorted(row['names']) and [list(x) for x in actual] == row['actual']
                and sorted(name for name, _ in actual) == sorted(listed)
                and all(outcome == 'ok' for _, outcome in actual), 'selected census changed: ' + label)
        names.extend(listed)
    require(len(result['selections']) == 15 and len(names) == len(set(names)) == 78,
            '76 component plus two native census changed')
    require(len(set(names) | {name for name, _ in adoption['actual']}) == 82, 'combined distinct census changed')
    builds = []
    require(len(result['phases']) == 39, 'phase census changed')
    for phase in result['phases']:
        label = phase['label']
        terminal = read(ROOT / 'checks' / (label + '.exit.json'))
        require(phase['exit'] == terminal['exit_code'] == 0
                and terminal['log_sha256'] == book['checks/' + label + '.log']['sha256'], 'phase exit/log changed')
        if 'artifact' in phase:
            require(phase['artifact']['fresh'] is False and phase['compiler'], 'primary not fresh')
            builds.extend(phase['artifact']['filenames'])
    require(len(builds) == len(set(builds)) == 9 and len(result['outputs_after']) == 64
            and result['outputs_before'] == result['outputs_after'], 'output census/bookends changed')
    outputs = {path: record(Path(path)) for path in result['outputs_after']}
    require(outputs == result['outputs_after'], 'current primary/direct extern/checker changed')
    require(result['owner_before'] == result['owner_after'] and result['processes_after']['drained']
            and not result['processes_after']['matching_processes'], 'owner/process terminal receipt changed')
    return result, set(builds), outputs


def main():
    require(sys.flags.isolated and sys.dont_write_bytecode and not sys.flags.optimize, 'use python3 -I -B')
    require(Path(__file__).resolve() == DEST / 'archive_records.py', 'wrong report location')
    require(not (DEST / 'records').exists() and not (DEST / 'inventory.json').exists(), 'fresh archive required')
    before = inputs()
    result, primary, outputs = authenticate(before)
    inventory, copied_bytes, local_bytes = {}, 0, 0
    for relative, identity in sorted(before.items()):
        original = ROOT / relative
        local = (original.name in ('before.json', 'after.json', 'upstream-before.json', 'upstream-after.json')
                 or relative.startswith('checks/') and original.name.endswith('-build.log'))
        archived = None if local else 'records/' + relative
        if local:
            local_bytes += identity['bytes']
        else:
            path = DEST / archived
            path.parent.mkdir(parents=True, exist_ok=True)
            with original.open('rb') as source, path.open('xb') as destination:
                shutil.copyfileobj(source, destination)
            path.chmod(identity['mode'])
            require(record(path) == identity and (path.stat().st_dev, path.stat().st_ino)
                    != (original.stat().st_dev, original.stat().st_ino), 'copy differs or aliases input')
            copied_bytes += identity['bytes']
        inventory[relative] = dict(original=str(original), record=identity, archived=archived,
            local_only_reason='large compiler log or full source/upstream input book' if local else None)
    require(inputs() == before, 'raw inputs changed while copying')
    require({path: record(Path(path)) for path in outputs} == outputs, 'outputs changed while copying')
    artifacts = {path: dict(record=value, archived=False,
        role='primary' if path in primary else 'bundled-checker' if Path(path).name == 'drat-trim' else 'direct-extern')
        for path, value in outputs.items()}
    copied = sum(row['archived'] is not None for row in inventory.values())
    require(copied == 179 and len(inventory) - copied == 15 and copied_bytes == 3264350
            and local_bytes == 25823904, 'archive scope changed')
    document = dict(schema='trust-cg.shared-prelude-cohort-record-archive.v1', head=HEAD, tree=TREE,
        input_book_sha256=INPUT_BOOK_SHA, input_records=194, copied_records=copied,
        copied_bytes=copied_bytes, local_only_records=15, local_only_bytes=local_bytes,
        records=inventory, artifacts=artifacts, copier=record(Path(__file__)),
        artifacts_independently_retained_by_this_archive=False, cache_release_authorized=False,
        verified_compiler=False, proof_required=False, connected_ty_qualification=False, performance_claim=False)
    with (DEST / 'inventory.json').open('x') as stream:
        json.dump(document, stream, indent=2, sort_keys=True)
        stream.write('\n')
    print(json.dumps(dict(copied=copied, local_only=15, copied_bytes=copied_bytes,
                         inventory=record(DEST / 'inventory.json')), sort_keys=True))


if __name__ == '__main__':
    main()
