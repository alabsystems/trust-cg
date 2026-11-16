#!/usr/bin/env python3
"""Write UNADMITTED certificate-cohort proposal data; successful staging exits 4.

This never edits the canonical cohort, resolves dependencies, runs a compiler,
authenticates publication, or constructs bump_trust_ir_pin.Authority. Explicit
version selections use the pin owner's same reviewed one-hop migrations; they
grant no additional authority. The normal public pin transaction and all eight
guards remain required after publication.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

import bump_trust_ir_pin as bump


def git_read(repository: Path, *arguments: str) -> bytes:
    environment = {key: value for key, value in os.environ.items()
                   if not key.startswith('GIT_')}
    environment.update(GIT_CONFIG_GLOBAL='/dev/null', GIT_CONFIG_NOSYSTEM='1',
                       GIT_NO_REPLACE_OBJECTS='1', GIT_NO_LAZY_FETCH='1',
                       GIT_ALLOW_PROTOCOL='file', GIT_TERMINAL_PROMPT='0')
    result = subprocess.run(['git', '--no-replace-objects', '-C', str(repository), *arguments],
                            env=environment, capture_output=True)
    bump.require(result.returncode == 0,
                 'local candidate read refused: ' + result.stderr.decode(errors='replace'))
    return result.stdout


def source_roots(repository: Path, *, worktree_required: bool = False) -> tuple[Path, tuple[Path, ...]]:
    """Require an actual worktree root or an explicit bare DATA store root."""
    repository = repository.resolve(strict=True)
    bare = git_read(repository, 'rev-parse', '--is-bare-repository').strip()
    bump.require(bare in (b'true', b'false'), 'unknown local repository kind')
    bump.require(not worktree_required or bare == b'false', 'canonical source needs a worktree root')
    gitdir = Path(os.fsdecode(git_read(repository, 'rev-parse', '--absolute-git-dir').strip())).resolve(strict=True)
    actual = (gitdir if bare == b'true' else
              Path(os.fsdecode(git_read(repository, 'rev-parse', '--show-toplevel').strip())).resolve(strict=True))
    bump.require(os.path.samefile(repository, actual),
                 'pass the actual worktree root or bare DATA store root, not a subdirectory')
    common = Path(os.fsdecode(git_read(repository, 'rev-parse', '--path-format=absolute', '--git-common-dir').strip())).resolve(strict=True)
    return actual, (actual, gitdir, common)


class ObjectData:
    """Immutable, hash-checked local Git DATA, without publication authority."""

    def __init__(self, repository: Path, revision: str):
        self.repository, self.protected_roots = source_roots(repository)
        self.revision = bump.exact_sha(revision)
        self.objects: dict[str, dict] = {}
        raw = self.object('commit', self.revision)
        match = re.match(rb'tree ([0-9a-f]{40})\n', raw)
        bump.require(match is not None, 'candidate commit has no canonical tree')
        self.tree = match[1].decode('ascii')

    def object(self, kind: str, oid: str) -> bytes:
        raw = git_read(self.repository, 'cat-file', kind, bump.exact_sha(oid))
        bump.require(hashlib.sha1(f'{kind} {len(raw)}\0'.encode('ascii') + raw).hexdigest() == oid,
                     'candidate object bytes differ from their Git identity')
        self.objects[oid] = {'kind': kind, 'bytes': len(raw),
                             'sha256': hashlib.sha256(raw).hexdigest()}
        return raw

    def blob(self, relative: str) -> bytes | None:
        bump.require(re.fullmatch(r'[A-Za-z0-9_.-]+(?:/[A-Za-z0-9_.-]+)*', relative) is not None
                     and not {'.', '..'}.intersection(relative.split('/')),
                     'unsafe candidate object path')
        tree = self.tree
        parts = relative.encode('ascii').split(b'/')
        for index, part in enumerate(parts):
            raw = self.object('tree', tree)
            entries, at = [], 0
            while at < len(raw):
                space, zero = raw.find(b' ', at), raw.find(b'\0', at)
                bump.require(at < space < zero and zero + 21 <= len(raw),
                             'malformed candidate tree')
                if raw[space + 1:zero] == part:
                    entries.append((raw[at:space], raw[zero + 1:zero + 21].hex()))
                at = zero + 21
            if not entries:
                return None
            bump.require(len(entries) == 1, 'ambiguous candidate path')
            mode, oid = entries[0]
            if index == len(parts) - 1:
                bump.require(mode in (b'100644', b'100755'),
                             'candidate input must be a regular blob')
                return self.object('blob', oid)
            bump.require(mode == b'40000', 'candidate input has a non-tree ancestor')
            tree = oid
        raise bump.Refusal('empty candidate path')

    def read(self, relative: str) -> dict:
        if Path(relative).name == 'Cargo.toml':
            bump.require(self.blob(str(Path(relative).with_name('Targo.toml'))) is None,
                         'candidate Targo manifest precedence is unsupported')
        raw = self.blob(relative)
        bump.require(raw is not None, 'candidate manifest absent: ' + relative)
        return bump.document(raw, self.revision + ':' + relative)

    def record(self) -> dict:
        return {'status': 'UNADMITTED_SOURCE_DATA', 'repository': str(self.repository),
                'revision': self.revision, 'tree': self.tree, 'objects': self.objects}


def stage(root: Path, ir: ObjectData, clean: ObjectData, ay: ObjectData,
          output: Path, ay_version: str, *, ir_version: str | None = None,
          clean_version: str | None = None) -> None:
    root, canonical_roots = source_roots(root, worktree_required=True)
    bump.require(output.is_absolute() and not output.exists() and not output.is_symlink(),
                 'proposal output must be a new absolute directory')
    bump.require(output.parent.resolve(strict=True) == output.parent
                 and all(not parent.is_symlink() for parent in output.parents),
                 'proposal output has a symlink parent')
    # Compare existing ancestor identities, not spellings: differently cased
    # paths can name the same directory on the normal macOS filesystem.
    protected = (*canonical_roots, *ir.protected_roots, *clean.protected_roots, *ay.protected_roots)
    for source in protected:
        bump.require(not any(os.path.samefile(parent, source) for parent in output.parents),
                     'proposal output must be outside every source repository')
    before = bump.snapshot(root)
    state = bump.current(root, before)
    selected_ay = bump.selected_ay_version(state, ay_version)
    selected_ir = bump.selected_ir_version(state, ir_version)
    selected_clean = bump.selected_clean_version(state, clean_version)
    current_ir = next(iter(set(state.ir_packages.values())))
    current_clean = next(iter(set(state.clean_packages.values())))
    bump.require(ir.read('Cargo.toml').get('workspace', {}).get('package', {}).get('version')
                 == selected_ir,
                 'candidate TrustIR package version differs')
    clean_revisions = set()
    for relative in ('crates/trust-ir/Cargo.toml', 'crates/trust-ir-build/Cargo.toml'):
        manifest = ir.read(relative)
        for section in ('dependencies', 'dev-dependencies'):
            for name, dependency in manifest.get(section, {}).items():
                if bump.family(name, 'clean'):
                    bump.require(name in {'clean-kernel', 'clean-mathverse', 'clean-olean', 'clean-verify'},
                                 'unsupported candidate Clean package')
                    clean_revisions.add(bump.pin(dependency, bump.CLEAN_URL, relative + ':' + name))
                    bump.require(dependency.get('version') == selected_clean,
                                 'candidate Clean package version differs')
    bump.require(clean_revisions == {clean.revision}, 'candidate Clean ownership differs')
    clean_workspace = clean.read('Cargo.toml').get('workspace', {})
    bump.require(clean_workspace.get('package', {}).get('version') == selected_clean,
                 'candidate Clean workspace version differs')
    bump.ay_dependencies(clean_workspace.get('dependencies', {}),
                         {'ay', 'ay-core', 'ay-dpll', 'ay-proof', 'ay-frontend',
                          'ay-translate', 'ay-lean-bridge'}, ay.revision, selected_ay,
                         'candidate Clean DATA')
    bump.ay_dependencies(ir.read('crates/trust-ir-ay/Cargo.toml').get('dependencies', {}),
                         {'ay', 'ay-proof'}, ay.revision, selected_ay, 'candidate IR DATA')
    bump.require(ay.read('Cargo.toml').get('workspace', {}).get('package', {}).get('version') == selected_ay,
                 'candidate AY workspace version differs')
    rule = ir.blob('crates/trust-ir/src/request/evidence.rs')
    bump.require(rule is not None, 'candidate rule source absent')
    proposal = bump.rewritten(before, state.ir, ir.revision, state.ay, ay.revision,
                              state.clean, clean.revision, state.ay_version, selected_ay,
                              old_clean_version=current_clean, new_clean_version=selected_clean,
                              old_ir_version=current_ir, new_ir_version=selected_ir)
    # Only the existing pure source rewriter produces bytes. Locks remain the
    # exact predecessor inputs: this phase makes no resolution or guard claim.
    try:
        output.mkdir(mode=0o700)
        for relative, data in proposal.items():
            path = output / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            with path.open('xb') as handle:
                handle.write(data)
            path.chmod(before[relative].mode)
        receipt = {
            'schema': 'trust-cg.x86-certificate-source-proposal.v1',
            'status': 'UNADMITTED', 'exit': 4,
            'scope': 'Source bytes only; no publication, resolution, guard, certificate or proof admission',
            'required_after_publication': 'Fresh public IR authentication, canonical pin transaction and all eight guards',
            'canonical_source': str(root),
            'canonical_inputs': {name: {'sha256': hashlib.sha256(row.data).hexdigest(), 'mode': row.mode}
                                 for name, row in before.items()},
            'selected_versions': {'trust-ir': selected_ir, 'clean': selected_clean, 'ay': selected_ay},
            'source_objects': {'trust-ir': ir.record(), 'clean': clean.record(), 'ay': ay.record()},
            'candidate_rule_source_sha256': hashlib.sha256(rule).hexdigest(),
            'proposed_files': {name: hashlib.sha256(data).hexdigest() for name, data in proposal.items()},
            'locks': 'UNCHANGED predecessor inputs; must be normally resolved and qualified separately',
        }
    finally:
        bump.unchanged(root, before)
    (output / 'proposal.json').write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--ir-objects', type=Path, required=True)
    parser.add_argument('--ir-revision', required=True)
    parser.add_argument('--clean-objects', type=Path, required=True)
    parser.add_argument('--clean-revision', required=True)
    parser.add_argument('--ay-objects', type=Path, required=True)
    parser.add_argument('--ay-revision', required=True)
    parser.add_argument('--ay-version', choices=[bump.AY_VERSION_MIGRATION[1]], required=True)
    parser.add_argument('--ir-version', choices=[bump.IR_VERSION_MIGRATION[1]])
    parser.add_argument('--clean-version', choices=[bump.CLEAN_VERSION_MIGRATION[1]])
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        stage(args.root, ObjectData(args.ir_objects, args.ir_revision),
              ObjectData(args.clean_objects, args.clean_revision),
              ObjectData(args.ay_objects, args.ay_revision), args.output, args.ay_version,
              ir_version=args.ir_version, clean_version=args.clean_version)
        print('UNADMITTED: proposal source data only; canonical transaction and all eight guards still required')
        return 4
    except (bump.Refusal, OSError, UnicodeError) as error:
        print('REFUSED: ' + str(error))
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
