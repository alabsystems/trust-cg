"""Local Git source/path controls only; no compiler or publication authority."""
from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import bump_trust_ir_pin as bump
import stage_x86_certificate_proposal as stage
import test_bump_trust_ir_pin as fixtures

_, IR_TARGET = bump.IR_VERSION_MIGRATION
_, CLEAN_TARGET = bump.CLEAN_VERSION_MIGRATION


def git(root, *arguments):
    env = {key: value for key, value in os.environ.items() if not key.startswith('GIT_')}
    env.update(GIT_CONFIG_GLOBAL='/dev/null', GIT_CONFIG_NOSYSTEM='1', GIT_NO_LAZY_FETCH='1')
    result = subprocess.run(['git', '-C', str(root), '-c', 'user.name=SourceFixture',
                             '-c', 'user.email=source-fixture@example.invalid', *arguments],
                            capture_output=True, text=True, env=env)
    if result.returncode:
        raise AssertionError(result.stderr)
    return result.stdout.strip()


class ProposalTests(unittest.TestCase):
    def setUp(self):
        # Reuse the independent existing canonical pin-data fixture, without
        # invoking its synthetic authority, resolver or compiler commands.
        self.canonical = fixtures.TransactionTests()
        self.canonical.setUp()
        self.addCleanup(self.canonical.doCleanups)
        self.root = self.canonical.root
        for relative in bump.OWNED:
            path = self.root / relative
            path.write_bytes(path.read_bytes().replace(b'0.26.0', b'0.27.0'))
        git(self.root, 'init', '--quiet', '--template=')
        git(self.root, 'add', '.')
        git(self.root, 'commit', '--quiet', '-m', 'canonical synthetic source data')
        self.before = bump.snapshot(self.root)
        temporary = tempfile.TemporaryDirectory(prefix='test-certificate-source-')
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name).resolve()
        self.ay, self.ay_rev = self.repository('CandidateAY', {
            'Cargo.toml': '[workspace.package]\nversion="0.28.0"\n'})
        declarations = '\n'.join(f'{name}={{git="{bump.AY_URL}", rev="{self.ay_rev}", version="0.28.0"}}'
                                 for name in ('ay', 'ay-core', 'ay-dpll', 'ay-proof', 'ay-frontend',
                                              'ay-translate', 'ay-lean-bridge'))
        self.clean, self.clean_rev = self.repository('CandidateClean', {
            'Cargo.toml': (f'[workspace.package]\nversion="{CLEAN_TARGET}"\n'
                           '[workspace.dependencies]\n' + declarations)})
        core = ('[dependencies]\nclean-kernel={git="' + bump.CLEAN_URL + '",rev="'
                + self.clean_rev + f'",version="{CLEAN_TARGET}"}}\n')
        self.ir, self.ir_rev = self.repository('CandidateIR', {
            'Cargo.toml': f'[workspace.package]\nversion="{IR_TARGET}"\n',
            'crates/trust-ir/Cargo.toml': core,
            'crates/trust-ir-build/Cargo.toml': core,
            'crates/trust-ir-ay/Cargo.toml': '[dependencies]\n' + '\n'.join(
                f'{name}={{git="{bump.AY_URL}", rev="{self.ay_rev}", version="0.28.0"}}'
                for name in ('ay', 'ay-proof')),
            'crates/trust-ir/src/request/evidence.rs': '// candidate source DATA, not a checked rule\n'})
        self.output = self.directory / 'proposal'

    def repository(self, name, files):
        root = self.directory / name
        root.mkdir()
        git(root, 'init', '--quiet', '--template=')
        for relative, text in files.items():
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        git(root, 'add', '.')
        git(root, 'commit', '--quiet', '-m', 'immutable candidate source data')
        return root, git(root, 'rev-parse', 'HEAD')

    def sources(self):
        return (stage.ObjectData(self.ir, self.ir_rev), stage.ObjectData(self.clean, self.clean_rev),
                stage.ObjectData(self.ay, self.ay_rev))

    def invoke(self, output=None):
        stage.stage(self.root, *self.sources(), self.output if output is None else output, '0.28.0',
                    ir_version=IR_TARGET, clean_version=CLEAN_TARGET)

    def unchanged(self):
        self.assertEqual(bump.snapshot(self.root), self.before)

    def test_cli_only_writes_unadmitted_data_and_returns_four(self):
        argv = ['--root', str(self.root), '--ir-objects', str(self.ir), '--ir-revision', self.ir_rev,
                '--clean-objects', str(self.clean), '--clean-revision', self.clean_rev,
                '--ay-objects', str(self.ay), '--ay-revision', self.ay_rev,
                '--ay-version', '0.28.0', '--ir-version', IR_TARGET,
                '--clean-version', CLEAN_TARGET, '--output', str(self.output)]
        with (patch.object(bump, 'Authority', side_effect=AssertionError('no authority phase')),
              patch.object(bump, 'Commands', side_effect=AssertionError('no execution phase')),
              redirect_stdout(io.StringIO())):
            self.assertEqual(stage.main(argv), 4)
        receipt = json.loads((self.output / 'proposal.json').read_text())
        self.assertEqual((receipt['status'], receipt['exit']), ('UNADMITTED', 4))
        self.assertEqual(receipt['selected_versions'], {
            'trust-ir': IR_TARGET, 'clean': CLEAN_TARGET, 'ay': '0.28.0'})
        self.assertEqual(len(receipt['proposed_files']), 5)
        self.assertIn(self.ir_rev, (self.output / 'Cargo.toml').read_text())
        self.assertIn(f'version = "{CLEAN_TARGET}"',
                      (self.output / bump.VERIFY).read_text())
        for lock in bump.LOCKS:
            self.assertFalse((self.output / lock).exists())
        self.unchanged()

    def test_version_moves_require_both_explicit_reviewed_selections(self):
        for ir_version, clean_version, message in (
                (None, CLEAN_TARGET, 'TrustIR package version'),
                (IR_TARGET, None, 'Clean package version')):
            with self.subTest(ir_version=ir_version, clean_version=clean_version), \
                    self.assertRaisesRegex(bump.Refusal, message):
                stage.stage(self.root, *self.sources(), self.output, '0.28.0',
                            ir_version=ir_version, clean_version=clean_version)
            self.assertFalse(self.output.exists())
            self.unchanged()

    def test_actual_git_objects_ignore_dirty_working_tree(self):
        (self.ir / 'Cargo.toml').write_text('not the committed source')
        self.invoke()
        receipt = json.loads((self.output / 'proposal.json').read_text())
        self.assertEqual(receipt['source_objects']['trust-ir']['revision'], self.ir_rev)
        self.unchanged()

    def test_nested_source_selector_is_refused(self):
        with self.assertRaises(bump.Refusal):
            stage.ObjectData(self.ir / 'crates', self.ir_rev)
        self.assertFalse(self.output.exists())
        self.unchanged()

    def test_dot_git_selector_cannot_hide_the_worktree(self):
        with self.assertRaises(bump.Refusal):
            stage.ObjectData(self.ir / '.git', self.ir_rev)
        self.assertFalse(self.output.exists())

    def test_explicit_bare_data_store_is_supported(self):
        bare = self.directory / 'candidate.git'
        git(self.directory, 'clone', '--bare', '--quiet', '--no-hardlinks', str(self.ir), str(bare))
        data = stage.ObjectData(bare, self.ir_rev)
        self.assertEqual(data.read('Cargo.toml')['workspace']['package']['version'], IR_TARGET)
        with self.assertRaises(bump.Refusal):
            stage.stage(self.root, data, *self.sources()[1:], bare / 'output', '0.28.0',
                        ir_version=IR_TARGET, clean_version=CLEAN_TARGET)
        self.unchanged()

    def test_output_inside_actual_source_root_is_refused(self):
        for source in (self.root, self.ir, self.clean, self.ay, self.ir / '.git'):
            with self.subTest(source=source), self.assertRaises(bump.Refusal):
                self.invoke(source / 'output')
            self.assertFalse((source / 'output').exists())
        self.unchanged()

    def test_case_alias_cannot_hide_output_inside_source(self):
        alias = self.ir.with_name(self.ir.name.swapcase())
        if not alias.exists() or not os.path.samefile(alias, self.ir):
            self.skipTest('filesystem does not expose case aliases')
        with self.assertRaises(bump.Refusal):
            self.invoke(alias / 'output')
        self.assertFalse((self.ir / 'output').exists())
        self.unchanged()

    def test_existing_output_is_not_reused_or_clobbered(self):
        self.output.mkdir()
        sentinel = self.output / 'existing'
        sentinel.write_text('preserve')
        with self.assertRaises(bump.Refusal):
            self.invoke()
        self.assertEqual(sentinel.read_text(), 'preserve')
        self.unchanged()

    def test_symlink_output_parent_is_refused(self):
        alias = self.directory / 'alias'
        alias.symlink_to(self.directory, target_is_directory=True)
        with self.assertRaises(bump.Refusal):
            self.invoke(alias / 'proposal')
        self.assertFalse(self.output.exists())

    def test_symlink_manifest_is_refused(self):
        path = self.ir / 'Cargo.toml'
        path.unlink()
        path.symlink_to('other.toml')
        (self.ir / 'other.toml').write_text(f'[workspace.package]\nversion="{IR_TARGET}"\n')
        git(self.ir, 'add', '.')
        git(self.ir, 'commit', '--quiet', '-m', 'symlink source control')
        data = stage.ObjectData(self.ir, git(self.ir, 'rev-parse', 'HEAD'))
        with self.assertRaisesRegex(bump.Refusal, 'regular blob'):
            data.read('Cargo.toml')

    def test_manifest_precedence_is_refused(self):
        (self.ir / 'Targo.toml').write_text(f'[workspace.package]\nversion="{IR_TARGET}"\n')
        git(self.ir, 'add', '.')
        git(self.ir, 'commit', '--quiet', '-m', 'precedence source control')
        with self.assertRaisesRegex(bump.Refusal, 'precedence'):
            stage.ObjectData(self.ir, git(self.ir, 'rev-parse', 'HEAD')).read('Cargo.toml')

    def test_replacement_refs_do_not_replace_candidate_source(self):
        (self.ir / 'Cargo.toml').write_text('[workspace.package]\nversion="999.0.0"\n')
        git(self.ir, 'add', '.')
        git(self.ir, 'commit', '--quiet', '-m', 'replacement control')
        git(self.ir, 'replace', self.ir_rev, git(self.ir, 'rev-parse', 'HEAD'))
        self.invoke()
        self.unchanged()

    def test_wrong_coowner_refuses_without_output(self):
        (self.clean / 'Cargo.toml').write_text(
            f'[workspace.package]\nversion="{CLEAN_TARGET}"\n')
        git(self.clean, 'add', '.')
        git(self.clean, 'commit', '--quiet', '-m', 'wrong owner control')
        self.clean_rev = git(self.clean, 'rev-parse', 'HEAD')
        with self.assertRaisesRegex(bump.Refusal, 'ownership'):
            self.invoke()
        self.assertFalse(self.output.exists())
        self.unchanged()


if __name__ == '__main__':
    unittest.main()
