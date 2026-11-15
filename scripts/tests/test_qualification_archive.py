"""Original historical evidence stays exact without exposing Cargo packages."""
import gzip
import importlib.util
import io
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile
import tomllib
import unittest

ROOT = Path(__file__).resolve().parents[2]
RELATIVE = 'docs/qualification/2026-11-10-ir-fa04de5-sdk999-intake'
PACKET = ROOT / RELATIVE
# The public source snapshot omits docs entirely. A development tree with a
# missing/corrupt packet must fail instead of silently skipping this regression.
DEVELOPMENT_TREE = (ROOT / 'docs').is_dir()
if DEVELOPMENT_TREE:
    SPEC = importlib.util.spec_from_file_location('historical_archive', PACKET / 'check_archive.py')
    CHECKER = importlib.util.module_from_spec(SPEC)
    SPEC.loader.exec_module(CHECKER)


def pack(files, extra=None):
    data = io.BytesIO()
    with tarfile.open(fileobj=data, mode='w') as archive:
        for name, content in files.items():
            member = tarfile.TarInfo(name)
            member.mode = 0o644
            member.size = len(content)
            archive.addfile(member, io.BytesIO(content))
        if extra is not None:
            archive.addfile(extra)
    return gzip.compress(data.getvalue(), mtime=0)


@unittest.skipUnless(DEVELOPMENT_TREE, 'public snapshot: qualification docs are not exported')
class QualificationArchiveTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.files = CHECKER.read_packet(PACKET)

    def test_every_original_blob_is_preserved_without_live_manifests(self):
        prefix = '1b3e1a01fe0b7ea03ad52381a4215fe5f2541e43:' + RELATIVE + '/'
        names = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only',
                                         prefix[:-1]], cwd=ROOT, text=True).splitlines()
        self.assertEqual(set(self.files), set(names))
        for name, content in self.files.items():
            with self.subTest(name=name):
                self.assertEqual(content, subprocess.check_output(['git', 'show', prefix + name], cwd=ROOT))
        self.assertTrue(any(n.endswith('/Cargo.toml') for n in self.files))
        self.assertEqual(list(PACKET.rglob('Cargo.toml')), [])

    def test_changed_manifest_and_qualified_bytes_refuse(self):
        for name in ('ARTIFACT-HASHES.json', 'qualified-pin-files/crates/trust-cg-regalloc/Cargo.toml'):
            files = dict(self.files)
            files[name] += b'\nchanged'
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, 'changed'):
                CHECKER.decode_archive(pack(files))

    def test_missing_extra_and_duplicate_members_refuse(self):
        for files in ({k: v for k, v in self.files.items() if k != 'PLAN.json'},
                      dict(self.files, extra=b'extra')):
            with self.assertRaisesRegex(ValueError, 'inventory|extra'):
                CHECKER.decode_archive(pack(files))
        member = tarfile.TarInfo('PLAN.json')
        member.mode = 0o644
        with self.assertRaisesRegex(ValueError, 'duplicate|extra'):
            CHECKER.decode_archive(pack(self.files, member))

    def test_symlink_and_unconfined_members_refuse(self):
        for name, kind in (('../escape', tarfile.REGTYPE), ('linked', tarfile.SYMTYPE)):
            member = tarfile.TarInfo(name)
            member.mode = 0o644
            member.type = kind
            member.linkname = '/outside'
            with self.subTest(name=name), self.assertRaises(ValueError):
                CHECKER.decode_archive(pack({}, member))

    def test_decoded_size_and_truncation_refuse(self):
        with self.assertRaisesRegex(ValueError, 'decoded bound'):
            CHECKER.decode_archive(gzip.compress(b'x' * (CHECKER.MAX_BYTES + 1)))
        with self.assertRaises((EOFError, OSError)):
            CHECKER.decode_archive((PACKET / 'packet.tar.gz').read_bytes()[:100])

    def test_reintroduced_package_manifest_and_changed_linked_receipt_refuse(self):
        with tempfile.TemporaryDirectory() as directory:
            packet = Path(directory) / 'packet'
            shutil.copytree(PACKET, packet)
            (packet / 'Cargo.toml').write_text('[package]\nname="trust-cg-regalloc"\n')
            with self.assertRaisesRegex(ValueError, 'discoverable'):
                CHECKER.read_packet(packet)
            (packet / 'Cargo.toml').unlink()
            (packet / 'QUALIFICATION.json').write_text('{}')
            with self.assertRaisesRegex(ValueError, 'linked receipt'):
                CHECKER.read_packet(packet)

    def test_file_reader_bounds_input_before_decoding(self):
        with tempfile.TemporaryDirectory() as directory:
            packet = Path(directory)
            with (packet / 'packet.tar.gz').open('wb') as output:
                output.truncate(CHECKER.MAX_BYTES + 1)
            with self.assertRaisesRegex(ValueError, 'input bound'):
                CHECKER.read_packet(packet)

    def test_originally_shadowed_packages_have_one_committed_manifest(self):
        expected = {'trust-cg-regalloc': 'crates/trust-cg-regalloc/Cargo.toml',
                    'trust-cg-verify': 'crates/trust-cg-verify/Cargo.toml',
                    'rustc_codegen_trust_cg': 'crates/rustc-codegen-trust-cg/Cargo.toml'}
        found = {name: set() for name in expected}
        paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', 'HEAD'],
                                        cwd=ROOT, text=True).splitlines()
        for path in paths:
            if Path(path).name != 'Cargo.toml':
                continue
            raw = subprocess.check_output(['git', 'show', 'HEAD:' + path], cwd=ROOT)
            try:
                doc = tomllib.loads(raw.decode())
            except (ValueError, UnicodeError):
                continue
            package = doc.get('package', doc.get('project', {}))
            name = package.get('name') if isinstance(package, dict) else None
            if name in found:
                found[name].add(path)
        self.assertEqual(found, {name: {path} for name, path in expected.items()})


if __name__ == '__main__':
    unittest.main()
