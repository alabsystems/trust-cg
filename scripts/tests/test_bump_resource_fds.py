import importlib.util
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
import bump_trust_ir_pin as pin


class ResourceDescriptorTests(unittest.TestCase):
    """Transport parser controls; these grant no native scheduler/SDK authority."""

    def test_absent_advertisements_do_not_select_unrelated_descriptors(self):
        with tempfile.TemporaryFile() as owned:
            self.assertEqual(pin.resource_fds({}), ())
            self.assertGreaterEqual(owned.fileno(), 3)

    def test_closed_advertised_descriptor_refuses(self):
        with tempfile.TemporaryFile() as owned:
            duplicate = os.dup(owned.fileno())
            os.close(duplicate)
            with self.assertRaisesRegex(pin.Refusal, "descriptor is not live"):
                pin.resource_fds({"BUILD_SLOT_FENCE_FDS": str(duplicate)})

    def test_malformed_standard_and_duplicate_locators_refuse(self):
        for environment in [
            {"ATERM_SDK_LEASE_V3": "1"},
            {"TRUST_CPU_IMPLICIT_FD": "-1"},
            {"ATERM_WORKLOAD_CPU_FDS_V1": "3,3"},
            {"BUILD_SLOT_FENCE_FDS": ""},
            {"CARGO_MAKEFLAGS": "--jobserver-auth=0,1"},
        ]:
            with self.subTest(environment=environment):
                with self.assertRaises(pin.Refusal):
                    pin.resource_fds(environment)

    def test_out_of_native_range_descriptors_refuse(self):
        with tempfile.TemporaryFile() as owned:
            too_large = "9999999999"
            advertisements = [
                {name: too_large} for name in (
                    "ATERM_SDK_LEASE_V3", "ATERM_WORKLOAD_HOST_STORE_FD_V1",
                    "TRUST_CPU_IMPLICIT_FD", "ATERM_WORKLOAD_CPU_FDS_V1",
                    "BUILD_SLOT_FENCE_FDS",
                )
            ] + [
                {name: f"--jobserver-auth={owned.fileno()},{too_large}"}
                for name in ("CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS")
            ]
            for environment in advertisements:
                with self.subTest(environment=environment):
                    with self.assertRaisesRegex(pin.Refusal, "descriptor is not live"):
                        pin.resource_fds(environment)

    @unittest.skipUnless(os.name == "posix", "POSIX descriptor inheritance")
    def test_launcher_preserves_only_advertised_pipe_descriptors(self):
        read_fd, write_fd = os.pipe()
        try:
            with tempfile.TemporaryDirectory() as temporary, tempfile.TemporaryFile() as unrelated:
                os.set_inheritable(unrelated.fileno(), True)
                os.write(write_fd, b"x")
                child = r"""
import errno
import os
import sys
read_fd, write_fd, unrelated_fd = map(int, sys.argv[1:])
assert os.read(read_fd, 1) == b"x"
os.fstat(write_fd)
try:
    os.fstat(unrelated_fd)
except OSError as error:
    assert error.errno == errno.EBADF
else:
    raise AssertionError("unadvertised descriptor inherited")
print("advertised-only")
"""
                environment = {
                    "PATH": os.defpath,
                    "CARGO_MAKEFLAGS": f"--jobserver-auth={read_fd},{write_fd}",
                }
                with mock.patch.dict(os.environ, environment, clear=True):
                    commands = pin.Commands(Path(temporary), Path(temporary) / "unused-targo")
                    output = commands.run(
                        [sys.executable, "-I", "-c", child, str(read_fd),
                         str(write_fd), str(unrelated.fileno())],
                        cwd=Path(temporary), capture=True,
                    )
                self.assertEqual(output, "advertised-only\n")
        finally:
            os.close(read_fd)
            os.close(write_fd)

    def test_effective_jobserver_ignores_obsolete_closed_pipes(self):
        read_fd, write_fd = os.pipe()
        try:
            closed = os.dup(read_fd)
            os.close(closed)
            active = f"{read_fd},{write_fd}"
            obsolete = f"{closed},{closed}"
            flags = [
                f"--jobserver-auth={obsolete} --jobserver-auth={active}",
                f"--jobserver-fds={obsolete} --jobserver-fds={active}",
                f"--jobserver-auth={active} --jobserver-fds={obsolete}",
            ]
            for name in ("CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS"):
                for value in flags:
                    with self.subTest(name=name, flags=value):
                        self.assertEqual(pin.resource_fds({name: value}), (read_fd, write_fd))
        finally:
            os.close(read_fd)
            os.close(write_fd)

    def test_effective_jobserver_non_pipe_auth_never_revives_old_pipes(self):
        read_fd, write_fd = os.pipe()
        try:
            active = f"{read_fd},{write_fd}"
            flags = [
                f"--jobserver-auth={active} --jobserver-auth={last}"
                for last in ("-1,-1", f"-1,{write_fd}", "fifo:/not-opened", "native-semaphore", "")
            ] + [f"--jobserver-auth=-1,-1 --jobserver-fds={active}"]
            for name in ("CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS"):
                for value in flags:
                    with self.subTest(name=name, flags=value):
                        self.assertEqual(pin.resource_fds({name: value}), ())
        finally:
            os.close(read_fd)
            os.close(write_fd)

    def test_fifo_and_native_handoff_are_left_to_native_owner(self):
        self.assertEqual(pin.resource_fds({
            "CARGO_MAKEFLAGS": "-j --jobserver-auth=fifo:/not-opened-by-parser",
            "CARGO_JOBSERVER_HANDOFF": "opaque-native-owner-description",
        }), ())


if __name__ == "__main__":
    unittest.main()
