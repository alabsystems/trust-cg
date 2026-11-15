"""Pure fixture controls: no compiler, Cargo, solver, or model is invoked."""
import importlib.util
import os
from pathlib import Path
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


contract = load("sysroot_contract", HERE / "fixtures/bridge_build_probe/sysroot_contract.py")
harness = load("bridge_build_probe", HERE / "test_bridge_build_probe.py")


class SysrootContractTests(unittest.TestCase):
    root = Path("/controlled/fixture")
    target = "aarch64-unknown-linux-gnu"
    real = "/controlled/real-sysroot"

    def test_target_discovery_and_compile_roles_stay_distinct(self):
        self.assertEqual(contract.metadata_sysroot(["--print", "sysroot"], self.root, self.target),
                         self.root / "sysroot")
        self.assertEqual(contract.metadata_sysroot(["--print", "sysroot", "--target", self.target],
                                                  self.root, self.target), self.root / "target-sysroot")
        self.assertIsNone(contract.metadata_sysroot(["-Zhelp"], self.root, self.target))

    def test_wrong_missing_empty_and_extra_target_arguments_refuse(self):
        for suffix in [["--target"], ["--target", ""], ["--target", "wrong"],
                       ["--target", self.target, "extra"]]:
            with self.subTest(suffix=suffix), self.assertRaises(ValueError):
                contract.metadata_sysroot(["--print", "sysroot", *suffix], self.root, self.target)

    def test_default_target_and_both_explicit_sysroot_spellings(self):
        for name in ["target-sysroot", "explicit-sysroot"]:
            for flags in [["--sysroot", str(self.root / name)], ["--sysroot=" + str(self.root / name)]]:
                with self.subTest(flags=flags):
                    original = ["probe.rs", *flags, "-Dwarnings"]
                    expected = ["probe.rs", *( ["--sysroot", self.real] if len(flags) == 2
                                               else ["--sysroot=" + self.real]), "-Dwarnings"]
                    self.assertEqual(contract.translate_probe_sysroot(original, self.root, self.real), expected)
                    self.assertEqual(original, ["probe.rs", *flags, "-Dwarnings"])

    def test_missing_duplicate_discovery_or_arbitrary_sysroot_refuses(self):
        good = ["--sysroot", str(self.root / "target-sysroot")]
        for flags in [[], ["--sysroot"], ["--sysroot="], ["--sysroot", str(self.root / "sysroot")],
                      ["--sysroot", "/unreviewed"], good + good,
                      good + ["--sysroot=" + str(self.root / "explicit-sysroot")]]:
            with self.subTest(flags=flags), self.assertRaises(ValueError):
                contract.translate_probe_sysroot(flags, self.root, self.real)

    def test_nonabsolute_real_sysroot_refuses(self):
        with self.assertRaises(ValueError):
            contract.translate_probe_sysroot(["--sysroot", str(self.root / "target-sysroot")],
                                             self.root, "relative")

    def test_explicit_tool_inputs_never_fall_back_to_path_or_rustup(self):
        for value in [None, "trustc", "/not/a/tool"]:
            environment = {} if value is None else {"BRIDGE_PROBE_TRUSTC": value}
            with self.subTest(value=value), patch.dict(os.environ, environment, clear=True):
                with self.assertRaises(AssertionError):
                    harness.explicit_tool("BRIDGE_PROBE_TRUSTC")
        with patch.dict(os.environ, {"BRIDGE_PROBE_TRUSTC": str(Path(__file__).resolve())}, clear=True):
            self.assertEqual(harness.explicit_tool("BRIDGE_PROBE_TRUSTC"), Path(__file__).resolve())


if __name__ == "__main__":
    unittest.main(verbosity=2)
