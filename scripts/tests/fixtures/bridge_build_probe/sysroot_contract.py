"""Pure adapter for deliberately different discovery and compilation roots.

This models forwarding, not rustc-private ABI compatibility. Only reviewed
fixture roots may be translated to the real compiler's ordinary-Rust sysroot.
"""
from pathlib import Path


def metadata_sysroot(args, root, expected_target):
    if args == ["--print", "sysroot"]:
        return root / "sysroot"
    if args[:2] == ["--print", "sysroot"]:
        if not expected_target or args != ["--print", "sysroot", "--target", expected_target]:
            raise ValueError("fixture target sysroot query requires the exact TARGET")
        return root / "target-sysroot"
    return None


def translate_probe_sysroot(args, root, real_sysroot):
    """Retain argument order/spelling, replacing exactly one reviewed root."""
    if not Path(real_sysroot).is_absolute():
        raise ValueError("real compiler sysroot must be absolute")
    allowed = {str(root / "target-sysroot"), str(root / "explicit-sysroot")}
    result = list(args)
    roots = []
    index = 0
    while index < len(result):
        arg = result[index]
        if arg == "--sysroot":
            if index + 1 >= len(result):
                raise ValueError("missing sysroot argument")
            roots.append(result[index + 1])
            result[index + 1] = str(real_sysroot)
            index += 1
        elif arg.startswith("--sysroot="):
            roots.append(arg.removeprefix("--sysroot="))
            result[index] = "--sysroot=" + str(real_sysroot)
        index += 1
    if len(roots) != 1 or roots[0] not in allowed:
        raise ValueError("probe must use exactly one reviewed target or explicit sysroot")
    return result
