#!/usr/bin/env python3
"""Print the AArch64 native-test host matrix, or check its consistency.

Every `crates/trust-cg-codegen/tests/*.rs` integration target that links and
runs AArch64 code through a host C compiler/linker is classified by the hosts
on which that native execution is compiled in and not gated off: AArch64
macOS (Mach-O) and AArch64 Linux GNU (ELF). Membership in the required Linux
floor comes from `scripts/check_linux_aarch64.py` TARGETS.

The classification is static source evidence, not an execution record: a
host marked "yes" still has to run the target (a runtime SKIP there is a
failure under the floor runners). The default mode prints the table to stdout;
nothing is committed. `--check` prints nothing and fails when a floor target is
not Linux-capable by this classification, or when an override, static-only
entry or table row is stale.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path
import re
import sys
from typing import Iterable


ROOT = Path(__file__).resolve().parents[1]
TESTS = ROOT / "crates" / "trust-cg-codegen" / "tests"
FLOOR_SCRIPT = ROOT / "scripts" / "check_linux_aarch64.py"
CODEGEN = "trust-cg-codegen"

# Host cfg facts, with the crate's default `verify` feature enabled.
HOSTS = {
    "macos": {
        "target_arch": {"aarch64"}, "target_os": {"macos"}, "target_env": {""},
        "target_family": {"unix"}, "target_vendor": {"apple"},
        "target_endian": {"little"}, "target_pointer_width": {"64"},
        "feature": {"verify"}, "unix": True, "windows": False, "test": True,
        "debug_assertions": True,
    },
    "linux": {
        "target_arch": {"aarch64"}, "target_os": {"linux"}, "target_env": {"gnu"},
        "target_family": {"unix"}, "target_vendor": {"unknown"},
        "target_endian": {"little"}, "target_pointer_width": {"64"},
        "feature": {"verify"}, "unix": True, "windows": False, "test": True,
        "debug_assertions": True,
    },
}

# Link-and-run evidence: a host C compiler/linker driver or a shared runner.
NATIVE_MARKERS = re.compile(
    r'Command::new\(\s*(?:"(?:cc|c\+\+|clang|gcc|/usr/bin/clang|/usr/bin/cc)"'
    r"|native_host::C_COMPILER|&?compiler|cc|lldb)\s*\)"
    r"|\blink_run\s*\(|\brun_executable_with_timeout\s*\("
    r"|macho::linker::(?:\{[^}]*\blink\b|link\b)"
)
AARCH64 = re.compile(r'aarch64|arm64|AArch64|Aarch64')
NON_AARCH64_NAME = re.compile(r"x86|x64|riscv|wasm|coff|windows", re.IGNORECASE)
SHARED_HARNESS = re.compile(r'#\[path\s*=\s*"common/(?:native_host|aarch64_native)\.rs"\]')
HOST_AWARE_ELSE = re.compile(r'if\s+cfg!\(\s*target_os\s*=\s*"macos"\s*\)\s*\{')
LINUX_OBJECT = re.compile(r'"aarch64-unknown-linux-gnu"|ElfWriter|"-no-pie"')
PATH_INCLUDE = re.compile(r'#\[path\s*=\s*"([^"]+)"\]')

# Files whose single-host native execution is deliberate, with the reason.
# Keys absent here that classify single-host are listed as open.
HOST_SPECIFIC = {
    "e2e_aarch64_elf_link.rs": "ELF static/shared linking and exception passthrough semantics.",
    "e2e_aarch64_elf_tlsie.rs": "ELF TLS initial-exec relocations and glibc thread state.",
    "e2e_aarch64_eh_linux.rs": "ELF .eh_frame/.gcc_except_table landing pads linked with libstdc++/libgcc_s "
    "and Rust std, read back by GNU/LLVM tools; the Mach-O EH controls are the shared e2e_aarch64_eh_* targets.",
    "e2e_aarch64_variadic_linux.rs": "Generic AAPCS64 va_list/register-save variadics (Apple passes variadics on the stack).",
    "e2e_aarch64_aggregate_stack_linux.rs": "Generic AAPCS64 8-byte stack slots (Apple packs stack arguments).",
    "e2e_aarch64_bool_abi_linux.rs": "Generic AAPCS64 callee-side narrow-argument extension (Apple callers extend).",
    "e2e_aarch64_variadic_call.rs": "Apple variadic ABI (all variadic arguments on the stack).",
    "e2e_aarch64_variadic_darwin.rs": "DarwinPCS twin of e2e_aarch64_variadic_linux (anonymous "
    "arguments on the stack through Apple's char* va_list).",
    "e2e_aarch64_aggregate_stack_darwin.rs": "DarwinPCS twin of e2e_aarch64_aggregate_stack_linux "
    "(natural-size packing, odd-register pairs, clang's composite coercion).",
    "e2e_aarch64_bool_abi_darwin.rs": "DarwinPCS twin of e2e_aarch64_bool_abi_linux (caller and "
    "callee extension to 32 bits, Apple assembly callers and probes).",
    "e2e_aarch64_swift_aggregate.rs": "Apple Swift calling convention.",
    "e2e_aarch64_swift_scalar.rs": "Apple Swift calling convention.",
    "e2e_aarch64_link.rs": "In-crate Mach-O linker.",
    "e2e_native_link.rs": "In-crate Mach-O linker and dylib loading.",
    "aot_profile_execution.rs": "In-crate Mach-O linker for the AOT profile runtime.",
    "dialect_machine_execution.rs": "In-crate Mach-O writer and linker.",
    "stack_guard_admission.rs": "Stack canary lowering is Apple Mach-O only; the Linux triple is a pinned named refusal.",
    "e2e_aarch64_narrow_signed_cmp.rs": "The on-host A64 interpreter half parses Mach-O objects.",
    "o3_debug_lldb_line_200loc.rs": "LLDB line-table contract for Mach-O.",
    "e2e_macho_deployment_target.rs": "Mach-O LC_BUILD_VERSION deployment targets linked by ld64.",
    "macho_linked_image_evidence.rs": "Mach-O linked-image evidence records: ld64 chained-fixup and "
    "LC_DYLD_INFO images, dyld binding and the SDK's libSystem stub; its standalone-linker rows are "
    "host-neutral.",
    "e2e_aarch64_eh_raii_darwin.rs": "Mach-O compact-unwind and DWARF-fallback frames, typed catches "
    "through GOT-relocated TType slots and JIT tables registered with Darwin libunwind, against "
    "C++ and Rust reference builds; the ELF EH controls are e2e_aarch64_eh_linux.",
}

# Corrections where the static heuristic is known to be wrong, with reasons.
OVERRIDES: dict[str, tuple[bool, bool, str]] = {
    "aarch64_compile_scaling.rs": (
        True,
        False,
        "the shared harness and the C-reference link-and-run row are cfg-gated to macOS arm64; "
        "Linux GNU runs only the heap-metric cost-growth tests",
    ),
    "e2e_aarch64_memory_order_litmus.rs": (
        True,
        False,
        "the shared harness only compiles Darwin-target thread bodies there; the litmus "
        "link-and-run is cfg-gated to macOS arm64",
    ),
    "e2e_aarch64_large_aggregate_args_linux.rs": (
        False,
        True,
        "the shared harness parses objects only; the C-oracle link-and-run row is cfg-gated to "
        "Linux GNU",
    ),
}

# Files whose only native marker is a debugger or inspection tool that loads
# an object statically: no AArch64 code is linked or run, so they are not
# native link-and-run targets. Each entry must still match a native marker.
STATIC_ONLY = {
    "aarch64_elf_dwarf.rs": "lldb loads the relocatable ELF object without running it (macOS leg); "
    "its DWARF object checks run on both hosts.",
}


def strip_comments(text: str) -> str:
    """Drop `//` line comments (not inside string literals) and block comments."""
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.DOTALL)
    out = []
    for line in text.splitlines():
        in_string = False
        escaped = False
        cut = len(line)
        for index, char in enumerate(line):
            if escaped:
                escaped = False
                continue
            if char == "\\":
                escaped = True
            elif char == '"':
                in_string = not in_string
            elif not in_string and line.startswith("//", index):
                cut = index
                break
        out.append(line[:cut])
    return "\n".join(out)


def balanced(text: str, open_index: int) -> str:
    """Return the text inside the parenthesis opening at `open_index`."""
    depth = 0
    for index in range(open_index, len(text)):
        if text[index] == "(":
            depth += 1
        elif text[index] == ")":
            depth -= 1
            if depth == 0:
                return text[open_index + 1:index]
    raise ValueError("unbalanced cfg predicate")


class CfgError(ValueError):
    pass


def evaluate(predicate: str, host: dict) -> bool:
    """Evaluate a Rust cfg predicate for one host; unknown keys fail closed."""
    tokens = re.findall(r'[A-Za-z_][A-Za-z0-9_]*|"[^"]*"|[(),=]', predicate)
    position = 0

    def expression() -> bool:
        nonlocal position
        if position >= len(tokens):
            raise CfgError(f"truncated cfg predicate: {predicate!r}")
        name = tokens[position]
        position += 1
        if name in ("all", "any", "not") and position < len(tokens) and tokens[position] == "(":
            position += 1
            values = []
            while tokens[position] != ")":
                values.append(expression())
                if tokens[position] == ",":
                    position += 1
            position += 1
            if name == "all":
                return all(values)
            if name == "any":
                return any(values)
            if len(values) != 1:
                raise CfgError(f"not() takes one predicate: {predicate!r}")
            return not values[0]
        if position < len(tokens) and tokens[position] == "=":
            value = tokens[position + 1].strip('"')
            position += 2
            if name not in host or not isinstance(host[name], set):
                raise CfgError(f"unknown cfg key {name!r} in {predicate!r}")
            return value in host[name]
        if name not in host or not isinstance(host[name], bool):
            raise CfgError(f"unknown cfg flag {name!r} in {predicate!r}")
        return host[name]

    try:
        result = expression()
    except IndexError as error:
        raise CfgError(f"truncated cfg predicate: {predicate!r}") from error
    if position != len(tokens):
        raise CfgError(f"trailing tokens in cfg predicate: {predicate!r}")
    return result


def predicates(text: str, prefix: str) -> list[str]:
    found = []
    for match in re.finditer(re.escape(prefix), text):
        found.append(balanced(text, match.end() - 1))
    return found


def included_sources(path: Path, seen: set[Path] | None = None) -> str:
    """The file plus modules it includes through `#[path]`, one level deep."""
    seen = seen or set()
    seen.add(path)
    text = path.read_text(encoding="utf-8")
    parts = [text]
    for relative in PATH_INCLUDE.findall(text):
        child = (path.parent / relative).resolve()
        if child.is_file() and child not in seen and child.name != "rosetta.rs":
            seen.add(child)
            parts.append(child.read_text(encoding="utf-8"))
    return "\n".join(parts)


def floor_targets() -> set[tuple[str, str]]:
    spec = importlib.util.spec_from_file_location("check_linux_aarch64", FLOOR_SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return set(module.TARGETS)


def classify(path: Path) -> dict | None:
    """Return the host classification of one native test file, or None."""
    own = strip_comments(path.read_text(encoding="utf-8"))
    combined = strip_comments(included_sources(path))
    if NON_AARCH64_NAME.search(path.name) or not AARCH64.search(combined):
        return None
    if not NATIVE_MARKERS.search(combined):
        return None
    compiled = {
        host: all(evaluate(p, facts) for p in predicates(own, "#![cfg("))
        for host, facts in HOSTS.items()
    }
    os_predicates = [
        p for p in predicates(combined, "#[cfg(") + predicates(combined, "cfg!(")
        if "target_os" in p
    ]
    excluded = [host for host, value in compiled.items() if not value]
    if SHARED_HARNESS.search(own):
        basis = "shared native harness"
        native = dict(compiled)
    elif HOST_AWARE_ELSE.search(combined) and LINUX_OBJECT.search(combined):
        basis = "host-selected object format"
        native = dict(compiled)
    elif os_predicates:
        basis = "target_os guards"
        native = {
            host: compiled[host] and any(evaluate(p, facts) for p in os_predicates)
            for host, facts in HOSTS.items()
        }
    else:
        basis = "architecture guard only"
        native = dict(compiled)
    if excluded:
        basis = f"file cfg excludes {', '.join(excluded)}; {basis}"
    return {"name": path.name, "native": native, "basis": basis}


def rows() -> tuple[list[dict], list[str]]:
    floor = floor_targets()
    errors = []
    results = []
    for path in sorted(TESTS.glob("*.rs")):
        row = classify(path)
        target = path.stem
        in_floor = (CODEGEN, target) in floor
        if path.name in STATIC_ONLY:
            if row is None:
                errors.append(f"stale static-only entry for {path.name}: no native marker matches")
            row = None
        if row is None:
            if in_floor:
                results.append({
                    "name": path.name, "native": None, "basis": "no native link-and-run",
                    "floor": True,
                })
            continue
        if path.name in OVERRIDES:
            macos, linux, reason = OVERRIDES[path.name]
            if (row["native"]["macos"], row["native"]["linux"]) == (macos, linux):
                errors.append(f"stale override for {path.name}: heuristic already agrees")
            row["native"] = {"macos": macos, "linux": linux}
            row["basis"] = f"override: {reason}"
        row["floor"] = in_floor
        if in_floor and not row["native"]["linux"]:
            errors.append(f"floor target {target} is not Linux-capable by this classification")
        results.append(row)
    for name in list(HOST_SPECIFIC) + list(OVERRIDES) + list(STATIC_ONLY):
        if not (TESTS / name).is_file():
            errors.append(f"classification table names a missing file: {name}")
    return results, errors


def mark(value: bool) -> str:
    return "yes" if value else "no"


def render(results: Iterable[dict]) -> str:
    results = list(results)
    native = [row for row in results if row["native"] is not None]
    both = [row for row in native if row["native"]["macos"] and row["native"]["linux"]]
    macos_only = [row for row in native if row["native"]["macos"] and not row["native"]["linux"]]
    linux_only = [row for row in native if row["native"]["linux"] and not row["native"]["macos"]]
    neither = [row for row in native if not row["native"]["macos"] and not row["native"]["linux"]]
    floor_native = [row for row in native if row["floor"]]
    floor_other = [row for row in results if row["native"] is None]
    lines = [
        "# AArch64 native test host matrix",
        "",
        "Printed by `python3 scripts/native_test_host_matrix.py` from this checkout.",
        "",
        "Each `crates/trust-cg-codegen/tests/*.rs` target that links and runs AArch64",
        "code through a host C compiler/linker is classified by where that native",
        "execution is compiled in and not gated off: AArch64 macOS (Mach-O) and AArch64",
        "Linux GNU (ELF). The classification is static source evidence from file-level",
        "`cfg`, `target_os` guards and the shared harness `tests/common/native_host.rs`;",
        "it is not an execution record. \"Linux floor\" is membership in",
        "`scripts/check_linux_aarch64.py` TARGETS, whose runner rejects runtime skips.",
        "In-process JIT execution and the separate rustc bridge workspace are out of scope.",
        "",
        f"- Native files: {len(native)}; both hosts: {len(both)}; macOS only: {len(macos_only)};",
        f"  Linux GNU only: {len(linux_only)}; neither AArch64 host: {len(neither)}.",
        f"- In the Linux floor: {len(floor_native)} native files and {len(floor_other)} other codegen targets.",
        "",
        "| Test file | macOS native | Linux GNU native | Linux floor | Basis | Single-host reason |",
        "| --- | --- | --- | --- | --- | --- |",
    ]
    for row in native:
        single = row["native"]["macos"] != row["native"]["linux"]
        reason = HOST_SPECIFIC.get(row["name"], "open" if single else "")
        lines.append(
            f"| `{row['name']}` | {mark(row['native']['macos'])} | {mark(row['native']['linux'])} "
            f"| {mark(row['floor'])} | {row['basis']} | {reason} |"
        )
    if floor_other:
        lines.extend([
            "",
            "Linux floor codegen targets without native link-and-run (encoding, admission,",
            "object or in-process controls):",
            "",
        ])
        lines.extend(f"- `{row['name']}`" for row in floor_other)
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--print", action="store_true", help="print the matrix to stdout (default)")
    mode.add_argument("--check", action="store_true", help="only check the classification's consistency")
    args = parser.parse_args(argv)
    try:
        results, errors = rows()
    except (CfgError, ValueError) as error:
        print(f"native test host matrix: {error}", file=sys.stderr)
        return 1
    if not args.check:
        sys.stdout.write(render(results))
    for error in errors:
        print(f"native test host matrix: {error}", file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
