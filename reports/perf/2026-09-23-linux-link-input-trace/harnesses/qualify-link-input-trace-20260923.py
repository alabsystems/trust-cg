#!/usr/bin/env python3
"""Qualifying run for the L02-P9 closure-audit residuals (Linux AArch64, 2026-09-23).

Runs the touched test targets and the repository gates on a clean checkout,
then the direct probes behind the change, then source mutants of the new
checks, and writes every log and record under RUN/records:

- records/logs: the gate logs (touched test targets, the codegen library,
  every trust-cg-cli target, cargo check, formatting, script and
  documentation gates);
- records/direct: the linkers' own input traces (GNU ld 2.42 and LLD 22) for
  each route, the audit's two boundary commands and six further routes
  through the CLI at current source (refused) with their pic twins (link and
  run), the unreadable-trace refusal, the CLI link modes (image kind read by
  readelf, exit codes), the SHT_REL probe and the TEXTREL twin;
- records/mutation: each mutant's diff and the targeted tests' logs; every
  mutant must fail at least one of them, and the file is restored after each.
  Each leg's record keeps every test panic (location and first message line),
  so the kill reason is stated, not only the kill. The no-member-bytes mutant
  (added at the 2026-09-23 repair) resolves archive-member trace lines but
  reads no member, so only a member-route control can kill it.

RUN/inputs holds the modules used: tls_lib.tmbc, tls_user.tmbc and
tls_reader_thread.tmbc are copied from
reports/perf/2026-09-23-linux-tls-model-output-guard/records/inputs; the
other inputs are written by this script. Nothing here edits the checkout
except the mutation legs, which restore it; the tree must be clean before and
after.

Usage: qualify-link-input-trace-20260923.py WORKTREE RUN
"""

from __future__ import annotations

import gzip
import hashlib
import json
import os
import platform
import re
import shutil
import struct
import subprocess
import sys
from pathlib import Path

WORKTREE = Path(sys.argv[1]).resolve()
RUN = Path(sys.argv[2]).resolve()
RECORDS = RUN / "records"
LOGS = RECORDS / "logs"
DIRECT = RECORDS / "direct"
MUTATION = RECORDS / "mutation"
INPUTS = RECORDS / "inputs"
WORK = RUN / "work"
HOME = Path.home()
PATH = os.pathsep.join(
    [
        str(HOME / ".local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23/bin"),
        str(HOME / ".cargo/bin"),
        os.environ["PATH"],
    ]
)
ENV = dict(os.environ, PATH=PATH)
RESULT = re.compile(r"^test result: .*$", re.M)
RAN = re.compile(r"^(Ran \d+ tests.*|OK.*|FAILED.*)$", re.M)
TEST_LINE = re.compile(r"^test (\S+) \.\.\. (ok|FAILED|ignored)$", re.M)
CARGO = ["cargo"]
LLD_DIR = HOME / ".local/bin"
PRIOR_INPUTS = WORKTREE / "reports/perf/2026-09-23-linux-tls-model-output-guard/records/inputs"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(WORKTREE), *args], check=True, capture_output=True, text=True
    ).stdout.strip()


def shown(text: str) -> str:
    return text.replace(str(WORK), "$WORK").replace(str(RUN), "$RUN")


def panics(stdout: str) -> list[str]:
    """Each test panic: its location line and the message's first line, so a
    mutant's record states where and why each targeted test failed."""
    lines = stdout.splitlines()
    found = []
    for index, line in enumerate(lines):
        if "panicked at" in line:
            message = lines[index + 1] if index + 1 < len(lines) else ""
            found.append(f"{line.strip()} {message.strip()}")
    return found


def run(name: str, argv: list[str], *, directory: Path = LOGS, cwd: Path = WORKTREE, timeout: int = 1500) -> dict:
    """Run one gate command, keep its complete output as DIRECTORY/NAME.log."""
    completed = subprocess.run(argv, cwd=cwd, env=ENV, capture_output=True, text=True, timeout=timeout)
    text = (
        f"$ {' '.join(argv)}\n(cwd {cwd})\n--- stdout ---\n{completed.stdout}"
        f"--- stderr ---\n{completed.stderr}--- exit {completed.returncode} ---\n"
    )
    (directory / f"{name}.log").write_text(text)
    both = completed.stdout + completed.stderr
    record = {
        "name": name,
        "argv": argv,
        "exit": completed.returncode,
        "test_results": RESULT.findall(both) or RAN.findall(both),
        "failed_tests": [test for test, status in TEST_LINE.findall(both) if status == "FAILED"],
        "panics": panics(completed.stdout),
    }
    print(f"{name}: exit {completed.returncode} {record['test_results']} {record['failed_tests']}", flush=True)
    return record


def probe(name: str, argv: list[str], cwd: Path = None, timeout: int = 300, env=None) -> dict:
    """Run one direct probe; keep command, exit, stdout and stderr in records/direct/NAME.txt."""
    cwd = cwd or WORK
    try:
        completed = subprocess.run(argv, cwd=cwd, env=env or ENV, capture_output=True, text=True, timeout=timeout)
        exit_code, stdout, stderr = completed.returncode, completed.stdout, completed.stderr
    except subprocess.TimeoutExpired:
        exit_code, stdout, stderr = "timeout", "", ""
    (DIRECT / f"{name}.txt").write_text(
        f"$ {' '.join(shown(a) for a in argv)}\n(cwd {shown(str(cwd))})\n--- stdout ---\n{shown(stdout)}"
        f"--- stderr ---\n{shown(stderr)}--- exit {exit_code} ---\n"
    )
    print(f"probe {name}: exit {exit_code}", flush=True)
    return {"name": name, "argv": [shown(a) for a in argv], "exit": exit_code, "stdout": shown(stdout), "stderr": shown(stderr)}


def listing(directory: Path) -> list[str]:
    return sorted(p.name for p in directory.iterdir())


def tool(name: str, argv: list[str]) -> dict:
    path = shutil.which(argv[0], path=PATH) if "/" not in argv[0] else argv[0]
    resolved = Path(path).resolve() if path else None
    version = subprocess.run(argv, capture_output=True, text=True, env=ENV)
    text = version.stdout or version.stderr
    return {
        "name": name,
        "path": path,
        "resolved": str(resolved) if resolved else None,
        "sha256": sha256(resolved) if resolved else None,
        "version": text.splitlines()[0] if text else "",
    }


def as_sht_rel(data: bytes) -> bytes:
    """DATA with every SHT_RELA section rewritten as SHT_REL (zero addends only)."""
    out = bytearray(data)
    shoff = struct.unpack_from("<Q", out, 40)[0]
    shentsize, shnum = struct.unpack_from("<HH", out, 58)
    for index in range(shnum):
        header = shoff + index * shentsize
        if struct.unpack_from("<I", out, header + 4)[0] != 4:
            continue
        offset, size = struct.unpack_from("<QQ", out, header + 24)
        entries = [struct.unpack_from("<QQq", out, offset + 24 * k) for k in range(size // 24)]
        assert all(addend == 0 for _, _, addend in entries)
        packed = b"".join(struct.pack("<QQ", o, i) for o, i, _ in entries)
        out[offset:offset + len(packed)] = packed
        struct.pack_into("<I", out, header + 4, 9)
        struct.pack_into("<Q", out, header + 32, len(packed))
        struct.pack_into("<Q", out, header + 56, 16)
    return bytes(out)


ANSWER = """; TrustIr text format v1
module "tcg_cli_answer_main"

functy.0 = () -> (i32)

fn @main(functy.0) {
bb0:
    %0 = const i32 42
    ret %0
}
"""
START = "    .text\n    .globl _start\n    .type _start, %function\n_start:\n    bl main\n    mov x8, #93\n    svc #0\n"
TEXTREL = "    .section .rodata\n    .globl tcg_textrel_table\n    .p2align 3\ntcg_textrel_table:\n    .quad puts\n"
PLAIN_MAIN = "int main(void) { return 0; }\n"


def gates() -> list[dict]:
    cargo = [*CARGO]
    locked = ["--locked", "--offline", "-j", "8"]
    return [
        run("check-fmt", ["bash", "scripts/check_fmt.sh"]),
        run("check-codegen", [*cargo, "check", "-p", "trust-cg-codegen", *locked]),
        run("check-codegen-verify", [*cargo, "check", "-p", "trust-cg-codegen", "--features", "verify", *locked]),
        run("check-lower", [*cargo, "check", "-p", "trust-cg-lower", *locked]),
        run("test-codegen-lib", [*cargo, "test", "-p", "trust-cg-codegen", "--lib", *locked], timeout=2400),
        run("test-e2e_aarch64_elf_tlsie", [*cargo, "test", "-p", "trust-cg-codegen", "--test", "e2e_aarch64_elf_tlsie", *locked]),
        run("test-e2e_aarch64_link_runtime", [*cargo, "test", "-p", "trust-cg-codegen", "--test", "e2e_aarch64_link_runtime", *locked]),
        run("test-cli-all", [*cargo, "test", "-p", "trust-cg-cli", *locked], timeout=2400),
        run(
            "script-gate-tests",
            [
                "python3", "-B", "-m", "unittest",
                "scripts/tests/test_linux_aarch64_gate.py",
                "scripts/tests/test_darwin_aarch64_gate.py",
                "scripts/tests/test_linux_aarch64_bridge_gate.py",
            ],
        ),
        run("native-test-host-matrix", ["python3", "scripts/native_test_host_matrix.py", "--check"]),
        run("check-documentation", ["python3", "scripts/check_documentation.py", "--check"]),
        run("diagnostics-inventory", ["python3", "scripts/generate_diagnostics_inventory.py", "--check"]),
        run("evidence-plan-citations", ["python3", "scripts/check_evidence_archive.py", "--plan"]),
    ]


def direct(trust_cg: str) -> dict:
    results: dict = {"probes": [], "checks": {}}
    P = results["probes"]
    check = results["checks"]
    lld_env = dict(ENV, PATH=os.pathsep.join([str(LLD_DIR), PATH]))
    for name in ("tls_lib", "tls_user", "tls_reader_thread"):
        data = gzip.decompress((PRIOR_INPUTS / f"{name}.tmbc.gz").read_bytes())
        (INPUTS / f"{name}.tmbc").write_bytes(data)
        (WORK / f"{name}.tmbc").write_bytes(data)
    for name, text in (("answer.trust_ir", ANSWER), ("start.s", START), ("textrel.s", TEXTREL), ("plain_main.c", PLAIN_MAIN)):
        (INPUTS / name).write_text(text)
        (WORK / name).write_text(text)
    for flavor, model in (("le", "static"), ("pic", "pic")):
        (WORK / flavor).mkdir()
        P.append(probe(f"compile-{flavor}", [trust_cg, "-c", "--relocation-model", model, "-o", f"{flavor}/tcgtls.o", "tls_lib.tmbc"]))
        P.append(probe(f"ar-{flavor}-regular", ["ar", "rcs", f"{flavor}/libtcgarc.a", f"{flavor}/tcgtls.o"]))
        P.append(probe(f"ar-{flavor}-thin", ["ar", "rcsT", f"{flavor}/libtcgthin.a", f"{flavor}/tcgtls.o"]))
        (WORK / flavor / "input.ld").write_text(f"INPUT({WORK / flavor}/tcgtls.o)\n")
        (WORK / flavor / "group.ld").write_text(f"GROUP({WORK / flavor}/libtcgarc.a)\n")
        shutil.copy(WORK / flavor / "tcgtls.o", INPUTS / f"{flavor}-tcgtls.o")
    shutil.copy(WORK / "le/tcgtls.o", WORK / "le.o")
    shutil.copy(WORK / "pic/tcgtls.o", WORK / "pic.o")
    P.append(probe("compile-reader-pic", [trust_cg, "-c", "--relocation-model", "pic", "-o", "reader.o", "tls_reader_thread.tmbc"]))

    # 1. The linkers' own traces (outside the driver), one route each.
    routes = {
        "member": ["-L", "le", "-l", "tcgarc"],
        "thin": ["-Wl,--whole-archive,le/libtcgthin.a,--no-whole-archive"],
        "input": ["-Wl,le/input.ld"],
        "wl": ["-Wl,le.o"],
    }
    for linker, env, flags in (("gnu", ENV, []), ("lld", lld_env, ["-fuse-ld=lld", f"-B{LLD_DIR}"])):
        for route, args in routes.items():
            P.append(probe(
                f"trace-{linker}-{route}",
                ["cc", *flags, "-Wl,--trace,--trace", "-shared", "-o", f"raw-{linker}-{route}.so", "reader.o", *args],
                env=env,
            ))
    check["gnu_member_line"] = any("(le/libtcgarc.a)tcgtls.o" in p["stdout"] for p in P if p["name"] == "trace-gnu-member")
    check["lld_member_line"] = any("le/libtcgarc.a(tcgtls.o)" in p["stdout"] for p in P if p["name"] == "trace-lld-member")
    check["gnu_links_every_raw_route"] = all(p["exit"] == 0 for p in P if p["name"].startswith("trace-gnu-"))
    check["lld_refuses_every_raw_route"] = all(p["exit"] != 0 for p in P if p["name"].startswith("trace-lld-"))

    # 2. The CLI at current source: the audit's two commands, then six more
    # routes; each refused with no output. Pic twins link and run.
    cli_routes = {
        "wl": ["-Wl,le.o"],
        "lcolon": ["-L", ".", "-l", ":le.o"],
        "member": ["-L", "le", "-l", "tcgarc"],
        "whole": ["-Wl,--whole-archive,le/libtcgarc.a,--no-whole-archive"],
        "thin": ["-Wl,--whole-archive,le/libtcgthin.a,--no-whole-archive"],
        "input": ["-Wl,le/input.ld"],
        "group": ["-Wl,le/group.ld"],
        "startgroup": ["-Wl,--start-group,le.o,--end-group"],
    }
    before = listing(WORK)
    for route, args in cli_routes.items():
        P.append(probe(f"cli-route-{route}", [trust_cg, "--shared", "--relocation-model", "pic", "-o", f"libtcg{route}.so", *args, "tls_reader_thread.tmbc"]))
    after = listing(WORK)
    (DIRECT / "state-after-refused-routes.txt").write_text(json.dumps({"before": before, "after": after}, indent=2) + "\n")
    refused = [p for p in P if p["name"].startswith("cli-route-")]
    check["cli_routes_refused"] = all(
        p["exit"] == 1 and p["stderr"].count("error[link:") == 1 and "[TCG-LINK-TLS-MODEL]" in p["stderr"]
        for p in refused
    )
    check["cli_routes_left_nothing"] = before == after
    pic_routes = {
        "wl": ["-Wl,pic.o"],
        "lcolon": ["-L", ".", "-l", ":pic.o"],
        "member": ["-L", "pic", "-l", "tcgarc"],
        "whole": ["-Wl,--whole-archive,pic/libtcgarc.a,--no-whole-archive"],
        "thin": ["-Wl,--whole-archive,pic/libtcgthin.a,--no-whole-archive"],
        "input": ["-Wl,pic/input.ld"],
        "group": ["-Wl,pic/group.ld"],
        "startgroup": ["-Wl,--start-group,pic.o,--end-group"],
    }
    assert pic_routes.keys() == cli_routes.keys()
    for route, pic_args in pic_routes.items():
        P.append(probe(f"cli-pic-{route}", [trust_cg, "--shared", "--relocation-model", "pic", "-o", f"libtcgpic{route}.so", *pic_args, "tls_reader_thread.tmbc"]))
        P.append(probe(f"cli-user-{route}", [trust_cg, "-o", f"user_{route}", "-L", ".", "-l", f"tcgpic{route}", "--rpath", str(WORK), "tls_user.tmbc"]))
        P.append(probe(f"run-user_{route}", [f"./user_{route}"]))
    check["pic_twins_run_42"] = all(p["exit"] == 42 for p in P if p["name"].startswith("run-user_"))
    for library in ("libtcgpicwl.so", "libtcgpicmember.so"):
        P.append(probe(f"readelf-r-{library}", ["readelf", "-rW", library]))

    # 3. An unreadable trace refuses a shared object.
    for name, flag in (("verbose", "-Wl,--verbose"), ("map", "-Wl,-M")):
        P.append(probe(f"cli-trace-{name}", [trust_cg, "--shared", "--relocation-model", "pic", "-o", f"libtcgtrace{name}.so", flag, "tls_reader_thread.tmbc"]))
    check["unreadable_trace_refused"] = all(
        p["exit"] == 1 and "[TCG-LINK-INPUT-TRACE]" in p["stderr"] and p["stderr"].count("error[link:") == 1
        for p in P if p["name"].startswith("cli-trace-")
    )

    # 4. CLI link modes.
    P.append(probe("assemble-start", ["cc", "-c", "-o", "start.o", "start.s"]))
    modes = {
        "default": ([], "tls_prog"),
        "pie": (["--pie"], "tls_prog"),
        "no_pie": (["--no-pie"], "tls_prog"),
        "static": (["--static"], "tls_prog"),
        "nostdlib": (["--format=text", "--nostdlib", "-Wl,start.o"], "answer"),
        "nostdlib_static": (["--format=text", "--nostdlib", "--static", "-Wl,start.o"], "answer"),
    }
    (WORK / "tls_prog.tmbc").write_bytes(gzip.decompress((PRIOR_INPUTS / "tls_prog.tmbc.gz").read_bytes()))
    (INPUTS / "tls_prog.tmbc").write_bytes((WORK / "tls_prog.tmbc").read_bytes())
    for mode, (flags, program) in modes.items():
        source = "answer.trust_ir" if program == "answer" else "tls_prog.tmbc"
        P.append(probe(f"cli-mode-{mode}", [trust_cg, *flags, "-o", f"mode_{mode}", source]))
        P.append(probe(f"readelf-h-mode_{mode}", ["readelf", "-hW", f"mode_{mode}"]))
        P.append(probe(f"readelf-l-mode_{mode}", ["readelf", "-lW", f"mode_{mode}"]))
        P.append(probe(f"readelf-d-mode_{mode}", ["readelf", "-dW", f"mode_{mode}"]))
        P.append(probe(f"run-mode_{mode}", [f"./mode_{mode}"]))
    kinds = {}
    for mode in modes:
        header = next(p for p in P if p["name"] == f"readelf-h-mode_{mode}")["stdout"]
        segments = next(p for p in P if p["name"] == f"readelf-l-mode_{mode}")["stdout"]
        kind = re.search(r"Type:\s+(.*)", header).group(1).strip()
        kinds[mode] = {
            "type": kind,
            "interp": any(line.strip().startswith("INTERP ") for line in segments.splitlines()),
            "exit": next(p for p in P if p["name"] == f"run-mode_{mode}")["exit"],
        }
    check["mode_kinds"] = kinds
    check["modes_as_requested"] = (
        kinds["default"]["type"].startswith("DYN (Position-Independent")
        and kinds["pie"]["type"].startswith("DYN (Position-Independent")
        and kinds["no_pie"]["type"].startswith("EXEC")
        and kinds["static"]["type"].startswith("EXEC")
        and kinds["nostdlib"]["type"].startswith("DYN (Position-Independent")
        and kinds["nostdlib_static"]["type"].startswith("EXEC")
        and [kinds[m]["interp"] for m in modes] == [True, True, True, False, True, False]
        and all(kinds[m]["exit"] == 42 for m in modes)
    )
    P.append(probe("cli-mode-shared-pie", [trust_cg, "--shared", "--pie", "-o", "libmode.so", "tls_prog.tmbc"]))
    (WORK / "dyn").mkdir()
    P.append(probe("cli-dynonly-library", [trust_cg, "--shared", "--relocation-model", "pic", "-o", "dyn/libtcgdynonly.so", "tls_lib.tmbc"]))
    P.append(probe("cli-mode-static-dynonly", [trust_cg, "--static", "-o", "static_dynonly", "-L", "dyn", "-l", "tcgdynonly", "tls_user.tmbc"]))
    P.append(probe("cli-mode-dynamic-dynonly", [trust_cg, "-o", "dynamic_dynonly", "-L", "dyn", "-l", "tcgdynonly", "--rpath", str(WORK / "dyn"), "tls_user.tmbc"]))
    P.append(probe("run-dynamic_dynonly", ["./dynamic_dynonly"]))

    # 5. SHT_REL: GNU ld applies it outside the driver; the driver refuses it.
    (WORK / "le_rel.o").write_bytes(as_sht_rel((WORK / "le.o").read_bytes()))
    shutil.copy(WORK / "le_rel.o", INPUTS / "le_rel.o")
    P.append(probe("readelf-r-le_rel.o", ["readelf", "-rW", "le_rel.o"]))
    P.append(probe("outside-cc-shared-le_rel", ["cc", "-shared", "-o", "librel_raw.so", "le_rel.o"]))
    P.append(probe("objdump-librel_raw.so", ["objdump", "-d", "--disassemble=tcg_cli_tls_bump", "librel_raw.so"]))
    P.append(probe("cli-route-sht-rel", [trust_cg, "--shared", "--relocation-model", "pic", "-o", "libtcgrel.so", "-Wl,le_rel.o", "tls_reader_thread.tmbc"]))
    check["sht_rel_linked_outside"] = next(p for p in P if p["name"] == "outside-cc-shared-le_rel")["exit"] == 0
    check["sht_rel_refused_by_driver"] = next(p for p in P if p["name"] == "cli-route-sht-rel")["exit"] == 1

    # 6. TEXTREL: named under -z text; the twin carries TEXTREL.
    P.append(probe("assemble-textrel", ["cc", "-c", "-fno-stack-protector", "-o", "textrel.o", "textrel.s"]))
    P.append(probe("compile-plain-main", ["cc", "-c", "-fno-stack-protector", "-o", "plain_main.o", "plain_main.c"]))
    P.append(probe("textrel-z-text", ["cc", "-pie", "-o", "textrel", "-Wl,-z,noexecstack", "plain_main.o", "textrel.o", "-Wl,-z,text"]))
    P.append(probe("textrel-twin", ["cc", "-pie", "-o", "textrel_twin", "-Wl,-z,noexecstack", "plain_main.o", "textrel.o"]))
    P.append(probe("readelf-d-textrel_twin", ["readelf", "-dW", "textrel_twin"]))
    P.append(probe("run-textrel_twin", ["./textrel_twin"]))
    return results


MUTANTS = [
    (
        "no-trace",
        "a Linux link is never traced (the trace-based output check never runs)",
        "    let traced = request.traces_link_inputs();\n",
        "    let traced = false;\n",
        [
            ("link_options", ["test", "-p", "trust-cg-cli", "--test", "link_options"]),
            ("tlsie-traced", ["test", "-p", "trust-cg-codegen", "--test", "e2e_aarch64_elf_tlsie", "traced_archive_members"]),
        ],
    ),
    (
        "no-archive-members",
        "archive-member trace lines are not resolved",
        "        for (archive, member) in archive_member_spellings(line) {\n",
        "        for (archive, member) in archive_member_spellings(line).into_iter().take(0) {\n",
        [
            ("link_options-routes", ["test", "-p", "trust-cg-cli", "--test", "link_options", "every_link_route"]),
            ("lib-trace", ["test", "-p", "trust-cg-codegen", "--lib", "link_driver::tests::input_trace_examination"]),
        ],
    ),
    (
        "no-member-bytes",
        "archive-member trace lines are resolved, but no copy of a member is read "
        "(examine_input_trace never calls examine for an archive member)",
        "            for copy in copies {\n",
        "            for copy in copies.into_iter().take(0) {\n",
        [
            ("link_options-routes", ["test", "-p", "trust-cg-cli", "--test", "link_options", "every_link_route"]),
            ("tlsie-traced", ["test", "-p", "trust-cg-codegen", "--test", "e2e_aarch64_elf_tlsie", "traced_archive_members"]),
            ("lib-trace", ["test", "-p", "trust-cg-codegen", "--lib", "link_driver::tests::input_trace_examination"]),
        ],
    ),
    (
        "no-sht-rel",
        "SHT_REL sections are not read",
        "    records.relocations.extend(rel_section_records(bytes)?);\n",
        "    records.relocations.extend(rel_section_records(bytes)?.into_iter().take(0));\n",
        [
            ("tlsie-sht-rel", ["test", "-p", "trust-cg-codegen", "--test", "e2e_aarch64_elf_tlsie", "sht_rel"]),
            ("lib-sht-rel", ["test", "-p", "trust-cg-codegen", "--lib", "link_driver::tests::sht_rel"]),
        ],
    ),
    (
        "skip-every-positional",
        "every positional input is skipped in the trace, even one the pre-link scan could not read",
        "            if !files_seen.contains(&key) && !scanned.contains(&key) {\n",
        "            if !files_seen.contains(&key)\n"
        "                && !scanned.contains(&key)\n"
        "                && !positional\n"
        "                    .iter()\n"
        "                    .any(|object| canonical(object).as_ref() == Some(&key))\n"
        "            {\n",
        [
            ("lib-unreadable", ["test", "-p", "trust-cg-codegen", "--lib", "link_driver::tests::an_unreadable_input_trace"]),
        ],
    ),
]


def mutations() -> list[dict]:
    source = WORKTREE / "crates/trust-cg-codegen/src/link_driver.rs"
    original = source.read_text()
    records = []
    for name, what, old, new, runs in MUTANTS:
        directory = MUTATION / name
        directory.mkdir(parents=True)
        assert original.count(old) == 1, name
        source.write_text(original.replace(old, new))
        diff = subprocess.run(["git", "-C", str(WORKTREE), "diff"], capture_output=True, text=True).stdout
        (directory / "mutant.diff").write_text(diff)
        legs = []
        try:
            for leg, args in runs:
                legs.append(run(leg, [*CARGO, *args, "--locked", "--offline", "-j", "8"], directory=directory))
        finally:
            source.write_text(original)
        # A mutant counts as killed only when a test failed; a build failure
        # would say nothing about the check.
        killed = any(leg["failed_tests"] for leg in legs)
        records.append({"name": name, "what": what, "legs": legs, "killed": killed})
        print(f"mutant {name}: {'killed' if killed else 'SURVIVED'}", flush=True)
    return records


def main() -> int:
    for directory in (LOGS, DIRECT, MUTATION, INPUTS, WORK):
        directory.mkdir(parents=True, exist_ok=True)
    head = git("rev-parse", "HEAD")
    tree = git("rev-parse", "HEAD^{tree}")
    status_before = git("status", "--porcelain", "--untracked-files=all")
    if status_before:
        print("checkout is dirty; refusing to qualify", file=sys.stderr)
        return 1
    host = {
        "uname": " ".join(platform.uname()),
        "glibc": subprocess.run(["ldd", "--version"], capture_output=True, text=True).stdout.splitlines()[0],
    }
    tools = [
        tool("cc", ["cc", "--version"]),
        tool("ld", ["ld", "--version"]),
        tool("ld.lld", [str(LLD_DIR / "ld.lld"), "--version"]),
        tool("readelf", ["readelf", "--version"]),
        tool("ar", ["ar", "--version"]),
        tool("objdump", ["objdump", "--version"]),
        tool("rustc", ["rustc", "--version"]),
        tool("cargo", ["cargo", "--version"]),
    ]
    gate_records = gates()
    trust_cg = WORKTREE / "target/debug/trust-cg"
    binary = {"path": str(trust_cg), "sha256": sha256(trust_cg)}
    direct_records = direct(str(trust_cg))
    status_mid = git("status", "--porcelain", "--untracked-files=all")
    mutation_records = mutations()
    # The mutants rebuilt the binary; rebuild it from the restored source.
    rebuild = run("rebuild-after-mutants", [*CARGO, "build", "-p", "trust-cg-cli", "--locked", "--offline", "-j", "8"])
    status_after = git("status", "--porcelain", "--untracked-files=all")
    # The member-route mutant must be killed by a member route: the route
    # test's first failure is the `member` link succeeding (it links the
    # le archive member, which the mutant no longer reads).
    member_legs = [
        leg for record in mutation_records if record["name"] == "no-member-bytes"
        for leg in record["legs"] if leg["name"] == "link_options-routes"
    ]
    member_route_kill = bool(member_legs) and any(
        re.search(r"link_options\.rs:\d+:\d+: member: ", panic) for panic in member_legs[0]["panics"]
    )
    results = {
        "run": "L02-P9 closure-audit residuals: traced link inputs and CLI link modes",
        "date": "2026-09-23",
        "source_sha": head,
        "tree_sha": tree,
        "dirty_before": bool(status_before),
        "dirty_after_probes": bool(status_mid),
        "dirty_after": bool(status_after),
        "host": host,
        "tools": tools,
        "trust_cg_binary": binary,
        "gates": gate_records,
        "direct": direct_records,
        "mutations": mutation_records,
        "member_route_kill": member_route_kill,
        "rebuild_after_mutants": rebuild,
        "inputs": {p.name: sha256(p) for p in sorted(INPUTS.iterdir())},
    }
    (RECORDS / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    ok = (
        not status_before
        and not status_mid
        and not status_after
        and all(g["exit"] == 0 for g in gate_records)
        and all(m["killed"] for m in mutation_records)
        and member_route_kill
        and all(v for k, v in direct_records["checks"].items() if isinstance(v, bool))
    )
    print("QUALIFIED" if ok else "NOT QUALIFIED", flush=True)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
