"""A throwaway trust-cg constellation for the soundness gate's own tests.

It builds, under one temporary directory:

* a trust-cg Git repository whose scripts/ holds the PRODUCTION
  soundness_check.sh, soundness_attestation.py, soundness_remote.sh,
  matrix_results.py, run_with_timeout.py, trust_cargo.sh,
  trust_toolchain.py and private_cache.py, plus stubs for
  gate_env.sh (PATH prelude only), export_vt_tables.py,
  check_companion_coherence.py and check_x86_icmp_certificates.py (which
  logs its argv and answers as FIXTURE_FAIL / FIXTURE_X86_ICMP_MISSING
  steer it); its three Cargo locks name the fixture Clean
  and AY repositories' real commits;
* Clean, AY and aterm repositories;
* a fake toolchain on PATH (node, lake, ssh, and the stock `rustc` that
  ISLAND_TWIN_RUSTC names) and a fake installed Trust package (bin/trustc,
  bin/targo, bin/ay and the private-crate rlibs scripts/trust_toolchain.py
  requires) whose behaviour is steered by environment variables, logging
  every workload it is asked to run;
* a fake x86-64 host behind the fake `ssh`: it runs the production remote
  script locally, but its `bash scripts/soundness_check.sh --attest --host-legs
  x86_64-native` writes a record claiming a native x86-64 host (CPUID
  GenuineIntel), because this machine cannot run those legs natively.

Nothing here reaches the network or a real remote.
"""

from __future__ import annotations

import json
import os
import re
from pathlib import Path
import shutil
import stat
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
SCRIPTS = ROOT / "scripts"
PRODUCTION_SCRIPTS = (
    "soundness_check.sh", "soundness_attestation.py", "soundness_remote.sh", "matrix_results.py", "github_transport.py",
    "run_with_timeout.py", "trust_cargo.sh", "trust_toolchain.py", "private_cache.py", "host_boundary.py",
)
TRUST_COMMIT = "7" * 40
TRUST_HOST = "aarch64-apple-darwin"
TRUST_IR = "1" * 40
AY_PIN_VERSION = "0.27.0"
AY_STAMP = f"{AY_PIN_VERSION}+build.9999.f28345ff184e@2026-09-01T00:00:00Z"
ORG = "example"


# This test process's own interpreter, by its canonical path: what a planted
# python3 a test writes runs (repair round 3 of OD-XHOST-GATE-CWD-20261025).
# The fixture's python fakes name `python3` on their `#!/usr/bin/env python3`
# line and so find it on the legs' PATH by name, as a real leg's Cargo test or
# script does (repair round 4: in round 3 they named this interpreter, and a
# python3 the prelude put first on PATH never ran as theirs).
FIXTURE_PYTHON3 = os.path.realpath(sys.executable)


def write(path: Path, text: str, executable: bool = False) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    if executable:
        path.chmod(path.stat().st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)
    return path


def git(repo: Path, *args: str, env: dict | None = None) -> str:
    return subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True, text=True,
                          env=env).stdout.strip()


def bash_array(source: str, name: str) -> list[str]:
    """The items of the top-level array `NAME=( ... )` in `source`, one per
    line as soundness_check.sh writes them. Each line's `#` comment is dropped
    BEFORE the closing `)` is looked for, as bash reads it: a comment holding
    a parenthesis had ended the array early, so the two `canary_cert::`
    filters after such a comment in TRUST_CG_LIB_GATES were read as absent."""
    items = []
    for line in source.split(f"\n{name}=(", 1)[1].splitlines():
        item, closing, _ = line.split("#")[0].partition(")")
        if item.strip():
            items.append(item.strip())
        if closing:
            return items
    raise AssertionError(f"{name} has no closing parenthesis in soundness_check.sh")


def bash_scalar(source: str, name: str) -> int:
    """The integer a top-level `NAME=<digits>` assignment gives (for example a baseline pin)."""
    match = re.search(rf"^{name}=(\d+)\b", source, re.M)
    assert match, f"{name} is not assigned in soundness_check.sh"
    return int(match.group(1))


GATE_ENV_STUB = """# gate_env.sh fixture: the PATH prelude, and a passing check.
gate_env_prelude() {
    PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
    export PATH
    return 0
}
if [ -n "${BASH_VERSION:-}" ] && [ "${BASH_SOURCE[0]}" != "$0" ]; then
    gate_env_prelude
    return $?
fi
fixture_env_sh="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)/fixture-env.sh"
[ ! -f "$fixture_env_sh" ] || . "$fixture_env_sh"
echo "gate_env: fixture check $*" >>"$SOUNDNESS_FIXTURE_LOG"
echo "gate_env: RESULT PASS: 0 failure(s) [none], 0 warning(s) [none]"
exit "${FIXTURE_GATE_ENV_RC:-0}"
"""

EXPORT_VT_STUB = """import argparse, json
parser = argparse.ArgumentParser()
parser.add_argument("--aterm"); parser.add_argument("--revision"); parser.add_argument("--output")
args = parser.parse_args()
with open(args.output, "w") as handle:
    json.dump({"schema": "aterm.vt-islands.tables", "version": 1, "aterm_commit": args.revision}, handle)
print(json.dumps({"aterm_commit": args.revision}))
"""

COHERENCE_STUB = """import sys
print("companion identities: COHERENT")
sys.exit(0)
"""

# The x86-64 vector-compare certificate gate. The real one builds AY and runs
# AY and Clean; the stub keeps its exit contract (0 pass, 1 finding or a
# missing input, 3 a missing input explicitly skipped) and logs its argv.
X86_ICMP_CERTIFICATES_STUB = r"""import json, os, sys
from pathlib import Path
for directory in Path(__file__).resolve().parents:
    candidate = directory / "fixture-env.json"
    if candidate.is_file():
        for key, value in json.loads(candidate.read_text()).items():
            os.environ.setdefault(key, value)
        break
args = sys.argv[1:]
with open(os.environ["SOUNDNESS_FIXTURE_LOG"], "a") as log:
    log.write("check_x86_icmp_certificates " + " ".join(args) + "\n")
if "x86_icmp_certificates" in os.environ.get("FIXTURE_FAIL", "").split(","):
    print("[x86-icmp-certificates] FAIL query-digest-mismatch: V4I32 Ult (fixture)")
    sys.exit(1)
if os.environ.get("FIXTURE_X86_ICMP_MISSING") == "1":
    print("[x86-icmp-certificates] MISSING clean-source-missing: no Clean source with the rule's revision (fixture)")
    if "--skip-missing-toolchain" in args:
        print("[x86-icmp-certificates] SKIPPED (explicit --skip-missing-toolchain): the certificates were NOT re-run")
        sys.exit(3)
    print("[x86-icmp-certificates] FAIL toolchain-input-missing: clean-source-missing (fixture)")
    sys.exit(1)
print("[x86-icmp-certificates] PASS: 32 certificate-ground cells re-certified (fixture)")
"""

# The per-host Trust compiler pin, in the form scripts/run_public_release_checks.sh
# spells it (soundness_attestation.trustc_pins reads it from the candidate).
FIXTURE_TRUSTC = "rustc 1.99.0-dev (7777777 2026-09-17) (trustc 0.1.0)"
RELEASE_PIN_STUB = f"""#!/bin/bash
# fixture: the per-host Trust compiler pin only
case "$actual_host" in
    aarch64-apple-darwin)
        expected_trustc='{FIXTURE_TRUSTC}'
        ;;
esac
"""

# Cargo is synthetic in this constellation and executes no C compiler. Keep
# its declared Darwin host usable on Linux test runners too: only the copied
# fixture's discovery function is replaced, while production record validation
# and the actual native discovery/stdio controls remain unchanged.
DARWIN_ORACLE_STUB = '''def darwin_c_oracle() -> dict:
    root = Path(__file__).resolve().parents[2] / "darwin-oracle-fixture"
    compiler = root / "usr/bin/clang"
    sdk = root / "SDKs/MacOSX.sdk"
    settings = sdk / "SDKSettings.json"
    return {"discovery": {"program": DARWIN_XCRUN, "sdk": "macosx"},
            "compiler": {"path": str(compiler), "sha256": sha256_file(compiler),
                         "version": "Apple clang (synthetic soundness fixture; no native C executed)"},
            "sdk": {"path": str(sdk), "settings": str(settings), "sha256": sha256_file(settings)}}

'''

DARWIN_BOUNDARY_STUB = '''def judge_darwin_c_oracle(boundary):
    # The fixture executes only synthetic Cargo commands. Judge the same
    # synthetic compiler/SDK that its attestation records, not the host SDK.
    root = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(__file__))),
                        "darwin-oracle-fixture")
    compiler = os.path.join(root, "usr", "bin", "clang")
    if boundary.resolve(compiler, "the Darwin C oracle") is not None:
        boundary.judge_tree(os.path.join(root, "usr"), "the Darwin C compiler install root")
    boundary.judge_tree(os.path.join(root, "SDKs", "MacOSX.sdk"), "the Darwin C oracle SDK")

'''

# One fake program for every toolchain command: its behaviour depends on the
# name it was invoked as. Every workload is logged as "<name> <argv>".
FAKE_TOOL = r'''#!/usr/bin/env python3
import json, os, sys
from pathlib import Path
# The fixture's steering variables (FIXTURE_*, SOUNDNESS_FIXTURE_LOG,
# FAKE_X86_GATE) also live in <base>/fixture-env.json, because an --attest run
# re-executes itself with only the allowlisted environment and so never passes
# them to the fakes it starts. A fake reads the file beside its fixture.
def _fixture_env():
    for directory in Path(__file__).resolve().parents:
        candidate = directory / "fixture-env.json"
        if candidate.is_file():
            return json.loads(candidate.read_text())
    return {}
for _key, _value in _fixture_env().items():
    os.environ.setdefault(_key, _value)
name = Path(sys.argv[0]).name
args = sys.argv[1:]
# FIXTURE_UMASK_LOG: every fake records the umask it was started under.
if os.environ.get("FIXTURE_UMASK_LOG"):
    _mask = os.umask(0)
    os.umask(_mask)
    with open(os.environ["FIXTURE_UMASK_LOG"], "a") as handle:
        handle.write("{} {:04o} {}\n".format(name, _mask, " ".join(args[:2])))
# FIXTURE_CWD_LOG: every fake records the working directory it was started in
# (name, directory, first two arguments; tab-separated).
if os.environ.get("FIXTURE_CWD_LOG"):
    with open(os.environ["FIXTURE_CWD_LOG"], "a") as handle:
        handle.write("{}\t{}\t{}\n".format(name, os.getcwd(), " ".join(args[:2])))
log = os.environ.get("SOUNDNESS_FIXTURE_LOG")
if log:
    with open(log, "a") as handle:
        handle.write(name + " " + " ".join(args) + "\n")
fail = set(filter(None, os.environ.get("FIXTURE_FAIL", "").split(",")))
PASSING = ("running 1 test\ntest witness ... ok\n\n"
           "test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s\n")
FAILING = ("running 1 test\ntest witness ... FAILED\n\n"
           "test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s\n")

def selector():
    for flag in ("--test", "--lib", "--example"):
        if flag in args:
            return args[args.index(flag) + 1]
    return ""

if name == "rustc":
    if args[:1] == ["-V"]:
        print("rustc 1.97.1 (fixture 2026-08-01)")
    elif args[:1] == ["-vV"]:
        print("rustc 1.97.1 (fixture 2026-08-01)\nbinary: rustc\ncommit-hash: " + "0" * 40
              + "\nhost: aarch64-apple-darwin\nrelease: 1.97.1")
    elif "--print" in args and "target-libdir" in args:
        print(os.environ["FIXTURE_WASM_LIBDIR"])
    elif "--print" in args and "sysroot" in args:
        print(os.environ["FIXTURE_SYSROOT"])
    sys.exit(0)
if name == "trustc":
    if args[:1] == ["-vV"]:
        print("rustc 1.99.0-dev (7777777 2026-09-17) (trustc 0.1.0)\nbinary: trustc\ncommit-hash: "
              + "7" * 40 + "\ncommit-date: 2026-09-17\nhost: " + os.environ.get("FIXTURE_TRUST_HOST",
              "aarch64-apple-darwin") + "\nrelease: 1.99.0-dev")
    elif "--print" in args and "sysroot" in args:
        print(os.environ["FIXTURE_SYSROOT"])
    sys.exit(0)
if name == "targo":
    if args[:1] == ["--version"]:
        print("targo 1.99.0-dev (7777777 2026-09-17) (targo 0.1.0)"); sys.exit(0)
    if args[:1] != ["--unverified"]:
        print("fixture targo: only the explicit unverified lane is expected", file=sys.stderr); sys.exit(2)
    rest, index = [], 1
    while index < len(args):
        if args[index] == "--config":
            index += 2
            continue
        rest.append(args[index]); index += 1
    name, args = "cargo", rest
if name == "rustup":
    if args[:1] == ["run"] and len(args) > 2:  # `trust`, or the island twin (`stable`)
        os.execvp(args[2], args[2:])
    if args[:2] == ["toolchain", "list"]:
        print("1.97.1-aarch64-apple-darwin")
    sys.exit(0)
if name == "node":
    if args[:1] == ["--version"]:
        print("v24.0.0"); sys.exit(0)
    if selector() in fail or Path(args[0]).name in fail:
        print("DIVERGE fixture"); sys.exit(1)
    if args[0].endswith("wasm_island_differential.mjs"):
        print("island differential checks agree: 3 (fixture)")
    else:
        print("5/5 differential checks agree")
    sys.exit(0)
if name == "lake":
    if args[:2] == ["env", "lean"]:
        # formal/lean/scripts/AxiomAudit.lean: the success line, or its failure.
        if "lean-axiom-audit" in fail:
            print("scripts/AxiomAudit.lean:84:0: error: AXIOM-AUDIT FAIL: 1 finding(s):")
            print("sorryAx <- Trust.fixture")
            sys.exit(1)
        print("AXIOM-AUDIT declarations=7 sorryAx=0 project_axioms=0 native_bv_decide_axioms=0 "
              "native_dependents=0 capstone=[propext, Classical.choice, Quot.sound]")
        sys.exit(0)
    sys.exit(1 if "lake" in fail else 0)
if name == "clean":
    stem = Path(args[-1]).stem
    if stem in fail:
        print("Checked 5 declarations\n  4 passed, 1 failed"); sys.exit(1)
    print("Checked 5 declarations\n  5 passed, 0 failed"); sys.exit(0)
if name == "cargo":
    if args[:1] == ["-V"]:
        print("cargo 1.97.1 (fixture 2026-08-01)"); sys.exit(0)
    if args[:1] == ["test"]:
        target = selector()
        if target in fail and os.environ.get("FIXTURE_FAIL_AFTER_STAGED") == "1":
            # Fail only once the dispatched x86-64 record is staged locally, so
            # the stop provably happens after the import (no timing race).
            import subprocess as _sp, time as _time
            # The outcome goes to the workload log: this process's own output
            # lands in the leg log, never on the gate's stderr.
            for _ in range(600):
                if _sp.run(["git", "-C", os.environ["FIXTURE_CG"], "for-each-ref", "refs/soundness/import/"],
                           capture_output=True, text=True).stdout.strip():
                    outcome = "fixture: failing after the x86-64 record was staged"
                    break
                _time.sleep(0.1)
            else:
                outcome = "fixture: the x86-64 record was never staged"
            if log:
                with open(log, "a") as handle:
                    handle.write(outcome + "\n")
        print(FAILING if target in fail else PASSING)
        if target == "proof_gate_strict":
            # executed_ay_identity_is_reported: the AY this test binary admits.
            import hashlib
            ay = Path(os.environ["FIXTURE_SYSROOT"]) / "bin" / "ay"
            if os.environ.get("FIXTURE_AY_UNRESOLVED") == "1":
                print("proof_gate_strict: executed-ay unresolved: TCG-AY-IDENTITY-UNRECORDED (fixture)")
            else:
                digest = os.environ.get("FIXTURE_CAMPAIGN_AY_SHA256") or hashlib.sha256(ay.read_bytes()).hexdigest()
                route = os.environ.get("FIXTURE_CAMPAIGN_AY_ROUTE", "toolchain-pinned-ay")
                print(f"proof_gate_strict: executed-ay sha256={digest} route={route} ay={ay}")
        sys.exit(101 if target in fail else 0)
    if args[:1] == ["run"]:
        example = selector()
        rest = args[args.index("--") + 1:]
        if example in fail:
            sys.exit(101)
        if example.endswith("_island") or example.endswith("_islands"):
            out = Path(rest[-1]); out.mkdir(parents=True, exist_ok=True)
            for suffix in (".wasm", "_twin.rs", "_expected.json"):
                (out / (example + suffix)).write_text("fixture\n")
            print("island written"); sys.exit(0)
        out = rest[0]
        Path(out + ".wasm").write_text("fixture\n"); Path(out + ".json").write_text("{}\n")
        print("wrote " + out + ".wasm"); sys.exit(0)
    if args[:1] == ["build"]:
        if "clean-build" in fail:
            sys.exit(101)
        # The fake tool dispatches on its invocation name: copy it as `clean`,
        # a regular file with the modes Cargo's own output gets under the
        # caller's umask (the gate runs Clean only from a file no other user
        # can write).
        target = Path(os.environ["CARGO_TARGET_DIR"]) / "release" / "clean"
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.is_symlink() or target.exists():
            target.unlink()
        target.write_bytes(Path(os.environ["FIXTURE_TOOL"]).read_bytes())
        mask = os.umask(0)
        os.umask(mask)
        target.chmod(0o777 & ~mask)
        sys.exit(0)
print("fake tool: unhandled " + name + " " + " ".join(args), file=sys.stderr)
sys.exit(99)
'''

# The fake ssh: `ssh [-o opt]... <host> <remote argv...>`. Like OpenSSH, it
# joins the remote argv with spaces into one command line and runs that with
# the remote shell (an empty argument vanishes, as it does over real ssh), in
# a local "remote home", with a `bash` wrapper that replaces the remote x86-64
# gate by FAKE_X86_GATE (records claiming native x86-64 execution).
FAKE_SSH = r'''#!/usr/bin/env python3
import json, os, subprocess, sys
from pathlib import Path
# The fixture's steering variables (FIXTURE_*, SOUNDNESS_FIXTURE_LOG,
# FAKE_X86_GATE) also live in <base>/fixture-env.json, because an --attest run
# re-executes itself with only the allowlisted environment and so never passes
# them to the fakes it starts. A fake reads the file beside its fixture.
def _fixture_env():
    for directory in Path(__file__).resolve().parents:
        candidate = directory / "fixture-env.json"
        if candidate.is_file():
            return json.loads(candidate.read_text())
    return {}
for _key, _value in _fixture_env().items():
    os.environ.setdefault(_key, _value)
args = sys.argv[1:]
while args and args[0] == "-o":
    args = args[2:]
host, remote = args[0], args[1:]
with open(os.environ["SOUNDNESS_FIXTURE_LOG"], "a") as log:
    log.write("ssh " + host + " " + " ".join(remote[:4]) + "\n")
if os.environ.get("FIXTURE_SSH_UNREACHABLE") == "1":
    print("ssh: connect to host " + host + ": Connection refused", file=sys.stderr)
    sys.exit(255)
home = os.environ["FIXTURE_REMOTE_HOME"]
env = dict(os.environ, HOME=home, PATH=os.environ["FIXTURE_REMOTE_PATH"])
env.pop("TRUST_CG_DIR", None)
sys.exit(subprocess.call(["/bin/bash", "-c", " ".join(remote)], cwd=home, env=env))
'''

REMOTE_BASH = r'''#!/bin/bash
if [ "$1" = scripts/soundness_check.sh ] && [ "$*" = "scripts/soundness_check.sh --attest --host-legs x86_64-native" ]; then
  exec python3 "$FAKE_X86_GATE"
fi
exec /bin/bash "$@"
'''

REMOTE_UNAME = r'''#!/bin/sh
case "$*" in
  -m) echo x86_64 ;;
  -s) echo Linux ;;
  -sm) echo "Linux x86_64" ;;
  *) exec /usr/bin/uname "$@" ;;
esac
'''

# The fake executor advertises the versions the production remote preflight
# requires. Its native gate is replaced by FAKE_X86_GATE, so these helpers
# deliberately support identity probes only, never a real compile or disassembly.
REMOTE_CC = r'''#!/bin/sh
[ "$*" = --version ] || exit 64
echo "clang version 22.0.0 (fixture)"
'''

REMOTE_LLVM_OBJDUMP = r'''#!/bin/sh
[ "$*" = --version ] || exit 64
echo "LLVM version 22.0.0 (fixture)"
'''

REMOTE_GIT = r'''#!/bin/sh
[ "$1" = ls-remote ] && [ "${FIXTURE_REMOTE_NO_CREDENTIALS:-0}" != 1 ] && exit 0
[ "$1" = ls-remote ] && exit 128
exec /usr/bin/git "$@"
'''

# Writes the record a native x86-64 host's `--attest --host-legs x86_64-native`
# run would write, for the checked-out commit in the current directory.
FAKE_X86_GATE = r'''
import hashlib, json, os, py_compile, subprocess, sys, tempfile
from pathlib import Path
if os.environ.get("FIXTURE_X86_GATE_FAIL") == "1":
    print("x86-64 legs failed (fixture)"); sys.exit(1)
repo = Path.cwd()
# Exercise Python's real bytecode writer under the remote gate's inherited
# umask. Name the fixture artifact inside the clone independently of this
# interpreter's default cache prefix; change no Python flags or file modes.
source = repo / "scripts" / "soundness_attestation.py"
cache_file = source.parent / "__pycache__" / f"{source.stem}.{sys.implementation.cache_tag}.pyc"
bytecode = Path(py_compile.compile(str(source), cfile=str(cache_file), doraise=True))
witness = json.dumps({"repo": str(repo.resolve()), "source": str(source.resolve()),
                      "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                      "bytecode": str(bytecode.resolve()), "bytes": bytecode.stat().st_size,
                      "pycache_prefix": sys.pycache_prefix,
                      "dont_write_bytecode": sys.dont_write_bytecode,
                      # The shell's working-directory name, from which the
                      # real gate derives TRUST_CG_DIR (`cd ... && pwd`).
                      "pwd": os.environ.get("PWD", "")}, sort_keys=True)
with open(os.environ["SOUNDNESS_FIXTURE_LOG"], "a") as log:
    log.write("fixture-x86-bytecode " + witness + "\n")
print("fixture-x86-bytecode " + witness, flush=True)
sys.path.insert(0, str(repo / "scripts"))
import soundness_attestation as sa
commit = sa.rev_parse(repo, "HEAD")
inventory = sa.list_json_at(repo, commit)
host = {"triple": "x86_64-unknown-linux-gnu", "system": "Linux", "machine": "x86_64", "translated": False,
        "cpuinfo": {"vendor_id": "GenuineIntel", "model name": "Intel(R) Xeon(R) fixture"},
        "cpuid": {"available": True, "vendor": "GenuineIntel", "brand": "Intel(R) Xeon(R) fixture",
                  "hypervisor": False, "hypervisor_vendor": "", "sse41": True}}
if os.environ.get("FIXTURE_X86_EMULATED") == "1":
    host["cpuid"]["brand"] = "QEMU Virtual CPU version 2.5+"
native, reasons = sa.native_x86_64_verdict(host)
host["native_x86_64"] = True
host["native_x86_64_refusals"] = reasons
legs = [{"id": leg, "class": cls, "status": "PASS", "seconds": 1, "detail": "fixture"}
        for leg, cls in sa.expected_legs(inventory, "x86_64-native", True).items()]
record = {
    "schema": sa.SCHEMA, "subject": {"commit": commit, "tree": sa.rev_parse(repo, commit + "^{tree}")},
    "scope": "x86_64-native", "host": host,
    "runner": {name: sa.blob_id(repo, commit, path) for name, path in sa.RUNNER_FILES.items()},
    "inventory": {"sha256": sa.inventory_sha(inventory), "legs": inventory["legs"]},
    "dependencies": sa.dependency_tuple(repo, commit),
    "rust_toolchain_channel": sa.toolchain_channel(repo, commit),
    "toolchains": {"trust": {"commit": "7" * 40, "host": "x86_64-unknown-linux-gnu",
                             "identity": "rustc 1.99.0-dev (7777777 2026-09-17) (trustc 0.1.0)\nbinary: trustc\n"
                                         "commit-hash: " + "7" * 40
                                         + "\nhost: x86_64-unknown-linux-gnu\nrelease: 1.99.0-dev",
                             "targo_version": "targo 1.99.0-dev (7777777 2026-09-17) (targo 0.1.0)",
                             "overlay": None}},
    "executed": {"trustc": {"path": "/remote/trust/bin/trustc", "sha256": "a" * 64},
                 "targo": {"path": "/remote/trust/bin/targo", "sha256": "b" * 64}},
    "environment": sa.environment_report(
        {"TRUST_CG_RUN_FORMAL_PROOF_TESTS": "1", "TRUST_CG_REQUIRE_X86_SILICON": "1"},
        explicit=[], effective={"WASM_CFG_FUZZ_FUNCS": "200"}, checkout=str(repo)),
    "legs": legs, "imported": [], "signing": {"scheme": None},
}
with tempfile.TemporaryDirectory() as temporary:
    Path(temporary, "attestation.json").write_text(json.dumps(record))
    if os.environ.get("FIXTURE_X86_BYPASS_WRITE") == "1":
        # A host that skips the tool's own checks: the importer must refuse.
        tree = sa.write_tree(repo, Path(temporary))
        oid = sa.git(repo, "commit-tree", tree, "-p", commit, "-m", "unchecked").strip()
        sa.git(repo, "update-ref", sa.ref_name(commit, host["triple"]), oid)
        sys.exit(0)
    sys.exit(subprocess.call([sys.executable, str(repo / "scripts/soundness_attestation.py"), "write",
                              "--repo", str(repo), "--record-dir", temporary]))
'''


class Constellation:
    """The fixture. `env()` is the environment a gate run gets."""

    def __init__(self, base: Path):
        self.base = base
        self.home = base / "home"
        self.bin = self.home / ".cargo" / "bin"
        self.sysroot = base / "trust-sysroot"
        self.cg = base / "trust-cg"
        self.clean = base / "clean"
        self.ay = base / "ay"
        self.aterm = base / "aterm"
        self.remote_home = base / "remote-home"
        self.log = base / "workloads.log"
        self.tmp = base / "tmp"
        for directory in (self.bin, self.home / ".elan" / "bin", self.sysroot / "bin", self.remote_home,
                          self.tmp, base / "wasm-libdir"):
            directory.mkdir(parents=True, exist_ok=True)
        self.system_bin = system_commands(base / "system-bin")
        # A per-user TMPDIR only its owner can write, as /tmp (sticky) or
        # macOS's per-user directory is: an --attest run exports the
        # candidate's proofs below its LOGDIR there and refuses an export
        # whose ancestors another user could rename entries in. Under umask
        # 0002 mkdir made it 0775.
        self.tmp.chmod(0o700)
        (base / "wasm-libdir" / "libcore-fixture.rlib").write_text("")
        self.git_config = write(base / "gitconfig", "[user]\n\tname = Fixture\n\temail = fixture@example.invalid\n"
                                "[commit]\n\tgpgSign = false\n[init]\n\tdefaultBranch = main\n"
                                "[advice]\n\tdetachedHead = false\n")
        self._toolchain()
        self._companions()
        self._trust_cg()

    # ------------------------------------------------------------------
    def base_env(self) -> dict:
        env = {
            "HOME": str(self.home), "PATH": f"{self.bin}:{self.sysroot / 'bin'}:{self.system_bin}",
            "TMPDIR": str(self.tmp), "LANG": "C", "LC_ALL": "C",
            "GIT_CONFIG_GLOBAL": str(self.git_config), "GIT_CONFIG_NOSYSTEM": "1",
            "SOUNDNESS_FIXTURE_LOG": str(self.log),
            "FIXTURE_WASM_LIBDIR": str(self.base / "wasm-libdir"), "FIXTURE_SYSROOT": str(self.sysroot),
            "FIXTURE_TOOL": str(self.bin / "fake-tool"),
            "FIXTURE_BIN": str(self.bin), "FIXTURE_REMOTE_HOME": str(self.remote_home),
            "FIXTURE_REMOTE_PATH": f"{self.base / 'remote-bin'}:{self.bin}:{self.sysroot / 'bin'}"
                                   f":{self.system_bin}",
            "FAKE_X86_GATE": str(self.base / "fake_x86_gate.py"), "FIXTURE_CG": str(self.cg),
        }
        python_dir = str(Path(sys.executable).parent)
        env["PATH"] = env["PATH"] + ":" + python_dir
        env["FIXTURE_REMOTE_PATH"] += ":" + python_dir
        return env

    def env(self, **extra: str) -> dict:
        env = self.base_env()
        env.update(TRUST_CG_DIR=str(self.cg), CLEAN_SOURCE_DIR=str(self.clean), AY_SOURCE_DIR=str(self.ay),
                   ATERM_DIR=str(self.aterm), SOUNDNESS_DEPS_DIR=str(self.base / "deps"),
                   SOUNDNESS_X86_HOST="fixture-x86", SOUNDNESS_SSH_CONNECT_TIMEOUT="5",
                   ISLAND_TWIN_RUSTC=str(self.bin / "rustc"))
        env.update(extra)
        return {key: value for key, value in env.items() if value is not None}

    def write_fixture_env(self, env: dict) -> None:
        """The steering variables of `env`, for fakes started under a scrubbed environment."""
        import shlex
        steering = {key: value for key, value in env.items()
                    if key.startswith(("FIXTURE_", "SOUNDNESS_FIXTURE_")) or key == "FAKE_X86_GATE"}
        (self.base / "fixture-env.json").write_text(json.dumps(steering))
        (self.base / "fixture-env.sh").write_text(
            "".join(f"{key}={shlex.quote(value)}\n" for key, value in sorted(steering.items())))

    def run_gate(self, *args: str, umask: int | None = None, cwd: Path | None = None, script: str | None = None,
                 **extra: str) -> subprocess.CompletedProcess:
        """Run the fixture's soundness_check.sh (under `umask` when given),
        started in `cwd` (default: the fixture's trust-cg checkout) and named
        to bash as `script` (default: its absolute path; a relative name such
        as `scripts/soundness_check.sh` resolves in `cwd`)."""
        self.log.write_text("")
        env = self.env(**extra)
        self.write_fixture_env(env)
        # The gate itself gets no steering variable: an --attest run would
        # refuse SOUNDNESS_FIXTURE_LOG and drop the rest; the fakes read the file.
        env = {key: value for key, value in env.items()
               if not (key.startswith(("FIXTURE_", "SOUNDNESS_FIXTURE_")) or key == "FAKE_X86_GATE")}
        return subprocess.run(["bash", script or str(self.cg / "scripts" / "soundness_check.sh"), *args],
                              cwd=self.cg if cwd is None else cwd, env=env, capture_output=True, text=True,
                              timeout=600, umask=-1 if umask is None else umask)

    def tool(self, *args: str, env: dict | None = None) -> subprocess.CompletedProcess:
        return subprocess.run([sys.executable, str(self.cg / "scripts" / "soundness_attestation.py"), *args],
                              env=env or self.env(), capture_output=True, text=True, timeout=300)

    def workloads(self) -> list[str]:
        return self.log.read_text().splitlines() if self.log.exists() else []

    # ------------------------------------------------------------------
    def _toolchain(self) -> None:
        tool = write(self.bin / "fake-tool", FAKE_TOOL, executable=True)
        for name in ("cargo", "rustc", "rustup", "node"):
            (self.bin / name).symlink_to(tool)
        (self.home / ".elan" / "bin" / "lake").symlink_to(tool)
        # The installed Trust package: real files (scripts/trust_toolchain.py
        # resolves symlinks and follows only atpkg launcher shims).
        for name in ("trustc", "targo"):
            write(self.sysroot / "bin" / name, FAKE_TOOL, executable=True)
        for crate in ("rustc_middle", "rustc_codegen_ssa"):
            write(self.sysroot / "lib" / "rustlib" / TRUST_HOST / "lib" / f"lib{crate}-fixture.rlib", "")
        write(self.sysroot / "bin" / "ay", f"#!/bin/sh\necho 'ay {AY_STAMP}'\n", executable=True)
        write(self.bin / "ssh", FAKE_SSH, executable=True)
        write(self.base / "remote-bin" / "bash", REMOTE_BASH, executable=True)
        # The remote host is x86-64 Linux and can read the dependency sources.
        write(self.base / "remote-bin" / "uname", REMOTE_UNAME, executable=True)
        write(self.base / "remote-bin" / "git", REMOTE_GIT, executable=True)
        write(self.base / "remote-bin" / "cc", REMOTE_CC, executable=True)
        write(self.base / "remote-bin" / "llvm-objdump", REMOTE_LLVM_OBJDUMP, executable=True)
        write(self.base / "fake_x86_gate.py", FAKE_X86_GATE)

    def _companions(self) -> None:
        env = dict(os.environ, GIT_CONFIG_GLOBAL=str(self.git_config), GIT_CONFIG_NOSYSTEM="1")
        source = (SCRIPTS / "soundness_check.sh").read_text()
        for repo in (self.clean, self.ay, self.aterm):
            repo.mkdir()
            git(repo, "init", "-q", env=env)
            write(repo / "README", repo.name + "\n")
        for stem in bash_array(source, "CLEAN_LEAN"):
            write(self.clean / "proofs" / f"{stem}.lean", "-- fixture\n")
        write(self.clean / ".gitignore", "/target\n")
        for repo in (self.clean, self.ay, self.aterm):
            git(repo, "add", "-A", env=env)
            git(repo, "commit", "-qm", "fixture", env=env)
        git(self.aterm, "update-ref", "refs/remotes/origin/main", "HEAD", env=env)
        self.clean_rev = git(self.clean, "rev-parse", "HEAD", env=env)
        self.ay_rev = git(self.ay, "rev-parse", "HEAD", env=env)

    def lock(self, with_ay: bool = True) -> str:
        def source(repo: str, rev: str) -> str:
            return f'source = "git+https://github.com/{ORG}/{repo}.git?rev={rev}#{rev}"'
        text = f'version = 4\n\n[[package]]\nname = "trust-ir"\nversion = "0.1.0"\n{source("trust-ir", TRUST_IR)}\n'
        text += f'\n[[package]]\nname = "clean-kernel"\nversion = "0.1.0"\n{source("clean", self.clean_rev)}\n'
        if with_ay:
            text += f'\n[[package]]\nname = "ay-pb"\nversion = "{AY_PIN_VERSION}"\n{source("ay", self.ay_rev)}\n'
        return text

    def _trust_cg(self) -> None:
        env = dict(os.environ, GIT_CONFIG_GLOBAL=str(self.git_config), GIT_CONFIG_NOSYSTEM="1")
        cg = self.cg
        cg.mkdir()
        git(cg, "init", "-q", env=env)
        # Raw attestation helpers also commit without this fixture's global
        # configuration. Keep their identity local to the throwaway repository.
        git(cg, "config", "user.name", "Fixture", env=env)
        git(cg, "config", "user.email", "fixture@example.invalid", env=env)
        (cg / "scripts").mkdir()
        # Each production script with the mode the fixture's umask gives a new
        # file (its executable bits kept), not this checkout's own mode: an
        # --attest run judges the candidate checkout's every entry
        # (scripts/host_boundary.py).
        mask = os.umask(0)
        os.umask(mask)
        for name in PRODUCTION_SCRIPTS:
            shutil.copyfile(SCRIPTS / name, cg / "scripts" / name)
            executable = stat.S_IMODE((SCRIPTS / name).stat().st_mode) & 0o111
            (cg / "scripts" / name).chmod((0o777 if executable else 0o666) & ~mask)
        oracle_root = self.base / "darwin-oracle-fixture"
        write(oracle_root / "usr/bin/clang", "#!/bin/sh\necho synthetic-fixture-clang\n", executable=True)
        write(oracle_root / "SDKs/MacOSX.sdk/SDKSettings.json", '{"Version":"synthetic-fixture"}\n')
        attestation = cg / "scripts/soundness_attestation.py"
        source = attestation.read_text()
        start = source.index("def darwin_c_oracle() -> dict:\n")
        end = source.index("\ndef darwin_c_oracle_problem(", start)
        attestation.write_text(source[:start] + DARWIN_ORACLE_STUB + source[end:])
        boundary = cg / "scripts/host_boundary.py"
        source = boundary.read_text()
        start = source.index("def judge_darwin_c_oracle(boundary):\n")
        end = source.index("\ndef judge_all(", start)
        boundary.write_text(source[:start] + DARWIN_BOUNDARY_STUB + source[end:])
        write(cg / "scripts" / "gate_env.sh", GATE_ENV_STUB)
        write(cg / "scripts" / "export_vt_tables.py", EXPORT_VT_STUB)
        write(cg / "scripts" / "check_companion_coherence.py", COHERENCE_STUB)
        write(cg / "scripts" / "check_x86_icmp_certificates.py", X86_ICMP_CERTIFICATES_STUB)
        write(cg / "scripts" / "run_public_release_checks.sh", RELEASE_PIN_STUB)
        write(cg / "Cargo.toml", f'[workspace]\nmembers = []\n\n[workspace.package]\n'
              f'repository = "https://github.com/{ORG}/trust-cg"\n')
        write(cg / "Cargo.lock", self.lock())
        write(cg / "crates" / "rustc-codegen-trust-cg" / "Cargo.lock", self.lock())
        write(cg / "fuzz" / "Cargo.lock", self.lock(with_ay=False))
        write(cg / "rust-toolchain.toml", '[toolchain]\nchannel = "trust"\n')
        # As in the real repository: the Python a gate imports from scripts/
        # leaves bytecode that must not make a clone dirty.
        write(cg / ".gitignore", "__pycache__/\n")
        write(cg / "crates" / "rustc-codegen-trust-cg" / "rust-toolchain.toml", '[toolchain]\nchannel = "trust"\n')
        write(cg / "crates" / "trust-cg-regalloc" / "Cargo.toml",
              f'[dependencies]\nay-pb = {{ version = "{AY_PIN_VERSION}", git = "https://github.com/{ORG}/ay.git", '
              f'rev = "{self.ay_rev}", optional = true }}\n')
        source = (SCRIPTS / "soundness_check.sh").read_text()
        for stem in bash_array(source, "TRUST_CG_LEAN"):
            write(cg / "proofs" / f"{stem}.lean", "-- fixture\n")
        write(cg / "formal" / "lean" / "lakefile.lean", "-- fixture\n")
        write(cg / "formal" / "lean" / "scripts" / "AxiomAudit.lean", "-- fixture\n")
        sorries = bash_scalar(source, "BASELINE_LEAN_SORRY")
        axioms = bash_scalar(source, "BASELINE_LEAN_AXIOM")
        write(cg / "formal" / "lean" / "Trust" / "Model.lean",
              "-- fixture\n" + "".join("  sorry\n" for _ in range(sorries))
              + "".join(f"axiom a{i} : True\n" for i in range(axioms)))
        for mjs in ("wasm_difftest.mjs", "wasm_island_differential.mjs"):
            write(cg / "crates" / "trust-cg-codegen" / "examples" / mjs, "// fixture\n")
        git(cg, "add", "-A", env=env)
        git(cg, "commit", "-qm", "fixture trust-cg", env=env)

    def commit_all(self, message: str) -> str:
        env = dict(os.environ, GIT_CONFIG_GLOBAL=str(self.git_config), GIT_CONFIG_NOSYSTEM="1")
        git(self.cg, "add", "-A", env=env)
        git(self.cg, "commit", "-qm", message, env=env)
        return git(self.cg, "rev-parse", "HEAD", env=env)

    def head(self) -> str:
        return git(self.cg, "rev-parse", "HEAD")


def _no_other_writer_above(directory: str) -> bool:
    """Whether `directory` and every canonical ancestor are owned by this
    user or root and writable by neither group nor others."""
    path = os.path.realpath(directory)
    while True:
        try:
            metadata = os.lstat(path)
        except OSError:
            return False
        if metadata.st_uid not in (os.geteuid(), 0) or stat.S_IMODE(metadata.st_mode) & 0o022:
            return False
        parent = os.path.dirname(path)
        if parent == path:
            return True
        path = parent


# The directories a PATH lookup of the host's system commands searches, in
# the order the fixture's runs searched them before `system_commands`.
SYSTEM_PATH = ("/usr/bin", "/bin", "/usr/sbin", "/sbin")


def system_commands(directory: Path) -> Path:
    """Make `directory`, new and private, the fixture runs' view of the
    host's system commands, and return it: one link for each name a PATH
    lookup in SYSTEM_PATH finds (its first entry of that name), pointing at
    the path the lookup found it by, so a run's host trust boundary
    (scripts/host_boundary.py) judges the same lookups it judged with those
    directories on PATH.

    A name is left out when its file is not a regular file this user can
    examine, or when that file or a directory above it is owned by anyone
    but this user or root or is writable by a group or others
    (`_no_other_writer_above`, the fixture's own rule, not the one under
    test). Such an entry is the host's, not the fixture's, and the boundary
    refused every run whose PATH held its directory, whatever the test had
    planted: on macOS 27.0.1, /usr/bin/safaridriver and /usr/bin/safarimcp
    resolve through /System/Volumes/Preboot/Cryptexes (mode 0777, no sticky
    bit), and /usr/sbin/weakpass_edit points into /usr/sbin/authserver
    (root's, mode 0700), which this user cannot examine. On a host whose
    system commands are root's and writable by root alone nothing is left
    out. The production gate still judges the PATH it is given, the host's
    own directories included (OD-FIXTURE-SYSTEM-COMMANDS-20261022)."""
    directory.mkdir(mode=0o700)
    seen = set()
    for system in SYSTEM_PATH:
        try:
            names = sorted(os.listdir(system))
        except OSError:
            continue
        for name in names:
            if name in seen:
                continue
            seen.add(name)
            found = os.path.join(system, name)
            try:
                regular = stat.S_ISREG(os.stat(found).st_mode)
            except OSError:
                continue
            if regular and _no_other_writer_above(found):
                # Apple's /usr/bin/python3 dispatches to a different executable.
                # The gate pins that actual interpreter; expose the same file to
                # fixture legs rather than the dispatcher that the boundary rejects.
                if name == "python3":
                    probe = subprocess.run(
                        [found, "-I", "-S", "-c",
                         "import os, sys; print(os.path.realpath(sys.executable))"],
                        capture_output=True, text=True, timeout=30, check=True,
                    )
                    found = probe.stdout.strip()
                    if not os.path.isabs(found) or not _no_other_writer_above(found):
                        continue
                (directory / name).symlink_to(found)
    return directory


# A benign marker module of the X-HOST-P13 sixth closure audit's reproducer
# (OD-XHOST-GATE-CWD-20261025), planted under a standard library module's
# name: it appends one line to a marker file, then hands the import over to
# the standard library's module, so a program that imports it goes on
# unchanged.
MARKER_MODULE = '''# benign marker module (X-HOST-P13 sixth closure audit, OD-XHOST-GATE-CWD-20261025)
import os as _os, sys as _sys
with open({marker!r}, "a") as _handle:
    _handle.write("{name}.py imported: argv=%r cwd=%s\\n" % (_sys.argv[:2], _os.getcwd()))
_here = _os.path.dirname(_os.path.abspath(__file__))
_saved = list(_sys.path)
_sys.path[:] = [_entry for _entry in _sys.path if _os.path.abspath(_entry or ".") != _here]
_sys.modules.pop({name!r}, None)
import importlib as _importlib
_real = _importlib.import_module({name!r})
_sys.path[:] = _saved
_sys.modules[{name!r}] = _real
'''
MARKER_MODULE_NAMES = ("json", "hashlib", "datetime")


def plant_marker_modules(directory: Path, marker: Path, mode: int = 0o666) -> list[Path]:
    """Plant MARKER_MODULE as json.py, hashlib.py and datetime.py in
    `directory`, each `mode` (writable by every user by default), logging to
    `marker`."""
    planted = []
    for name in MARKER_MODULE_NAMES:
        path = directory / f"{name}.py"
        path.write_text(MARKER_MODULE.format(marker=str(marker), name=name))
        os.chmod(path, mode)
        planted.append(path)
    return planted


def fixture_root() -> str:
    """The directory fixture constellations are made in. An --attest run
    refuses a candidate checkout or cache below a directory in which another
    user can create an entry (ruling LD-75: that user could create the
    `.cargo` Cargo reads there), so /tmp, world-writable and sticky, cannot
    hold one; and the shared-group cases need ancestors no group can write.
    SOUNDNESS_TEST_TMPDIR when set (the runner's choice, used as given); else
    the system temporary directory when no group or other user can write it
    or any ancestor (macOS's per-user TMPDIR); else XDG_RUNTIME_DIR, or
    /run/user/<uid>, the Linux per-user runtime directory, on the same
    condition. Raises with the remedy when none qualifies."""
    import tempfile
    explicit = os.environ.get("SOUNDNESS_TEST_TMPDIR")
    if explicit:
        return explicit
    candidates = [tempfile.gettempdir(), os.environ.get("XDG_RUNTIME_DIR") or "", f"/run/user/{os.geteuid()}"]
    for candidate in candidates:
        if candidate and os.path.isabs(candidate) and os.path.isdir(candidate) and \
                _no_other_writer_above(candidate):
            return candidate
    raise RuntimeError("no directory for the soundness fixtures: an --attest run refuses a checkout below a "
                       "directory another user can create entries in (LD-75), and none of "
                       f"{[c for c in candidates if c]} is free of one; set SOUNDNESS_TEST_TMPDIR to a directory "
                       "that only you (or root) can write, and every directory above it too")


class FixtureDirectory:
    """A temporary directory whose cleanup tolerates processes a stopped run
    was still winding down (a killed remote dispatch), made below
    fixture_root().

    `name` is the directory's canonical path. The gate names every path its
    privacy rule judged by its canonical path (soundness_check.sh
    `private_path`), and on macOS the temporary directory itself is reached
    through a symlink (/var -> /private/var), so a fixture world built under
    the canonical path is spelled the way the gate prints it.
    """

    def __init__(self, prefix: str):
        import tempfile
        self.name = os.path.realpath(tempfile.mkdtemp(prefix=prefix, dir=fixture_root()))

    def cleanup(self) -> None:
        import time
        for _ in range(20):
            shutil.rmtree(self.name, ignore_errors=True)
            if not os.path.exists(self.name):
                return
            time.sleep(0.25)


def logdir_of(result: subprocess.CompletedProcess) -> Path | None:
    """The run's log directory, from its banner line `logs     : <dir>`."""
    for line in result.stdout.splitlines():
        if line.startswith("logs     : "):
            return Path(line.split(":", 1)[1].strip())
    return None


def load_inventory(cg: Path) -> list[dict]:
    result = subprocess.run(["bash", str(cg / "scripts" / "soundness_check.sh"), "--list-json"],
                            capture_output=True, text=True, check=True, env=dict(os.environ, TRUST_CG_DIR=str(cg)))
    return json.loads(result.stdout)["legs"]
