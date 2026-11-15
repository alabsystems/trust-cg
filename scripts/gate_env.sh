#!/usr/bin/env bash
#
# gate_env.sh — the repository-owned gate environment prelude and preflight.
#
# TWO USES
# --------
#   source scripts/gate_env.sh              # bash or zsh: PATH prelude ONLY
#   gate_env_prelude --with-lean            # (after sourcing) also ~/.elan/bin
#   scripts/gate_env.sh [options]           # run the preflight checks below
#
# Sourcing is side-effect-minimal and never fails a caller on host state: it
# defines gate_env_prelude and applies it. The Rust toolchain is the installed
# Trust package on PATH (rust-toolchain.toml pins `channel = "trust"`; owner
# directive 2026-09-28), so the prelude no longer puts rustup's stock proxies
# first. With --with-lean, "$HOME/.elan/bin" goes first; with
# --with-managed-bin, aterm's managed bin/ follows. Existing copies of those
# entries are removed first, so resolution is exactly that of a plain prepend.
# soundness_check.sh sources this instead of its own prelude.
#
# Running it performs the checks and prints every resolved identity so a gate
# log records the toolchain it ran under. Findings are named, stable codes.
# FAIL (exit 1):
#   GATE_ENV_RUST_PIN_DRIFT / _UNREADABLE  rust-toolchain.toml is not
#                                          `channel = "trust"`
#   GATE_ENV_TRUST_TOOLCHAIN_ABSENT        no Trust toolchain resolves: there is
#                                          no stock fallback
#   GATE_ENV_TRUSTC_NOT_ON_PATH            only an aterm-managed trustc resolves;
#                                          the gates run the PATH package
#   GATE_ENV_TARGO_MISSING / _NOT_TARGO    no PATH targo beside trustc, or it
#                                          rejects `--unverified` (upstream cargo
#                                          shipped under the name does)
#   GATE_ENV_TRUST_UNSTAMPED               the effective trustc reports no
#                                          branded 40-hex commit identity
#   GATE_ENV_HOST_NOT_AARCH64              trustc host is not aarch64-apple-darwin
#                                          or aarch64-unknown-linux-gnu (with
#                                          --allow-x86_64-host, x86_64-apple-darwin
#                                          and x86_64-unknown-linux-gnu are accepted)
#   GATE_ENV_TRUST_TOOLCHAINS_DIVERGENT    rustup's `trust` link and the PATH (or
#                                          atpkg-managed) trustc are different
#                                          toolchains (another root that is not a
#                                          byte-identical copy of the same commit)
#                                          and TRUST_CG_TOOLCHAIN_LANE does not
#                                          select one (rustup | path) (pass it on
#                                          this command line only: Trust
#                                          compilers refuse any exported
#                                          TRUST_CG_* or TCG_* variable)
#   GATE_ENV_TRUST_LANE_INVALID / _UNAVAILABLE, GATE_ENV_TRUST_PATH_SPLIT,
#   GATE_ENV_TRUST_IDENTITY_UNKNOWN        a resolved Trust compiler's -vV or
#                                          --print sysroot fails
#   GATE_ENV_LEAN_TOOLCHAIN_ABSENT         formal/lean/lean-toolchain's Lean is not
#                                          installed; the re-provisioning recipe
#                                          from reports/2026-09-10-soundness-
#                                          prerequisites is printed
#   GATE_ENV_LEAN_PIN_UNREADABLE, GATE_ENV_LAKE_MISSING / _REROUTED,
#   GATE_ENV_LEAN_VERSION_MISMATCH
#   GATE_ENV_AY_PIN_UNREADABLE             the ay-pb pin in
#                                          crates/trust-cg-regalloc/Cargo.toml
#                                          cannot be read
#   GATE_ENV_OVERRIDE_NOT_EXECUTABLE       AY_SOLVER_PATH / TCG_EXTERNAL_CLEAN_CHECKER
#                                          / TCG_CLEAN_CHECKER names no executable
#   GATE_ENV_AY_OVERRIDE_REFUSED           AY_SOLVER_PATH is relative, or its bytes
#                                          are not the effective Trust toolchain's
#                                          bin/ay, so trust-cg-verify would refuse it
#                                          (crates/trust-cg-verify/src/ay_identity.rs)
#   GATE_ENV_PYTHON_MISSING                the check itself cannot run
#   GATE_ENV_PYTHON_TOMLLIB                Python lacks the certificate gate parser
# WARN (exit status unchanged):
#   GATE_ENV_AY_PIN_MISMATCH / GATE_ENV_AY_VERSION_UNKNOWN  (loud; stdout and
#     stderr) the EFFECTIVE AY is not the ay-pb pin version. That is the one AY
#     trust-cg admits: the effective Trust toolchain's bin/ay (an AY_SOLVER_PATH
#     is admitted only as a byte copy of it). aterm's managed ay is never
#     consulted by trust-cg, so it is listed but neither executed nor compared.
#     No AY is executed by this preflight: each Trust bundle's AY version is
#     the build stamp read from the file's bytes, printed with its SHA-256.
#     Never a solver switch; --require-ay-pin makes the effective solver's
#     mismatch, unknown version or absence (GATE_ENV_AY_UNRESOLVED) a FAIL.
#   GATE_ENV_BUNDLE_AY_PIN_MISMATCH        another Trust bundle ships another ay
#   GATE_ENV_MANAGED_TOOL_ABSENT, GATE_ENV_TRUST_LANE_OVERRIDE (divergence
#   accepted by an explicit TRUST_CG_TOOLCHAIN_LANE), GATE_ENV_TRUST_ENV_CONTROLS
#   (TRUST_CG_* or TCG_* variables are set; Trust identities are probed without
#   them)
#
# Options (check mode only):
#   --with-managed-bin   also put aterm's managed bin/ on PATH before checking
#   --require-ay-pin     fail unless the effective AY equals the ay-pb pin version
#   --allow-x86_64-host  also accept an x86-64 Darwin/Linux trustc host (the
#                        soundness gate passes it on a native x86-64 host)
#   -h, --help           print this header
#
# Exit status: 0 = no FAIL (warnings allowed), 1 = at least one FAIL or the
# check could not run, 2 = invalid usage.
#
# Probes set RUSTUP_AUTO_INSTALL=0, so rustup (1.28.1 or later) reports a missing
# toolchain instead of downloading it; elan's lake proxy is never executed.
#
# WHAT THIS IS NOT: it does not install, relink or select tools, does not enable
# Trust verification, and is not a soundness, proof or attestation result. A PASS
# only says the listed identities were resolved and matched these contracts.
#
# The sourced portion (everything outside gate_env_main's embedded Python) must
# stay POSIX-shell/zsh compatible and safe under `set -u`/`set -e` callers.

gate_env_repo_root() {
    if [ -n "${TRUST_CG_DIR:-}" ]; then
        printf '%s' "$TRUST_CG_DIR"
        return 0
    fi
    # Check mode runs under bash only (see the entry point below).
    # CDPATH=: a relative script directory is never looked up in a CDPATH
    # (OD-XHOST-GATE-CWD-20261025, repair round 2).
    (CDPATH= cd -- "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
}

gate_env_managed_bin_dir() {
    # aterm's managed launchers. ATPKG_BIN is aterm's own name for this
    # directory; otherwise use atpkg's platform default, the same prefixes
    # crates/trust-cg-verify/src/aterm_toolchain.rs searches.
    if [ -n "${ATPKG_BIN:-}" ]; then
        printf '%s' "$ATPKG_BIN"
    elif [ "$(uname -s 2>/dev/null)" = Darwin ]; then
        printf '%s' "${HOME:-}/Library/Application Support/aterm/pkg/bin"
    else
        printf '%s' "${HOME:-}/.local/share/aterm/pkg/bin"
    fi
}

# Print $2 (a PATH string) with every entry exactly equal to $1 removed. Empty
# entries (the current directory) are preserved; nothing new is introduced.
gate_env_path_without() {
    _gate_env_rest=":$2:"
    while :; do
        case "$_gate_env_rest" in
            *":$1:"*)
                _gate_env_rest="${_gate_env_rest%%":$1:"*}:${_gate_env_rest#*":$1:"}"
                ;;
            *) break ;;
        esac
    done
    _gate_env_rest="${_gate_env_rest#:}"
    printf '%s' "${_gate_env_rest%:}"
}

gate_env_prelude() {
    _gate_env_with_lean=0
    _gate_env_with_managed=0
    for _gate_env_arg in "$@"; do
        case "$_gate_env_arg" in
            --with-lean) _gate_env_with_lean=1 ;;
            --with-managed-bin) _gate_env_with_managed=1 ;;
            *)
                printf 'gate_env: unknown prelude option: %s\n' "$_gate_env_arg" >&2
                return 2
                ;;
        esac
    done
    _gate_env_head=""
    _gate_env_path="${PATH:-}"
    if [ "$_gate_env_with_lean" = 1 ]; then
        if [ -z "${HOME:-}" ]; then
            printf '%s\n' 'gate_env: HOME is unset; cannot locate ~/.elan/bin' >&2
            return 1
        fi
        _gate_env_head="$HOME/.elan/bin"
        _gate_env_path="$(gate_env_path_without "$HOME/.elan/bin" "$_gate_env_path")"
    fi
    if [ "$_gate_env_with_managed" = 1 ]; then
        _gate_env_bin="$(gate_env_managed_bin_dir)"
        if [ -d "$_gate_env_bin" ]; then
            _gate_env_head="${_gate_env_head:+$_gate_env_head:}$_gate_env_bin"
            _gate_env_path="$(gate_env_path_without "$_gate_env_bin" "$_gate_env_path")"
        fi
    fi
    if [ -z "$_gate_env_head" ]; then
        :
    elif [ -n "$_gate_env_path" ]; then
        PATH="$_gate_env_head:$_gate_env_path"
    else
        PATH="$_gate_env_head"
    fi
    export PATH
    unset _gate_env_with_lean _gate_env_with_managed _gate_env_arg \
        _gate_env_head _gate_env_path _gate_env_bin _gate_env_rest
    return 0
}

gate_env_usage() {
    awk 'NR == 1 { next } !/^#/ { exit } { sub(/^# ?/, ""); print }' "$1"
}

gate_env_main() {
    _gate_env_script="$1"
    shift
    _gate_env_prelude_args="--with-lean"
    for _gate_env_arg in "$@"; do
        case "$_gate_env_arg" in
            -h|--help) gate_env_usage "$_gate_env_script"; return 0 ;;
            --with-managed-bin) _gate_env_prelude_args="--with-lean --with-managed-bin" ;;
            --require-ay-pin|--allow-x86_64-host) ;;
            *)
                printf 'gate_env: unknown option: %s (see --help)\n' "$_gate_env_arg" >&2
                return 2
                ;;
        esac
    done
    # The check's python3, resolved ONCE and before the prelude below changes
    # PATH (it puts $HOME/.elan/bin first): the soundness gate's pinned
    # interpreter when the gate started this check (SOUNDNESS_PYTHON3, its
    # canonical path), else the one PATH finds now (repair round 3 of
    # OD-XHOST-GATE-CWD-20261025). A python3 the prelude's PATH names first
    # never runs. Check mode runs under bash only (`type -P`).
    SOUNDNESS_PYTHON3="${SOUNDNESS_PYTHON3:-$(type -P python3 || true)}"
    case "$SOUNDNESS_PYTHON3" in
        /*) ;;
        *)
            printf '%s\n' "gate_env: FAIL GATE_ENV_PYTHON_MISSING: the check needs python3: no executable file by an absolute path (SOUNDNESS_PYTHON3, else PATH) was found (found: ${SOUNDNESS_PYTHON3:-nothing})" >&2
            return 1
            ;;
    esac
    if [ ! -f "$SOUNDNESS_PYTHON3" ] || [ ! -x "$SOUNDNESS_PYTHON3" ]; then
        printf '%s\n' "gate_env: FAIL GATE_ENV_PYTHON_MISSING: SOUNDNESS_PYTHON3=${SOUNDNESS_PYTHON3:-} is not an executable file; the check cannot run" >&2
        return 1
    fi
    # shellcheck disable=SC2086  # two fixed words, deliberately split
    gate_env_prelude $_gate_env_prelude_args || return 1
    _gate_env_root="$(gate_env_repo_root)" || return 1
    # -I: the check imports only the standard library and, by the explicit
    # sys.path entry below, scripts/trust_toolchain.py. Without it `python3 -`
    # puts the working directory first on sys.path, so a json.py or
    # datetime.py there ran as this user (sixth X-HOST-P13 closure audit;
    # OD-XHOST-GATE-CWD-20261025). PYTHON* variables are ignored too.
    "$SOUNDNESS_PYTHON3" -I - "$_gate_env_root" "$@" <<'GATE_ENV_PY'
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

EXPECTED_CHANNEL = "trust"
AARCH64_HOSTS = ("aarch64-apple-darwin", "aarch64-unknown-linux-gnu")
TIMEOUT_SECONDS = 120
PREREQ_REPORT = "reports/2026-09-10-soundness-prerequisites"

ROOT = Path(sys.argv[1])
sys.path.insert(0, str(ROOT / "scripts"))
from trust_toolchain import COMPILER_DIGEST_BIN, launcher_target, same_compiler  # noqa: E402

OPTIONS = sys.argv[2:]
REQUIRE_AY_PIN = "--require-ay-pin" in OPTIONS
X86_64_HOSTS = ("x86_64-apple-darwin", "x86_64-unknown-linux-gnu")
ACCEPTED_HOSTS = AARCH64_HOSTS + (X86_64_HOSTS if "--allow-x86_64-host" in OPTIONS else ())
FAILURES = []
WARNINGS = []
# Probes must not install anything. rustup's proxies install a missing
# toolchain on first use (a network download) unless RUSTUP_AUTO_INSTALL=0.
PROBE_ENV = dict(os.environ, RUSTUP_AUTO_INSTALL="0")


def emit(kind, text):
    print(f"gate_env: {kind} {text}" if kind else f"gate_env: {text}", flush=True)


def ok(text):
    emit("PASS", text)


def info(text):
    emit("INFO", text)


def fail(code, text):
    FAILURES.append(code)
    emit("FAIL", f"{code}: {text}")


def warn(code, text, loud=False):
    WARNINGS.append(code)
    line = f"gate_env: WARN {code}: {text}"
    if loud:
        bar = "gate_env: " + "!" * 72
        for stream in (sys.stdout, sys.stderr):
            print(bar, line, bar, sep="\n", file=stream, flush=True)
    else:
        print(line, flush=True)


def section(title):
    print(f"gate_env: ---- {title}", flush=True)


def run(argv, cwd=None, env=None):
    """Run a probe; return (rc, stdout, stderr). rc is None if it could not run."""
    try:
        result = subprocess.run(
            argv, cwd=cwd, env=PROBE_ENV if env is None else env, stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=TIMEOUT_SECONDS, check=False,
        )
    except subprocess.TimeoutExpired:
        return None, "", f"timed out after {TIMEOUT_SECONDS}s"
    except OSError as error:
        return None, "", str(error)
    return (result.returncode, result.stdout.decode("utf-8", "replace"),
            result.stderr.decode("utf-8", "replace"))


def first_line(text):
    for line in text.splitlines():
        if line.strip():
            return line.strip()
    return ""


def executable(path):
    return path is not None and os.path.isfile(path) and os.access(path, os.X_OK)


def is_reroute(path):
    # atpkg marks its reroute directory; a stub there is never an install.
    return (Path(path).parent / ".atpkg-reroute-dir").exists()


def vv_fields(text):
    fields = {}
    for line in text.splitlines()[1:]:
        key, sep, value = line.partition(": ")
        if sep:
            fields[key.strip()] = value.strip()
    return fields


def managed_prefixes():
    """Managed package roots, in the order of aterm_toolchain.rs's fallback."""
    prefixes = []
    if os.environ.get("ATPKG_BIN"):
        prefixes.append(Path(os.environ["ATPKG_BIN"]).parent)
    home = os.environ.get("HOME", "")
    if home:
        if sys.platform == "darwin":
            prefixes.append(Path(home) / "Library/Application Support/aterm/pkg")
        else:
            prefixes.append(Path(home) / ".local/share/aterm/pkg")
    return prefixes


def store_path_ok(path, tool, package):
    # <prefix>/store/<package>/<version>/bin/<tool>
    parts = Path(path).parts
    return (len(parts) >= 5 and parts[-1] == tool and parts[-2] == "bin"
            and parts[-4] == package and parts[-5] == "store")


def parse_pkg_which(text, tool):
    # "<tool> → <launcher> → <store binary> — managed <id> — ..."
    for line in text.splitlines():
        if not line.startswith(f"{tool} → "):
            continue
        chain = line.split(" — ", 1)[0].split(" → ")
        candidate = chain[-1].strip()
        if os.path.isabs(candidate):
            return candidate
    return None


def managed_tool(tool, package):
    """Resolve an aterm-managed tool to its versioned store executable.

    Launchers are never parsed: the answer is either `aterm pkg which`'s
    resolved store path or <prefix>/store/<package>/current/bin/<tool>.
    """
    aterm = shutil.which("aterm")
    if aterm:
        rc, out, err = run([aterm, "pkg", "which", tool])
        if rc == 0:
            candidate = parse_pkg_which(out, tool)
            if candidate and store_path_ok(candidate, tool, package) and executable(candidate):
                return os.path.realpath(candidate), f"aterm pkg which {tool}"
            info(f"`aterm pkg which {tool}` named no store executable: "
                 f"{first_line(out) or first_line(err) or '(no output)'}")
        else:
            info(f"`aterm pkg which {tool}` exited {rc}: {first_line(err) or first_line(out)}")
    for prefix in managed_prefixes():
        candidate = prefix / "store" / package / "current" / "bin" / tool
        if executable(str(candidate)):
            return os.path.realpath(candidate), f"store layout under {prefix}"
    return None, None


def sha256_file(path):
    digest = hashlib.sha256()
    with open(path, "rb") as source:
        for chunk in iter(lambda: source.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


# AY's build stamp, `<version>+build.<increment>.<commit>@<UTC time>`, is the
# string `ay --version` prints, and it is embedded in the binary's bytes.
AY_BUILD_STAMP = re.compile(
    rb"(\d+\.\d+\.\d+)\+build\.(\d+)\.([0-9a-f]{7,40})@\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ")


def ay_version(path):
    """The AY build (version, commit, one-line description) read from its BYTES.

    No AY is executed here. trust-cg's AY identity rule
    (crates/trust-cg-verify/src/ay_identity.rs) never runs a candidate to
    decide anything, and this preflight has no recorded digest to admit one
    against, so it reads the build stamp embedded in the file instead of
    running `--version`. The stamp is a label, not an identity: the identity is
    the SHA-256, which is printed with it and is what the override check
    compares. A file whose bytes carry no stamp, or several different builds'
    stamps, has an unknown version.
    """
    try:
        data = Path(path).read_bytes()
    except OSError as error:
        return None, None, f"unreadable: {error}"
    digest = hashlib.sha256(data).hexdigest()
    builds = sorted({match.groups() for match in AY_BUILD_STAMP.finditer(data)})
    if len(builds) != 1:
        found = "no AY build stamp" if not builds else f"{len(builds)} different AY build stamps"
        return None, None, f"{found} in its bytes; sha256 {digest} (not executed)"
    version, increment, commit = (part.decode() for part in builds[0])
    return version, commit, (f"ay {version} build {increment} commit {commit}, read from its bytes; "
                             f"sha256 {digest} (not executed)")


# ---------------------------------------------------------------------------
NOW = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
emit("", f"gate environment preflight at {NOW}")
emit("", f"repository: {ROOT}")
rc, head, _ = run(["git", "-C", str(ROOT), "rev-parse", "HEAD"])
emit("", f"revision: {head.strip() if rc == 0 else 'not a Git checkout'}")
emit("", f"platform: {sys.platform} {os.uname().machine}")
emit("", "PATH head: " + " | ".join(os.get_exec_path()[:4]))

# The x86 certificate gate uses this same isolated interpreter and stdlib.
# Refuse here, before the expensive campaign, rather than at its final leg.
info(f"Python interpreter: {sys.executable} {sys.version.split()[0]}")
try:
    import tomllib
except ImportError as error:
    fail("GATE_ENV_PYTHON_TOMLLIB", f"isolated Python requires stdlib tomllib: {error}")
else:
    ok("isolated Python imports stdlib tomllib")

# ---------------------------------------------------------------------------
section("Trust toolchain pin (rust-toolchain.toml)")
toolchain_file = ROOT / "rust-toolchain.toml"
try:
    channels = re.findall(r'^channel\s*=\s*"([^"]+)"\s*$', toolchain_file.read_text(), re.M)
except OSError as error:
    channels = []
    info(f"cannot read {toolchain_file}: {error}")
if len(channels) != 1:
    fail("GATE_ENV_RUST_PIN_UNREADABLE",
         f"{toolchain_file} must contain exactly one channel line (found {len(channels)})")
elif channels[0] != EXPECTED_CHANNEL:
    fail("GATE_ENV_RUST_PIN_DRIFT",
         f"rust-toolchain.toml channel {channels[0]!r} is not the Trust toolchain ({EXPECTED_CHANNEL!r}); "
         "ALab systems build with Trust, and a toolchain change must update gate_env.sh and its tests together")
else:
    ok(f"rust-toolchain.toml channel {EXPECTED_CHANNEL}")
info("Cargo legs run through the Trust package's targo (scripts/trust_cargo.sh); "
     "bare `rustc`/`cargo` on PATH are not consulted")

# ---------------------------------------------------------------------------
section("aterm-managed proof tools and explicit overrides")
managed = {}
for tool in ("ay", "clean"):
    path, source = managed_tool(tool, tool)
    managed[tool] = path
    if tool == "ay":
        # trust-cg admits only the owning Trust toolchain's bin/ay
        # (crates/trust-cg-verify/src/ay_identity.rs); a managed ay is never
        # a solver there, so it is not executed and its absence is no finding.
        if path is not None:
            info(f"managed ay: {path} (via {source}): not consulted by trust-cg; not executed")
        continue
    if path is None:
        warn("GATE_ENV_MANAGED_TOOL_ABSENT",
             f"no aterm-managed {tool} (checked `aterm pkg which`, ATPKG_BIN and "
             f"{', '.join(str(p) for p in managed_prefixes()) or 'no HOME'})")
        continue
    rc, out, err = run([path, "--version"])
    version_line = first_line(out) if rc == 0 else f"--version failed: {first_line(err) or rc}"
    info(f"managed {tool}: {path} (via {source}): {version_line}")

overrides = {}
for variable in ("AY_SOLVER_PATH", "TCG_EXTERNAL_CLEAN_CHECKER", "TCG_CLEAN_CHECKER"):
    value = os.environ.get(variable)
    if value is None:
        continue
    if not executable(value):
        fail("GATE_ENV_OVERRIDE_NOT_EXECUTABLE", f"{variable}={value} is not an executable file")
        continue
    if variable == "AY_SOLVER_PATH":
        if not os.path.isabs(value):
            fail("GATE_ENV_AY_OVERRIDE_REFUSED",
                 f"AY_SOLVER_PATH={value} is not absolute; trust-cg-verify never looks an AY up "
                 "(TCG-AY-IDENTITY-OVERRIDE-NOT-ABSOLUTE)")
            continue
        # Judged below by its bytes against the toolchain AY; never executed.
        overrides[variable] = value
        info(f"override AY_SOLVER_PATH: {value}: sha256 {sha256_file(value)}")
        continue
    overrides[variable] = os.path.realpath(value)
    rc, out, err = run([value, "--version"])
    info(f"override {variable}: {overrides[variable]}: "
         f"{first_line(out) if rc == 0 else first_line(err) or rc}")
if "TCG_EXTERNAL_CLEAN_CHECKER" in overrides and "TCG_CLEAN_CHECKER" in overrides:
    info("TCG_EXTERNAL_CLEAN_CHECKER takes precedence over legacy TCG_CLEAN_CHECKER")

# ---------------------------------------------------------------------------
section("Trust toolchains (rustup `trust` link vs PATH/managed trustc)")


# Trust compilers refuse every untracked TRUST_CG_* / TCG_* environment control
# (measured: `--print sysroot` exits 1, "... is an untracked Trust
# semantic/codegen control"). Probe their identity without those variables, and
# say so when they are present: a Trust-lane build in this environment would
# fail the same way. TRUST_CG_TOOLCHAIN_LANE is itself such a variable, so pass it
# on the gate_env.sh command line only.
TRUST_ENV_CONTROLS = sorted(k for k in os.environ if k.startswith(("TRUST_CG_", "TCG_")))
TRUST_PROBE_ENV = {k: v for k, v in PROBE_ENV.items() if k not in TRUST_ENV_CONTROLS}


def trust_identity(compiler):
    # An atpkg launcher shim execs the package compiler; name that file.
    target = launcher_target(Path(compiler))
    if target is not None and executable(str(target)):
        compiler = str(target)
    rc, out, err = run([compiler, "-vV"], cwd=str(ROOT), env=TRUST_PROBE_ENV)
    if rc != 0:
        return None, f"{compiler} -vV failed: {first_line(err) or first_line(out) or rc}"
    fields = vv_fields(out)
    # Never infer a sysroot from the path: a launcher's grandparent is not one.
    rc, sysroot, err = run([compiler, "--print", "sysroot"], cwd=str(ROOT), env=TRUST_PROBE_ENV)
    if rc != 0 or not sysroot.strip():
        return None, f"{compiler} --print sysroot failed: {first_line(err) or rc}"
    root = os.path.realpath(sysroot.strip())
    return {
        "compiler": compiler, "root": root, "version": first_line(out),
        "binary": fields.get("binary", ""), "commit": fields.get("commit-hash", ""),
        "llvm": fields.get("LLVM version", ""), "host": fields.get("host", ""),
    }, None


def describe(label, identity):
    info(f"{label}: {identity['compiler']}")
    info(f"  sysroot {identity['root']}; {identity['version']}; binary {identity['binary'] or '?'}; "
         f"commit-hash {identity['commit'] or '?'}; LLVM {identity['llvm'] or '?'}")
    bundle_ay = Path(identity["root"]) / "bin" / "ay"
    if executable(str(bundle_ay)):
        identity["ay"] = ay_version(str(bundle_ay))
        info(f"  bundled ay: {identity['ay'][2]}")


lanes = {}
rustup = shutil.which("rustup")
rustup_rustc = None
if rustup:
    rc, out, err = run([rustup, "which", "--toolchain", "trust", "rustc"], cwd=str(ROOT))
    if rc == 0 and out.strip():
        rustup_rustc = out.strip().splitlines()[-1]
        source = "rustup which --toolchain trust rustc"
    else:
        info(f"rustup `trust` toolchain: not linked ({first_line(err) or first_line(out) or rc})")
else:
    link = Path(os.environ.get("RUSTUP_HOME") or Path(os.environ.get("HOME", "/")) / ".rustup") \
        / "toolchains" / "trust" / "bin" / "rustc"
    if executable(str(link)):
        rustup_rustc = str(link)
        source = "RUSTUP_HOME toolchains/trust (rustup itself is not on PATH)"
    else:
        info("rustup `trust` toolchain: rustup not on PATH and no toolchains/trust link")
if rustup_rustc:
    identity, error = trust_identity(rustup_rustc)
    if identity:
        identity["source"] = source
        lanes["rustup"] = identity
        describe(f"rustup `trust` ({source})", identity)
    else:
        fail("GATE_ENV_TRUST_IDENTITY_UNKNOWN",
             f"rustup `trust` resolves but its identity cannot be measured, so divergence cannot be decided: {error}")

def package_file(tool):
    """A PATH tool's package file: the file an atpkg launcher shim execs."""
    resolved = Path(tool).resolve()
    target = launcher_target(resolved)
    return target.resolve() if target is not None else resolved


trustc = shutil.which("trustc")
targo = shutil.which("targo")
if trustc:
    if targo is None:
        fail("GATE_ENV_TARGO_MISSING", f"PATH trustc {trustc} has no PATH targo beside it")
    elif package_file(trustc).parent != package_file(targo).parent:
        fail("GATE_ENV_TRUST_PATH_SPLIT",
             f"PATH trustc ({trustc}) and targo ({targo}) do not resolve to one installed package")
    else:
        # The one discriminator between targo and upstream cargo shipped under
        # its name: upstream rejects `--unverified`. It runs the package file,
        # never a launcher shim: the gates run that file, and a shim's shell
        # prelude, which the resolver reads but never runs
        # (DR-ATPKG-PRELUDE-SHIM-20261015), could answer for it.
        targo_file = str(package_file(targo))
        rc, out, err = run([targo_file, "--unverified", "--version"], cwd=str(ROOT), env=TRUST_PROBE_ENV)
        if rc == 0 and first_line(out).startswith("targo "):
            ok(f"PATH targo is targo: {first_line(out)}")
        else:
            fail("GATE_ENV_TARGO_NOT_TARGO",
                 f"{targo_file} --unverified --version: {first_line(err) or first_line(out) or rc}; "
                 "upstream cargo under the name targo rejects the flag")
    path_source = "PATH"
else:
    trustc, path_source = managed_tool("trustc", "trust")
    if trustc:
        path_source = f"managed package via {path_source}; NOT on PATH"
        fail("GATE_ENV_TRUSTC_NOT_ON_PATH",
             f"the gates resolve trustc/targo from PATH (scripts/trust_toolchain.py), but the managed "
             f"package {trustc} is not on PATH; put aterm's bin/ on PATH (or pass --with-managed-bin)")
if trustc:
    identity, error = trust_identity(trustc)
    if identity:
        identity["source"] = path_source
        lanes["path"] = identity
        describe(f"PATH/managed trustc ({path_source})", identity)
    else:
        fail("GATE_ENV_TRUST_IDENTITY_UNKNOWN",
             f"PATH/managed trustc resolves but its identity cannot be measured, so divergence cannot be "
             f"decided: {error}")
else:
    info("PATH/managed trustc: none (no trustc on PATH and no managed trust package)")
if TRUST_ENV_CONTROLS and (rustup_rustc or trustc):
    warn("GATE_ENV_TRUST_ENV_CONTROLS",
         f"{', '.join(TRUST_ENV_CONTROLS)} set here; Trust compilers refuse untracked TRUST_CG_*/TCG_* "
         "variables for real invocations, so the identities above were probed without them. Keep them out "
         "of Trust-lane build environments; pass TRUST_CG_TOOLCHAIN_LANE on the gate_env.sh command line only")

def same_compiler_copies(first, second):
    # Two roots carry one compiler when they report the same branded commit and
    # the same compiler bytes (scripts/trust_toolchain.py compiler_digest):
    # aterm's rustup `trust` link is a copied tree of the store package.
    # Anything else stays divergent.
    return same_compiler(Path(first["root"]), first["commit"], Path(second["root"]), second["commit"])


def build_tool_differences(first, second):
    names = sorted({p.name for root in (first, second) for p in (Path(root) / "bin").iterdir()}
                   - set(COMPILER_DIGEST_BIN))
    differences = []
    for name in names:
        left, right = Path(first) / "bin" / name, Path(second) / "bin" / name
        if not (left.is_file() and right.is_file()) or sha256_file(left) != sha256_file(right):
            differences.append(name)
    return differences


if (len(lanes) == 2 and lanes["rustup"]["root"] != lanes["path"]["root"]
        and same_compiler_copies(lanes["rustup"], lanes["path"])):
    ok(f"rustup `trust` ({lanes['rustup']['root']}) carries the same compiler as the PATH/managed "
       f"package {lanes['path']['root']}: commit-hash {lanes['path']['commit']}, byte-identical "
       + ", ".join(f"bin/{name}" for name in COMPILER_DIGEST_BIN) + ", lib/ and libexec/")
    differing = build_tool_differences(lanes["rustup"]["root"], lanes["path"]["root"])
    if differing:
        info("their other bin/ tools differ (not the compiler; the gates run the PATH package's targo): "
             + ", ".join(differing))
    lanes["rustup"]["root"] = lanes["path"]["root"]
selected = os.environ.get("TRUST_CG_TOOLCHAIN_LANE", "")
effective = None
if selected and selected not in ("rustup", "path"):
    fail("GATE_ENV_TRUST_LANE_INVALID",
         f"TRUST_CG_TOOLCHAIN_LANE={selected!r}; accepted values are 'rustup' and 'path'")
elif selected and selected not in lanes:
    fail("GATE_ENV_TRUST_LANE_UNAVAILABLE",
         f"TRUST_CG_TOOLCHAIN_LANE={selected} selects a Trust toolchain that was not resolved here")
elif len(lanes) == 2 and lanes["rustup"]["root"] != lanes["path"]["root"]:
    both = (f"rustup `trust` -> {lanes['rustup']['root']} (commit-hash {lanes['rustup']['commit'] or '?'}) vs "
            f"PATH/managed trustc -> {lanes['path']['root']} (commit-hash {lanes['path']['commit'] or '?'})")
    if not selected:
        fail("GATE_ENV_TRUST_TOOLCHAINS_DIVERGENT",
             f"two different Trust toolchains: {both}. `channel = \"trust\"` builds "
             "through the rustup proxies (crates/rustc-codegen-trust-cg) use the rustup link while "
             "run_full_test_matrix.sh --check-rustc-backend-env and check_linux_aarch64_bridge.py use PATH "
             "trustc/targo, so the backend would be built and loaded by different compilers depending on "
             "the entry point. Relink one to the other (`rustup toolchain link trust <sealed sysroot>` or "
             "`aterm pkg repair`), or set TRUST_CG_TOOLCHAIN_LANE=rustup|path to name the one this run uses")
    else:
        effective = lanes[selected]
        warn("GATE_ENV_TRUST_LANE_OVERRIDE",
             f"TRUST_CG_TOOLCHAIN_LANE={selected} selects {effective['root']} despite {both}; "
             + ("PATH-resolving scripts (run_full_test_matrix.sh, check_linux_aarch64_bridge.py) do not honour "
                "this selection" if selected == "rustup" else
                "`channel = \"trust\"` builds through the rustup proxies still resolve the rustup link"))
elif lanes:
    # The gates run the PATH package (scripts/trust_cargo.sh), so it is the
    # effective toolchain whenever it resolved.
    effective = lanes[selected] if selected else lanes.get("path") or next(iter(lanes.values()))
    if len(lanes) == 2:
        ok(f"rustup `trust` and PATH/managed trustc are one toolchain: {effective['root']}")
    else:
        info(f"only the {next(iter(lanes))} Trust lane is present: {effective['root']}")
else:
    fail("GATE_ENV_TRUST_TOOLCHAIN_ABSENT",
         "no Trust toolchain resolved: every Cargo leg runs on the installed Trust package and there is "
         "no stock fallback")
if effective is not None:
    if effective["binary"] != "trustc" or not re.fullmatch(r"[0-9a-f]{40}", effective["commit"]):
        fail("GATE_ENV_TRUST_UNSTAMPED",
             f"{effective['root']} reports binary {effective['binary'] or '(none)'} and commit-hash "
             f"{effective['commit'] or '(none)'}; the gates require the branded trustc with a 40-hex commit")
    if effective["host"] not in ACCEPTED_HOSTS:
        fail("GATE_ENV_HOST_NOT_AARCH64",
             f"trustc host is {effective['host'] or '(none)'}; expected one of {', '.join(ACCEPTED_HOSTS)}")
    else:
        ok(f"trustc host {effective['host']}")

# ---------------------------------------------------------------------------
section("AY solver coherence (crates/trust-cg-regalloc ay-pb pin)")
# The one AY trust-cg admits (crates/trust-cg-verify/src/ay_identity.rs): the
# bin/ay of the Trust toolchain that hosts the backend or builds
# trust-cg-verify, by the SHA-256 of its bytes; an absolute AY_SOLVER_PATH only
# as a byte copy of it.
info("Trust-lane builds of trust-cg-verify admit only that toolchain's bin/ay")
toolchain_ay = None
if effective is not None:
    candidate = Path(effective["root"]) / "bin" / "ay"
    if executable(str(candidate)):
        toolchain_ay = str(candidate)
if "AY_SOLVER_PATH" in overrides:
    override = overrides["AY_SOLVER_PATH"]
    if toolchain_ay is not None and sha256_file(override) == sha256_file(toolchain_ay):
        ok(f"AY_SOLVER_PATH {override} is a byte copy of {toolchain_ay}")
    else:
        fail("GATE_ENV_AY_OVERRIDE_REFUSED",
             f"AY_SOLVER_PATH {override} is not a byte copy of the effective Trust toolchain's AY "
             f"({toolchain_ay or 'none'}); trust-cg-verify refuses it (TCG-AY-IDENTITY-MISMATCH), "
             "it never falls back")
cargo_toml = ROOT / "crates/trust-cg-regalloc/Cargo.toml"
pin_version = pin_rev = None
try:
    pins = re.findall(r"^ay-pb\s*=\s*\{([^}\n]*)\}\s*$", cargo_toml.read_text(), re.M)
except OSError as error:
    pins = []
    info(f"cannot read {cargo_toml}: {error}")
if len(pins) == 1:
    version_match = re.search(r'\bversion\s*=\s*"=?(\d+\.\d+\.\d+)"', pins[0])
    rev_match = re.search(r'\brev\s*=\s*"([0-9a-f]{40})"', pins[0])
    if version_match and rev_match:
        pin_version, pin_rev = version_match.group(1), rev_match.group(1)
if pin_version is None:
    fail("GATE_ENV_AY_PIN_UNREADABLE",
         f"{cargo_toml} must contain exactly one `ay-pb = {{ version = \"X.Y.Z\", ..., rev = \"<40-hex>\" }}` line")
else:
    info(f"ay-pb pin: {pin_version} at rev {pin_rev}")

    def compare(label, path, strict):
        version, commit, line = ay_version(path)
        revision = f"; source revision {commit}" if commit else ""
        if version is None:
            code = "GATE_ENV_AY_VERSION_UNKNOWN"
            text = f"{label} {path} reports no version ({line})"
            if strict:
                fail(code, text)
            else:
                warn(code, text, loud=True)
        elif version != pin_version:
            code = "GATE_ENV_AY_PIN_MISMATCH"
            text = (f"{label} {path} is ay {version}{revision}, but crates/trust-cg-regalloc pins ay-pb "
                    f"{pin_version} (rev {pin_rev}). Proof-gate campaigns on this host would exercise a "
                    "different solver than the qualified pin; gate_env does NOT switch solvers "
                    "(use a Trust toolchain whose bin/ay is the pinned AY)")
            if strict:
                fail(code, text)
            else:
                warn(code, text, loud=True)
        else:
            # Only the version is compared: a coherent binary's build commit need
            # not equal the Cargo pin's source revision.
            ok(f"{label} ay {version} matches the ay-pb pin version{revision} "
               f"(pin rev {pin_rev}; revisions are not compared)")

    if toolchain_ay is None:
        text = "no effective Trust toolchain with a bin/ay: trust-cg has no admissible AY here"
        if REQUIRE_AY_PIN:
            fail("GATE_ENV_AY_UNRESOLVED", text)
        else:
            info(text)
    else:
        compare("effective Trust toolchain", toolchain_ay, REQUIRE_AY_PIN)
    for lane, identity in sorted(lanes.items()):
        bundled = identity.get("ay")
        if not bundled or identity is effective:
            continue
        if bundled[0] == pin_version:
            info(f"{lane} Trust bundle ay {bundled[0]} matches the ay-pb pin version")
        else:
            warn("GATE_ENV_BUNDLE_AY_PIN_MISMATCH",
                 f"{lane} Trust bundle ay is {bundled[0] or 'unknown'} ({bundled[2]}), pin is {pin_version}")

# ---------------------------------------------------------------------------
section("Lean (formal/lean/lean-toolchain) for the ENC-1 lake build")
pin_file = ROOT / "formal/lean/lean-toolchain"
try:
    lean_pin = pin_file.read_text().strip()
except OSError:
    lean_pin = ""
lean_match = re.fullmatch(r"leanprover/lean4:v(\d+\.\d+\.\d+)", lean_pin)
if not lean_match:
    fail("GATE_ENV_LEAN_PIN_UNREADABLE",
         f"{pin_file} must contain exactly 'leanprover/lean4:vX.Y.Z' (found {lean_pin!r})")
else:
    lean_version = lean_match.group(1)
    info(f"lean-toolchain pin: {lean_pin}")
    elan_home = Path(os.environ.get("ELAN_HOME") or Path(os.environ.get("HOME", "/")) / ".elan")
    toolchain_dir = elan_home / "toolchains" / lean_pin.replace("/", "--").replace(":", "---")
    elan_lean = toolchain_dir / "bin" / "lean"

    def is_elan_proxy(path):
        real = Path(path).resolve()
        if real.name in ("elan", "elan-init"):
            return True
        return Path(path).parent == elan_home / "bin"

    def recipe():
        print(f"gate_env:   re-provision Lean {lean_version} (see {PREREQ_REPORT}/README.md, "
              "'Portable tool recipe'), then rerun this check:")
        print(f"gate_env:   (a) elan, network: elan toolchain install {lean_pin}")
        digests_path = ROOT / PREREQ_REPORT / "publisher-digests.json"
        try:
            digests = json.loads(digests_path.read_text())
            lean = digests["lean"]
        except (OSError, ValueError, KeyError, TypeError) as error:
            print(f"gate_env:   (b) no recorded publisher artifact ({digests_path}: {error})")
            return
        archive = lean.get("name", "")
        host_suffix = "darwin_aarch64" if sys.platform == "darwin" else "linux_aarch64"
        if lean.get("tag_name") != f"v{lean_version}" or not archive.endswith(f"{host_suffix}.tar.zst"):
            print(f"gate_env:   (b) {digests_path.name} records {archive or 'no archive'} "
                  f"({lean.get('tag_name', '?')}), not a {host_suffix} v{lean_version} artifact; "
                  "obtain and record a publisher digest for this host first")
            return
        directory = archive[: -len(".tar.zst")]
        print(f"gate_env:   (b) recorded publisher artifact ({digests_path.relative_to(ROOT)}, "
              f"recorded {digests.get('recorded_at', '?')}):")
        print(f"gate_env:       url      {lean.get('url')}")
        print(f"gate_env:       sha256   {lean.get('sha256')}  size {lean.get('size')}")
        print(f"gate_env:       metadata {lean.get('publisher_metadata')} (re-check the digest there)")
        print('gate_env:       export CG_SOUNDNESS_TOOLS="$(mktemp -d)"   # isolated installation root')
        print(f'gate_env:       curl --fail --location --output "$CG_SOUNDNESS_TOOLS/{archive}" {lean.get("url")}')
        print(f'gate_env:       echo "{lean.get("sha256")}  $CG_SOUNDNESS_TOOLS/{archive}" | shasum -a 256 -c -')
        print(f'gate_env:       tar -xf "$CG_SOUNDNESS_TOOLS/{archive}" -C "$CG_SOUNDNESS_TOOLS"')
        print(f'gate_env:       export PATH="$CG_SOUNDNESS_TOOLS/{directory}/bin:$PATH"')
        print("gate_env:       (soundness_check.sh prepends ~/.elan/bin; where that directory exists its "
              "lake proxy wins, so prefer (a) there)")

    lake = shutil.which("lake")
    if lake is None:
        fail("GATE_ENV_LAKE_MISSING", "no lake on PATH after the prelude; soundness_check.sh's ENC-1 leg needs it")
        recipe()
    elif is_reroute(lake):
        fail("GATE_ENV_LAKE_REROUTED", f"lake resolves to the atpkg reroute stub {lake}, not a Lean install")
        recipe()
    elif is_elan_proxy(lake):
        info(f"lake: {lake} (elan proxy; ELAN_HOME {elan_home})")
        if executable(str(elan_lean)):
            rc, out, err = run([str(elan_lean), "--version"])
            line = first_line(out) if rc == 0 else first_line(err)
            if rc == 0 and f"version {lean_version}" in line:
                ok(f"elan toolchain {toolchain_dir}: {line}")
            else:
                fail("GATE_ENV_LEAN_VERSION_MISMATCH", f"{elan_lean} --version: {line or rc}")
        else:
            installed = sorted(p.name for p in (elan_home / "toolchains").glob("*")) \
                if (elan_home / "toolchains").is_dir() else []
            fail("GATE_ENV_LEAN_TOOLCHAIN_ABSENT",
                 f"{lean_pin} is not installed under {elan_home}/toolchains "
                 f"(installed: {', '.join(installed) or 'none'}); lake would try a network install at gate time")
            recipe()
    else:
        rc, out, err = run([lake, "--version"], cwd=str(ROOT))
        line = first_line(out) if rc == 0 else first_line(err)
        if rc == 0 and f"Lean version {lean_version}" in line:
            ok(f"lake {lake}: {line}")
        else:
            fail("GATE_ENV_LEAN_VERSION_MISMATCH",
                 f"lake {lake} reports {line or rc!r}, not Lean version {lean_version}")
            recipe()
    lean = shutil.which("lean")
    if lean and is_reroute(lean):
        info(f"`lean` on PATH is the atpkg reroute stub {lean}; the gate uses lake, which is unaffected")

# ---------------------------------------------------------------------------
def codes(items):
    return ", ".join(sorted(set(items))) or "none"


verdict = "FAIL" if FAILURES else "PASS"
emit("", f"RESULT {verdict}: {len(FAILURES)} failure(s) [{codes(FAILURES)}], "
         f"{len(WARNINGS)} warning(s) [{codes(WARNINGS)}]")
sys.exit(1 if FAILURES else 0)
GATE_ENV_PY
}

# ---------------------------------------------------------------------------
# Entry: sourced -> prelude only; executed -> checks.
# ---------------------------------------------------------------------------
_gate_env_sourced=0
if [ -n "${ZSH_VERSION:-}" ]; then
    case "${ZSH_EVAL_CONTEXT:-}" in
        *:file*) _gate_env_sourced=1 ;;
    esac
elif [ -n "${BASH_VERSION:-}" ]; then
    if [ "${BASH_SOURCE[0]}" != "$0" ]; then
        _gate_env_sourced=1
    fi
fi
if [ "$_gate_env_sourced" = 1 ]; then
    unset _gate_env_sourced
    gate_env_prelude
    return $?
fi
unset _gate_env_sourced
set -u
set -o pipefail
gate_env_main "${BASH_SOURCE[0]:-$0}" "$@"
exit $?
