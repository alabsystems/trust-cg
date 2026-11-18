#!/usr/bin/env python3
"""benchmarks/beat-llvm/peak_rss.py — portable peak-RSS capture for one command.

Peak RSS comes from the kernel's rusage accounting. Run as a wrapper process,
the sampler spawns exactly one child and reads
`getrusage(RUSAGE_CHILDREN).ru_maxrss` after that child has been waited for.
Because the wrapper has a single child, the figure is the largest resident set
of any ONE process in the measured tree: the command itself or a descendant
that its parent waited for (trustc's `cc`/`ld` link step included). It is a
per-process maximum, not a simultaneous sum over the tree — the same quantity
BSD `/usr/bin/time -l` and GNU `/usr/bin/time -v` report, without depending on
either binary or its output format. The harness previously parsed BSD
`/usr/bin/time -l` output only, so every Linux row recorded null.

The harness process cannot read `RUSAGE_CHILDREN` around a subprocess itself:
that counter is a high-water mark over EVERY child the process has ever waited
for, so after the first large compile no later, smaller child could be told
apart. A fresh wrapper per measurement starts from zero.

`ru_maxrss` units differ by kernel: bytes on Darwin, KiB on Linux and the other
BSDs. The wrapper normalises to bytes before writing its record, so a consumer
never sees a raw unit.

Sampler floor: a child's `ru_maxrss` can include memory the kernel attributes
to it before its own image runs (Linux's exec keeps the larger of the pre-exec
address space's high-water mark and the new image's). A wrapper-spawned child
therefore cannot report less than some floor, which `cross_check` measures by
running a trivial program through the same path. Values at or near the floor
are upper bounds, not resolved measurements; the floor is recorded with every
run instead of being assumed.

On Linux a small native wrapper (peak_rss_linux.c) replaces the Python image
at the fork boundary, reducing that real floor. It is compiled once into a
private temporary directory per harness process, outside every measurement,
and removed when that process exits. Failure to build/run it produces no
measurement; it never silently falls back to the old high-floor Linux path.
Darwin retains the Python wrapper and byte-valued kernel accounting.

Wrapper:
    python3 peak_rss.py --out FILE [--timeout S] [--inherit-resources] -- CMD ARGS...
  The child's stdout/stderr are inherited (not captured). Exit status is the
  child's; 128+N when the child is killed by signal N; TIMEOUT_EXIT (124) when
  --timeout expires (the direct child is killed and reaped); 127 when CMD
  cannot be executed. FILE receives one JSON object (see `wrapper_record`).

Module:
    measure(cmd, env=None, timeout=None, *, inherit_resources=False) -> Sample
  Sample.peak_rss_bytes is None unless the child ran to completion and exited
  normally (any exit status): a killed, timed-out or unexecutable child has no
  meaningful peak. Sample.wall_s is the child's wall time as seen by the
  wrapper (fork/exec/wait of the child only; the wrapper's own start-up is
  excluded).

Compiler callers can forward the original scheduler and resource descriptions
with `inherit_resources=True`. The native compiler authenticates them.
"""

import argparse
import functools
import hashlib
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import time
from collections import namedtuple
from pathlib import Path

WRAPPER = Path(__file__).resolve()
TIMEOUT_EXIT = 124
EXEC_FAILED_EXIT = 127
TIME_BIN = "/usr/bin/time"

Sample = namedtuple("Sample", "returncode status peak_rss_bytes wall_s stdout stderr")

METHOD_ID = "linux-native-rusage-v1" if sys.platform == "linux" else "python-rusage-v1"
METHOD = ("getrusage(RUSAGE_CHILDREN).ru_maxrss read by a single-child "
          + ("native Linux wrapper (benchmarks/beat-llvm/peak_rss_linux.c)"
             if sys.platform == "linux" else "Python wrapper (benchmarks/beat-llvm/peak_rss.py)")
          + " after the child is reaped, normalised to "
          "bytes; the largest single process in the measured tree, not a sum")

_BSD_TIME = re.compile(r"(\d+)\s+maximum resident set size")
_GNU_TIME = re.compile(r"Maximum resident set size \(kbytes\):\s*(\d+)")


class ResourceRefusal(RuntimeError):
    """A requested resource description could not be forwarded."""


def resource_fds(environment):
    # Only compiler launches need this helper. Keep its imports out of the RSS
    # sampler process for ordinary programs and for the calibration probes.
    scripts = str(WRAPPER.parents[2] / "scripts")
    if scripts not in sys.path:
        sys.path.insert(0, scripts)
    import trust_toolchain

    try:
        return trust_toolchain.resource_fds(environment)
    except trust_toolchain.ToolchainError as error:
        raise ResourceRefusal(str(error)) from error


def maxrss_unit(platform=None):
    """Unit of `ru_maxrss` on this kernel: bytes on Darwin, KiB elsewhere."""
    return "bytes" if (platform or sys.platform) == "darwin" else "KiB"


def normalize_maxrss(ru_maxrss, platform=None):
    """`ru_maxrss` as bytes, or None when the kernel reported nothing."""
    if ru_maxrss is None or ru_maxrss <= 0:
        return None
    return int(ru_maxrss) if maxrss_unit(platform) == "bytes" else int(ru_maxrss) * 1024


def wrapper_record(ru_maxrss, returncode, status, wall_s=None, platform=None):
    platform = platform or sys.platform
    return {
        "ru_maxrss_raw": ru_maxrss,
        "ru_maxrss_unit": maxrss_unit(platform),
        "ru_maxrss_bytes": normalize_maxrss(ru_maxrss, platform),
        "platform": platform,
        "returncode": returncode,
        "status": status,
        "wall_s": wall_s,
    }


@functools.lru_cache(maxsize=1)
def _native_sampler(compiler):
    """Keep the private native image alive, and clean it on process exit.

    Cache ownership is this Python process only: no shared path, stale binary,
    or cache eviction can change the measurement implementation mid-run.
    """
    directory = tempfile.TemporaryDirectory(prefix="peak-rss-native-")
    source = WRAPPER.with_name("peak_rss_linux.c")
    binary = Path(directory.name) / "peak-rss"
    command = [*compiler, "-std=c11", "-O2", "-Wall", "-Wextra", "-Werror",
               str(source), "-o", str(binary)]
    try:
        result = subprocess.run(command, capture_output=True, text=True)
        if result.returncode != 0:
            raise OSError(f"native RSS sampler build failed: {result.stderr}")
        identity = {
            "method_id": METHOD_ID, "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "binary_sha256": hashlib.sha256(binary.read_bytes()).hexdigest(),
            "compile_command": command,
        }
        return directory, binary, identity
    except BaseException:
        directory.cleanup()
        raise


def native_sampler(env=None):
    environment = os.environ if env is None else env
    compiler = shlex.split(environment.get("CC", "cc"))
    if not compiler:
        raise OSError("native RSS sampler needs a C compiler (CC or cc)")
    executable = shutil.which(compiler[0], path=environment.get("PATH", os.defpath))
    if executable is None:
        raise OSError(f"native RSS sampler C compiler is unavailable: {compiler[0]}")
    return _native_sampler((executable, *compiler[1:]))


def sampler_identity(env=None):
    """The actual native image used by this process, or its explicit failure."""
    if sys.platform != "linux":
        return {"method_id": METHOD_ID, "source_sha256": hashlib.sha256(WRAPPER.read_bytes()).hexdigest()}
    try:
        return dict(native_sampler(env)[2])
    except (OSError, ValueError) as error:
        return {"method_id": METHOD_ID, "status": "wrapper-failed", "error": str(error)}


def wrapper_main(argv):
    import resource

    ap = argparse.ArgumentParser(prog="peak_rss.py", description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--out", required=True, help="file that receives the JSON record")
    ap.add_argument("--timeout", type=float, default=None, help="kill the child after S seconds")
    ap.add_argument("--inherit-resources", action="store_true",
                    help="forward the original advertised resource descriptors to the command")
    ap.add_argument("cmd", nargs=argparse.REMAINDER, help="-- CMD ARGS...")
    args = ap.parse_args(argv)
    cmd = args.cmd[1:] if args.cmd and args.cmd[0] == "--" else args.cmd
    if not cmd:
        ap.error("no command given after --")
    try:
        inherited = resource_fds(os.environ) if args.inherit_resources else ()
    except ResourceRefusal as error:
        print(f"peak_rss: {error}", file=sys.stderr)
        Path(args.out).write_text(json.dumps(wrapper_record(None, EXEC_FAILED_EXIT, "wrapper-failed")))
        return EXEC_FAILED_EXIT
    if sys.platform == "linux":
        try:
            native = native_sampler()[1]
            command = [str(native), "--out", args.out]
            if args.timeout is not None:
                command += ["--timeout", str(args.timeout)]
            return subprocess.run([*command, "--", *cmd], pass_fds=inherited).returncode
        except (OSError, ValueError) as error:
            print(f"peak_rss: {error}", file=sys.stderr)
            Path(args.out).write_text(json.dumps(wrapper_record(None, EXEC_FAILED_EXIT, "wrapper-failed")))
            return EXEC_FAILED_EXIT
    status, wall = "ok", None
    t0 = time.perf_counter()
    try:
        # subprocess.run kills AND reaps the child on timeout, so its partial
        # peak is already folded into RUSAGE_CHILDREN when it is read below; the
        # record reports the timeout so the consumer discards that value.
        rc = subprocess.run(cmd, timeout=args.timeout, pass_fds=inherited).returncode
        wall = round(time.perf_counter() - t0, 6)
    except subprocess.TimeoutExpired:
        rc, status = TIMEOUT_EXIT, "timeout"
    except OSError as error:
        print(f"peak_rss: cannot execute {cmd[0]}: {error}", file=sys.stderr)
        rc, status = EXEC_FAILED_EXIT, "exec-failed"
    if status == "ok" and rc < 0:
        # Killed by a signal: a crash's high-water mark is not the program's peak.
        rc, status = 128 - rc, "signaled"
    ru = resource.getrusage(resource.RUSAGE_CHILDREN)
    Path(args.out).write_text(json.dumps(wrapper_record(ru.ru_maxrss, rc, status, wall)))
    return rc


def measure(cmd, env=None, timeout=None, python=None, *, inherit_resources=False):
    """Run `cmd` under the wrapper and return its Sample (output captured as text).

    The wrapper enforces `timeout` itself so the measured child is the process
    it kills; the outer bound below only guards against a wedged wrapper.
    """
    environment = os.environ if env is None else env
    try:
        inherited = resource_fds(environment) if inherit_resources else ()
    except ResourceRefusal as error:
        return Sample(EXEC_FAILED_EXIT, "wrapper-failed", None, None, "", str(error))

    fd, out = tempfile.mkstemp(prefix="peak-rss-", suffix=".json")
    os.close(fd)
    try:
        try:
            # A supplied Python path remains an explicit wrapper override (and
            # must fail if missing). The normal Linux harness launches the
            # already-built native image directly, with no Python child image.
            if sys.platform == "linux" and python is None:
                wrapper = [str(native_sampler(env)[1])]
            else:
                wrapper = [python or sys.executable, str(WRAPPER)]
                if inherit_resources:
                    wrapper.append("--inherit-resources")
        except (OSError, ValueError) as error:
            return Sample(EXEC_FAILED_EXIT, "wrapper-failed", None, None, "", str(error))
        wrapper += ["--out", out]
        if timeout is not None:
            wrapper += ["--timeout", str(timeout)]
        wrapper += ["--", *cmd]
        try:
            r = subprocess.run(wrapper, capture_output=True, text=True, env=env, pass_fds=inherited,
                               timeout=None if timeout is None else timeout + 60)
        except subprocess.TimeoutExpired:
            return Sample(TIMEOUT_EXIT, "timeout", None, None, "", "")
        except OSError as error:
            return Sample(EXEC_FAILED_EXIT, "wrapper-failed", None, None, "", str(error))
        try:
            record = json.loads(Path(out).read_text())
        except (OSError, ValueError):
            record = None
        if not isinstance(record, dict):
            record = {}
        status = record.get("status", "no-record")
        ok = status == "ok"
        return Sample(r.returncode, status, record.get("ru_maxrss_bytes") if ok else None,
                      record.get("wall_s") if ok else None, r.stdout, r.stderr)
    finally:
        try:
            os.unlink(out)
        except OSError:
            pass


def parse_time_output(text):
    """Peak RSS in bytes from BSD `time -l` or GNU `time -v` stderr, else None."""
    m = _BSD_TIME.search(text)
    if m:
        return int(m.group(1))
    m = _GNU_TIME.search(text)
    if m:
        return int(m.group(1)) * 1024
    return None


def time_wrapper_flag(platform=None):
    """The `/usr/bin/time` flag that prints peak RSS on this platform."""
    return "-l" if (platform or sys.platform) == "darwin" else "-v"


def time_wrapper_peak_rss(cmd, env=None, timeout=None, time_bin=TIME_BIN):
    """Peak RSS in bytes via `/usr/bin/time` (the legacy sampler), or None.

    Kept as an independent cross-check of `measure`: a different program
    reading the same kernel counter. None when the binary is absent, fails, or
    prints neither known format (busybox/shell builtins).
    """
    if not (os.path.isfile(time_bin) and os.access(time_bin, os.X_OK)):
        return None
    try:
        r = subprocess.run([time_bin, time_wrapper_flag(), *cmd], capture_output=True,
                           text=True, env=env, timeout=timeout)
    except (OSError, subprocess.TimeoutExpired):
        return None
    if r.returncode != 0:
        return None
    return parse_time_output(r.stderr)


# Touching every page is what makes them resident: `bytes * n` writes each byte.
CALIBRATION_MIB = 64
CALIBRATION_CODE = f'x = b"\\x01" * ({CALIBRATION_MIB} << 20)'
CROSS_CHECK_TOLERANCE = 0.05


def trivial_command():
    """A program that does nothing, for the sampler-floor probe, or None."""
    for candidate in ("/usr/bin/true", "/bin/true"):
        if os.path.isfile(candidate) and os.access(candidate, os.X_OK):
            return [candidate]
    found = shutil.which("true")
    return [found] if found else None


def relative_difference(a, b):
    if not a or not b:
        return None
    return round(abs(a - b) / max(a, b), 4)


def cross_check(env=None, python=None):
    """Calibrate the sampler and record its agreement with `/usr/bin/time`.

    Two probes, each measured with both samplers:
      * floor — a trivial program (`true`): the smallest peak this path can
        report. Program peaks near it are upper bounds, not resolved values.
      * calibration — one known allocation: `rusage_bytes` must cover it, and
        where `/usr/bin/time` exists the two readings should agree within
        `CROSS_CHECK_TOLERANCE`.
    Disagreement is recorded, not hidden, and so is whether `/usr/bin/time`
    exists at all (`time_wrapper_present`): a present binary that fails or
    prints an unknown format leaves `agree` null without being absent. Nothing
    here passes or fails a row; contract/check_gates.py decides whether this
    record qualifies RSS readings for the gates.json RSS predicates.
    """
    cmd = [python or sys.executable, "-c", CALIBRATION_CODE]
    rusage = measure(cmd, env=env, timeout=120, python=python).peak_rss_bytes
    time_bytes = time_wrapper_peak_rss(cmd, env=env, timeout=120)
    trivial = trivial_command()
    floor = measure(trivial, env=env, timeout=60, python=python).peak_rss_bytes if trivial else None
    time_floor = time_wrapper_peak_rss(trivial, env=env, timeout=60) if trivial else None
    difference = relative_difference(rusage, time_bytes)
    return {
        "command": f"python -c '{CALIBRATION_CODE}'",
        "allocation_bytes": CALIBRATION_MIB << 20,
        "rusage_bytes": rusage,
        "rusage_covers_allocation": rusage is not None and rusage >= CALIBRATION_MIB << 20,
        "time_wrapper": f"{TIME_BIN} {time_wrapper_flag()}" if time_bytes is not None else None,
        "time_wrapper_present": os.path.isfile(TIME_BIN) and os.access(TIME_BIN, os.X_OK),
        "time_wrapper_bytes": time_bytes,
        "relative_difference": difference,
        "agree": None if difference is None else difference <= CROSS_CHECK_TOLERANCE,
        "floor_command": " ".join(trivial) if trivial else None,
        "sampler_floor_bytes": floor,
        "time_wrapper_floor_bytes": time_floor,
    }


if __name__ == "__main__":
    sys.exit(wrapper_main(sys.argv[1:]))
