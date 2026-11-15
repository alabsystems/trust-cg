#!/usr/bin/env python3
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
#
"""Run one command in an isolated, bounded process group.

Exit codes: the command's own status; 122 when the summed resident set of the
process group exceeded ``--max-rss-gib`` or became unmeasurable while the
ceiling was in force; 124 on wall-clock timeout; 125/126/127 for launch
errors. Resident-set supervision reads Linux ``/proc`` only; requesting it on
any other host refuses to launch rather than running unsupervised.

The ceiling is a sampled backstop over the command's process group: a
descendant that leaves the group (``setsid``/``setpgid``) escapes both the
ceiling and the timeout, and an allocation spike shorter than the sampling
interval can be missed. Every supervised run that launches ends with one
``RSS_RECEIPT`` line on stderr naming the ceiling, the sampled peak, the
sample count and the outcome; the peak is an observed sample, never a
measured maximum.
"""

from __future__ import annotations

import argparse
import math
import os
import shlex
import signal
import subprocess
import sys
import time
from collections.abc import Callable, Sequence

RSS_LIMIT_EXIT = 122
TIMEOUT_EXIT = 124
LAUNCH_ERROR_EXIT = 125
NOT_EXECUTABLE_EXIT = 126
NOT_FOUND_EXIT = 127
POLL_SECONDS = 0.05
# Resident-set samples are a /proc walk, so they run less often than the exit
# poll; a ceiling that cannot be measured for this long is not being upheld.
RSS_POLL_SECONDS = 0.2
RSS_UNMEASURABLE_SECONDS = 2.0
RSS_RECEIPT = "run_with_timeout: RSS_RECEIPT"
MIB = 1024 ** 2
GIB = 1024 ** 3


def nonnegative_duration(value: str) -> float:
    try:
        duration = float(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError(f"not a number: {value}") from error
    if not math.isfinite(duration) or duration < 0:
        raise argparse.ArgumentTypeError(
            f"must be a finite, non-negative number: {value}"
        )
    return duration


def positive_duration(value: str) -> float:
    duration = nonnegative_duration(value)
    if duration == 0:
        raise argparse.ArgumentTypeError("must be greater than zero")
    return duration


def positive_gib(value: str) -> float:
    try:
        gib = float(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError(f"not a number: {value}") from error
    if not math.isfinite(gib) or gib <= 0:
        raise argparse.ArgumentTypeError(f"must be a finite, positive number: {value}")
    return gib


def rss_supervision_support() -> str | None:
    """Name the resident-set supervision this host can enforce, else None."""
    if sys.platform.startswith("linux") and os.path.isfile("/proc/self/statm"):
        return "linux-proc"
    return None


def process_group_rss_bytes(
    process_group: int, proc_root: str = "/proc", page_size: int | None = None,
) -> int | None:
    """Sum the resident pages of every process in PROCESS_GROUP.

    ``/proc/<pid>/stat`` field 5 (after the parenthesised command name) is the
    process group and ``/proc/<pid>/statm`` field 2 is resident pages. A
    process that exits during the walk is skipped; a table with no readable
    process at all is reported as None, never as an empty group. Pages shared
    between members count once per member, so the sum can exceed the group's
    physical footprint: the ceiling errs toward killing, never toward admitting.
    """
    if page_size is None:
        page_size = os.sysconf("SC_PAGE_SIZE")
    try:
        names = os.listdir(proc_root)
    except OSError:
        return None
    total = 0
    readable = False
    for name in names:
        if not name.isdigit():
            continue
        try:
            with open(os.path.join(proc_root, name, "stat"), "rb") as handle:
                fields = handle.read().rsplit(b")", 1)[1].split()
            readable = True
            if int(fields[2]) != process_group:
                continue
            with open(os.path.join(proc_root, name, "statm"), "rb") as handle:
                resident_pages = int(handle.read().split()[1])
        except (OSError, ValueError, IndexError):
            continue
        total += resident_pages * page_size
    return total if readable else None


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run COMMAND in a new session, forward HUP/INT/TERM, and kill the "
            "whole process group if it exceeds SECONDS."
        ),
        allow_abbrev=False,
    )
    parser.add_argument(
        "--chdir",
        metavar="DIR",
        help="run COMMAND with DIR as its working directory",
    )
    parser.add_argument(
        "--grace-seconds",
        metavar="SECONDS",
        type=nonnegative_duration,
        default=5.0,
        help="wait this long after SIGTERM before SIGKILL (default: 5)",
    )
    parser.add_argument(
        "--max-rss-gib",
        metavar="GIB",
        type=positive_gib,
        default=None,
        help=(
            "kill the process group once its summed resident set exceeds GIB "
            "(Linux /proc supervision only; refused elsewhere)"
        ),
    )
    parser.add_argument("timeout_seconds", metavar="SECONDS", type=positive_duration)
    parser.add_argument("command", metavar="COMMAND", nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    if args.command[:1] == ["--"]:
        args.command = args.command[1:]
    if not args.command:
        parser.error("COMMAND is required")
    return args


def group_exists(process_group: int) -> bool:
    # Popen.pid should always be positive, but never let a malformed value
    # reach killpg: group 0 is this runner's own process group and group 1 may
    # contain an unrelated session leader.
    if process_group <= 1:
        return False
    try:
        os.killpg(process_group, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def signal_group(process_group: int, signum: int) -> None:
    if process_group <= 1:
        return
    try:
        os.killpg(process_group, signum)
    except ProcessLookupError:
        pass
    except PermissionError:
        # Darwin can briefly report EPERM for a process group containing only
        # exited, not-yet-reaped members. There is no live process left to kill.
        pass


def wait_for_group_exit(process_group: int, seconds: float) -> bool:
    deadline = time.monotonic() + seconds
    while group_exists(process_group):
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            return False
        time.sleep(min(POLL_SECONDS, remaining))
    return True


def terminate_group(process_group: int, grace_seconds: float) -> bool:
    if not group_exists(process_group):
        return True
    signal_group(process_group, signal.SIGTERM)
    if wait_for_group_exit(process_group, grace_seconds):
        return True
    signal_group(process_group, signal.SIGKILL)
    # Give the operating system a short opportunity to reap killed descendants.
    return wait_for_group_exit(
        process_group, min(max(grace_seconds, 0.1), 1.0)
    )


def normalized_returncode(returncode: int) -> int:
    if returncode < 0:
        return 128 - returncode
    return returncode


def run(
    args: argparse.Namespace,
    rss_probe: Callable[[int], int | None] | None = None,
) -> int:
    command_label = shlex.join(args.command)
    limit_bytes = None
    if args.max_rss_gib is not None:
        limit_bytes = int(args.max_rss_gib * GIB)
        if rss_probe is None:
            if rss_supervision_support() is None:
                print(
                    f"run_with_timeout: --max-rss-gib is unsupported on {sys.platform}: "
                    "only Linux /proc process-group supervision is implemented; "
                    "refusing to run unsupervised",
                    file=sys.stderr,
                )
                return LAUNCH_ERROR_EXIT
            rss_probe = process_group_rss_bytes
    try:
        process = subprocess.Popen(
            args.command,
            cwd=args.chdir,
            start_new_session=True,
        )
    except FileNotFoundError as error:
        if args.chdir is not None and not os.path.isdir(args.chdir):
            print(
                f"run_with_timeout: working directory not found: {args.chdir}",
                file=sys.stderr,
            )
            return LAUNCH_ERROR_EXIT
        print(f"run_with_timeout: command not found: {error.filename}", file=sys.stderr)
        return NOT_FOUND_EXIT
    except PermissionError as error:
        print(f"run_with_timeout: command is not executable: {error.filename}", file=sys.stderr)
        return NOT_EXECUTABLE_EXIT
    except OSError as error:
        print(f"run_with_timeout: could not launch {command_label}: {error}", file=sys.stderr)
        return LAUNCH_ERROR_EXIT

    process_group = process.pid
    forwarded_signal: int | None = None

    def forward(signum: int, _frame: object) -> None:
        nonlocal forwarded_signal
        if forwarded_signal is None:
            forwarded_signal = signum
        signal_group(process_group, signum)

    previous_handlers = {}
    for handled_signal in (signal.SIGHUP, signal.SIGINT, signal.SIGTERM):
        previous_handlers[handled_signal] = signal.signal(handled_signal, forward)

    deadline = time.monotonic() + args.timeout_seconds
    timed_out = False
    rss_breach: str | None = None
    peak_bytes = 0
    samples = 0
    next_sample = time.monotonic()
    unmeasurable_since: float | None = None
    cleanup_succeeded = True
    try:
        while process.poll() is None and forwarded_signal is None:
            now = time.monotonic()
            remaining = deadline - now
            if remaining <= 0:
                timed_out = True
                break
            if limit_bytes is not None and now >= next_sample:
                next_sample = now + RSS_POLL_SECONDS
                try:
                    observed = rss_probe(process_group)
                except Exception as error:  # never leave the group unsupervised
                    print(
                        f"run_with_timeout: resident-set probe failed: {error}",
                        file=sys.stderr,
                    )
                    observed = None
                if observed is None:
                    if unmeasurable_since is None:
                        unmeasurable_since = now
                    elif now - unmeasurable_since >= RSS_UNMEASURABLE_SECONDS:
                        rss_breach = "unmeasurable"
                        break
                else:
                    unmeasurable_since = None
                    samples += 1
                    peak_bytes = max(peak_bytes, observed)
                    if observed > limit_bytes:
                        rss_breach = "exceeded"
                        break
            time.sleep(min(POLL_SECONDS, remaining))

        if timed_out:
            print(
                f"run_with_timeout: command exceeded "
                f"{args.timeout_seconds:g}s: {command_label}",
                file=sys.stderr,
            )
            terminate_group(process_group, args.grace_seconds)
        elif rss_breach == "exceeded":
            print(
                f"run_with_timeout: resident set exceeded {args.max_rss_gib:g} GiB "
                f"({peak_bytes // MIB} MiB): {command_label}",
                file=sys.stderr,
            )
            # A group over its memory ceiling gets no grace: SIGTERM handlers
            # could keep allocating while the host is already under pressure.
            signal_group(process_group, signal.SIGKILL)
            wait_for_group_exit(process_group, 1.0)
        elif rss_breach == "unmeasurable":
            print(
                f"run_with_timeout: resident set unmeasurable for "
                f"{RSS_UNMEASURABLE_SECONDS:g}s; ceiling {args.max_rss_gib:g} GiB "
                f"cannot be upheld: {command_label}",
                file=sys.stderr,
            )
            signal_group(process_group, signal.SIGKILL)
            wait_for_group_exit(process_group, 1.0)
        elif forwarded_signal is not None:
            terminate_group(process_group, args.grace_seconds)

        if process.poll() is None:
            try:
                process.wait(timeout=min(max(args.grace_seconds, 0.1), 1.0))
            except subprocess.TimeoutExpired:
                signal_group(process_group, signal.SIGKILL)
                try:
                    process.wait(timeout=1.0)
                except subprocess.TimeoutExpired:
                    cleanup_succeeded = False

        # A command can exit while leaving descendants behind. Do not let those
        # escape the bounded release/soundness operation.
        cleanup_succeeded = (
            terminate_group(process_group, args.grace_seconds)
            and process.poll() is not None
            and cleanup_succeeded
        )
    finally:
        for handled_signal, previous_handler in previous_handlers.items():
            signal.signal(handled_signal, previous_handler)

    if limit_bytes is not None:
        # The receipt is retained in the caller's log so a report can record the
        # observed peak; it is a sampled backstop, never a measured maximum.
        print(
            f"{RSS_RECEIPT} ceiling_gib={args.max_rss_gib:g} "
            f"peak_mib={peak_bytes // MIB} samples={samples} "
            f"outcome={rss_breach or 'within'}",
            file=sys.stderr,
        )
    if not cleanup_succeeded:
        print(
            f"run_with_timeout: process group did not terminate: {command_label}",
            file=sys.stderr,
        )
    if timed_out:
        return TIMEOUT_EXIT
    if rss_breach is not None:
        return RSS_LIMIT_EXIT
    if forwarded_signal is not None:
        return 128 + forwarded_signal
    if not cleanup_succeeded or process.returncode is None:
        return LAUNCH_ERROR_EXIT
    return normalized_returncode(process.returncode)


def main(argv: Sequence[str] | None = None) -> int:
    return run(parse_args(sys.argv[1:] if argv is None else argv))


if __name__ == "__main__":
    raise SystemExit(main())
