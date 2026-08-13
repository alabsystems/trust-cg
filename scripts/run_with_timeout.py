#!/usr/bin/env python3
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
#
"""Run one command in an isolated, bounded process group."""

from __future__ import annotations

import argparse
import math
import os
import shlex
import signal
import subprocess
import sys
import time
from collections.abc import Sequence

TIMEOUT_EXIT = 124
LAUNCH_ERROR_EXIT = 125
NOT_EXECUTABLE_EXIT = 126
NOT_FOUND_EXIT = 127
POLL_SECONDS = 0.05


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
    parser.add_argument("timeout_seconds", metavar="SECONDS", type=positive_duration)
    parser.add_argument("command", metavar="COMMAND", nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    if args.command[:1] == ["--"]:
        args.command = args.command[1:]
    if not args.command:
        parser.error("COMMAND is required")
    return args


def group_exists(process_group: int) -> bool:
    try:
        os.killpg(process_group, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def signal_group(process_group: int, signum: int) -> None:
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


def run(args: argparse.Namespace) -> int:
    command_label = shlex.join(args.command)
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
    cleanup_succeeded = True
    try:
        while process.poll() is None and forwarded_signal is None:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                timed_out = True
                break
            time.sleep(min(POLL_SECONDS, remaining))

        if timed_out:
            print(
                f"run_with_timeout: command exceeded "
                f"{args.timeout_seconds:g}s: {command_label}",
                file=sys.stderr,
            )
            terminate_group(process_group, args.grace_seconds)
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

    if not cleanup_succeeded:
        print(
            f"run_with_timeout: process group did not terminate: {command_label}",
            file=sys.stderr,
        )
    if timed_out:
        return TIMEOUT_EXIT
    if forwarded_signal is not None:
        return 128 + forwarded_signal
    if not cleanup_succeeded or process.returncode is None:
        return LAUNCH_ERROR_EXIT
    return normalized_returncode(process.returncode)


def main(argv: Sequence[str] | None = None) -> int:
    return run(parse_args(sys.argv[1:] if argv is None else argv))


if __name__ == "__main__":
    raise SystemExit(main())
