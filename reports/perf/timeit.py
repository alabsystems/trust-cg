#!/usr/bin/env python3
# GOAL-3 perf-baseline timing driver.
#
# Usage:
#   timeit.py <mode> <reps> -- <cmd> [args...]
#
# mode = "cpu"  : report best-of-<reps> CPU time of the child (user+sys), in ms.
#                 Used for EXEC timing — immune to system load / co-scheduled
#                 work, which corrupts wall-clock on a shared machine.
#   mode = "wall": report best-of-<reps> wall-clock time, in ms.
#                 Used for COMPILE timing (rustc spawns subprocesses/threads;
#                 wall is the user-visible compile latency).
#
# Prints two lines to stdout:
#   MS=<min_ms>
#   RC=<exit_code_of_last_run>
#
# All child stdout/stderr is discarded. One python process per measurement, so
# interpreter startup is amortized across all <reps> runs (not paid per run).
#
# Author: Andrew Yates · Copyright 2026 Andrew Yates · License: Apache-2.0
import os
import sys
import time
import subprocess


def main():
    argv = sys.argv[1:]
    mode = argv[0]
    reps = int(argv[1])
    # Optional: "--errfile <path>" before the "--" separator. When set, the
    # LAST rep's stderr is written there (so a timed compile pass can also be
    # the fail-closed diagnostic source, with no extra status compile).
    errfile = None
    i = 2
    if argv[i] == "--errfile":
        errfile = argv[i + 1]
        i += 2
    assert argv[i] == "--", "expected -- separator"
    cmd = argv[i + 1:]

    best_ms = None
    rc = None
    devnull = open(os.devnull, "wb")
    for rep in range(reps):
        last = rep == reps - 1
        errfd = devnull.fileno()
        errfh = None
        if last and errfile is not None and mode == "wall":
            errfh = open(errfile, "wb")
            errfd = errfh.fileno()
        if mode == "cpu":
            # Fork+exec and harvest the child's rusage so we measure ONLY the
            # child's CPU time, independent of wall-clock scheduling noise.
            pid = os.fork()
            if pid == 0:
                os.dup2(devnull.fileno(), 1)
                os.dup2(devnull.fileno(), 2)
                try:
                    os.execvp(cmd[0], cmd)
                except Exception:
                    os._exit(127)
            _, status, rusage = os.wait4(pid, 0)
            cpu_s = rusage.ru_utime + rusage.ru_stime
            ms = cpu_s * 1000.0
            if os.WIFEXITED(status):
                rc = os.WEXITSTATUS(status)
            elif os.WIFSIGNALED(status):
                rc = 128 + os.WTERMSIG(status)
            else:
                rc = -1
        else:  # wall
            t0 = time.perf_counter()
            p = subprocess.run(cmd, stdout=devnull, stderr=errfd)
            t1 = time.perf_counter()
            ms = (t1 - t0) * 1000.0
            rc = p.returncode
        if errfh is not None:
            errfh.close()
        if best_ms is None or ms < best_ms:
            best_ms = ms

    print(f"MS={best_ms:.1f}")
    print(f"RC={rc}")


if __name__ == "__main__":
    main()
