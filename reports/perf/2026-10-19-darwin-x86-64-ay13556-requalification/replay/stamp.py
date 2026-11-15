#!/usr/bin/env python3
"""Copy stdin to stdout, each line prefixed with the seconds since start (for timing a
compile's per-function body replays from its `x86-body-trace` lines)."""
import sys
import time

t0 = time.time()
for line in sys.stdin:
    sys.stdout.write(f"[{time.time() - t0:9.3f}] {line}")
    sys.stdout.flush()
