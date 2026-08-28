#!/usr/bin/env python3
"""Adversarial regression tests for harness_row.sh's evidence boundary."""

from __future__ import annotations

import os
from pathlib import Path
import shutil
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
HARNESS = HERE / "harness_row.sh"


def write_executable(path: Path, contents: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(contents, encoding="utf-8")
    path.chmod(0o755)


def run(command: list[str], *, cwd: Path, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(command, cwd=cwd, env=env, text=True, capture_output=True)


with tempfile.TemporaryDirectory(prefix="trust-cg-harness-row-test-") as raw_tmp:
    tmp = Path(raw_tmp)
    repo = tmp / "repo"
    marker_dir = tmp / "markers"
    marker_dir.mkdir()

    harness = repo / "benchmarks/compile-apples/tools/harness_row.sh"
    harness.parent.mkdir(parents=True)
    shutil.copy2(HARNESS, harness)

    write_executable(
        repo / "benchmarks/beat-llvm/run.py",
        """#!/usr/bin/env python3
import os
from pathlib import Path
import sys
import time

mode = os.environ["FAKE_RUN_MODE"]
print(f"fake benchmark mode={mode}")
if mode == "fail":
    raise SystemExit(7)
if mode == "fresh":
    results = Path("benchmarks/beat-llvm/results")
    results.mkdir(parents=True, exist_ok=True)
    result = results / f"fresh-{time.time_ns()}.json"
    result.write_text("{}\\n", encoding="utf-8")
    print(f"results/{result.name}")
""",
    )
    write_executable(
        repo / "benchmarks/beat-llvm/contract/check_gates.py",
        """#!/usr/bin/env python3
import os
from pathlib import Path
import sys

Path(os.environ["FAKE_MARKER_DIR"], "gate").write_text(sys.argv[1], encoding="utf-8")
print("PASS fresh evidence")
""",
    )
    write_executable(
        repo / "scripts/check_perf_ratchet.py",
        """#!/usr/bin/env python3
import os
from pathlib import Path
import sys

assert sys.argv[1] == "--append"
Path(os.environ["FAKE_MARKER_DIR"], "ratchet").write_text(sys.argv[2], encoding="utf-8")
print("ratchet accepted fresh evidence")
""",
    )
    dylib = repo / "backend.so"
    dylib.write_bytes(b"test backend placeholder\n")

    subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
    subprocess.run(["git", "config", "user.name", "Harness Test"], cwd=repo, check=True)
    subprocess.run(["git", "config", "user.email", "harness@test.invalid"], cwd=repo, check=True)
    subprocess.run(["git", "add", "."], cwd=repo, check=True)
    subprocess.run(["git", "commit", "-qm", "fixture"], cwd=repo, check=True)

    results = repo / "benchmarks/beat-llvm/results"
    results.mkdir(parents=True)
    stale = results / "stale.json"
    stale.write_text("{}\n", encoding="utf-8")

    base_env = dict(os.environ)
    base_env.update(FAKE_MARKER_DIR=str(marker_dir), TCG_TARGET="test-target")

    for mode, expected_fragment in (
        ("fail", "fake benchmark mode=fail"),
        ("no-result", "without producing a fresh result JSON"),
    ):
        for marker in marker_dir.iterdir():
            marker.unlink()
        result = run(
            ["bash", str(harness), str(repo), str(dylib)],
            cwd=repo,
            env=dict(base_env, FAKE_RUN_MODE=mode),
        )
        combined = result.stdout + result.stderr
        assert result.returncode != 0, f"{mode} unexpectedly succeeded:\n{combined}"
        assert expected_fragment in combined, combined
        assert not (marker_dir / "gate").exists(), f"{mode} reached the gate checker"
        assert not (marker_dir / "ratchet").exists(), f"{mode} ratcheted stale evidence"

    result = run(
        ["bash", str(harness), str(repo), str(dylib)],
        cwd=repo,
        env=dict(base_env, FAKE_RUN_MODE="fresh"),
    )
    combined = result.stdout + result.stderr
    assert result.returncode == 0, combined
    gate_result = (marker_dir / "gate").read_text(encoding="utf-8")
    ratchet_result = (marker_dir / "ratchet").read_text(encoding="utf-8")
    assert gate_result == ratchet_result
    assert Path(gate_result).name.startswith("fresh-")
    assert Path(gate_result).name != stale.name

print("harness_row stale-evidence adversarial tests: 3 passed")
