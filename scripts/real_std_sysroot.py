#!/usr/bin/python3
"""Build real frozen Rust libraries, retaining exact backend and invocation evidence.

The LLVM and no-proof-certs lanes are diagnostic correctness experiments.
Only full-cg-proof retains the backend's mandatory machine-proof gate.
No lane on its own establishes self-hosting or release qualification.
"""
import argparse
import datetime
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import time

ROOT = OUT = TC = TRUST_SOURCE = COMPILER_COMMIT = TARGET = None
CONFIGURATION_PATH = CONFIGURATION = COMPILER_IDENTITY = CONFIGURATION_SHA256 = None
WRAPPER = Path(__file__).with_name("real_std_sysroot_wrapper.py")

def initialize(configuration):
    """Initialize explicitly after CLI parsing, so help needs no configuration."""
    global ROOT, OUT, TC, TRUST_SOURCE, COMPILER_COMMIT, TARGET
    global CONFIGURATION_PATH, CONFIGURATION, COMPILER_IDENTITY, CONFIGURATION_SHA256
    CONFIGURATION_PATH = Path(configuration).resolve()
    contents = CONFIGURATION_PATH.read_bytes()
    CONFIGURATION_SHA256 = hashlib.sha256(contents).hexdigest()
    CONFIGURATION = json.loads(contents)
    ROOT = Path(CONFIGURATION["repository"]).resolve()
    OUT = Path(CONFIGURATION["output"]).resolve()
    TC = Path(CONFIGURATION["toolchain"]).resolve()
    TRUST_SOURCE = Path(CONFIGURATION["compiler_source"]).resolve()
    COMPILER_COMMIT = CONFIGURATION["compiler_commit"]
    TARGET = CONFIGURATION["target"]
    COMPILER_IDENTITY = identity_preflight()
    assert sha(CONFIGURATION_PATH) == CONFIGURATION_SHA256, "configuration changed during identity preflight"
    return {key: globals()[key] for key in ["ROOT", "OUT", "TC", "TARGET", "CONFIGURATION_PATH", "CONFIGURATION", "COMPILER_IDENTITY"]}

def identity_preflight():
    assert re.fullmatch(r"[0-9a-f]{40}", COMPILER_COMMIT), "require an exact full compiler commit"
    version = subprocess.run([str(TC / "bin/trustc"), "-vV"], env=clean_environment(), text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)
    identity = dict(line.split(": ", 1) for line in version.stdout.splitlines() if ": " in line)
    assert identity.get("binary") == "trustc", "the configured compiler must be branded trustc"
    assert identity.get("commit-hash") == COMPILER_COMMIT, "compiler -vV and configured source commit differ"
    resolved = subprocess.check_output(["git", "-C", str(TRUST_SOURCE), "rev-parse", "--verify", COMPILER_COMMIT + "^{commit}"], text=True).strip()
    assert resolved == COMPILER_COMMIT, "configured exact compiler source is unavailable"
    target_list = subprocess.check_output([str(TC / "bin/trustc"), "--print=target-list"], env=clean_environment(), text=True)
    assert TARGET in target_list.splitlines(), "configured target is not supported by this compiler"
    return {"version_stdout": version.stdout, "version_stderr": version.stderr,
            "compiler_commit": identity["commit-hash"], "compiler_source_commit": resolved,
            "compiler_sha256": sha(TC / "bin/trustc"), "build_tool_sha256": sha(TC / "bin/targo"),
            "configured_target": TARGET, "host": identity["host"]}

def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        while chunk := stream.read(1 << 20):
            digest.update(chunk)
    return digest.hexdigest()

def file_manifest(root):
    return {str(path.relative_to(root)): sha(path) for path in sorted(root.rglob("*")) if path.is_file() and ".git" not in path.relative_to(root).parts}

def write(path, value):
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(value, indent=2) + "\n")
    tmp.replace(path)

def prepare():
    before_config, before_driver = sha(CONFIGURATION_PATH), sha(__file__)
    assert identity_preflight() == COMPILER_IDENTITY, "compiler identity changed before source preparation"
    OUT.mkdir(parents=True, exist_ok=True)
    source = OUT / "source"
    record_path = OUT / "source.json"
    if record_path.exists():
        record = json.loads(record_path.read_text())
        assert record["compiler_commit"] == COMPILER_COMMIT and record["source"] == str(source)
        assert record["packaged_library"] == str(TC / "lib/rustlib/src/rust/library")
        assert file_manifest(TC / "lib/rustlib/src/rust/library") == record["packaged_library_files_sha256"]
        assert file_manifest(source) == record["files_sha256"]
        return record
    assert not source.exists(), "partial source preparation must be inspected; no automatic deletion"
    packaged = TC / "lib/rustlib/src/rust/library"
    before = file_manifest(packaged)
    shutil.copytree(packaged, source / "library")
    # The package carries its unchanged [patch] entry but omits this first-party crate.
    # Restore the compiler's exact source, without editing its manifest or using current Trust.
    archive = subprocess.check_output(["git", "-C", str(TRUST_SOURCE), "archive", COMPILER_COMMIT, "crates/trust-memchr"])
    with tarfile.open(fileobj=io.BytesIO(archive)) as tf:
        tf.extractall(source, filter="data")
    after = file_manifest(packaged)
    assert before == after
    assert {name: sha(source / "library" / name) for name in before} == before
    record = {"schema": "trust-cg.std-source-snapshot.v1", "compiler_commit": COMPILER_COMMIT,
              "source": str(source), "packaged_library": str(packaged),
              "packaged_library_files_sha256": before, "first_party_memchr_git_commit": COMPILER_COMMIT,
              "first_party_memchr_archive_sha256": hashlib.sha256(archive).hexdigest(),
              "files_sha256": file_manifest(source), "library_manifest_unchanged": True,
              "library_lockfile_unchanged": True,
              "scope": "Complete packaged library workspace and exact first-party memchr source; no source/manifest rewriting."}
    record.update(configuration_sha256=before_config, driver_sha256=before_driver, compiler_identity=COMPILER_IDENTITY,
                  configuration_unchanged=sha(CONFIGURATION_PATH) == before_config,
                  driver_unchanged=sha(__file__) == before_driver,
                  compiler_identity_unchanged=identity_preflight() == COMPILER_IDENTITY)
    assert all(record[key] for key in ["configuration_unchanged", "driver_unchanged", "compiler_identity_unchanged"])
    write(record_path, record)
    return record

def prepare_std():
    original = prepare()
    source = OUT / "source-std"
    record_path = OUT / "source-std-lock-resolved.json"
    if not record_path.exists():
        record_path = OUT / "source-std.json"
    if record_path.exists():
        record = json.loads(record_path.read_text())
        assert record["compiler_commit"] == COMPILER_COMMIT and record["source"] == str(source)
        assert file_manifest(source) == record["files_sha256"]
        return record
    assert not source.exists()
    shutil.copytree(Path(original["source"]), source)
    manifest = source / "library/Cargo.toml"
    old = manifest.read_text()
    original_members = 'members = [\n  "std",\n  "sysroot",\n  "coretests",\n  "alloctests",\n]'
    assert old.count(original_members) == 1
    new = old.replace(original_members, 'members = ["std"]')
    manifest.write_text(new)
    assert {name: sha(source / name) for name in original["files_sha256"] if name != "library/Cargo.toml"} == {name: digest for name, digest in original["files_sha256"].items() if name != "library/Cargo.toml"}
    record = {"schema": "trust-cg.std-source-snapshot.v1", "source": str(source),
              "compiler_commit": COMPILER_COMMIT, "parent_source_record_sha256": sha(OUT / "source.json"),
              "files_sha256": file_manifest(source), "library_lockfile_unchanged": True,
              "library_rust_sources_unchanged": True, "library_manifest_unchanged": False,
              "manifest_change": {"old_sha256": hashlib.sha256(old.encode()).hexdigest(), "new_sha256": sha(manifest),
                                  "before": original_members, "after": 'members = ["std"]'},
              "workspace_members_not_selected": ["sysroot", "coretests", "alloctests"],
              "scope": "Explicit std-library workspace selection, restoring the earlier retained census route after the packaged sysroot member required an omitted compiler-development graph. Every std feature and production dependency remains intact. Not the full extended Trust sysroot graph."}
    write(record_path, record)
    return record

def resolve_std():
    sources = prepare_std()
    assert not (OUT / "source-std-lock-resolved.json").exists()
    source = Path(sources["source"])
    record_dir = OUT / "std-lock-resolution"
    record_dir.mkdir()
    shutil.copy2(source / "library/Cargo.lock", record_dir / "Cargo.lock.original")
    command = [str(TC / "bin/targo"), "metadata", "--manifest-path", str(source / "library/Cargo.toml"), "--offline", "--format-version=1"]
    result = command_run(command, source / "library", clean_environment(), record_dir / "metadata.log", 120, 4)
    current = file_manifest(source)
    assert {name: digest for name, digest in current.items() if name != "library/Cargo.lock"} == {name: digest for name, digest in sources["files_sha256"].items() if name != "library/Cargo.lock"}
    record = dict(sources)
    record.update(parent_std_source_record_sha256=sha(OUT / "source-std.json"),
                  files_sha256=current, library_lockfile_unchanged=False,
                  lockfile_resolution={"execution": result, "old_sha256": sha(record_dir / "Cargo.lock.original"), "new_sha256": sha(source / "library/Cargo.lock"),
                                       "reason": "Cargo requires resolution after explicitly selecting only std workspace membership; original --locked refusal remains retained. Every subsequent build uses this generated locked offline graph."})
    write(record_dir / "resolution.json", record)
    assert result["returncode"] == 0
    write(OUT / "source-std-lock-resolved.json", record)
    print(json.dumps({"source": str(source), "lockfile_sha256": sha(source / "library/Cargo.lock"), "metadata_returncode": result["returncode"]}), flush=True)
    return record

def prepare_extended():
    original = prepare()
    source = OUT / "source-extended"
    record_path = OUT / "source-extended.json"
    if record_path.exists():
        record = json.loads(record_path.read_text())
        assert record["compiler_commit"] == COMPILER_COMMIT and record["source"] == str(source)
        assert file_manifest(source) == record["files_sha256"]
        return record
    assert not source.exists()
    shutil.copytree(Path(original["source"]), source)
    archive = subprocess.check_output(["git", "-C", str(TRUST_SOURCE), "archive", COMPILER_COMMIT, "crates/trust-bignum"])
    with tarfile.open(fileobj=io.BytesIO(archive)) as tf:
        tf.extractall(source, filter="data")
    inherited = subprocess.check_output(["git", "-C", str(TRUST_SOURCE), "show", COMPILER_COMMIT + ":crates/Cargo.toml"], text=True)
    def section(name):
        match = re.search(r"(?ms)^\[" + re.escape(name) + r"\]\n.*?(?=^\[|\Z)", inherited)
        assert match
        return match.group(0)
    clean_pin = subprocess.check_output(["git", "-C", str(TRUST_SOURCE), "ls-tree", COMPILER_COMMIT, "first-party/clean"], text=True).split()[2]
    scaffold = '[workspace]\nresolver = "2"\nmembers = ["trust-bignum", "trust-memchr"]\n\n' + section("workspace.package") + section("workspace.lints.rust")
    scaffold += '\n[workspace.dependencies]\nclean-kernel = { git = "https://github.com/alabsystems/clean.git", rev = "' + clean_pin + '", features = ["math-overlays"] }\n'
    (source / "crates/Cargo.toml").write_text(scaffold)
    record = {"schema": "trust-cg.std-source-snapshot.v1", "source": str(source), "compiler_commit": COMPILER_COMMIT,
              "parent_source_record_sha256": sha(OUT / "source.json"), "files_sha256": file_manifest(source),
              "library_manifest_unchanged": True, "library_lockfile_unchanged": True, "library_rust_sources_unchanged": True,
              "first_party_bignum_git_commit": COMPILER_COMMIT, "first_party_bignum_archive_sha256": hashlib.sha256(archive).hexdigest(),
              "crates_namespace": {"package_and_rust_lints_source": COMPILER_COMMIT + ":crates/Cargo.toml", "source_sha256": hashlib.sha256(inherited.encode()).hexdigest(),
                                   "dev_only_clean_source_commit": clean_pin, "dev_only_clean_original_features": ["math-overlays"],
                                   "scaffold_sha256": sha(source / "crates/Cargo.toml")},
              "scope": "Complete unchanged packaged library workspace, exact omitted Trust bignum/memchr sources, and explicit standalone crates namespace with the original inherited package/lint values. Clean's test-only dependency is pinned to the original submodule source; compiler development tests are not qualified."}
    assert {name: sha(source / name) for name in original["files_sha256"]} == original["files_sha256"]
    write(record_path, record)
    return record

def clean_environment():
    env = {key: value for key, value in os.environ.items() if not key.startswith(("RUST", "CARGO", "TARGO", "TRUST", "TCG_", "AY_", "STD_")) and key not in {"LD_LIBRARY_PATH", "DYLD_LIBRARY_PATH", "DYLD_FALLBACK_LIBRARY_PATH"}}
    env.update(PATH=str(TC / "bin") + ":/usr/bin:/bin", RUSTC=str(TC / "bin/trustc"),
               RUSTDOC=str(TC / "bin/trustdoc"), RUSTUP_TOOLCHAIN=str(TC), RUSTC_BOOTSTRAP="1",
               LD_LIBRARY_PATH=str(TC / "lib") + ":" + str(TC / "lib/rustlib" / TARGET / "lib"),
               LC_ALL="C.UTF-8", CARGO_BUILD_JOBS="2", CARGO_INCREMENTAL="0", RUST_MIN_STACK="16777216")
    return env

def command_run(command, cwd, env, out, timeout, max_rss):
    bounded = ["python3", str(ROOT / "scripts/run_with_timeout.py"), "--max-rss-gib", str(max_rss), str(timeout), "--", *command]
    started = time.monotonic()
    with out.open("wb") as log:
        proc = subprocess.run(bounded, cwd=cwd, env=env, stdout=log, stderr=subprocess.STDOUT)
    return {"command": command, "bounded_command": bounded, "cwd": str(cwd),
            "returncode": proc.returncode, "wall_seconds": time.monotonic() - started,
            "log": str(out), "log_sha256": sha(out)}

def unit_graph_from_log(text):
    """Read Cargo's graph without accepting another JSON diagnostic as it."""
    graphs = []
    decoder = json.JSONDecoder()
    for start in re.finditer(r"(?m)^\s*\{", text):
        try:
            value, _ = decoder.raw_decode(text[start.start():].lstrip())
        except ValueError:
            continue
        if isinstance(value, dict) and {"version", "units", "roots"} <= value.keys():
            graphs.append(value)
    assert len(graphs) == 1, "require exactly one Cargo unit graph"
    assert graphs[0]["version"] == 1, "unsupported Cargo unit graph version"
    return graphs[0]


def required_unit_outcomes(graph, invocations, target, lane):
    """Account for required units even when dependency failures prevent rustc."""
    assert graph["units"] and graph["roots"], "empty Cargo unit graph"
    indexed = [(index, unit) for index, unit in enumerate(graph["units"])
               if unit["platform"] == target and unit["mode"] == "build"
               and unit["target"]["kind"] != ["custom-build"]]
    required = {index for index, _ in indexed}
    assert required and set(graph["roots"]) <= required, "required library roots missing from graph"
    result = []
    for index, unit in indexed:
        name = unit["target"]["name"].replace("-", "_")
        source = Path(unit["target"]["src_path"]).resolve()
        features = set(unit["features"])
        matches = []
        for row in invocations:
            if not row.get("target_crate") or row.get("target") != target or row.get("crate") != name:
                continue
            command = row["command"]
            sources = [Path(arg) if Path(arg).is_absolute() else Path(row["cwd"]) / arg
                       for arg in command if not arg.startswith("-")
                       and (arg.endswith(".rs") or Path(arg).is_absolute())]
            actual_features = set()
            for arg in command:
                if arg.startswith("--cfg="):
                    arg = arg[len("--cfg="):]
                if arg.startswith('feature="'):
                    actual_features.add(json.loads(arg[len("feature="):]))
            if source in {p.resolve() for p in sources} and features == actual_features:
                matches.append(row)
        expected = ("cg" if lane in ("full-cg", "full-cg-proof")
                    or (lane == "mixed" and name in ("core", "alloc")) else "llvm")
        if not matches:
            outcome = "not_attempted"
        elif len(matches) != 1:
            outcome = "ambiguous"
        elif not matches[0]["complete"]:
            outcome = "incomplete"
        elif matches[0]["returncode"] != 0:
            outcome = "failed"
        elif matches[0]["backend"] != expected:
            outcome = "wrong_backend"
        elif "-Ztrust-ir-lower=on" not in matches[0]["command"]:
            outcome = "noncanonical"
        else:
            outcome = "compiled"
        result.append({"unit_index": index, "package_id": unit["pkg_id"], "crate": name,
                       "source": str(source), "features": sorted(features),
                       "expected_backend": expected, "outcome": outcome})
    return result


def build(args):
    sources = {"full": prepare, "std": prepare_std, "extended": prepare_extended}[args.source_profile]()
    baseline_path = Path(args.baseline).resolve()
    baseline = json.loads(baseline_path.read_text())
    assert baseline["qualified"] and baseline["source_unchanged"]
    assert baseline["compiler_sha256"] == sha(TC / "bin/trustc")
    assert baseline["build_tool_sha256"] == sha(TC / "bin/targo")
    backend = baseline["backend"]
    assert sha(backend["path"]) == backend["sha256"]
    run_dir = OUT / args.label
    run_dir.mkdir()  # Refuse reuse, including a previous failed build.
    shutil.copy2(__file__, run_dir / "driver.py")
    shutil.copy2(WRAPPER, run_dir / "compiler-wrapper.py")
    frozen_wrapper = run_dir / "compiler-wrapper.py"
    config = {"lane": args.lane, "opt": args.opt, "backend": backend, "target": TARGET, "invocations": str(run_dir / "invocations")}
    (run_dir / "invocations").mkdir()
    write(run_dir / "wrapper-config.json", config)
    env = clean_environment()
    env.update(CARGO_TARGET_DIR=str(run_dir / "target"), RUSTC_WRAPPER=str(frozen_wrapper),
               STD_CORRECTNESS_CONFIG=str(run_dir / "wrapper-config.json"),
               CARGO_ENCODED_RUSTFLAGS="\x1f".join(["-Ztrust-verify=off", "-Zforce-unstable-if-unmarked", "-Ccodegen-units=1"]),
               CARGO_PROFILE_DEV_DEBUG="0", CARGO_PROFILE_DEV_OPT_LEVEL=str(args.opt), CARGO_PROFILE_DEV_CODEGEN_UNITS="1")
    source = Path(sources["source"])
    command = [str(TC / "bin/targo"), "--unverified", "build", "--manifest-path", str(source / "library/Cargo.toml"),
               "-p", args.package, "--lib", "--features=backtrace,panic-unwind", "--target", TARGET,
               "--locked", "--offline", "-j", "2", "--message-format=json", "--keep-going", "-vv"]
    record = {"schema": "trust-cg.std-real-library-build.v1", "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "complete": False, "correctness_qualified": False, "lane": args.lane, "opt": args.opt, "package": args.package, "target": TARGET,
              "canonical_query_providers": True, "frontend_ir_lowering": "on (advisory)",
              "backend_build_source_coherent": True, "backend_build_coherence_scope": "Successful isolated immutable backend build and source stability; this is not correctness or proof qualification.",
              "baseline": str(baseline_path), "baseline_sha256": sha(baseline_path), "backend": backend,
              "source_record_sha256": sha(OUT / ("source.json" if args.source_profile == "full" else ("source-extended.json" if args.source_profile == "extended" else ("source-std-lock-resolved.json" if (OUT / "source-std-lock-resolved.json").exists() else "source-std.json")))), "source_profile": args.source_profile, "backend_source_head": baseline["head"],
              "compiler_sha256": sha(TC / "bin/trustc"), "build_tool_sha256": sha(TC / "bin/targo"),
              "wrapper_sha256": sha(frozen_wrapper), "driver_sha256": sha(run_dir / "driver.py"), "environment": {key: env[key] for key in ["PATH", "RUSTC", "RUSTDOC", "RUSTUP_TOOLCHAIN", "RUSTC_BOOTSTRAP", "LD_LIBRARY_PATH", "CARGO_TARGET_DIR", "RUSTC_WRAPPER", "STD_CORRECTNESS_CONFIG", "CARGO_ENCODED_RUSTFLAGS", "CARGO_PROFILE_DEV_DEBUG", "CARGO_PROFILE_DEV_OPT_LEVEL", "CARGO_PROFILE_DEV_CODEGEN_UNITS", "CARGO_INCREMENTAL"]},
              "original_driver_sha256": sha(__file__), "original_wrapper_sha256": sha(WRAPPER), "compiler_identity": COMPILER_IDENTITY,
              "configuration": str(CONFIGURATION_PATH), "configuration_sha256": sha(CONFIGURATION_PATH),
              "scope": "Real requested library package with complete backtrace+panic-unwind features and locked target dependency graph; host build scripts use LLVM. Native consumer qualification is a separate required step. Frontend compilation is the explicit unverified diagnostic lane."}
    write(run_dir / "build.json", record)
    unit_command = [arg for arg in command if arg not in
                    ("--message-format=json", "--keep-going", "-vv")]
    unit_command += ["--unit-graph", "-Zunstable-options"]
    record["unit_graph_execution"] = command_run(
        unit_command, source / "library", env, run_dir / "unit-graph.log",
        min(args.timeout, 300), args.max_rss_gib)
    try:
        assert record["unit_graph_execution"]["returncode"] == 0, "Cargo unit graph failed"
        graph = unit_graph_from_log((run_dir / "unit-graph.log").read_text(errors="replace"))
        record["required_units"] = required_unit_outcomes(graph, [], TARGET, args.lane)
    except (AssertionError, KeyError, ValueError) as error:
        record.update(complete=True, build_passed=False, failed_phase="unit-graph",
                      unit_graph_error=str(error))
        write(run_dir / "build.json", record)
        print(json.dumps({"build_passed": False, "failed_phase": "unit-graph",
                          "error": str(error)}), flush=True)
        return 1
    write(run_dir / "unit-graph.json", graph)
    record["unit_graph_sha256"] = sha(run_dir / "unit-graph.json")
    write(run_dir / "build.json", record)
    record["execution"] = command_run(command, source / "library", env, run_dir / "build.log", args.timeout, args.max_rss_gib)
    invocations = [json.loads(path.read_text()) for path in sorted((run_dir / "invocations").glob("*.json"))]
    record["required_units"] = required_unit_outcomes(graph, invocations, TARGET, args.lane)
    record["required_unit_counts"] = {
        outcome: sum(row["outcome"] == outcome for row in record["required_units"])
        for outcome in sorted({row["outcome"] for row in record["required_units"]})}
    record["invocations"] = [{key: row.get(key) for key in ["crate", "target", "target_crate", "backend", "returncode", "wall_seconds", "complete"]} for row in invocations]
    record["target_crates"] = sorted({row["crate"] for row in invocations if row["target_crate"]})
    refusals = []
    for path in sorted((run_dir / "invocations").glob("*.stderr.log")):
        for line in path.read_text(errors="replace").splitlines():
            try:
                event = json.loads(line)
            except ValueError:
                continue
            if isinstance(event, dict) and event.get("code") == "TCG-MIR-UNSUPPORTED":
                fields = event["fields"]
                failed = fields["failed_roots"].split("\n  - ")
                assert len(failed) == int(fields["failed_root_count"])
                refusals.append({"stderr_log": str(path), "stderr_sha256": sha(path), "count": len(failed), "failed_roots": failed, "event": event})
    write(run_dir / "failed-roots.json", refusals)
    record["failed_roots_record_sha256"] = sha(run_dir / "failed-roots.json")
    record["failed_root_counts"] = [{"stderr_log": row["stderr_log"], "count": row["count"]} for row in refusals]
    record["source_unchanged"] = file_manifest(source) == sources["files_sha256"]
    record["backend_unchanged"] = sha(backend["path"]) == backend["sha256"]
    record["compiler_unchanged"] = sha(TC / "bin/trustc") == record["compiler_sha256"]
    record["build_tool_unchanged"] = sha(TC / "bin/targo") == record["build_tool_sha256"]
    record["wrapper_unchanged"] = sha(frozen_wrapper) == record["wrapper_sha256"]
    record["driver_unchanged"] = sha(__file__) == record["original_driver_sha256"] and sha(run_dir / "driver.py") == record["driver_sha256"]
    record["original_wrapper_unchanged"] = sha(WRAPPER) == record["original_wrapper_sha256"]
    record["configuration_unchanged"] = sha(CONFIGURATION_PATH) == record["configuration_sha256"]
    record["baseline_unchanged"] = sha(baseline_path) == record["baseline_sha256"]
    record["compiler_identity_unchanged"] = identity_preflight() == COMPILER_IDENTITY
    record["build_passed"] = record["execution"]["returncode"] == 0 and all(record[key] for key in ["source_unchanged", "backend_unchanged", "compiler_unchanged", "build_tool_unchanged", "wrapper_unchanged", "driver_unchanged", "original_wrapper_unchanged", "configuration_unchanged", "baseline_unchanged", "compiler_identity_unchanged"])
    record["build_passed"] &= all(row["outcome"] == "compiled" for row in record["required_units"])
    deps = run_dir / "target" / TARGET / "debug/deps"
    record["artifacts"] = [{"path": str(path), "sha256": sha(path), "bytes": path.stat().st_size} for path in sorted(deps.glob("*")) if path.suffix in {".rlib", ".so"}]
    record["complete"] = True
    write(run_dir / "build.json", record)
    print(json.dumps({key: record[key] for key in ["lane", "opt", "build_passed", "required_unit_counts", "target_crates", "invocations", "execution"]}), flush=True)
    return 0 if record["build_passed"] else 1

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--configuration", required=True, help="Explicit frozen toolchain/source/output configuration JSON")
    parser.add_argument("operation", choices=["prepare", "prepare-std", "prepare-extended", "resolve-std", "build"])
    parser.add_argument("--baseline")
    parser.add_argument("--lane", choices=["llvm", "mixed", "full-cg", "full-cg-proof"])
    parser.add_argument("--opt", type=int, choices=range(4))
    parser.add_argument("--label")
    parser.add_argument("--source-profile", choices=["full", "std", "extended"], default="full")
    parser.add_argument("--package", choices=["std", "sysroot"], default="std")
    parser.add_argument("--timeout", type=int, default=7200)
    parser.add_argument("--max-rss-gib", type=int, default=16)
    args = parser.parse_args()
    initialize(args.configuration)
    if args.operation == "resolve-std":
        resolve_std()
        return 0
    if args.operation in {"prepare", "prepare-std", "prepare-extended"}:
        result = {"prepare": prepare, "prepare-std": prepare_std, "prepare-extended": prepare_extended}[args.operation]()
        print(json.dumps({"source": result["source"], "files": len(result["files_sha256"])}), flush=True)
        return 0
    assert args.baseline and args.lane and args.label and args.opt is not None
    assert "/" not in args.label and args.label not in {"", ".", ".."}
    return build(args)

if __name__ == "__main__":
    raise SystemExit(main())
