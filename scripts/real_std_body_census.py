#!/usr/bin/python3
"""Census real std bodies against explicitly identified LLVM-built dependencies.

This diagnostic never substitutes for the complete all-CG sysroot graph.
"""
import argparse
import collections
import datetime
import json
from pathlib import Path
import re
import runpy
import shutil

HELPERS = runpy.run_path(str(Path(__file__).with_name("real_std_sysroot.py")))
sha, write, file_manifest, clean_environment, command_run = (HELPERS[key] for key in ["sha", "write", "file_manifest", "clean_environment", "command_run"])

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--configuration", required=True)
    parser.add_argument("--control", required=True, help="Closed complete LLVM-control build.json")
    parser.add_argument("--baseline", required=True, help="Sealed source-coherent backend build.json")
    parser.add_argument("--label", required=True)
    parser.add_argument("--opt", choices=range(4), type=int, default=0)
    parser.add_argument("--timeout", type=int, default=1200)
    parser.add_argument("--max-rss-gib", type=int, default=16)
    parser.add_argument("--diag-dump", action="store_true", help="Retain backend IR dumps for source diagnosis")
    args = parser.parse_args()
    context = HELPERS["initialize"](args.configuration)
    ROOT, OUT, TC = (context[key] for key in ["ROOT", "OUT", "TC"])
    control_path, baseline_path = Path(args.control).resolve(), Path(args.baseline).resolve()
    control, baseline = (json.loads(p.read_text()) for p in [control_path, baseline_path])
    assert control["complete"] and control["build_passed"] and control["lane"] == "llvm"
    assert baseline["qualified"] and baseline["source_unchanged"]
    assert baseline["compiler_sha256"] == control["compiler_sha256"] == sha(TC / "bin/trustc")
    backend = baseline["backend"]
    assert sha(backend["path"]) == backend["sha256"]
    invocations = [(p, json.loads(p.read_text())) for p in (control_path.parent / "invocations").glob("std-*.json")]
    invocations = [(p, row) for p, row in invocations if row["crate"] == "std" and row["target_crate"]]
    assert len(invocations) == 1
    invocation_path, original = invocations[0]
    assert original["complete"] and original["returncode"] == 0 and original["backend"] == "llvm"
    assert original["target"] == context["TARGET"], "census configuration target differs from actual std invocation"
    assert "/" not in args.label and args.label not in {"", ".", ".."}
    run_dir = OUT / args.label
    run_dir.mkdir()
    shutil.copy2(__file__, run_dir / "census-driver.py")
    products = run_dir / "products"
    products.mkdir()
    command = list(original["command"])
    command[command.index("--out-dir") + 1] = str(products)
    assert not any("codegen-backend" in arg for arg in command)
    backend_args = "diag-json no-proof-certs" + (" diag-dump" if args.diag_dump else "")
    command += ["-Copt-level=" + str(args.opt), "-Zcodegen-backend=" + backend["path"], "-Ztrust-ir-cg-args=" + backend_args]
    env = clean_environment()
    env.update(original["environment"])
    # Cargo's jobserver belongs to the closed control process; no inherited fds.
    env.pop("CARGO_MAKEFLAGS", None)
    env["CARGO_TARGET_DIR"] = str(run_dir)
    deps = []
    for i, arg in enumerate(command):
        if arg == "--extern":
            name, filename = command[i + 1].split("=", 1)
            path = Path(filename)
            assert path.is_file()
            deps.append({"extern": name, "path": str(path), "sha256": sha(path), "backend": "llvm", "source_control_build": str(control_path)})
    assert deps and len({row["extern"] for row in deps}) == len(deps)
    all_control_artifacts = [{"path": row["path"], "sha256": row["sha256"], "backend": "llvm"} for row in control["artifacts"]]
    assert all(sha(row["path"]) == row["sha256"] for row in all_control_artifacts)
    source = Path(original["cwd"]).parent
    before = file_manifest(source)
    generated = Path(env["OUT_DIR"])
    generated_before = file_manifest(generated)
    record = {"schema": "trust-cg.real-std-body-census.v1", "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "complete": False, "correctness_qualified": False, "all_cg_sysroot_qualified": False,
              "scope": "Actual complete std crate source/features replayed with sealed CG backend and every dependency explicitly LLVM-built. Diagnostic only; original complete all-CG dependency failures remain open.",
              "backend_source_head": baseline["head"], "backend": backend, "opt": args.opt,
              "baseline": str(baseline_path), "baseline_sha256": sha(baseline_path),
              "llvm_control": str(control_path), "llvm_control_sha256": sha(control_path),
              "original_std_invocation": str(invocation_path), "original_std_invocation_sha256": sha(invocation_path),
              "compiler_sha256": sha(TC / "bin/trustc"), "driver_sha256": sha(run_dir / "census-driver.py"),
              "original_driver_sha256": sha(__file__), "helper_sha256": sha(Path(__file__).with_name("real_std_sysroot.py")),
              "configuration": str(context["CONFIGURATION_PATH"]), "configuration_sha256": sha(context["CONFIGURATION_PATH"]),
              "compiler_identity": context["COMPILER_IDENTITY"],
              "environment": env, "llvm_extern_dependencies": deps, "llvm_control_artifacts": all_control_artifacts,
              "source": str(source), "source_files_sha256": before, "generated_source": str(generated), "generated_files_sha256": generated_before,
              "command_changes": {"out_dir": str(products), "backend": backend["path"], "opt": args.opt, "backend_args": backend_args}}
    write(run_dir / "result.json", record)
    record["execution"] = command_run(command, original["cwd"], env, run_dir / "std-body.log", args.timeout, args.max_rss_gib)
    events, roots = [], []
    for line in (run_dir / "std-body.log").read_text(errors="replace").splitlines():
        try:
            event = json.loads(line)
        except ValueError:
            continue
        if isinstance(event, dict) and str(event.get("code", "")).startswith("TCG-"):
            events.append(event)
            if event["code"] == "TCG-MIR-UNSUPPORTED":
                failed = event["fields"]["failed_roots"].split("\n  - ")
                assert len(failed) == int(event["fields"]["failed_root_count"])
                roots += failed
    write(run_dir / "backend-events.json", events)
    write(run_dir / "failed-roots.json", roots)
    causes = collections.Counter()
    for root in roots:
        source_span = re.split(r"\(#\d+\)\): ", root, maxsplit=1)
        reason = source_span[1] if len(source_span) == 2 else root.split(": ", 1)[1] if ": " in root else root
        tag = re.search(r"\[TCG-[A-Z0-9-]+\]", reason)
        cause = tag.group() if tag else reason.split(": ", 1)[0].split(" (", 1)[0]
        causes[cause] += 1
    record.update(complete=True, refused_roots=len(roots), causes=dict(causes),
                  failed_roots_sha256=sha(run_dir / "failed-roots.json"), events_sha256=sha(run_dir / "backend-events.json"),
                  source_unchanged=before == file_manifest(source), generated_source_unchanged=generated_before == file_manifest(generated),
                  llvm_dependencies_unchanged=all(sha(row["path"]) == row["sha256"] for row in all_control_artifacts),
                  compiler_unchanged=sha(TC / "bin/trustc") == record["compiler_sha256"],
                  driver_unchanged=sha(__file__) == record["original_driver_sha256"] and sha(run_dir / "census-driver.py") == record["driver_sha256"],
                  helper_unchanged=sha(Path(__file__).with_name("real_std_sysroot.py")) == record["helper_sha256"],
                  configuration_unchanged=sha(context["CONFIGURATION_PATH"]) == record["configuration_sha256"],
                  compiler_identity_unchanged=HELPERS["identity_preflight"]() == context["COMPILER_IDENTITY"],
                  baseline_unchanged=sha(baseline_path) == record["baseline_sha256"],
                  control_unchanged=sha(control_path) == record["llvm_control_sha256"],
                  backend_unchanged=sha(backend["path"]) == backend["sha256"],
                  artifacts=[{"path": str(p), "sha256": sha(p)} for p in sorted(products.iterdir()) if p.suffix in {".rlib", ".so"}])
    record["std_build_passed"] = record["execution"]["returncode"] == 0 and all(record[key] for key in ["source_unchanged", "generated_source_unchanged", "llvm_dependencies_unchanged", "compiler_unchanged", "backend_unchanged", "driver_unchanged", "helper_unchanged", "configuration_unchanged", "compiler_identity_unchanged", "baseline_unchanged", "control_unchanged"])
    write(run_dir / "result.json", record)
    print(json.dumps({key: record[key] for key in ["std_build_passed", "refused_roots", "execution"]}), flush=True)
    return 0 if record["std_build_passed"] else 1

if __name__ == "__main__":
    raise SystemExit(main())
