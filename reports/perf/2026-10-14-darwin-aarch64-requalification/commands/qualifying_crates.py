#!/usr/bin/env python3
"""The population real-corpus version 1.0.0's 27 crates were drawn from (review round 1).

Usage: qualifying_crates.py <trust-cg checkout> <trust checkout> > qualifying-crates.tsv

For every crates.io package that the Trust compiler's Cargo.lock (the
checkout's HEAD; ~/trust on this host, last changed 2026-09-16) names, and
every path package it names whose crates.io archive at that version is in the
registry cache (memchr 2.8.3 and rustc-hash 2.1.2 are such rows of version
1.0.0), it
applies the manifest's first selection rule with the harness's own code
(benchmarks/real-corpus/run.py registry_archive, safe_extract, crate_plan):
the archive is in this host's Cargo registry cache, the crate has a library
target that is not a proc-macro, no build script and no required dependency,
and its default features, or failing that no default features, enable no
optional dependency. It prints one TSV row per package and a count summary on
stderr. It compiles nothing.
"""
import importlib.util
import subprocess
import sys
import tempfile
import tomllib
from pathlib import Path

repo, trust = Path(sys.argv[1]), Path(sys.argv[2])
spec = importlib.util.spec_from_file_location("rc", repo / "benchmarks/real-corpus/run.py")
rc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rc)
lock = tomllib.loads(subprocess.run(["git", "-C", str(trust), "show", "HEAD:Cargo.lock"],
                                    check=True, capture_output=True, text=True).stdout)
cargo_home = Path.home() / ".cargo"
manifest = rc.load_manifest(repo / "benchmarks/real-corpus/manifest.json")
chosen = {(r["source"]["name"], r["source"]["version"]) for r in manifest["rows"]
          if r["source"]["type"] == "crates-io"}
counts = {}
print("name\tversion\tverdict\tin_manifest\tdetail")
for package in sorted(lock["package"], key=lambda p: (p["name"], p["version"])):
    name, version = package["name"], package["version"]
    archive = rc.registry_archive(cargo_home, name, version)
    registry = str(package.get("source", "")).startswith("registry+")
    if not registry and archive is None:
        continue  # a Trust workspace or path package with no crates.io archive
    detail = "" if registry else "path package in the lock; crates.io archive at its version"
    if archive is None:
        verdict = "excluded: archive not in the registry cache"
    else:
        with tempfile.TemporaryDirectory(prefix="qualifying-") as tmp:
            rc.safe_extract(archive.read_bytes(), Path(tmp))
            crate = Path(tmp) / f"{name}-{version}"
            toml = tomllib.loads((crate / "Cargo.toml").read_text())
            lib = toml.get("lib") or {}
            if lib.get("proc-macro") or lib.get("proc_macro"):
                verdict = "excluded: proc-macro"
            else:
                verdict = None
                for label, source in (("qualifies: default features", {}),
                                      ("qualifies: no default features", {"default_features": False})):
                    try:
                        plan = rc.crate_plan(crate, source)
                    except rc.ManifestError as error:
                        detail = str(error)
                        if "optional dependency" in detail and source == {}:
                            continue
                        verdict = "excluded: " + detail
                        break
                    if not plan["root"].is_file():
                        verdict, detail = "excluded: no library target", ""
                    else:
                        verdict = label
                    break
    key = verdict.split(":")[0] if verdict.startswith("qualifies") else verdict.split(" [")[0].split(" {")[0]
    key = "excluded: crate requires dependencies" if verdict.startswith("excluded: crate requires") else key
    counts[key] = counts.get(key, 0) + 1
    print(f"{name}\t{version}\t{verdict}\t{'yes' if (name, version) in chosen else 'no'}\t{detail}")
for key, value in sorted(counts.items(), key=lambda kv: -kv[1]):
    print(f"{value:4} {key}", file=sys.stderr)
