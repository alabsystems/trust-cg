#!/usr/bin/env python3
"""How benchmarks/real-corpus/manifest.json version 1.0.0 was generated (2026-10-14).

Usage: make_manifest.py <checkout>

It reads the bridge's real-program guests and the scale_gate and
compile-scaling generators through benchmarks/real-corpus/run.py, hashes each
.crate archive in this host's Cargo registry cache (the SHA-256 is the
crates.io checksum), and writes the manifest. The crate list is a hand-picked
subset of the crates that meet the first of the manifest's `selection_rules`
(at the version the Trust compiler's Cargo.lock, ~/trust on 2026-10-14, names,
with no build script and no required dependency), chosen before any proofs-on
measurement of them by no further written criterion. qualifying_crates.py
lists the 189 crates that meet that rule, and manifest version 1.0.1 (edited
by hand from this script's output) states the sampling in `selection_rules`.
The `library/` tree id is `git rev-parse 321aaeda7:library` in a Trust
checkout. A later manifest version is written by hand or by an updated copy of
this script, never by editing version 1.0.0's rows in place.
"""
import hashlib, json, sys, importlib.util
from pathlib import Path
REPO = Path(sys.argv[1])
spec = importlib.util.spec_from_file_location("rc", REPO / "benchmarks/real-corpus/run.py")
rc = importlib.util.module_from_spec(spec); spec.loader.exec_module(rc)
REG = Path.home() / ".cargo/registry/cache/index.crates.io-1949cf8c6b5b557f"
rows = []
guests_file = "crates/rustc-codegen-trust-cg/tests/real_program_corpus/corpus_guests.rs"
guests = rc.corpus_guests(REPO / guests_file)
for name, text in guests.items():
    rows.append({"id": f"real-program/{name}", "kind": "real-program", "crate_type": "bin", "run": True,
                 "edition": "2021",
                 "source": {"type": "corpus-guest", "file": guests_file, "guest": name,
                            "sha256": rc.sha256_text(text)}})
crates = [  # name, version, features, default_features
    ("adler2", "2.0.1", [], True), ("aho-corasick", "1.1.5", ["std"], False),
    ("arrayvec", "0.7.8", [], True), ("bitflags", "2.13.1", [], True),
    ("either", "1.18.0", [], True), ("fastrand", "2.5.0", [], True), ("fnv", "1.0.7", [], True),
    ("foldhash", "0.2.0", [], True), ("glob", "0.3.4", [], True),
    ("hashbrown", "0.15.5", ["inline-more", "raw-entry"], False), ("heck", "0.5.0", [], True),
    ("hex", "0.4.3", [], True), ("itoa", "1.0.18", [], True), ("memchr", "2.8.3", [], True),
    ("minimal-lexical", "0.2.1", [], True), ("percent-encoding", "2.3.2", [], True),
    ("regex-syntax", "0.8.11", [], True), ("rustc-hash", "2.1.2", [], True),
    ("same-file", "1.0.6", [], True), ("scopeguard", "1.2.0", [], True), ("siphasher", "1.0.3", [], True),
    ("smallvec", "1.15.2", [], True), ("strsim", "0.11.1", [], True), ("termcolor", "1.4.1", [], True),
    ("unicode-ident", "1.0.24", [], True), ("unicode-segmentation", "1.13.3", [], True),
    ("unicode-width", "0.2.2", [], True)]
for name, version, features, default in crates:
    digest = hashlib.sha256((REG / f"{name}-{version}.crate").read_bytes()).hexdigest()
    src = {"type": "crates-io", "name": name, "version": version, "sha256": digest}
    if features:
        src["features"] = features
    if not default:
        src["default_features"] = False
    rows.append({"id": f"crate/{name}-{version}", "kind": "real-crate", "crate_type": "lib",
                 "source": src})
for opt in ("0", "3"):
    rows.append({"id": f"trust-sysroot/core-O{opt}", "kind": "trust-sysroot", "crate_type": "lib",
                 "opt_level": opt, "edition": "2024", "crate_name": "core",
                 "env": {"RUSTC_BOOTSTRAP": "1"}, "timeout_s": 3600,
                 "source": {"type": "trust-git", "revision": "321aaeda75478038420d97830f14724c33c8dc39",
                            "path": "library", "tree": "fbda2d979e5915f5ef620c6ca79c0631a7bc4cac",
                            "archive_paths": ["library/core", "library/stdarch", "library/portable-simd"],
                            "root": "core/src/lib.rs"}})
for size, _ in rc.SCALE_GATE.SIZES:
    text = rc.generated_source({"generator": "scale_gate", "size": size})
    rows.append({"id": f"ladder/scale_gate/{size}", "kind": "scale-ladder", "crate_type": "bin",
                 "run": True, "edition": "2021", "opt_level": "3",
                 "source": {"type": "generator", "generator": "scale_gate", "size": size,
                            "sha256": rc.sha256_text(text)}})
ladder = {"blocks": [100, 200, 400, 800], "loops": [15, 30, 60, 120], "funcs": [50, 100, 200, 400],
          "arraysize": [4096, 16384, 65536, 262144]}
for shape, sizes in ladder.items():
    for n in sizes:
        src = {"generator": "compile-scaling", "shape": shape, "n": n}
        text = rc.generated_source(src)
        rows.append({"id": f"ladder/compile-scaling/{shape}-{n}", "kind": "scale-ladder",
                     "crate_type": "bin", "run": True, "edition": "2021", "opt_level": "2",
                     "rustc_flags": ["-Coverflow-checks=off", "-Ccodegen-units=1", "-Cdefault-linker-libraries=y"],
                     "source": {"type": "generator", **src, "sha256": rc.sha256_text(text)}})
manifest = {
    "schema": "trust-cg-real-corpus-manifest-v1",
    "corpus": "l14-real-corpus",
    "version": "1.0.0",
    "date": "2026-10-14",
    "ledger": ["L14-P7"],
    "description": "The larger L14-P7 denominator beyond the 18-program beat-llvm corpus: the bridge's 13 real-program guests, 27 crates.io library crates from the Trust toolchain's own Cargo.lock (no build script, no required dependency, compiled alone with the default or the named dependency-free features), the installed Trust compiler's own library/core at its revision (O0 and O3), and the scale_gate and compile-scaling ladders. Every row is intent-to-treat.",
    "selection_rules": [
        "A crates.io crate is in the Trust compiler's Cargo.lock at this version, has no build script and no required dependency, and its default features enable no optional dependency (otherwise the named dependency-free features are used).",
        "A row's identity is its source digest: the .crate archive SHA-256 (the crates.io checksum), the guest or generator text SHA-256, or the git tree of library/ at the driver's revision. A changed digest is a new corpus version, never an edit in place.",
        "Rows are never removed because of a bridge outcome; a version may add rows, and removes one only with a stated reason recorded in revisions."
    ],
    "defaults": {"opt_level": "3", "panic": "abort", "timeout_s": 900, "n_compile": 3, "n_run": 5},
    "revisions": [{"version": "1.0.0", "date": "2026-10-14",
                   "note": "First version, fixed before the first proofs-on measurement of these rows."}],
    "rows": rows,
}
out = REPO / "benchmarks/real-corpus/manifest.json"
out.write_text(json.dumps(manifest, indent=1) + "\n")
print(len(rows), "rows")
