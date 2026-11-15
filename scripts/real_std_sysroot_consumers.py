#!/usr/bin/python3
"""Execute unchanged library consumers using only one identified rebuilt sysroot."""
import argparse
import json
from pathlib import Path
import re
import runpy
import shutil
import subprocess

HELPERS = runpy.run_path(str(Path(__file__).with_name("real_std_sysroot.py")))
sha, write, clean_environment, command_run = (HELPERS[key] for key in ["sha", "write", "clean_environment", "command_run"])

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--configuration", required=True)
    parser.add_argument("build", help="Closed real-library build.json")
    parser.add_argument("--label", required=True)
    parser.add_argument("--backend-build", help="Separate successful sealed backend build receipt for CG consumers; library artifact identity stays bound to the original build")
    parser.add_argument("--opts", type=int, nargs="+", choices=range(4), default=[0, 1, 2, 3])
    args = parser.parse_args()
    context = HELPERS["initialize"](args.configuration)
    ROOT, TC, TARGET = (context[key] for key in ["ROOT", "TC", "TARGET"])
    build_path = Path(args.build).resolve()
    build = json.loads(build_path.read_text())
    assert build["complete"] and build["build_passed"]
    build_command = build["execution"]["command"]
    build_target = build.get("target", build_command[build_command.index("--target") + 1])
    assert build_target == TARGET, "consumer configuration target differs from actual library build"
    assert TARGET == context["COMPILER_IDENTITY"]["host"], "native consumers require the compiler host target"
    assert sha(build["backend"]["path"]) == build["backend"]["sha256"]
    assert sha(TC / "bin/trustc") == build["compiler_sha256"]
    consumer_backend = build["backend"]
    consumer_backend_source_head = build["backend_source_head"]
    consumer_backend_build_path = Path(args.backend_build).resolve() if args.backend_build else None
    consumer_backend_build_sha256 = None
    if consumer_backend_build_path:
        consumer_build = json.loads(consumer_backend_build_path.read_text())
        assert consumer_build.get("qualified") and consumer_build.get("source_unchanged") and consumer_build.get("exit_code") == 0, "consumer backend must be a successful source-coherent build, not a correctness qualification"
        assert consumer_build["compiler_sha256"] == build["compiler_sha256"], "consumer backend and exact library compiler identities differ"
        consumer_backend = consumer_build["backend"]
        assert consumer_backend.get("immutable_for_subsequent_reproductions"), "consumer backend must name an immutable sealed artifact"
        assert sha(consumer_backend["path"]) == consumer_backend["sha256"], "sealed consumer backend artifact differs from its receipt"
        consumer_backend_source_head = consumer_build["head"]
        consumer_backend_build_sha256 = sha(consumer_backend_build_path)
    configuration_path = context["CONFIGURATION_PATH"]
    out = build_path.parent / args.label
    out.mkdir()
    shutil.copy2(__file__, out / "consumer-driver.py")
    shutil.copy2(Path(__file__).with_name("real_std_sysroot.py"), out / "real_std_sysroot.py")
    libdir = out / "sysroot/lib/rustlib" / TARGET / "lib"
    libdir.mkdir(parents=True)
    artifacts = []
    for artifact in build["artifacts"]:
        src = Path(artifact["path"])
        assert sha(src) == artifact["sha256"]
        dst = libdir / src.name
        shutil.copy2(src, dst)
        dst.chmod(0o444)
        assert sha(dst) == artifact["sha256"]
        artifacts.append({"path": str(dst), "source": str(src), "sha256": sha(dst)})
    std_libraries = sorted(libdir.glob("libstd*.so"))
    assert len(std_libraries) == 1
    std_library = std_libraries[0]
    fixtures = out / "fixtures"
    fixtures.mkdir()
    prior = Path(context["CONFIGURATION"]["core_fixture_directory"]).resolve()
    fixture_paths = [prior / name for name in ["core-consumer.rs", "core-driver.c", "real-runtime.rs", "mixed-core-panic.rs", "core-reference-format.rs"]]
    fixture_paths += [Path(context["CONFIGURATION"].get("alloc_fixture_directory", str(ROOT / "crates/rustc-codegen-trust-cg/tests/support/sysroot_native_layout"))).resolve() / name for name in ["alloc_consumer.rs", "alloc_driver.c"]]
    fixture_record = []
    for src in fixture_paths:
        dst = fixtures / src.name
        shutil.copy2(src, dst)
        fixture_record.append({"source": str(src), "source_sha256": sha(src), "path": str(dst), "sha256": sha(dst)})
    env = clean_environment()
    exports = subprocess.check_output(["nm", "-D", "--defined-only", str(std_library)], env=env, text=True)
    (out / "std-dynamic-symbols.txt").write_text(exports)
    symbols = [line.split()[-1] for line in exports.splitlines() if "3str5count14do_count_chars" in line]
    assert len(symbols) == 1, "the real core count function must be exported uniquely"
    consumer_path = fixtures / "core-consumer.rs"
    old = consumer_path.read_text()
    new, count = re.subn(r'(?<=#\[link_name = ")[^"]+(?="\])', symbols[0], old)
    assert count == 1
    consumer_path.write_text(new)
    record = {"schema": "trust-cg.std-exact-sysroot-consumers.v1", "complete": False,
              "native_passed": False, "build": str(build_path), "build_sha256": sha(build_path),
              "library_build_lane": build["lane"], "library_build_opt": build["opt"],
              "backend_source_head": consumer_backend_source_head, "backend": consumer_backend,
              "library_backend_source_head": build["backend_source_head"], "library_backend": build["backend"],
              "consumer_backend_build": str(consumer_backend_build_path) if consumer_backend_build_path else None,
              "consumer_backend_build_sha256": consumer_backend_build_sha256,
              "consumer_backend_coherence_is_correctness_qualification": False,
              "compiler_sha256": sha(TC / "bin/trustc"),
              "driver_sha256": sha(__file__), "helper_sha256": sha(Path(__file__).with_name("real_std_sysroot.py")), "compiler_identity": context["COMPILER_IDENTITY"],
              "configuration": str(configuration_path), "configuration_sha256": sha(configuration_path),
              "artifacts": artifacts, "fixtures": fixture_record,
              "private_core_symbol_adaptation": {"before_sha256": __import__("hashlib").sha256(old.encode()).hexdigest(), "after_sha256": sha(consumer_path), "symbol": symbols[0], "change": "Only the metadata-dependent link_name is replaced with the exact rebuilt library's exported symbol; assertions and test inputs are unchanged."},
              "consumer_opts": args.opts, "commands": [], "cells": [],
              "scope": "Executed UTF-8, alloc/Unicode/drain, formatting and panic/drop consumers linked to this exact rebuilt library. No count-only, host-only, mixed-library or no-proof run establishes full self-hosting/proof qualification."}
    write(out / "results.json", record)
    def run(label, command, cwd, run_env, timeout=240):
        row = command_run(command, cwd, run_env, out / (label + ".log"), timeout, 8)
        row["label"] = label
        record["commands"].append(row)
        write(out / "results.json", record)
        return row
    run("std-dynamic", ["readelf", "-Wd", str(std_library)], out, env)
    run("std-relocations", ["readelf", "-Wr", str(std_library)], out, env)
    programs = [("core", "core-consumer.rs", "core-driver.c", "PASS linked_core checks=81097"),
                ("alloc", "alloc_consumer.rs", "alloc_driver.c", "PASS linked_alloc checks=177224"),
                ("format", "core-reference-format.rs", None, "PASS linked_core_reference_format checks=21504"),
                ("panic", "mixed-core-panic.rs", None, "PASS linked_core_unwind panics=16 drops=16"),
                ("runtime", "real-runtime.rs", None, "PASS real_core_runtime panics=96 drops=96")]
    for opt in args.opts:
        for lane in ["llvm", "cg"]:
            for name, rust_source, c_source, expected in programs:
                stem = f"{name}-{lane}-O{opt}"
                directory = out / stem
                directory.mkdir()
                executable = directory / "native.elf"
                static_alloc = name == "alloc"
                product = directory / ("libconsumer.a" if static_alloc else "libconsumer.so") if c_source else executable
                cmd = [str(TC / "bin/trustc"), "--sysroot", str(out / "sysroot"), "--edition=2024", "--target", TARGET,
                       "-Cpanic=" + ("abort" if static_alloc else "unwind"), f"-Copt-level={opt}", "-Ccodegen-units=1", "-Ztrust-verify=off", str(fixtures / rust_source), "-o", str(product)]
                if not static_alloc:
                    cmd += ["-Cprefer-dynamic"]
                if c_source:
                    cmd += ["--crate-name=sysroot_consumer", "--crate-type=" + ("staticlib" if static_alloc else "cdylib")]
                if lane == "cg":
                    cmd += ["-Zcodegen-backend=" + consumer_backend["path"], "-Ztrust-ir-cg-args=diag-json no-proof-certs"]
                cell = {"program": name, "consumer_lane": lane, "opt": opt, "expected_output": expected, "passed": False}
                record["cells"].append(cell)
                result = run(stem + "-compile", cmd, out, env)
                cell["compile_returncode"] = result["returncode"]
                if result["returncode"]:
                    continue
                if c_source:
                    linkmap = directory / "link.map"
                    link_command = ["cc", "-O2", str(fixtures / c_source), "-L" + str(directory), "-lconsumer"]
                    if static_alloc:
                        # Rebuilt alloc uses unwind; satisfy its emitted personality
                        # reference with this exact real std, never a stub.
                        link_command += [str(std_library)]
                    link_command += ["-Wl,-Map," + str(linkmap), "-Wl,-rpath-link," + str(libdir), "-Wl,-rpath," + str(directory), "-Wl,-rpath," + str(libdir), "-ldl", "-lpthread", "-lm", "-o", str(executable)]
                    result = run(stem + "-link", link_command, out, env)
                    cell["link_returncode"] = result["returncode"]
                    if result["returncode"]:
                        continue
                    cell["linkmap_sha256"] = sha(linkmap)
                    cell["exact_consumer_archive_found"] = str(product) in linkmap.read_text()
                    cell["consumer_product_sha256"] = sha(product)
                run(stem + "-elf", ["readelf", "-Wd", str(executable)], out, env)
                runtime = dict(env)
                runtime.update(LD_LIBRARY_PATH=str(libdir) + ":" + str(directory) + ":" + env["LD_LIBRARY_PATH"], LD_DEBUG="libs")
                result = run(stem + "-native", [str(executable)], out, runtime, timeout=60)
                text = Path(result["log"]).read_text(errors="replace")
                cell.update(native_returncode=result["returncode"], executable_sha256=sha(executable), output_found=expected in text,
                            exact_std_loader_found=("calling init: " + str(std_library)) in text)
                cell["link_provenance"] = "Custom sysroot rlib hashes and compile command, exact consumer static archive in native link map, and exact rebuilt libstd personality loaded" if static_alloc else "Exact rebuilt libstd dynamic-loader initialization"
                exact_library_found = cell["exact_consumer_archive_found"] and cell["exact_std_loader_found"] if static_alloc else cell["exact_std_loader_found"]
                cell["passed"] = result["returncode"] == 0 and cell["output_found"] and exact_library_found
                write(out / "results.json", record)
    record["artifacts_unchanged"] = all(sha(row["path"]) == row["sha256"] and sha(row["source"]) == row["sha256"] for row in artifacts)
    record["backend_unchanged"] = sha(consumer_backend["path"]) == consumer_backend["sha256"]
    record["library_backend_unchanged"] = sha(build["backend"]["path"]) == build["backend"]["sha256"]
    record["consumer_backend_build_unchanged"] = not consumer_backend_build_path or sha(consumer_backend_build_path) == consumer_backend_build_sha256
    record["build_record_unchanged"] = sha(build_path) == record["build_sha256"]
    record["compiler_unchanged"] = sha(TC / "bin/trustc") == record["compiler_sha256"]
    record["configuration_unchanged"] = sha(configuration_path) == record["configuration_sha256"]
    record["driver_unchanged"] = sha(__file__) == record["driver_sha256"] and sha(out / "consumer-driver.py") == record["driver_sha256"]
    record["helper_unchanged"] = sha(Path(__file__).with_name("real_std_sysroot.py")) == record["helper_sha256"] and sha(out / "real_std_sysroot.py") == record["helper_sha256"]
    record["compiler_identity_unchanged"] = HELPERS["identity_preflight"]() == record["compiler_identity"]
    record["fixtures_unchanged"] = all(sha(row["source"]) == row["source_sha256"] and sha(row["path"]) == (record["private_core_symbol_adaptation"]["after_sha256"] if Path(row["path"]).name == "core-consumer.rs" else row["sha256"]) for row in fixture_record)
    record["complete"] = True
    record["native_passed"] = len(record["cells"]) == len(args.opts) * 2 * len(programs) and all(cell["passed"] for cell in record["cells"]) and all(record[key] for key in ["artifacts_unchanged", "backend_unchanged", "library_backend_unchanged", "consumer_backend_build_unchanged", "build_record_unchanged", "compiler_unchanged", "configuration_unchanged", "fixtures_unchanged", "driver_unchanged", "helper_unchanged", "compiler_identity_unchanged"])
    write(out / "results.json", record)
    print(json.dumps({"native_passed": record["native_passed"], "cells": len(record["cells"]), "passed_cells": sum(cell["passed"] for cell in record["cells"]), "results": str(out / "results.json")}), flush=True)
    return 0 if record["native_passed"] else 1

if __name__ == "__main__":
    raise SystemExit(main())
