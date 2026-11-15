#!/usr/bin/env python3
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
"""Collect TY's TrustIR modules into the compile corpus.

TY writes every module it hands the native compiler as a replay artifact when
`TY_TRUST_CG_REPLAY_ARTIFACT_DIR` is set (tla-trust-cg `compile/telemetry.rs`):
`<seq>-<stage>-<module>.trust_irbin` (the canonical binary container) plus a
`.metadata.json` naming the opt level, the target and the external symbols the
runtime bound. The `pre_jit` and `linked` stages of one compile carry the same
module; this keeps one copy per distinct module (by SHA-256) and records the
runtime's extern names in the manifest entry.

Two TY configurations produce the corpus:
  ty-semantic  `--source-compile-diagnostic --max-states 1`: the semantic image
               (the whole-spec native lowering) plus its callout batches.
  ty-prod      the production default with `--max-states 1`: the modules the
               shipping configuration compiles (fused BFS levels, callout
               batches), which do not exist on every row.

Usage (dump first, then collect):

    TY_TRUST_CG_REPLAY_ARTIFACT_DIR=<dump>/<mode>/<row> ty check <spec> --config <cfg> \\
        --force --workers 1 --output json [--source-compile-diagnostic] --max-states 1
    collect_ty.py --dump <dump> --manifest corpus.json --ty-commit <sha>

Rows come from TY's 40 strict-exact semantic rows
(reports/perf/2026-09-25-semantic-lane-standard-instance/census.json in TY).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
MODES = {"diag": "ty-semantic", "prod": "ty-prod"}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dump", type=Path, required=True, help="directory holding <mode>/<row>/trust-ir-modules")
    ap.add_argument("--manifest", type=Path, default=HERE / "corpus.json")
    ap.add_argument("--ty-commit", required=True, help="TY commit that produced the dump")
    args = ap.parse_args()

    manifest = json.loads(args.manifest.read_text())
    entries = [e for e in manifest["entries"] if not e["origin"].startswith("ty-")]
    out_dir = HERE / "modules" / "ty"
    if out_dir.exists():
        shutil.rmtree(out_dir)
    out_dir.mkdir(parents=True)

    seen: dict[str, str] = {}
    added = 0
    for mode, origin in MODES.items():
        mode_dir = args.dump / mode
        if not mode_dir.is_dir():
            continue
        for row_dir in sorted(p for p in mode_dir.iterdir() if p.is_dir()):
            mods = row_dir / "trust-ir-modules"
            if not mods.is_dir():
                continue
            index = 0
            for binfile in sorted(mods.glob("*.trust_irbin")):
                if ".linked-" in binfile.name:
                    continue  # same module as the pre_jit stage of this compile
                data = binfile.read_bytes()
                digest = hashlib.sha256(data).hexdigest()
                if digest in seen:
                    continue
                meta_path = binfile.with_name(binfile.name.replace(".trust_irbin", ".metadata.json"))
                meta = json.loads(meta_path.read_text())
                name = f"{origin}/{row_dir.name}/{index}"
                index += 1
                seen[digest] = name
                rel = Path("modules") / "ty" / f"{origin}--{row_dir.name}--{index - 1}.trust_irbin"
                (HERE / rel).write_bytes(data)
                # pre_jit metadata lists names; linked metadata lists {name, address}.
                externs = sorted(
                    s["name"] if isinstance(s, dict) else s
                    for s in meta.get("extern_symbols", {}).get("module_external_declarations", [])
                )
                entries.append(
                    {
                        "name": name,
                        "file": str(rel),
                        "origin": origin,
                        "opt_level": meta["opt_level"],
                        # The AOT object lane refuses these modules on Darwin (direct
                        # module-function binding); TY compiles them through the JIT.
                        "lanes": ["jit-raw", "jit-raw-checked"],
                        "externs": externs,
                        "provenance": {
                            "ty_commit": args.ty_commit,
                            "stage": meta["stage"],
                            "sha256": digest,
                            "bytes": len(data),
                        },
                    }
                )
                added += 1
    manifest["entries"] = entries
    args.manifest.write_text(json.dumps(manifest, indent=1) + "\n")
    print(f"collected {added} distinct TY modules into {out_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
