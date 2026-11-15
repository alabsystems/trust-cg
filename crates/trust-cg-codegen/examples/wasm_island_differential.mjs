// trust-cg-codegen/examples/wasm_island_differential.mjs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The islands' THREE-WAY differential, in-repo.
//
// The island generators (`wasm_canary_island`, `wasm_vt_islands`) author one
// spec in three spellings — the trust-ir builder, an emitted rustc/LLVM twin
// SOURCE, and interpreter-checked expectations — but a generator run only
// ever exercised two of them: it interprets the builder and compiles the
// trust-ir to wasm, then writes the twin source to disk and stops. The twin
// was never compiled and neither module was ever RUN inside this repo, so
// "differential-experimental" was, in repository terms, an intention.
//
// This runner closes that: it compiles the emitted twin with rustc for
// wasm32, instantiates BOTH modules, and replays every baked expectation
// against both. Any divergence — trust-cg vs interpreter, twin vs
// interpreter, or the two compilers against each other — exits nonzero.
//
//   node wasm_island_differential.mjs <island.wasm> <twin.rs> <expected.json>
//
// The manifest shape is discriminated by its keys, so one runner serves every
// island: `inputs`/`expected` (canary, one export `canary(a,b)`),
// `vt_inputs`/`width_runs` (vt islands, `vt_step(s,b)`+`wcwidth(cp)`), or
// `windows`/`import` (the P2 memhash island, `mem_hash(ptr,words)` reading an
// IMPORTED memory — there both modules are handed ONE memory object, which is
// the whole point of that island).

import { execFileSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

const [islandPath, twinPath, expectedPath] = process.argv.slice(2);
if (!islandPath || !twinPath || !expectedPath) {
  console.error(
    "usage: wasm_island_differential.mjs <island.wasm> <twin.rs> <expected.json>",
  );
  process.exit(2);
}

/** The island corpus recipe, spelled identically in the generator: an
 *  xorshift32 fill with planted all-zero and all-0xFF runs. Both modules and
 *  the reference read these exact bytes. */
function fillCorpus(memory) {
  const view = new Uint8Array(memory.buffer);
  let x = 0x12345678 >>> 0;
  for (let i = 0; i < view.length; i++) {
    x ^= x << 13; x >>>= 0;
    x ^= x >>> 17;
    x ^= x << 5; x >>>= 0;
    view[i] = x & 0xff;
  }
  view.fill(0x00, 1024, 1024 + 256);
  view.fill(0xff, 2048, 2048 + 256);
}

const fail = (msg) => {
  console.error(`FAIL: ${msg}`);
  process.exit(1);
};

/** Compile the emitted twin source with rustc for wasm32 — this is the step
 *  a generator run never took, and it is why an out-of-range table literal
 *  could ship as "success" before.
 *
 *  STOCK EXCEPTION (Trust lacks a wasm32-unknown-unknown core/std; measured
 *  `trustc --target wasm32-unknown-unknown` -> E0463 can't find crate for
 *  `core`): the twin compiler is the stock rustc named by ISLAND_TWIN_RUSTC,
 *  used for wasm32 only. It is never looked up on PATH, and no floating
 *  toolchain channel is selected for it. */
function buildTwin(src, extraLinkArgs = []) {
  const twinRustc = process.env.ISLAND_TWIN_RUSTC;
  if (!twinRustc) {
    fail("ISLAND_TWIN_RUSTC is unset: name a stock rustc with the wasm32-unknown-unknown target");
  }
  const dir = mkdtempSync(join(tmpdir(), "island-twin-"));
  const out = join(dir, "twin.wasm");
  try {
    execFileSync(
      twinRustc,
      [
        "--edition",
        "2024",
        "--target",
        "wasm32-unknown-unknown",
        "-C",
        "opt-level=s",
        "-C",
        "panic=abort",
        ...extraLinkArgs.flatMap((a) => ["-C", `link-arg=${a}`]),
        "--crate-type",
        "cdylib",
        src,
        "-o",
        out,
      ],
      {
        stdio: "pipe",
        // Only this independent LLVM twin uses the documented stock lane.
        env: {
          ...process.env,
          ATERM_STOCK_REASON: "canonical independent wasm LLVM twin oracle",
        },
      },
    );
  } catch (e) {
    fail(`the emitted twin does not compile: ${String(e.stderr ?? e).slice(0, 800)}`);
  }
  return { bytes: readFileSync(out), dir };
}

async function instantiate(bytes, what, imports = undefined) {
  if (!WebAssembly.validate(bytes)) fail(`${what} failed WebAssembly.validate`);
  const { instance } = await WebAssembly.instantiate(bytes, imports);
  return instance.exports;
}

const exp = JSON.parse(readFileSync(expectedPath, "utf8"));

// A P2 island imports the host's memory; both modules must receive the SAME
// object or the differential compares two address spaces (which is exactly
// how a twin that forgot --import-memory announces itself).
let imports;
let sharedMemory;
if (Array.isArray(exp.import)) {
  const [impModule, impName] = exp.import;
  sharedMemory = new WebAssembly.Memory({ initial: exp.pages });
  imports = { [impModule]: { [impName]: sharedMemory } };
  // ONE memory object, published under BOTH names: the island's normative
  // namespace and the twin's, which `wasm-ld --import-memory` fixes at
  // `env.memory`. Handing the two modules different objects would compare two
  // address spaces — the failure this island exists to make visible.
  if (Array.isArray(exp.twin_import)) {
    const [twinModule, twinName] = exp.twin_import;
    imports[twinModule] = { ...(imports[twinModule] ?? {}), [twinName]: sharedMemory };
  }
  fillCorpus(sharedMemory);
}

const island = await instantiate(readFileSync(islandPath), "the trust-cg module", imports);
const twinBuild = buildTwin(twinPath, exp.twin_link_args ?? []);
const twin = await instantiate(twinBuild.bytes, "the rustc/LLVM twin", imports);

let checks = 0;
let bad = 0;
// Named honestly per island: the canary/vt manifests are baked by the trust-ir
// INTERPRETER, the memhash manifest by a Rust reference walk re-checked here
// by an independent JS spelling (the interpreter would have to model the
// host's memory, which is the one thing the host owns).
let thirdSpelling = "trust-ir interpreter";
const report = (label, args, want, gotIsland, gotTwin) => {
  if (bad < 5) {
    console.error(
      `DIVERGE ${label}(${args}): interpreter=${want} trust-cg=${gotIsland} llvm-twin=${gotTwin}`,
    );
  }
  bad++;
};

/** One expectation, checked against BOTH compilers. */
const check3 = (label, fnName, args, want) => {
  const fi = island[fnName];
  const ft = twin[fnName];
  if (typeof fi !== "function") fail(`the trust-cg module exports no ${fnName}`);
  if (typeof ft !== "function") fail(`the twin exports no ${fnName}`);
  const gi = fi(...args) >>> 0;
  const gt = ft(...args) >>> 0;
  checks++;
  if (gi !== want || gt !== want) report(label, args.join(","), want, gi, gt);
};

if (Array.isArray(exp.inputs) && Array.isArray(exp.expected)) {
  // ── canary island ──
  if (exp.inputs.length !== exp.expected.length) {
    fail(`manifest is torn: ${exp.inputs.length} inputs vs ${exp.expected.length} expectations`);
  }
  if (exp.inputs.length === 0) fail("manifest is EMPTY (vacuous run)");
  for (let k = 0; k < exp.inputs.length; k++) {
    const [a, b] = exp.inputs[k];
    check3("canary", "canary", [a | 0, b | 0], exp.expected[k] >>> 0);
  }
} else if (Array.isArray(exp.vt_inputs) && Array.isArray(exp.width_runs)) {
  // ── vt islands ──
  if (exp.vt_inputs.length !== exp.vt_expected.length) {
    fail(`manifest is torn: ${exp.vt_inputs.length} vt inputs vs ${exp.vt_expected.length} expectations`);
  }
  if (exp.vt_inputs.length === 0 || exp.width_runs.length === 0) {
    fail("manifest is EMPTY (vacuous run)");
  }
  for (let k = 0; k < exp.vt_inputs.length; k++) {
    const [s, b] = exp.vt_inputs[k];
    const want = exp.vt_expected[k] >>> 0;
    check3("vt_step", "vt_step", [s | 0, b | 0], want);
    // P3: the same spec spelled as an indexed load out of a data segment,
    // shipped in the SAME module as the compare tree. A defect would have to
    // occur identically in generated comparisons and in a memory lookup to
    // survive — and the twin, a third algorithm, has to agree as well.
    if (typeof island.vt_step_tbl === "function") {
      check3("vt_step_tbl", "vt_step_tbl", [s | 0, b | 0], want);
    }
  }
  for (let k = 0; k < exp.width_samples.length; k++) {
    check3("wcwidth", "wcwidth", [exp.width_samples[k] | 0], exp.width_expected[k] >>> 0);
  }
  // exhaustive over the whole codepoint domain plus the beyond-range band,
  // expanding the shipped runs as the reference
  let ri = 0;
  for (let cp = 0; cp <= 0x110100; cp++) {
    let want;
    if (cp > 0x10ffff) {
      want = 1;
    } else {
      while (exp.width_runs[ri][1] < cp) ri++;
      want = exp.width_runs[ri][2] >>> 0;
      if (want > 2) fail(`shipped run answers width ${want} at ${cp} — outside the 0..=2 contract`);
    }
    check3("wcwidth", "wcwidth", [cp | 0], want);
  }
} else if (Array.isArray(exp.windows) && Array.isArray(exp.import)) {
  // ── P2 memhash island: both modules read ONE imported memory ──
  if (exp.windows.length !== exp.expected.length) {
    fail(`manifest is torn: ${exp.windows.length} windows vs ${exp.expected.length} expectations`);
  }
  if (exp.windows.length === 0) fail("manifest is EMPTY (vacuous run)");
  thirdSpelling = "reference walk (Rust-baked, JS-rechecked)";
  const dv = new DataView(sharedMemory.buffer);
  // the JS reference spelling of the same spec, over the same memory
  const ref = (ptr, words) => {
    let h = 0x811c9dc5 >>> 0;
    for (let i = 0; i < words; i++) {
      h = (h ^ dv.getUint32(ptr + i * 4, true)) >>> 0;
      h = Math.imul(h, 0x01000193) >>> 0;
    }
    return h >>> 0;
  };
  for (let k = 0; k < exp.windows.length; k++) {
    const [ptr, words] = exp.windows[k];
    const want = exp.expected[k] >>> 0;
    if (ref(ptr, words) !== want) {
      fail(`the JS reference disagrees with the baked expectation at [${ptr},${words}] — the spellings have drifted`);
    }
    check3("mem_hash", "mem_hash", [ptr | 0, words | 0], want);
  }
} else {
  fail("unrecognized manifest: expected canary (inputs/expected), vt (vt_inputs/width_runs) or memhash (windows/import) keys");
}

rmSync(twinBuild.dir, { recursive: true, force: true });

if (bad > 0) {
  console.error(`${bad} of ${checks} island differential checks DIVERGED`);
  process.exit(1);
}
console.log(
  `island differential checks agree: ${checks} (trust-cg == rustc/LLVM twin == ${thirdSpelling})` +
    (sharedMemory ? " — both modules reading ONE imported memory" : ""),
);
