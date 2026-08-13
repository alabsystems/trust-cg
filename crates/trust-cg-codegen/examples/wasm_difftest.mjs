// Differential validator: runs the compiled wasm against the trust-ir
// interpreter's expectations (emitted by wasm_difftest.rs).
//   node wasm_difftest.mjs /tmp/difftest.wasm /tmp/difftest.json
// Exits nonzero on any divergence (a miscompile).
import { readFileSync } from "node:fs";

const [wasmPath, jsonPath] = process.argv.slice(2);
const bytes = readFileSync(wasmPath);
const manifest = JSON.parse(readFileSync(jsonPath, "utf8"));
const { instance } = await WebAssembly.instantiate(bytes);

let total = 0, fails = 0;
for (const c of manifest.cases) {
  const fn = instance.exports[c.name];
  if (typeof fn !== "function") {
    console.log(`MISSING export ${c.name}`);
    fails++;
    continue;
  }
  for (let i = 0; i < c.inputs.length; i++) {
    const got = fn(...c.inputs[i]) >>> 0;        // i32 result, as unsigned
    const want = c.expected[i] >>> 0;
    total++;
    if (got !== want) {
      fails++;
      if (fails <= 10) {
        console.log(`DIVERGE ${c.name}(${c.inputs[i].join(",")}): wasm=${got} interp=${want}`);
      }
    }
  }
}
console.log(`${total - fails}/${total} differential checks agree (interpreter == wasm)`);
if (fails) {
  console.log(`FAIL: ${fails} divergence(s)`);
  process.exit(1);
}
