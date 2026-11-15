// Replay one call sequence on two wasm32 modules built from `hook.rs` and
// compare each result (a trap is a result) and the handler's observations.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Usage: node drive.mjs <oracle.wasm> <candidate.wasm>
// Prints one line per call and `disagreements=K handler_runs=N` (the oracle's
// handler invocations); exits non-zero on any disagreement.

import fs from 'node:fs';

const [oraclePath, candidatePath] = process.argv.slice(2);

async function run(path) {
  const { instance } = await WebAssembly.instantiate(fs.readFileSync(path), {});
  const ex = instance.exports;
  const call = (name, ...args) => {
    try {
      return ex[name](...args) >>> 0;
    } catch (e) {
      if (!(e instanceof WebAssembly.RuntimeError)) throw e;
      return 'trap';
    }
  };
  const sequence = [
    ['idx', 2], ['idx', 9], ['sidx', 3, 2], ['sidx', 3, 5], ['sidx', 0, 0],
    ['sum_upto', 10], ['sum_upto', 30], ['idx', 4], ['idx', 0xffffffff],
  ];
  return sequence.map(([name, ...args]) =>
    `${name}(${args}) = ${call(name, ...args)} | line=${call('last_line')} ` +
    `col=${call('last_col')} msg=${call('last_msg')} hits=${call('hits')} ` +
    `hash=${call('msg_hash')} len=${call('msg_len')}`);
}

const oracle = await run(oraclePath);
const candidate = await run(candidatePath);
let disagreements = 0;
for (let i = 0; i < oracle.length; i++) {
  if (oracle[i] !== candidate[i]) {
    disagreements++;
    console.log(`DIFF oracle:    ${oracle[i]}\n     candidate: ${candidate[i]}`);
  } else {
    console.log(`same ${oracle[i]}`);
  }
}
const runs = Number(/hits=(\d+)/.exec(oracle[oracle.length - 1])[1]);
console.log(`disagreements=${disagreements} handler_runs=${runs}`);
process.exit(disagreements ? 1 : 0);
