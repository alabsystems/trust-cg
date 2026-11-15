// Run every export of two wasm32 modules over one input grid and compare.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Usage: node compare.mjs [--signatures] <oracle.wasm> <candidate.wasm>
// Every exported function's signature is read from the ORACLE module's binary
// (type, import, function and export sections), so a corpus needs no table,
// and the candidate's export of the same name must have the same wasm
// signature. `--signatures` compares only the signatures (exports whose
// by-memory parameters cannot be driven with scalars), printing
// `exports=N signature_mismatches=K` and exiting non-zero on any mismatch.
// Exports take i32/i64/f32/f64 scalars; one or two parameters are driven over
// the full cross product of the grid below, three or more over 600 sampled
// tuples. A trap is a result: both sides must trap together. Stateful exports
// see the same call sequence. Signed-zero results that differ only in sign are
// SOFT (Rust's `f32/f64::max/min` lower to `maximum_number_nsz`/
// `minimum_number_nsz`, which may return either zero) and do not fail.
// Prints `exports=N checks=M disagreements=K` and exits non-zero on any
// disagreement, on an export the candidate lacks, or when no export ran.

import fs from 'node:fs';

const signaturesOnly = process.argv[2] === '--signatures';
const [oraclePath, candidatePath] = process.argv.slice(signaturesOnly ? 3 : 2);

function uleb(bytes, at) {
  let value = 0;
  let shift = 0;
  for (;;) {
    const byte = bytes[at.i++];
    value += (byte & 0x7f) * 2 ** shift;
    if ((byte & 0x80) === 0) return value;
    shift += 7;
  }
}

function signatures(buffer) {
  const b = new Uint8Array(buffer);
  const at = { i: 8 };
  const types = [];
  const funcTypes = [];
  const exports = [];
  while (at.i < b.length) {
    const id = b[at.i++];
    const size = uleb(b, at);
    const end = at.i + size;
    if (id === 1) {
      for (let n = uleb(b, at); n > 0; n--) {
        at.i++; // 0x60
        const params = [];
        for (let k = uleb(b, at); k > 0; k--) params.push(b[at.i++]);
        const results = [];
        for (let k = uleb(b, at); k > 0; k--) results.push(b[at.i++]);
        types.push({ params, results });
      }
    } else if (id === 2) {
      for (let n = uleb(b, at); n > 0; n--) {
        at.i += uleb(b, at); // module name
        at.i += uleb(b, at); // field name
        const kind = b[at.i++];
        if (kind === 0) funcTypes.push(uleb(b, at));
        else if (kind === 1) { at.i++; if (uleb(b, at) & 1) uleb(b, at); uleb(b, at); }
        else if (kind === 2) { if (uleb(b, at) & 1) uleb(b, at); uleb(b, at); }
        else if (kind === 3) at.i += 2;
      }
    } else if (id === 3) {
      for (let n = uleb(b, at); n > 0; n--) funcTypes.push(uleb(b, at));
    } else if (id === 7) {
      for (let n = uleb(b, at); n > 0; n--) {
        const len = uleb(b, at);
        const name = Buffer.from(b.slice(at.i, at.i + len)).toString();
        at.i += len;
        const kind = b[at.i++];
        const index = uleb(b, at);
        if (kind === 0) exports.push({ name, index });
      }
    }
    at.i = end;
  }
  const out = {};
  for (const e of exports) out[e.name] = types[funcTypes[e.index]];
  return out;
}

const KIND = { 0x7f: 'i32', 0x7e: 'i64', 0x7d: 'f32', 0x7c: 'f64' };
const GRID = {
  i32: [0, 1, -1, 2, 3, 5, 7, -7, 8, 15, 16, 31, 32, 33, 63, 64, 65, 100, 127, 128, 255, 256, -128,
    999, 1000, 0x7fff, 0x8000, 0xffff, 12345, -99, 48, 57, 0xe9, 0xd800, 0x10ffff, 0x40000000,
    0x7fffffff, -0x80000000],
  i64: [0n, 1n, -1n, 2n, 3n, 7n, 12n, 27n, 63n, 64n, 97n, 255n, 1000n, 0xffffffffn, 0x100000000n,
    -0x100000000n, 123456789012345n, 1n << 62n, (1n << 63n) - 1n, -(1n << 63n), -12345n],
  f32: [0, -0, 1, -1, 0.5, 2.5, -2.5, 3.75, 1e30, -1e30, Infinity, -Infinity, NaN, 3e9, 1.5e-40,
    16777217, 0.1],
  f64: [0, -0, 1, -1, 0.5, 2.5, -2.5, 3.75, 1e300, -1e300, Infinity, -Infinity, NaN, 3e9, -3e9,
    2147483647.9, -2147483648.5, 9007199254740993, 0.1, 5e-324],
};

const sigs = signatures(fs.readFileSync(oraclePath));
const candidateSigs = signatures(fs.readFileSync(candidatePath));
const kindList = (vs) => vs.map((v) => KIND[v] ?? v).join(',');
const sigText = (s) => (s ? `(${kindList(s.params)})->(${kindList(s.results)})` : 'missing');
let signatureMismatches = 0;
for (const [name, sig] of Object.entries(sigs)) {
  if (sigText(sig) === sigText(candidateSigs[name])) continue;
  // A missing export is counted once, as `MISSING`, when the exports run.
  if (!signaturesOnly && !candidateSigs[name]) continue;
  signatureMismatches++;
  const got = sigText(candidateSigs[name]);
  console.log(`SIGNATURE ${name}: oracle=${sigText(sig)} candidate=${got}`);
}
if (signaturesOnly) {
  const n = Object.keys(sigs).length;
  console.log(`exports=${n} signature_mismatches=${signatureMismatches}`);
  process.exit(signatureMismatches || !n ? 1 : 0);
}

const load = async (p) => (await WebAssembly.instantiate(fs.readFileSync(p), {})).instance.exports;
const oracle = await load(oraclePath);
const candidate = await load(candidatePath);

const show = (r) => {
  if (Array.isArray(r)) return `[${r.map(show).join(',')}]`;
  if (typeof r === 'number') return Number.isNaN(r) ? 'NaN' : Object.is(r, -0) ? '-0' : String(r);
  return String(r);
};
const call = (f, args) => {
  try {
    return show(f(...args));
  } catch (e) {
    if (e instanceof WebAssembly.RuntimeError) return 'trap';
    throw e;
  }
};

let seed = 0x12345678;
const pick = (n) => {
  seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0;
  return seed % n;
};

let exports = 0;
let checks = 0;
let disagreements = signatureMismatches;
for (const [name, sig] of Object.entries(sigs)) {
  if (typeof oracle[name] !== 'function') continue;
  if (typeof candidate[name] !== 'function') {
    console.log(`MISSING ${name}`);
    disagreements++;
    continue;
  }
  const kinds = sig.params.map((v) => KIND[v]);
  if (kinds.some((k) => !k)) throw new Error(`${name}: non-scalar parameter`);
  const doms = kinds.map((k) => GRID[k]);
  let argsets;
  if (doms.length === 0) argsets = [[], [], []];
  else if (doms.length === 1) argsets = doms[0].map((x) => [x]);
  else if (doms.length === 2) argsets = doms[0].flatMap((x) => doms[1].map((y) => [x, y]));
  else argsets = Array.from({ length: 600 }, () => doms.map((d) => d[pick(d.length)]));
  exports++;
  for (const args of argsets) {
    const want = call(oracle[name], args);
    const got = call(candidate[name], args);
    checks++;
    if (want === got) continue;
    const zero = (s) => s === '0' || s === '-0';
    if (zero(want) && zero(got)) continue;
    disagreements++;
    if (disagreements <= 20) console.log(`DIFF ${name}(${args.map(show).join(', ')}): oracle=${want} candidate=${got}`);
  }
}
console.log(`exports=${exports} checks=${checks} disagreements=${disagreements}`);
process.exit(disagreements || !exports ? 1 : 0);
