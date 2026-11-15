// benchmarks/wasm-vs-llvm/wasmtool.mjs — the wasm side of the wasm-vs-llvm harness.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
//   node wasmtool.mjs measure --work DIR --lane NAME=PATH ... [--soft-zero EXPORT ...] [--budget-floor-ms MS] --out FILE
//   node [engine flags] wasmtool.mjs time --work DIR --lane NAME ... --n N --target-ms MS --out FILE
//   node wasmtool.mjs selftest
//
// `measure` takes the oracle lane first (rustc+LLVM, B1) and every other lane
// after it. For each lane it decodes the module (static metrics), drives every
// exported function over the deterministic input grid on a fresh instance and
// compares the result of every call with the oracle's, traps included
// (differential). Every module runs in its own worker thread under a time
// budget: a lane whose module fails to compile or instantiate, or that does
// not answer within max(CANDIDATE_FLOOR_MS, CANDIDATE_FACTOR x the oracle's
// time), records a `run_failure` (the driver makes that a MISMATCH); the
// oracle failing is recorded as `oracle_failure`. A +0/-0 difference is a
// disagreement unless the export is listed with --soft-zero (the corpus
// manifest names those exports and why); a soft case is counted and recorded.
// NaN payloads are not observable at the JS boundary, so NaN equals NaN.
//
// The calls on which the oracle does not trap, in grid order, form the
// WORKLOAD. Each lane gets a loop module: the lane's own module plus one
// appended function, `__wvl_loop(reps)`, that runs the workload `reps` times
// inside wasm and folds every result into an i64 accumulator (every NaN folded
// to one pattern; -0 folded to +0 only for --soft-zero exports). The loop
// module is written to DIR for `time`. A copy of the loop module with every
// ORIGINAL function instrumented (the appended loop is not) counts, over one
// pass of the workload, executed instructions, memory operations, calls and
// loop-header entries, and measures the stack high-water.
//
// Counting is exact for a workload that does not trap: each straight-line
// segment (split after every structured-control, branch, return and
// `unreachable` instruction, and after `else`/`end`) adds its static counts at
// its start. `end` and `else` are structural markers and are not counted, in
// the static count as in the dynamic one.
//
// The stack high-water is `__stack_pointer`'s initial value minus the lowest
// stack address in use: the lower of the smallest value any `global.set`
// wrote to `__stack_pointer` and the smallest effective address any load,
// store or non-empty bulk-memory operation touched below that initial value.
// Code may use memory below the stack pointer without moving it (LLVM's leaf
// functions do), so the writes alone undercount. The stack region is
// everything below the initial stack pointer only in a stack-first layout
// (rustc links wasm32 with --stack-first): one memory, and every active data
// segment at or above the initial stack pointer. A module that does not show
// that layout gets no stack reading.
//
// `time` loads the loop modules written by `measure`, runs `__wvl_loop` once
// as warm-up, calibrates `reps` on the oracle lane until one sample takes at
// least --target-ms, then takes N interleaved samples per lane (the lane order
// rotates each round). The engine mode is whatever flags node was started
// with; the driver names it. `first_call_ms` is the first single pass on a
// fresh instance (lazy compilation and the first tier included), one sample,
// context only.
//
// Everything fails closed: an opcode outside the decoded vocabulary, a module
// with relocations, a stack pointer that cannot be identified by name, a
// layout that is not stack-first, or an instrumented run whose accumulator
// differs from the plain loop's leaves that metric null with a reason, never
// a guess.

import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { Worker, isMainThread, parentPort, workerData } from 'node:worker_threads';

// ---------- LEB128 ----------
function readU(b, p) {
  let r = 0n, s = 0n, x;
  do { x = b[p.i++]; if (x === undefined) throw new Error('truncated LEB'); r |= BigInt(x & 0x7f) << s; s += 7n; } while (x & 0x80);
  return r;
}
const readUN = (b, p) => Number(readU(b, p));
function readS(b, p) {
  let r = 0n, s = 0n, x;
  do { x = b[p.i++]; if (x === undefined) throw new Error('truncated LEB'); r |= BigInt(x & 0x7f) << s; s += 7n; } while (x & 0x80);
  if (x & 0x40) r -= 1n << s;
  return r;
}
function encU(v) {
  let n = BigInt(v); const out = [];
  do { let byte = Number(n & 0x7fn); n >>= 7n; if (n !== 0n) byte |= 0x80; out.push(byte); } while (n !== 0n);
  return out;
}
function encS(v) {
  let n = BigInt(v); const out = [];
  for (;;) {
    const byte = Number(n & 0x7fn); n >>= 7n;
    const done = (n === 0n && !(byte & 0x40)) || (n === -1n && (byte & 0x40));
    out.push(done ? byte : byte | 0x80);
    if (done) return out;
  }
}
const encName = (s) => { const u = Buffer.from(s, 'utf8'); return [...encU(u.length), ...u]; };
const section = (id, payload) => [id, ...encU(payload.length), ...payload];

// ---------- module parsing ----------
const VALTYPES = new Set([0x7f, 0x7e, 0x7d, 0x7c, 0x7b, 0x70, 0x6f]);
const VT_NAME = { 0x7f: 'i32', 0x7e: 'i64', 0x7d: 'f32', 0x7c: 'f64' };
// Canonical order of the known sections; data count (12) sits between 9 and 10.
const SECTION_RANK = { 1: 1, 2: 2, 3: 3, 4: 4, 5: 5, 6: 6, 7: 7, 8: 8, 9: 9, 12: 10, 10: 11, 11: 12 };

export function parseModule(bytes) {
  const b = new Uint8Array(bytes);
  if (b.length < 8 || b[0] !== 0 || b[1] !== 0x61 || b[2] !== 0x73 || b[3] !== 0x6d || b[4] !== 1) {
    throw new Error('not a wasm v1 module');
  }
  const m = { bytes: b, sections: [], types: [], importedFuncTypes: [], importedGlobals: 0,
    funcTypes: [], globals: [], exports: [], bodies: [], globalNames: {}, customNames: [],
    memories: 0, dataSegments: [] };
  const p = { i: 8 };
  while (p.i < b.length) {
    const id = b[p.i++]; const size = readUN(b, p); const start = p.i; const end = start + size;
    if (end > b.length) throw new Error(`section ${id} overruns the file`);
    const sec = { id, start, end, name: null };
    const q = { i: start };
    if (id === 0) {
      const nl = readUN(b, q); sec.name = Buffer.from(b.slice(q.i, q.i + nl)).toString(); q.i += nl;
      m.customNames.push(sec.name);
      if (sec.name === 'name') parseNames(b, q, end, m);
    } else if (id === 1) {
      for (let n = readUN(b, q); n > 0; n--) {
        if (b[q.i++] !== 0x60) throw new Error('non-function type');
        const ps = []; for (let k = readUN(b, q); k > 0; k--) ps.push(b[q.i++]);
        const rs = []; for (let k = readUN(b, q); k > 0; k--) rs.push(b[q.i++]);
        m.types.push({ ps, rs });
      }
    } else if (id === 2) {
      for (let n = readUN(b, q); n > 0; n--) {
        q.i += readUN(b, q); q.i += readUN(b, q);
        const kind = b[q.i++];
        if (kind === 0) m.importedFuncTypes.push(readUN(b, q));
        else if (kind === 1) { q.i++; const fl = readUN(b, q); readUN(b, q); if (fl & 1) readUN(b, q); }
        else if (kind === 2) { const fl = readUN(b, q); readUN(b, q); if (fl & 1) readUN(b, q); m.memories++; }
        else if (kind === 3) { q.i += 2; m.importedGlobals++; }
        else throw new Error(`import kind ${kind}`);
      }
    } else if (id === 3) {
      for (let n = readUN(b, q); n > 0; n--) m.funcTypes.push(readUN(b, q));
    } else if (id === 5) {
      m.memories += readUN(b, q);
    } else if (id === 6) {
      for (let n = readUN(b, q); n > 0; n--) {
        const type = b[q.i++]; const mut = b[q.i++]; const initStart = q.i;
        let init = null;
        if (b[q.i] === 0x41) { q.i++; init = Number(readS(b, q)); if (b[q.i] !== 0x0b) init = null; }
        // Skip the rest of the constant expression up to its `end`.
        q.i = initStart; skipConstExpr(b, q);
        m.globals.push({ type, mut, init });
      }
    } else if (id === 7) {
      for (let n = readUN(b, q); n > 0; n--) {
        const nl = readUN(b, q); const name = Buffer.from(b.slice(q.i, q.i + nl)).toString(); q.i += nl;
        const kind = b[q.i++]; const idx = readUN(b, q);
        m.exports.push({ name, kind, idx });
      }
    } else if (id === 10) {
      for (let n = readUN(b, q); n > 0; n--) {
        const sz = readUN(b, q); const bodyStart = q.i; const bodyEnd = bodyStart + sz;
        const r = { i: bodyStart }; let nlocals = 0n;
        for (let k = readUN(b, r); k > 0; k--) { nlocals += readU(b, r); r.i++; }
        m.bodies.push({ start: bodyStart, end: bodyEnd, codeStart: r.i, declaredLocals: Number(nlocals) });
        q.i = bodyEnd;
      }
    } else if (id === 11) {
      // Data segments: flags 0 (active, memory 0), 1 (passive), 2 (active, explicit memory).
      for (let n = readUN(b, q); n > 0; n--) {
        const flags = readUN(b, q); let offset = null;
        if (flags === 0 || flags === 2) {
          if (flags === 2) readUN(b, q);
          const exprStart = q.i;
          if (b[q.i] === 0x41) { q.i++; offset = Number(readS(b, q)) >>> 0; if (b[q.i] !== 0x0b) offset = null; }
          q.i = exprStart; skipConstExpr(b, q);
        } else if (flags !== 1) {
          throw new Error(`data segment flags ${flags}`);
        }
        const len = readUN(b, q); q.i += len;
        m.dataSegments.push({ active: flags !== 1, offset, len });
      }
    }
    m.sections.push(sec);
    p.i = end;
  }
  if (m.bodies.length !== m.funcTypes.length) throw new Error('function and code section counts differ');
  for (const n of m.customNames) {
    if (n === 'linking' || n.startsWith('reloc.')) throw new Error(`relocatable module (custom section ${n}); a linked module is required`);
  }
  return m;
}

function skipConstExpr(b, q) {
  for (;;) {
    const op = b[q.i++];
    if (op === 0x0b) return;
    if (op === 0x41 || op === 0x42) readS(b, q);
    else if (op === 0x43) q.i += 4;
    else if (op === 0x44) q.i += 8;
    else if (op === 0x23 || op === 0xd2) readU(b, q);
    else if (op === 0xd0) readS(b, q);
    else if (op === 0x6a || op === 0x6b || op === 0x6c || op === 0x7c || op === 0x7d || op === 0x7e) { /* extended const */ }
    else throw new Error(`constant expression opcode 0x${op.toString(16)}`);
  }
}

function parseNames(b, q, end, m) {
  while (q.i < end) {
    const sid = b[q.i++]; const ssz = readUN(b, q); const sEnd = q.i + ssz;
    if (sid === 7) {
      for (let n = readUN(b, q); n > 0; n--) {
        const idx = readUN(b, q); const nl = readUN(b, q);
        m.globalNames[idx] = Buffer.from(b.slice(q.i, q.i + nl)).toString(); q.i += nl;
      }
    }
    q.i = sEnd;
  }
}

// ---------- instruction decoding ----------
const LOAD_OPS = (op) => op >= 0x28 && op <= 0x35;
const STORE_OPS = (op) => op >= 0x36 && op <= 0x3e;
const CALL_OPS = new Set([0x10, 0x11, 0x12, 0x13]);
// A segment ends after each of these (structured control, branches, returns,
// unreachable, and the else/end markers).
const SEGMENT_END = new Set([0x00, 0x02, 0x03, 0x04, 0x05, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x12, 0x13]);
const MARKERS = new Set([0x05, 0x0b]);
const BULK_MEMORY_SUBOPS = new Set([8, 10, 11]);

function skipBlockType(b, p) {
  if (b[p.i] === 0x40 || VALTYPES.has(b[p.i])) p.i++;
  else readS(b, p);
}

// Decodes one instruction at p.i; returns {op, sub, start, end, idx, offset}
// (offset: a memory access's static offset).
export function readInstr(b, p) {
  const start = p.i; const op = b[p.i++]; let sub = null; let idx = null; let offset = null;
  if (op === undefined) throw new Error('truncated body');
  switch (true) {
    case op === 0x00 || op === 0x01 || op === 0x05 || op === 0x0b || op === 0x0f || op === 0x1a || op === 0x1b:
      break;
    case op === 0x02 || op === 0x03 || op === 0x04:
      skipBlockType(b, p); break;
    case op === 0x0c || op === 0x0d:
      readU(b, p); break;
    case op === 0x0e:
      for (let n = readUN(b, p) + 1; n > 0; n--) readU(b, p); break;
    case op === 0x10 || op === 0x12:
      idx = readUN(b, p); break;
    case op === 0x11 || op === 0x13:
      readU(b, p); readU(b, p); break;
    case op === 0x1c:
      for (let n = readUN(b, p); n > 0; n--) p.i++; break;
    case op >= 0x20 && op <= 0x26:
      idx = readUN(b, p); break;
    case op >= 0x28 && op <= 0x3e: {
      const align = readUN(b, p);
      if ((align & 0x40) && readUN(b, p) !== 0) throw new Error('memory access to a memory other than 0');
      offset = readUN(b, p); break;
    }
    case op === 0x3f || op === 0x40:
      readU(b, p); break;
    case op === 0x41 || op === 0x42:
      readS(b, p); break;
    case op === 0x43:
      p.i += 4; break;
    case op === 0x44:
      p.i += 8; break;
    case op >= 0x45 && op <= 0xc4:
      break;
    case op === 0xd0:
      readS(b, p); break;
    case op === 0xd1:
      break;
    case op === 0xd2:
      readU(b, p); break;
    case op === 0xfc: {
      sub = readUN(b, p);
      if (sub <= 7) break;
      if (sub === 8 || sub === 10 || sub === 12 || sub === 14) { readU(b, p); readU(b, p); break; }
      if (sub === 9 || sub === 11 || sub === 13 || sub === 15 || sub === 16 || sub === 17) { readU(b, p); break; }
      throw new Error(`unsupported opcode 0xfc ${sub}`);
    }
    default:
      throw new Error(`unsupported opcode 0x${op.toString(16)}`);
  }
  if (p.i > b.length) throw new Error('instruction overruns the body');
  return { op, sub, start, end: p.i, idx, offset };
}

function decodeBody(b, body) {
  const p = { i: body.codeStart }; const out = [];
  while (p.i < body.end) out.push(readInstr(b, p));
  if (p.i !== body.end || out.length === 0 || out[out.length - 1].op !== 0x0b) throw new Error('malformed function body');
  return out;
}

function classify(ins, spIndex) {
  const memop = LOAD_OPS(ins.op) || STORE_OPS(ins.op) || (ins.op === 0xfc && BULK_MEMORY_SUBOPS.has(ins.sub));
  return {
    insn: MARKERS.has(ins.op) ? 0 : 1,
    mem: memop ? 1 : 0,
    load: LOAD_OPS(ins.op) ? 1 : 0,
    store: STORE_OPS(ins.op) ? 1 : 0,
    bulk: ins.op === 0xfc && BULK_MEMORY_SUBOPS.has(ins.sub) ? 1 : 0,
    call: CALL_OPS.has(ins.op) ? 1 : 0,
    local: ins.op >= 0x20 && ins.op <= 0x22 ? 1 : 0,
    spWrite: ins.op === 0x24 && spIndex !== null && ins.idx === spIndex ? 1 : 0,
  };
}

export function stackPointerIndex(m) {
  const found = Object.entries(m.globalNames).filter(([, n]) => n === '__stack_pointer').map(([i]) => Number(i));
  if (found.length !== 1) return { index: null, init: null, reason: 'no unique __stack_pointer global name' };
  const index = found[0];
  if (index < m.importedGlobals) return { index, init: null, reason: '__stack_pointer is imported' };
  const g = m.globals[index - m.importedGlobals];
  if (!g || g.type !== 0x7f || g.mut !== 1 || g.init === null) return { index, init: null, reason: '__stack_pointer is not a mutable i32 with a constant initializer' };
  return { index, init: g.init >>> 0, reason: null };
}

// Why the region below __stack_pointer's initial value is not exactly the
// stack (null when it is): one memory, and every active data segment at or
// above the initial stack pointer (wasm-ld --stack-first).
export function stackLayoutProblem(m, sp) {
  if (sp.init === null) return sp.reason;
  if (m.memories !== 1) return `${m.memories} memories; the stack region is defined for exactly one`;
  for (const seg of m.dataSegments) {
    if (!seg.active) continue;
    if (seg.offset === null) return 'an active data segment with a non-constant offset';
    if (seg.offset < sp.init) return `an active data segment at ${seg.offset}, below __stack_pointer's initial ${sp.init}: not a stack-first layout`;
  }
  return null;
}

// ---------- static metrics ----------
export function staticMetrics(bytes) {
  const m = parseModule(bytes);
  const sp = stackPointerIndex(m);
  const code = m.sections.find((s) => s.id === 10);
  const t = { file_bytes: bytes.length, code_bytes: code ? code.end - code.start : 0,
    defined_functions: m.bodies.length, static_insns: 0, declared_locals: 0, static_loads: 0,
    static_stores: 0, static_bulk_memory: 0, static_memops: 0, static_local_ops: 0,
    static_calls: 0, sp_writes: null, framed_functions: null };
  let spWrites = 0, framed = 0;
  for (const body of m.bodies) {
    t.declared_locals += body.declaredLocals;
    let fnSp = 0;
    for (const ins of decodeBody(m.bytes, body)) {
      const c = classify(ins, sp.index);
      t.static_insns += c.insn; t.static_loads += c.load; t.static_stores += c.store;
      t.static_bulk_memory += c.bulk; t.static_memops += c.mem; t.static_local_ops += c.local;
      t.static_calls += c.call; fnSp += c.spWrite;
    }
    spWrites += fnSp; if (fnSp) framed++;
  }
  if (sp.index !== null) { t.sp_writes = spWrites; t.framed_functions = framed; }
  return { metrics: t, stack_pointer: sp };
}

// ---------- module rewriting ----------
// Rebuilds the module with sections replaced or inserted. `edits` maps a
// section id to a function (payloadBytes|null) -> new payload bytes.
function rebuild(m, edits) {
  const b = m.bytes; const chunks = [b.slice(0, 8)];
  // Chunks, not one array: a spread of a large body into push() overflows the call stack.
  const pending = new Map(Object.entries(edits).map(([k, v]) => [Number(k), v]));
  const flushBefore = (rank) => {
    for (const [id, fn] of [...pending].sort((x, y) => SECTION_RANK[x[0]] - SECTION_RANK[y[0]])) {
      if (SECTION_RANK[id] < rank) { chunks.push(Uint8Array.from(section(id, fn(null)))); pending.delete(id); }
    }
  };
  for (const sec of m.sections) {
    if (sec.id !== 0) flushBefore(SECTION_RANK[sec.id]);
    if (pending.has(sec.id)) {
      chunks.push(Uint8Array.from(section(sec.id, pending.get(sec.id)(b.slice(sec.start, sec.end))))); pending.delete(sec.id);
    } else {
      chunks.push(Uint8Array.from([sec.id, ...encU(sec.end - sec.start)]), b.slice(sec.start, sec.end));
    }
  }
  flushBefore(Infinity);
  return new Uint8Array(Buffer.concat(chunks));
}

// Appends entries to a vector section payload (count prefix + entries).
function appendVec(payload, entries) {
  if (!entries.length) return payload ? [...payload] : [...encU(0)];
  if (!payload) return [...encU(entries.length), ...entries.flat()];
  const p = { i: 0 }; const n = readUN(payload, p);
  return [...encU(n + entries.length), ...payload.slice(p.i), ...entries.flat()];
}

const CANON_F32_BITS = 0x7fc00000n;
const CANON_F64_BITS = 0x7ff8000000000000n;

function constBits(kind, value) {
  if (kind === 'i32') return [0x41, ...encS(BigInt.asIntN(32, BigInt(Math.trunc(Number(value)) | 0)))];
  if (kind === 'i64') return [0x42, ...encS(BigInt.asIntN(64, BigInt(value)))];
  if (kind === 'f32') { const f = new Float32Array([Number(value)]); return [0x41, ...encS(BigInt(new Int32Array(f.buffer)[0]))]; }
  if (kind === 'f64') { const f = new Float64Array([Number(value)]); return [0x42, ...encS(new BigInt64Array(f.buffer)[0])]; }
  throw new Error(`argument kind ${kind}`);
}

// Builds the loop module: the lane's module plus `__wvl_loop(reps: i32) -> i64`
// over CALLS ([{index, kinds, args, results, softZero}]), two opaque mutable
// zero globals that keep the engine from folding the constant arguments, and
// its exports. A float result folds into the accumulator by its bits, every
// NaN as one pattern, and -0 as +0 only for a softZero call.
export function loopModule(bytes, calls) {
  const m = parseModule(bytes);
  const typeIndex = m.types.length;
  const funcIndex = m.importedFuncTypes.length + m.funcTypes.length;
  const g0 = m.importedGlobals + m.globals.length; // $z32, $z64
  const body = [];
  body.push(0x02, 0x40, 0x03, 0x40, 0x20, 0, 0x45, 0x0d, 1);
  for (const c of calls) {
    c.kinds.forEach((k, j) => {
      const v = c.args[j];
      if (k === 'i32') body.push(...constBits('i32', v), 0x23, ...encU(g0), 0x73);
      else if (k === 'i64') body.push(...constBits('i64', v), 0x23, ...encU(g0 + 1), 0x85);
      else if (k === 'f32') body.push(...constBits('f32', v), 0x23, ...encU(g0), 0x73, 0xbe);
      else if (k === 'f64') body.push(...constBits('f64', v), 0x23, ...encU(g0 + 1), 0x85, 0xbf);
    });
    body.push(0x10, ...encU(c.index));
    for (let r = c.results.length - 1; r >= 0; r--) {
      const k = c.results[r];
      if (k === 'i32') body.push(0xad);
      // x + 0.0 folds -0 to +0 (and nothing else); the select folds every NaN.
      else if (k === 'f32') body.push(0x21, 2, 0x20, 2, ...(c.softZero ? [0x43, 0, 0, 0, 0, 0x92] : []), 0xbc, 0xad, 0x42, ...encS(CANON_F32_BITS), 0x20, 2, 0x20, 2, 0x5b, 0x1b);
      else if (k === 'f64') body.push(0x21, 3, 0x20, 3, ...(c.softZero ? [0x44, 0, 0, 0, 0, 0, 0, 0, 0, 0xa0] : []), 0xbd, 0x42, ...encS(CANON_F64_BITS), 0x20, 3, 0x20, 3, 0x61, 0x1b);
      body.push(0x20, 1, 0x42, 5, 0x89, 0x85, 0x21, 1);
    }
  }
  body.push(0x20, 0, 0x41, 1, 0x6b, 0x21, 0, 0x0c, 0, 0x0b, 0x0b, 0x20, 1, 0x0b);
  const locals = [3, 1, 0x7e, 1, 0x7d, 1, 0x7c];
  const fn = [...encU(locals.length + body.length), ...locals, ...body];
  const bytesOut = rebuild(m, {
    1: (p) => appendVec(p, [[0x60, 1, 0x7f, 1, 0x7e]]),
    3: (p) => appendVec(p, [encU(typeIndex)]),
    6: (p) => appendVec(p, [[0x7f, 1, 0x41, 0, 0x0b], [0x7e, 1, 0x42, 0, 0x0b]]),
    7: (p) => appendVec(p, [[...encName('__wvl_loop'), 0, ...encU(funcIndex)]]),
    10: (p) => appendVec(p, [fn]),
  });
  return { bytes: bytesOut, loopIndex: funcIndex };
}

// The value type a store instruction consumes.
const STORE_VALUE = { 0x36: 'i32', 0x37: 'i64', 0x38: 'f32', 0x39: 'f64', 0x3a: 'i32', 0x3b: 'i32', 0x3c: 'i64', 0x3d: 'i64', 0x3e: 'i64' };

// Instruments every function of a loop module except the appended loop:
// segment counters (insn, mem, call, loop heads), the smallest value written
// to __stack_pointer (spmin) and, in a stack-first layout, the smallest
// effective address touched below its initial value (touchmin, i64). The
// hooks are inserted around the original instructions and counted nowhere.
export function instrument(bytes, skipFunc) {
  const m = parseModule(bytes);
  const sp = stackPointerIndex(m);
  const layout = stackLayoutProblem(m, sp);
  const track = layout === null;
  const gBase = m.importedGlobals + m.globals.length;
  const G = { insn: gBase, mem: gBase + 1, call: gBase + 2, loop: gBase + 3, spmin: gBase + 4, touchmin: gBase + 5 };
  const bump = (g, k) => (k ? [0x23, ...encU(g), 0x42, ...encS(k), 0x7c, 0x24, ...encU(g)] : []);
  const spHook = sp.init === null ? [] : [0x23, ...encU(sp.index), 0x23, ...encU(G.spmin), 0x49, 0x04, 0x40,
    0x23, ...encU(sp.index), 0x24, ...encU(G.spmin), 0x0b];
  const newBodies = m.bodies.map((body, i) => {
    const fIndex = m.importedFuncTypes.length + i;
    const raw = [...m.bytes.slice(body.start, body.end)];
    if (fIndex === skipFunc) return [...encU(raw.length), ...raw];
    const instrs = decodeBody(m.bytes, body);
    // Scratch locals appended after the declared ones: three i32 ($a $b $c),
    // two i64 ($e $v64), one f32, one f64.
    const groups = []; const q = { i: body.start };
    for (let n = readUN(m.bytes, q); n > 0; n--) { const count = readUN(m.bytes, q); groups.push([count, m.bytes[q.i++]]); }
    const base = m.types[m.funcTypes[i]].ps.length + body.declaredLocals;
    const L = { a: base, b: base + 1, c: base + 2, e: base + 3, i64: base + 4, f32: base + 5, f64: base + 6 };
    const extra = track ? [[3, 0x7f], [2, 0x7e], [1, 0x7d], [1, 0x7c]] : [];
    const all = [...groups, ...extra];
    const out = [...encU(all.length), ...all.flatMap(([count, type]) => [...encU(count), type])];
    // touch(get, off): fold the effective address (get + off) into touchmin.
    const touch = (get, off) => [...get, 0xad, ...(off ? [0x42, ...encS(BigInt(off)), 0x7c] : []),
      0x22, ...encU(L.e), 0x23, ...encU(G.touchmin), 0x54, 0x04, 0x40,
      0x20, ...encU(L.e), 0x24, ...encU(G.touchmin), 0x0b];
    const get = (l) => [0x20, ...encU(l)];
    const set = (l) => [0x21, ...encU(l)];
    const before = (ins) => {
      if (LOAD_OPS(ins.op)) return [...set(L.a), ...touch(get(L.a), ins.offset), ...get(L.a)];
      if (STORE_OPS(ins.op)) {
        const v = STORE_VALUE[ins.op] === 'i32' ? L.b : L[STORE_VALUE[ins.op]];
        return [...set(v), ...set(L.a), ...touch(get(L.a), ins.offset), ...get(L.a), ...get(v)];
      }
      if (ins.op === 0xfc && BULK_MEMORY_SUBOPS.has(ins.sub)) {
        // memory.init/copy/fill take (dst, src-or-value, n); copy also reads src.
        return [...set(L.c), ...set(L.b), ...set(L.a), ...get(L.c), 0x04, 0x40, ...touch(get(L.a), 0),
          ...(ins.sub === 10 ? touch(get(L.b), 0) : []), 0x0b, ...get(L.a), ...get(L.b), ...get(L.c)];
      }
      return [];
    };
    let k = 0; let afterLoop = false;
    while (k < instrs.length) {
      let j = k; const c = { insn: 0, mem: 0, call: 0 };
      for (; j < instrs.length; j++) {
        const cl = classify(instrs[j], sp.index);
        c.insn += cl.insn; c.mem += cl.mem; c.call += cl.call;
        if (SEGMENT_END.has(instrs[j].op)) { j++; break; }
      }
      out.push(...bump(G.insn, c.insn), ...bump(G.mem, c.mem), ...bump(G.call, c.call), ...bump(G.loop, afterLoop ? 1 : 0));
      for (let t = k; t < j; t++) {
        const ins = instrs[t];
        if (track) out.push(...before(ins));
        out.push(...m.bytes.slice(ins.start, ins.end));
        if (ins.op === 0x24 && sp.index !== null && ins.idx === sp.index) out.push(...spHook);
      }
      afterLoop = instrs[j - 1].op === 0x03;
      k = j;
    }
    return [...encU(out.length), ...out];
  });
  const code = [...encU(newBodies.length), ...newBodies.flat()];
  const spInit = sp.init === null ? 0 : sp.init;
  const globals = [[0x7e, 1, 0x42, 0, 0x0b], [0x7e, 1, 0x42, 0, 0x0b], [0x7e, 1, 0x42, 0, 0x0b], [0x7e, 1, 0x42, 0, 0x0b],
    [0x7f, 1, 0x41, ...encS(BigInt.asIntN(32, BigInt(spInit))), 0x0b], [0x7e, 1, 0x42, ...encS(BigInt(spInit)), 0x0b]];
  const exports = Object.entries(G).map(([name, idx]) => [...encName(`__wvl_c_${name}`), 3, ...encU(idx)]);
  const out = rebuild(m, {
    6: (p) => appendVec(p, globals),
    7: (p) => appendVec(p, exports),
    10: () => code,
  });
  return { bytes: out, stackPointer: sp, stackLayout: layout };
}

// ---------- the deterministic grid (the scalar-export differential's domains) ----------
const I32 = [0, 1, -1, 2, 3, 5, 7, -7, 8, 15, 16, 31, 32, 33, 63, 64, 100, 127, 128, 255, 256, -128, 999, 1000, 0x7fff, 0x8000, 0xffff, 12345, -99, 65, 48, 57, 0xe9, 0xd800, 0x10ffff, 0x7fffffff, -0x80000000, 0x40000000];
const I64 = [0n, 1n, -1n, 2n, 3n, 7n, 12n, 27n, 63n, 64n, 97n, 255n, 1000n, 0xffffffffn, 0x100000000n, -0x100000000n, 123456789012345n, (1n << 62n), (1n << 63n) - 1n, -(1n << 63n), -12345n];
const F32 = [0, -0, 1, -1, 0.5, 2.5, -2.5, 3.75, 1e30, -1e30, Infinity, -Infinity, NaN, 3e9, 1.5e-40, 16777217, 0.1];
const F64 = [0, -0, 1, -1, 0.5, 2.5, -2.5, 3.75, 1e300, -1e300, Infinity, -Infinity, NaN, 3e9, -3e9, 2147483647.9, -2147483648.5, 9007199254740993, 0.1, 5e-324];
const DOM = { i32: I32, i64: I64, f32: F32, f64: F64 };
const GRID_SOURCE = JSON.stringify({ I32, I64: I64.map(String), F32: F32.map(String), F64: F64.map(String), sampled: 600, lcg: [0x12345678, 1664525, 1013904223] });

// Identifies the grid (values, sampling and LCG) for provenance.
export const gridSha256 = () => crypto.createHash('sha256').update(GRID_SOURCE).digest('hex');

// The call plan: every exported function, in the oracle's export order, over
// the grid (1-2 parameters: the full cross product; 3+: 600 tuples from a
// fixed LCG; none: three calls, for stateful exports).
export function callPlan(m) {
  const funcType = (idx) => (idx < m.importedFuncTypes.length ? m.importedFuncTypes[idx] : m.funcTypes[idx - m.importedFuncTypes.length]);
  let lcg = 0x12345678;
  const rnd = (n) => { lcg = (Math.imul(lcg, 1664525) + 1013904223) >>> 0; return lcg % n; };
  const plan = []; const skipped = [];
  for (const e of m.exports) {
    if (e.kind !== 0) continue;
    const t = m.types[funcType(e.idx)];
    const kinds = t.ps.map((v) => VT_NAME[v]); const results = t.rs.map((v) => VT_NAME[v]);
    if (kinds.some((k) => !k) || results.some((k) => !k)) { skipped.push(e.name); continue; }
    const doms = kinds.map((k) => DOM[k]);
    let argsets;
    if (doms.length === 0) argsets = [[], [], []];
    else if (doms.length === 1) argsets = doms[0].map((x) => [x]);
    else if (doms.length === 2) argsets = doms[0].flatMap((x) => doms[1].map((y) => [x, y]));
    else { argsets = []; for (let k = 0; k < 600; k++) argsets.push(doms.map((d) => d[rnd(d.length)])); }
    plan.push({ name: e.name, index: e.idx, kinds, results, argsets });
  }
  return { plan, skipped };
}

const show = (r) => {
  if (Array.isArray(r)) return '[' + r.map(show).join(',') + ']';
  if (typeof r === 'number') return Number.isNaN(r) ? 'NaN' : Object.is(r, -0) ? '-0' : String(r);
  return String(r);
};
const callOne = (f, args) => {
  try { return show(f(...args)); } catch (e) {
    return e instanceof WebAssembly.RuntimeError ? 'trap(' + e.message + ')' : 'jserror(' + e.message + ')';
  }
};
const message = (e) => String((e && e.message) || e);
const instantiate = async (bytes) => (await WebAssembly.instantiate(bytes, {})).instance.exports;
const signedZeroPair = (want, got) => (want === '0' && got === '-0') || (want === '-0' && got === '0');

// ---------- isolated execution ----------
// Every grid and loop run of `measure` executes in a worker thread that the
// parent terminates when its budget runs out, so a module that does not
// return cannot stall the harness and is recorded instead.
const ORACLE_BUDGET_MS = 120000;
const CANDIDATE_FLOOR_MS = 20000;
const CANDIDATE_FACTOR = 50;
const candidateBudget = (oracleMs, floorMs = CANDIDATE_FLOOR_MS) => Math.max(floorMs, Math.ceil(CANDIDATE_FACTOR * oracleMs));

// The worker side: {failure: compile|instantiate, detail} or the task's result.
async function runTask(task) {
  let mod;
  try { mod = await WebAssembly.compile(task.bytes); } catch (e) { return { failure: 'compile', detail: message(e) }; }
  let ex;
  try { ex = (await WebAssembly.instantiate(mod, {})).exports; } catch (e) { return { failure: 'instantiate', detail: message(e) }; }
  if (task.kind === 'plan') {
    const out = [];
    for (const e of task.plan) {
      const f = ex[e.name];
      for (const a of e.argsets) { out.push(typeof f === 'function' ? callOne(f, a) : 'missing'); Atomics.store(task.progress, 0, out.length); }
    }
    return { out };
  }
  const t0 = process.hrtime.bigint();
  try {
    const acc = BigInt.asUintN(64, ex.__wvl_loop(task.reps)).toString(16);
    const ms = Number(process.hrtime.bigint() - t0) / 1e6;
    const counters = Object.fromEntries(Object.keys(ex).filter((n) => n.startsWith('__wvl_c_'))
      .map((n) => [n.slice('__wvl_c_'.length), BigInt(ex[n].value).toString()]));
    return { acc, trap: null, ms, counters };
  } catch (e) {
    return { acc: null, trap: message(e), ms: null, counters: null };
  }
}

// The parent side: the task's result, {failure: 'timeout', detail, completed}
// when the budget ran out (completed: grid calls answered before it did), or
// {fault} when the worker itself failed.
function isolated(task, budgetMs) {
  return new Promise((resolve) => {
    const progress = new Int32Array(new SharedArrayBuffer(4));
    const t0 = process.hrtime.bigint();
    const worker = new Worker(new URL(import.meta.url), { workerData: { wasmtoolTask: { ...task, progress } } });
    let settled = false;
    const finish = (r) => {
      if (settled) return;
      settled = true; clearTimeout(timer); worker.terminate();
      resolve({ ...r, wall_ms: Number(process.hrtime.bigint() - t0) / 1e6 });
    };
    const timer = setTimeout(() => finish({ failure: 'timeout', detail: `no answer within ${budgetMs} ms`,
      completed: Atomics.load(progress, 0) }), budgetMs);
    worker.on('message', finish);
    worker.on('error', (e) => finish({ fault: message(e) }));
    worker.on('exit', (code) => finish({ fault: `worker exited (code ${code}) without an answer` }));
  });
}

// The grid call at position K of PLAN, for a report.
function callAt(plan, k) {
  for (const e of plan) {
    if (k < e.argsets.length) return `${e.name}(${e.argsets[k].map(show).join(', ')})`;
    k -= e.argsets.length;
  }
  return null;
}

// Compares a lane's grid run with the oracle's. A lane that did not run the
// grid to the end has `run_failure` (its module failed to compile or
// instantiate, or a call did not return within the budget) and no count of
// disagreements. Signed-zero differences are disagreements except on the
// exports of SOFTZERO.
function compareRuns(plan, want, run, softZero = new Set(), maxShown = 20) {
  const checks = plan.reduce((n, e) => n + e.argsets.length, 0);
  if (run.fault) return { checks, disagreements: null, harness_fault: run.fault };
  if (run.failure) {
    const failure = { stage: run.failure, detail: run.detail };
    if (run.failure === 'timeout') { failure.completed_calls = run.completed; failure.call = callAt(plan, run.completed); }
    return { checks, disagreements: null, run_failure: failure };
  }
  const got = run.out;
  let k = 0, hard = 0, soft = 0, trapBoth = 0; const shown = []; const failing = {}; const missing = []; const softCases = [];
  for (const e of plan) {
    for (const a of e.argsets) {
      const w = want[k], g = got[k]; k++;
      if (g === 'missing') { if (!missing.includes(e.name)) missing.push(e.name); continue; }
      if (w === g) { if (w.startsWith('trap')) trapBoth++; continue; }
      if (w.startsWith('trap') && g.startsWith('trap')) { trapBoth++; continue; }
      if (signedZeroPair(w, g) && softZero.has(e.name)) {
        soft++;
        if (softCases.length < maxShown) softCases.push({ export: e.name, args: a.map(show), oracle: w, candidate: g });
        continue;
      }
      hard++; failing[e.name] = (failing[e.name] || 0) + 1;
      if (shown.length < maxShown) shown.push(`${e.name}(${a.map(show).join(', ')}): oracle=${w} candidate=${g}`);
    }
  }
  return { checks, disagreements: hard, soft_signed_zero: soft, soft_cases: softCases, trap_both: trapBoth,
    missing_exports: missing, failing_exports: failing, first_disagreements: shown };
}

function workloadOf(plan, oracleResults, softZero = new Set()) {
  const calls = []; let k = 0;
  for (const e of plan) for (const a of e.argsets) {
    const r = oracleResults[k++];
    if (!r.startsWith('trap') && !r.startsWith('jserror')) {
      calls.push({ index: e.index, name: e.name, kinds: e.kinds, results: e.results, args: a, softZero: softZero.has(e.name) });
    }
  }
  return calls;
}

function remapCalls(calls, m) {
  // Exports are matched by name: each lane has its own function indices.
  const byName = Object.fromEntries(m.exports.filter((e) => e.kind === 0).map((e) => [e.name, e.idx]));
  return calls.map((c) => ({ ...c, index: byName[c.name] }));
}

async function runLoop(bytes, reps) {
  const ex = await instantiate(bytes);
  const t0 = process.hrtime.bigint();
  try {
    const acc = BigInt.asUintN(64, ex.__wvl_loop(reps)).toString(16);
    return { acc, trap: null, ex, ms: Number(process.hrtime.bigint() - t0) / 1e6 };
  } catch (e) {
    return { acc: null, trap: message(e), ex, ms: null };
  }
}

// A loop run's outcome on a lane record: a trap or a timeout is the lane's
// behaviour (`loop_trap`); a loop module that does not compile or instantiate
// is the harness's (`loop_error`), since the lane's own module did.
function loopOutcome(run) {
  if (run.fault) return { error: `loop worker: ${run.fault}` };
  if (run.failure === 'timeout') return { trap: `timeout: ${run.detail}` };
  if (run.failure) return { error: `loop module ${run.failure}: ${run.detail}` };
  return { acc: run.acc, trap: run.trap };
}

// ---------- measure ----------
async function measure(opts) {
  const lanes = opts.lanes; // [{name, path}], oracle first
  const work = opts.work;
  const softZero = new Set(opts.softZero);
  const res = { lanes: {}, oracle: lanes[0].name, grid_sha256: gridSha256(), soft_zero_exports: [...softZero].sort() };
  const mods = {};
  for (const l of lanes) {
    const bytes = new Uint8Array(fs.readFileSync(l.path));
    const r = { static: null, static_error: null };
    try { const s = staticMetrics(bytes); r.static = s.metrics; r.stack_pointer = s.stack_pointer; }
    catch (e) { r.static_error = message(e); }
    try { mods[l.name] = { bytes, m: parseModule(bytes) }; } catch (e) { r.parse_error = message(e); }
    res.lanes[l.name] = r;
  }
  const oracle = mods[lanes[0].name];
  if (!oracle) throw new Error(`oracle module unreadable: ${res.lanes[lanes[0].name].parse_error}`);
  const { plan, skipped } = callPlan(oracle.m);
  res.exports = plan.map((e) => e.name); res.skipped_exports = skipped;
  res.checks = plan.reduce((s, e) => s + e.argsets.length, 0);
  const oracleRun = await isolated({ kind: 'plan', bytes: oracle.bytes, plan }, ORACLE_BUDGET_MS);
  if (!oracleRun.out) {
    res.oracle_failure = oracleRun.fault ? `worker: ${oracleRun.fault}`
      : `${oracleRun.failure}: ${oracleRun.detail}${oracleRun.failure === 'timeout' ? ` at ${callAt(plan, oracleRun.completed)}` : ''}`;
    return res;
  }
  const want = oracleRun.out;
  const floorMs = opts.budgetFloorMs ?? CANDIDATE_FLOOR_MS;
  const budget = candidateBudget(oracleRun.wall_ms, floorMs);
  res.budget_ms = budget;
  for (const l of lanes.slice(1)) {
    const run = await isolated({ kind: 'plan', bytes: new Uint8Array(fs.readFileSync(l.path)), plan }, budget);
    res.lanes[l.name].differential = compareRuns(plan, want, run, softZero);
  }
  const workload = workloadOf(plan, want, softZero);
  res.workload = { calls: workload.length, status: workload.length ? 'ok' : 'empty' };
  if (!workload.length) return res;
  // Loop modules, the reps=1 accumulator check, and the instrumented pass.
  let loopBudget = ORACLE_BUDGET_MS;
  for (const l of lanes) {
    const r = res.lanes[l.name];
    if (!mods[l.name]) { r.loop_error = `module not decoded: ${r.parse_error}`; continue; }
    let loop;
    try {
      const calls = remapCalls(workload, mods[l.name].m);
      if (calls.some((c) => c.index === undefined)) { r.loop_error = 'an export of the workload is missing'; continue; }
      loop = loopModule(mods[l.name].bytes, calls);
    } catch (e) { r.loop_error = message(e); continue; }
    fs.writeFileSync(path.join(work, `${l.name}.loop.wasm`), loop.bytes);
    const plainRun = await isolated({ kind: 'loop', bytes: loop.bytes, reps: 1 }, loopBudget);
    const plain = loopOutcome(plainRun);
    if (l === lanes[0] && plainRun.ms) loopBudget = candidateBudget(plainRun.wall_ms, floorMs);
    if (plain.error) { r.loop_error = plain.error; continue; }
    if (l === lanes[0] && plain.trap !== null && plain.trap.startsWith('timeout')) {
      res.oracle_failure = `workload loop ${plain.trap}`; return res;
    }
    r.loop_acc = plain.acc; r.loop_trap = plain.trap;
    if (plain.trap !== null) continue;
    try {
      const inst = instrument(loop.bytes, loop.loopIndex);
      const run = await isolated({ kind: 'loop', bytes: inst.bytes, reps: 1 }, Math.max(loopBudget, CANDIDATE_FACTOR * 4 * plainRun.wall_ms));
      const out = loopOutcome(run);
      if (out.error || out.trap !== null || out.acc !== plain.acc) {
        r.dynamic_error = out.error || `instrumented workload diverged from the plain loop (acc ${out.acc} vs ${plain.acc}, trap ${out.trap})`;
      } else {
        const g = (n) => BigInt.asUintN(64, BigInt(run.counters[n]));
        r.dynamic = { dyn_insns: Number(g('insn')), dyn_memops: Number(g('mem')), dyn_calls: Number(g('call')), dyn_loop_heads: Number(g('loop')) };
        if (inst.stackLayout !== null) {
          r.stack_error = inst.stackLayout;
        } else {
          const init = inst.stackPointer.init;
          const written = Number(BigInt.asUintN(32, BigInt(run.counters.spmin)));
          const touched = Number(BigInt(run.counters.touchmin));
          const low = Math.min(written, touched);
          r.stack = { sp_init: init, sp_min_written: written, touch_min: touched, stack_hwm: init - low,
            stack_hwm_written: init - written };
        }
      }
    } catch (e) { r.dynamic_error = message(e); }
  }
  const o = res.lanes[lanes[0].name];
  if (o.loop_trap !== null && o.loop_trap !== undefined) res.workload.status = 'oracle_traps';
  return res;
}

// ---------- time ----------
async function time(opts) {
  const names = opts.laneNames; const n = opts.n; const targetMs = opts.targetMs;
  const loops = {}; const first = {};
  for (const name of names) {
    const file = path.join(opts.work, `${name}.loop.wasm`);
    if (!fs.existsSync(file)) return { error: `no loop module for lane ${name}` };
    const r = await runLoop(new Uint8Array(fs.readFileSync(file)), 1);
    if (r.trap !== null) return { error: `lane ${name} trapped in warm-up: ${r.trap}` };
    loops[name] = r.ex.__wvl_loop; first[name] = r.ms;
  }
  const clock = (f, reps) => { const t0 = process.hrtime.bigint(); f(reps); return Number(process.hrtime.bigint() - t0) / 1e6; };
  let reps = 1;
  try {
    for (;;) {
      const ms = clock(loops[names[0]], reps);
      if (ms >= targetMs || reps >= opts.maxReps) break;
      reps = Math.min(opts.maxReps, reps * Math.max(2, Math.ceil(targetMs / Math.max(ms, 0.001) * 1.2)));
    }
    for (const name of names) clock(loops[name], reps);
    const samples = Object.fromEntries(names.map((x) => [x, []]));
    for (let k = 0; k < n; k++) {
      for (let j = 0; j < names.length; j++) {
        const name = names[(j + k) % names.length];
        samples[name].push(clock(loops[name], reps));
      }
    }
    return { reps, samples_ms: samples, first_call_ms: first };
  } catch (e) {
    return { error: `trapped while timing at reps=${reps}: ${String(e.message || e)}` };
  }
}

// ---------- selftest ----------
// Hand-assembled modules with known counts: the decoder, the loop builder and
// the instrumenter are checked against them before any corpus number is trusted.
async function selftest() {
  const fails = [];
  const check = (cond, msg) => { if (!cond) fails.push(msg); };
  // (global $__stack_pointer (mut i32) (i32.const 1024))
  // func 0 "f" (i32) -> i32: sp -= 16; loop 3 times: acc += x; return acc (+ a store and a load)
  // func 1 "g" (f64) -> f64: f64.neg
  const types = section(1, [2, 0x60, 1, 0x7f, 1, 0x7f, 0x60, 1, 0x7c, 1, 0x7c]);
  const funcs = section(3, [2, 0, 1]);
  const mem = section(5, [1, 0, 1]);
  const glob = section(6, [1, 0x7f, 1, 0x41, ...encS(1024n), 0x0b]);
  const exps = section(7, [2, ...encName('f'), 0, 0, ...encName('g'), 0, 1]);
  const f = [1, 2, 0x7f, // two i32 locals: $i (1), $acc (2)
    0x23, 0, 0x41, 16, 0x6b, 0x24, 0, // sp -= 16
    0x41, 3, 0x21, 1, // i = 3
    0x02, 0x40, 0x03, 0x40, // block loop
    0x20, 2, 0x20, 0, 0x6a, 0x21, 2, // acc += x
    0x20, 1, 0x41, 1, 0x6b, 0x22, 1, // i -= 1 (tee)
    0x0d, 0, // br_if loop (while i != 0)
    0x0b, 0x0b, // end loop, end block
    0x23, 0, 0x20, 2, 0x36, 2, 0, // store acc at sp
    0x23, 0, 0x28, 2, 0, // load it back
    0x23, 0, 0x41, 16, 0x6a, 0x24, 0, // sp += 16
    0x0b];
  const g = [0, 0x20, 0, 0x9a, 0x0b];
  const code = section(10, [2, ...encU(f.length), ...f, ...encU(g.length), ...g]);
  const names = section(0, [...encName('name'), 7, ...encU(1 + 1 + 1 + 15), 1, 0, ...encName('__stack_pointer')]);
  const bytes = new Uint8Array([0, 0x61, 0x73, 0x6d, 1, 0, 0, 0, ...types, ...funcs, ...mem, ...glob, ...exps, ...code, ...names]);
  const s = staticMetrics(bytes);
  // f: 26 non-marker instructions; g: 2.
  check(s.metrics.static_insns === 26 + 2, `static_insns ${s.metrics.static_insns}`);
  check(s.metrics.declared_locals === 2, `declared_locals ${s.metrics.declared_locals}`);
  check(s.metrics.static_loads === 1 && s.metrics.static_stores === 1, 'loads/stores');
  check(s.metrics.sp_writes === 2 && s.metrics.framed_functions === 1, `sp ${s.metrics.sp_writes}/${s.metrics.framed_functions}`);
  check(s.stack_pointer.init === 1024, 'stack pointer init');
  const m = parseModule(bytes);
  const { plan } = callPlan(m);
  check(plan.length === 2 && plan[0].argsets.length === I32.length && plan[1].argsets.length === F64.length, 'call plan');
  const oracleRun = await isolated({ kind: 'plan', bytes, plan }, 10000);
  const want = oracleRun.out || [];
  check(want[0] === '0' && want[1] === '3', `f results ${want.slice(0, 2)}`);
  const workload = workloadOf(plan, want);
  check(workload.length === I32.length + F64.length, 'workload');
  const fOnly = [{ index: 0, name: 'f', kinds: ['i32'], results: ['i32'], args: [5] }];
  const loop = loopModule(bytes, fOnly);
  const plain = await runLoop(loop.bytes, 1);
  // acc = rotl(0, 5) ^ zext(15)
  check(plain.acc === (15).toString(16), `loop acc ${plain.acc}`);
  const inst = instrument(loop.bytes, loop.loopIndex);
  check(inst.stackLayout === null, `stack layout ${inst.stackLayout}`);
  const run = await runLoop(inst.bytes, 1);
  check(run.acc === plain.acc, 'instrumented acc');
  const v = (k) => Number(BigInt(run.ex[`__wvl_c_${k}`].value));
  // Executed: 6 before the block, then block and loop = 8; 3 iterations of 9
  // (the body and its br_if) = 27; after the loop 9 (store, load, sp restore).
  check(v('insn') === 8 + 27 + 9, `dyn insns ${v('insn')}`);
  check(v('mem') === 2, `dyn mem ${v('mem')}`);
  check(v('call') === 0, `dyn calls ${v('call')}`);
  check(v('loop') === 3, `loop heads ${v('loop')}`);
  check(v('spmin') === 1008, `spmin ${v('spmin')}`);
  check(v('touchmin') === 1008, `touchmin ${v('touchmin')}`);
  // The same through the isolated runner, as `measure` reads it.
  const isoRun = await isolated({ kind: 'loop', bytes: inst.bytes, reps: 1 }, 10000);
  check(isoRun.acc === plain.acc && isoRun.counters && isoRun.counters.insn === String(8 + 27 + 9), `isolated loop ${JSON.stringify(isoRun)}`);

  // Memory touched below the stack pointer without moving it (a leaf frame),
  // and bulk memory, count toward the stack high-water; a write-only view
  // would read 0 here.
  // func "h" (i32) -> i32: i32.store offset=4 at sp-48 (ea 980), i32.load at sp-44.
  // func "z" (i32) -> i32: memory.fill(sp-64, 0, x); memory.copy(4096, sp-200, x); 0.
  const lt = section(1, [1, 0x60, 1, 0x7f, 1, 0x7f]);
  const lf = section(3, [2, 0, 0]);
  const lx = section(7, [2, ...encName('h'), 0, 0, ...encName('z'), 0, 1]);
  const h = [0, 0x23, 0, 0x41, 48, 0x6b, 0x20, 0, 0x36, 2, 4, 0x23, 0, 0x41, 44, 0x6b, 0x28, 2, 0, 0x0b];
  const z = [0, 0x23, 0, 0x41, ...encS(64n), 0x6b, 0x41, 0, 0x20, 0, 0xfc, 11, 0,
    0x41, ...encS(4096n), 0x23, 0, 0x41, ...encS(200n), 0x6b, 0x20, 0, 0xfc, 10, 0, 0, 0x41, 0, 0x0b];
  const leafModule = (data) => new Uint8Array([0, 0x61, 0x73, 0x6d, 1, 0, 0, 0, ...lt, ...lf, ...mem, ...glob, ...lx,
    ...section(12, [data ? 1 : 0]),
    ...section(10, [2, ...encU(h.length), ...h, ...encU(z.length), ...z]),
    ...(data ? section(11, [1, 0, 0x41, ...encS(BigInt(data)), 0x0b, 1, 7]) : section(11, [0])), ...names]);
  const leaf = leafModule(0);
  const stackOf = async (bytesIn, calls) => {
    const lp = loopModule(bytesIn, calls);
    const ins = instrument(lp.bytes, lp.loopIndex);
    const r = await runLoop(ins.bytes, 1);
    const read = (k) => Number(BigInt(r.ex[`__wvl_c_${k}`].value));
    return { layout: ins.stackLayout, acc: r.acc, plainAcc: (await runLoop(lp.bytes, 1)).acc,
      hwm: 1024 - Math.min(read('spmin'), read('touchmin')), written: 1024 - read('spmin') };
  };
  const call = (name, index, x) => ({ index, name, kinds: ['i32'], results: ['i32'], args: [x] });
  const hs = await stackOf(leaf, [call('h', 0, 5)]);
  check(hs.layout === null && hs.acc === hs.plainAcc && hs.acc === (5).toString(16), `leaf acc ${JSON.stringify(hs)}`);
  check(hs.hwm === 44 && hs.written === 0, `leaf stack ${JSON.stringify(hs)}`);
  const zEmpty = await stackOf(leaf, [call('z', 1, 0)]);
  check(zEmpty.hwm === 0, `empty bulk ops touch nothing ${JSON.stringify(zEmpty)}`);
  const zFull = await stackOf(leaf, [call('z', 1, 8)]);
  check(zFull.hwm === 200, `bulk copy source ${JSON.stringify(zFull)}`);
  // A data segment below the initial stack pointer: not stack-first, no reading.
  const low = leafModule(16);
  check(stackLayoutProblem(parseModule(low), stackPointerIndex(parseModule(low))) !== null, 'data below the stack refused');
  check(stackLayoutProblem(parseModule(leafModule(2048)), stackPointerIndex(parseModule(leafModule(2048)))) === null, 'data above the stack accepted');

  // Floats fold by their bits: -0 differs from +0 unless the call is softZero;
  // every NaN folds as one pattern.
  const neg = (x, softZero = false) => [{ index: 1, name: 'g', kinds: ['f64'], results: ['f64'], args: [x], softZero }];
  const a = await runLoop(loopModule(bytes, neg(0)).bytes, 1);
  const b = await runLoop(loopModule(bytes, neg(-0)).bytes, 1);
  check(a.acc !== b.acc, 'signed zero kept by default');
  const as = await runLoop(loopModule(bytes, neg(0, true)).bytes, 1);
  const bs = await runLoop(loopModule(bytes, neg(-0, true)).bytes, 1);
  check(as.acc === bs.acc, 'signed zero folded for a softZero call');
  const c = await runLoop(loopModule(bytes, neg(NaN)).bytes, 1);
  check(c.acc === (CANON_F64_BITS).toString(16), `NaN canonicalized ${c.acc}`);
  // Differential: a lane that differs on one input is a disagreement.
  const altF = [...f]; altF[altF.indexOf(0x6a)] = 0x6b; // acc -= x
  const modWith = (fBody, gBody) => new Uint8Array([0, 0x61, 0x73, 0x6d, 1, 0, 0, 0, ...types, ...funcs, ...mem, ...glob, ...exps,
    ...section(10, [2, ...encU(fBody.length), ...fBody, ...encU(gBody.length), ...gBody]), ...names]);
  const cmp = compareRuns(plan, want, await isolated({ kind: 'plan', bytes: modWith(altF, g), plan }, 10000));
  // -3x == 3x (mod 2^32) only for x = 0 and x = -2^31.
  check(cmp.disagreements === I32.length - 2 && cmp.failing_exports.f === I32.length - 2, `differential ${JSON.stringify(cmp.failing_exports)}`);
  // 0.0 - x against f64.neg x: differs only in the sign of zero (x = 0).
  const subG = [0, 0x44, 0, 0, 0, 0, 0, 0, 0, 0, 0x20, 0, 0xa1, 0x0b];
  const zrun = await isolated({ kind: 'plan', bytes: modWith(f, subG), plan }, 10000);
  const hard = compareRuns(plan, want, zrun);
  check(hard.disagreements === 1 && hard.failing_exports.g === 1, `signed zero is a disagreement ${JSON.stringify(hard.failing_exports)}`);
  const soft = compareRuns(plan, want, zrun, new Set(['g']));
  check(soft.disagreements === 0 && soft.soft_signed_zero === 1 && soft.soft_cases[0].export === 'g'
    && soft.soft_cases[0].oracle === '-0' && soft.soft_cases[0].candidate === '0', `listed soft zero ${JSON.stringify(soft)}`);
  // A lane that does not compile, or does not return, is a run failure.
  const hangG = [0, 0x03, 0x40, 0x0c, 0, 0x0b, 0x20, 0, 0x9a, 0x0b];
  const hang = compareRuns(plan, want, await isolated({ kind: 'plan', bytes: modWith(f, hangG), plan }, 1500));
  check(hang.disagreements === null && hang.run_failure && hang.run_failure.stage === 'timeout'
    && hang.run_failure.completed_calls === I32.length && hang.run_failure.call === 'g(0)', `hang ${JSON.stringify(hang)}`);
  const badG = [0, 0x20, 0, 0x42, 0, 0x7c, 0x0b];
  const bad = compareRuns(plan, want, await isolated({ kind: 'plan', bytes: modWith(f, badG), plan }, 10000));
  check(bad.disagreements === null && bad.run_failure && bad.run_failure.stage === 'compile', `invalid ${JSON.stringify(bad)}`);
  // Unsupported opcodes fail closed.
  let threw = false; try { readInstr(new Uint8Array([0xfd, 0x0c]), { i: 0 }); } catch { threw = true; }
  check(threw, 'SIMD prefix refused');
  console.log(JSON.stringify({ selftest: fails.length ? 'FAIL' : 'OK', failures: fails }));
  return fails.length ? 1 : 0;
}

// ---------- CLI ----------
function parseArgs(argv) {
  const o = { lanes: [], laneNames: [], softZero: [], n: 5, targetMs: 20, maxReps: 1 << 20 };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--work') o.work = argv[++i];
    else if (a === '--out') o.out = argv[++i];
    else if (a === '--lane') {
      const v = argv[++i]; const eq = v.indexOf('=');
      if (eq >= 0) o.lanes.push({ name: v.slice(0, eq), path: v.slice(eq + 1) }); else o.laneNames.push(v);
    } else if (a === '--n') o.n = Number(argv[++i]);
    else if (a === '--target-ms') o.targetMs = Number(argv[++i]);
    else if (a === '--max-reps') o.maxReps = Number(argv[++i]);
    else if (a === '--soft-zero') o.softZero.push(argv[++i]);
    else if (a === '--budget-floor-ms') o.budgetFloorMs = Number(argv[++i]);
    else throw new Error(`unknown argument ${a}`);
  }
  return o;
}

async function main() {
  const [cmd, ...rest] = process.argv.slice(2);
  if (cmd === 'selftest') process.exit(await selftest());
  const o = parseArgs(rest);
  let result;
  if (cmd === 'measure') {
    if (!o.work || !o.out || o.lanes.length < 2) throw new Error('measure needs --work, --out and at least two --lane NAME=PATH');
    result = await measure(o);
  } else if (cmd === 'time') {
    if (!o.work || !o.out || !o.laneNames.length) throw new Error('time needs --work, --out and --lane NAME');
    result = await time(o);
    result.engine = { node: process.version, v8: process.versions.v8, execArgv: process.execArgv };
  } else {
    throw new Error('usage: wasmtool.mjs measure|time|selftest ...');
  }
  fs.writeFileSync(o.out, JSON.stringify(result));
}

if (!isMainThread && workerData && workerData.wasmtoolTask) {
  runTask(workerData.wasmtoolTask).then((r) => parentPort.postMessage(r), (e) => parentPort.postMessage({ fault: String((e && e.stack) || e) }));
} else if (isMainThread && import.meta.url === `file://${process.argv[1]}`) {
  main().catch((e) => { console.error(`wasmtool: ${e.stack || e}`); process.exit(2); });
}
