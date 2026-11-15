// trust-cg-codegen/tests/neon_butterfly_writeback_execution.rs
//
// NEON LD1/ST1 post-index with a LIVE base-register writeback, through the
// real trust-ir -> object pipeline: decoded, walked for liveness, executed
// against a C oracle and mutated.
//
// `neon_butterfly` (trust-cg-opt, scheduled at O2/Os/O3) vectorizes the
// radix-2 FFT butterfly inner loop over `struct complex { f32 rp, ip; }` (the
// Stanford Oscar `Fft` shape). Its vector body walks four pointers, one per
// stream, with `LD1 {Vt.4S}, [Xn], #16` for the two read streams and
// `ST1 {Vt.4S}, [Xn], #16` for the two output streams. Unlike `neon_fmap`'s
// remainder loop (see neon_ld1_st1_post_execution.rs), nothing recomputes
// those pointers: each `#16` writeback is the address the next iteration uses.
//
// Three trust-ir kernels are built in the exact shape the pass's matcher
// admits (read from `RecognizedButterfly::recognize`): a two-block do-while
// over an i64 induction whose header ends in `cmp iv, j; b.lt latch`, element
// addresses formed by MADD with one shared `Movz(8)`, the `+4` field by an
// offset, every operand reloaded after each store, `fneg`/`fmul` feeding a
// fused multiply-add (`llvm.fma.f32`) with the twiddle cell reloaded in the
// loop. They differ in how the addresses are formed (the Oscar recipe with
// `z[i+m]` and `w[i+k]`/`w[i+kb]` built inside the loop, or the invariant
// parts formed before it) and in the twiddle offset (0 or 8 bytes). `Compiler`
// compiles them at O0-O3; O2 and O3 schedule the pass (the public codegen
// `OptLevel` has no Os, so Os is not exercised here).
//
// Evidence, in order of strength:
// * decode: every word of the final object's code section is classified by
//   trust-cg-lift and by an independent bit mask; they must agree. Each
//   vectorized kernel must hold exactly two LD1 and two ST1 post-index `.4S`
//   words on four distinct base registers. The gate refuses O0/O1, O2 with
//   `neon_butterfly` disabled, and each LD1/ST1 word narrowed to 64 bits,
//   removed, rewritten to the no-writeback `[Xn]` form, or rewritten to the
//   register post-index form `[Xn], Xs`;
// * liveness: a walk over the decoded control flow of each kernel shows that
//   every writeback is read, as the base of the same LD1/ST1, on the next
//   loop iteration (through the loop's backward branch) before any
//   instruction redefines the register. The same walk reports every
//   `neon_fmap` remainder-loop writeback dead (a negative control compiled
//   here) and the butterfly writebacks dead once the backward branch is
//   removed;
// * execution: the host object is linked with `cc` against a C oracle that
//   runs the same do-while, one inline-asm scalar instruction per operation
//   in the loop's operand order, and compares the whole buffer bit for bit
//   after every call.
//   The calls cover vector pairs, the one-iteration scalar tail of odd trip
//   counts, whole-scalar calls (a single iteration, `i0 >= j`, a negative
//   `i0`, a bound at or above 2^31) and nineteen placements of the four
//   streams and the twiddle cell: disjoint, touching, reads overlapping each
//   other and the twiddle inside a read stream (all admitted by the pass's
//   seven-pair check) and stores overlapping a read, each other or the
//   twiddle (all routed to the scalar loop). The driver predicts each call's
//   path from those byte ranges independently of the object;
// * mutation: at O2 and O3 each LD1/ST1 word is rewritten to `[Xn]` (no
//   writeback) and to `[Xn], Xs`, where the decoded stream proves Xs holds a
//   constant other than 16 at every entry to the loop (a wrong stride). Every
//   such mutant must fail the oracle, and only in calls the driver predicts
//   run two or more vector iterations: never in single-iteration vector
//   calls (the last writeback is dead) and never in scalar-path calls. On
//   finite inputs every multi-iteration call must fail. Narrowed and removed
//   words must also fail, including in single-iteration calls.
//
// This is object and execution evidence for these shapes and inputs on the
// host that runs it; it is not a proof of `neon_butterfly`, of its alias
// check, of the LD1/ST1 encoder or of other shapes.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

#[path = "common/pinned_target.rs"]
mod pinned_target;

use std::collections::{BTreeMap, VecDeque};

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_lift::disasm::aarch64::{Instruction, LoadStorePairAddressMode, decode};
use trust_ir::{BinOp, CastOp, FuncId, ICmpOp, Ty, UnOp};
use trust_ir_build::ModuleBuilder;

#[path = "common/native_host.rs"]
mod native_host;
#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[path = "common/rosetta.rs"]
mod process;

const LINUX: &str = "aarch64-unknown-linux-gnu";
const DARWIN: &str = "aarch64-apple-darwin";
const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
/// Levels whose default pipeline schedules `neon_butterfly`.
const VECTOR_LEVELS: [OptLevel; 2] = [OptLevel::O2, OptLevel::O3];
const NOP: u32 = 0xd503_201f;
/// The `neon_fmap` negative control for the liveness walk (not executed).
const FMAP_CONTROL: &str = "fmap_rot_scale_f32_control";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Chains {
    /// The Oscar recipe: `z[i+m]`, `w[i+k]` and `w[i+kb]` are a second MADD
    /// of the invariant index onto the induction-scaled address, inside the
    /// loop.
    Nested,
    /// `z + m*8`, `w + k*8` and `w + kb*8` are formed before the loop, so each
    /// stream is one MADD of the induction onto a loop-invariant base.
    Hoisted,
}

#[derive(Clone, Copy, Debug)]
struct Kernel {
    name: &'static str,
    chains: Chains,
    /// Byte offset of the twiddle cell `{e.rp, e.ip}` from the `e` argument.
    e_off: u64,
}

const KERNELS: [Kernel; 3] = [
    Kernel {
        name: "bfly_nested_e0",
        chains: Chains::Nested,
        e_off: 0,
    },
    Kernel {
        name: "bfly_nested_e8",
        chains: Chains::Nested,
        e_off: 8,
    },
    Kernel {
        name: "bfly_hoisted_e8",
        chains: Chains::Hoisted,
        e_off: 8,
    },
];

/// `f(z, w, e, m, k, kb, i0, j)`: for `i = i0` and then while the old `i` is
/// below `j` (a do-while, so at least one iteration), with complex elements
/// of 8 bytes and the twiddle cell at `e + e_off`:
///
/// ```text
/// w[i+k].rp  = z[i].rp + z[i+m].rp
/// w[i+k].ip  = z[i].ip + z[i+m].ip
/// w[i+kb].rp = fma(e.rp, z[i].rp - z[i+m].rp, e.ip * -(z[i].ip - z[i+m].ip))
/// w[i+kb].ip = fma(e.rp, z[i].ip - z[i+m].ip, e.ip * (z[i].rp - z[i+m].rp))
/// ```
///
/// Each statement reloads its operands after the previous statement's store.
fn build_butterfly(mb: &mut ModuleBuilder, fma: FuncId, kernel: Kernel) {
    let ty = mb.add_func_type(
        vec![
            Ty::Ptr,
            Ty::Ptr,
            Ty::Ptr,
            Ty::I64,
            Ty::I64,
            Ty::I64,
            Ty::I64,
            Ty::I64,
        ],
        vec![],
    );
    let mut fb = mb.function(kernel.name, ty);
    let entry = fb.create_block();
    let z = fb.add_block_param(entry, Ty::Ptr);
    let w = fb.add_block_param(entry, Ty::Ptr);
    let e = fb.add_block_param(entry, Ty::Ptr);
    let m = fb.add_block_param(entry, Ty::I64);
    let k = fb.add_block_param(entry, Ty::I64);
    let kb = fb.add_block_param(entry, Ty::I64);
    let i0 = fb.add_block_param(entry, Ty::I64);
    let j = fb.add_block_param(entry, Ty::I64);
    let body = fb.create_block();
    let iv = fb.add_block_param(body, Ty::I64);
    let exit = fb.create_block();
    // One complex element is 8 bytes; `i64` has the same size and stride.
    let element = Ty::I64;
    fb.switch_to_block(entry);
    let hoisted = match kernel.chains {
        Chains::Hoisted => Some((
            fb.gep(element.clone(), z, vec![m]),
            fb.gep(element.clone(), w, vec![k]),
            fb.gep(element.clone(), w, vec![kb]),
        )),
        Chains::Nested => None,
    };
    fb.br(body, vec![i0]);
    fb.switch_to_block(body);
    let pz = fb.gep(element.clone(), z, vec![iv]);
    let (pzm, pa, pb) = match hoisted {
        Some((z2, wa, wb)) => (
            fb.gep(element.clone(), z2, vec![iv]),
            fb.gep(element.clone(), wa, vec![iv]),
            fb.gep(element.clone(), wb, vec![iv]),
        ),
        None => {
            let pzm = fb.gep(element.clone(), pz, vec![m]);
            let pw = fb.gep(element.clone(), w, vec![iv]);
            (
                pzm,
                fb.gep(element.clone(), pw, vec![k]),
                fb.gep(element.clone(), pw, vec![kb]),
            )
        }
    };
    let pz_ip = fb.gep_byte_offset(pz, 4);
    let pzm_ip = fb.gep_byte_offset(pzm, 4);
    let pa_ip = fb.gep_byte_offset(pa, 4);
    let pb_ip = fb.gep_byte_offset(pb, 4);
    let pe_rp = if kernel.e_off == 0 {
        e
    } else {
        fb.gep_byte_offset(e, kernel.e_off)
    };
    let pe_ip = fb.gep_byte_offset(e, kernel.e_off + 4);
    let f32 = Ty::F32;
    // (A) the sum stream.
    let x = fb.load(f32.clone(), pz);
    let y = fb.load(f32.clone(), pzm);
    let sum = fb.binop(BinOp::FAdd, f32.clone(), x, y);
    fb.store(f32.clone(), pa, sum);
    let x = fb.load(f32.clone(), pz_ip);
    let y = fb.load(f32.clone(), pzm_ip);
    let sum = fb.binop(BinOp::FAdd, f32.clone(), x, y);
    fb.store(f32.clone(), pa_ip, sum);
    // (B) the twiddle stream, `.rp`.
    let er = fb.load(f32.clone(), pe_rp);
    let x = fb.load(f32.clone(), pz);
    let y = fb.load(f32.clone(), pzm);
    let dr = fb.binop(BinOp::FSub, f32.clone(), x, y);
    let ei = fb.load(f32.clone(), pe_ip);
    let x = fb.load(f32.clone(), pz_ip);
    let y = fb.load(f32.clone(), pzm_ip);
    let di = fb.binop(BinOp::FSub, f32.clone(), x, y);
    let negated = fb.unop(UnOp::FNeg, f32.clone(), di);
    let product = fb.binop(BinOp::FMul, f32.clone(), ei, negated);
    let rp = fb.call(fma, vec![er, dr, product]);
    fb.store(f32.clone(), pb, rp);
    // (B) `.ip`.
    let er = fb.load(f32.clone(), pe_rp);
    let x = fb.load(f32.clone(), pz_ip);
    let y = fb.load(f32.clone(), pzm_ip);
    let di = fb.binop(BinOp::FSub, f32.clone(), x, y);
    let ei = fb.load(f32.clone(), pe_ip);
    let x = fb.load(f32.clone(), pz);
    let y = fb.load(f32.clone(), pzm);
    let dr = fb.binop(BinOp::FSub, f32.clone(), x, y);
    let product = fb.binop(BinOp::FMul, f32.clone(), ei, dr);
    let ip = fb.call(fma, vec![er, di, product]);
    fb.store(f32, pb_ip, ip);
    let one = fb.iconst(Ty::I64, 1);
    let next = fb.binop(BinOp::Add, Ty::I64, iv, one);
    let more = fb.icmp(ICmpOp::Slt, Ty::I64, iv, j);
    fb.condbr(more, body, vec![next], exit, vec![]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();
}

fn module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("neon_butterfly_writeback");
    // Strict IEEE fused multiply-add: the object may not split it, so the C
    // oracle's `fmaf` is its exact meaning.
    let fma_ty = mb.add_func_type(vec![Ty::F32, Ty::F32, Ty::F32], vec![Ty::F32]);
    let fma = mb.declare_function("llvm.fma.f32", fma_ty);
    for kernel in KERNELS {
        build_butterfly(&mut mb, fma, kernel);
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `y[i] = a * y[i]` over a guarded i64 do-while: `neon_fmap` vectorizes it
/// at O2/O3 with an LD1/ST1 post-index remainder loop whose pointers are
/// recomputed by MADD, so its writebacks are dead. Compiled only for the
/// liveness walk's negative control.
fn fmap_control_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("neon_fmap_dead_writeback_control");
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::F32, Ty::I32], vec![]);
    let mut fb = mb.function(FMAP_CONTROL, ty);
    let entry = fb.create_block();
    let y = fb.add_block_param(entry, Ty::Ptr);
    let a = fb.add_block_param(entry, Ty::F32);
    let n = fb.add_block_param(entry, Ty::I32);
    let guard = fb.create_block();
    let body = fb.create_block();
    let iv = fb.add_block_param(body, Ty::I64);
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::I32, 0);
    let positive = fb.icmp(ICmpOp::Sgt, Ty::I32, n, zero);
    fb.condbr(positive, guard, vec![], exit, vec![]);
    fb.switch_to_block(guard);
    let start = fb.iconst(Ty::I64, 0);
    fb.br(body, vec![start]);
    fb.switch_to_block(body);
    let py = fb.gep(Ty::F32, y, vec![iv]);
    let old = fb.load(Ty::F32, py);
    let scaled = fb.binop(BinOp::FMul, Ty::F32, a, old);
    fb.store(Ty::F32, py, scaled);
    let one = fb.iconst(Ty::I64, 1);
    let next = fb.binop(BinOp::Add, Ty::I64, iv, one);
    let bound = fb.cast(CastOp::ZExt, Ty::I32, Ty::I64, n);
    let done = fb.icmp(ICmpOp::Eq, Ty::I64, next, bound);
    fb.condbr(done, exit, vec![], body, vec![next]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Compile `module` for `triple` through the public `Compiler`, optionally
/// with one pass disabled (the same-level scalar control). Serial compilation
/// keeps the thread-local environment edit in force.
fn compile(
    triple: &str,
    level: OptLevel,
    module: &trust_ir::Module,
    disable: Option<&str>,
) -> Vec<u8> {
    let spec = TargetSpec::parse(triple).expect("target triple");
    trust_cg_codegen::env_lock::with_env_edits(|env| {
        match disable {
            Some(pass) => env.set("TRUST_CG_DISABLE_PASSES", pass),
            None => env.remove("TRUST_CG_DISABLE_PASSES"),
        }
        let compiler = Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level: level,
                parallel: false,
                ..CompilerConfig::default()
            },
            spec,
        )
        .with_codegen_license(permit_unlicensed());
        // `llvm.fma.f32` is a bodyless declaration, an FFI boundary: the
        // module pins the triple it is compiled for (`TargetInfoRequired`;
        // WS7.3 ingestion admission).
        let object = compiler
            .compile(&pinned_target::pinned(module, triple))
            .unwrap_or_else(|error| panic!("{triple} {level:?}: {error:?}"))
            .object_code;
        assert!(!object.is_empty());
        object
    })
}

/// Opt-in retention for an evidence archive: with
/// `TRUST_CG_BUTTERFLY_RECORD_DIR` set, `contents` is written there as `name`.
/// Unset (as on the floors), it does nothing.
fn record(name: &str, contents: &[u8]) {
    if let Some(directory) = std::env::var_os("TRUST_CG_BUTTERFLY_RECORD_DIR") {
        let directory = std::path::PathBuf::from(directory);
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(directory.join(name), contents).unwrap();
    }
}

// ---------------------------------------------------------------------------
// Object reader (ELF64 and Mach-O 64, little-endian), independent of the
// crate's writers and parsers.
// ---------------------------------------------------------------------------

struct TextImage {
    /// File offset of the code section.
    offset: usize,
    words: Vec<u32>,
    /// Function name -> byte range within the code section.
    functions: BTreeMap<String, (usize, usize)>,
}

impl TextImage {
    /// Word-index range of function `name`.
    fn function(&self, name: &str) -> Result<(usize, usize), String> {
        let &(start, end) = self
            .functions
            .get(name)
            .ok_or_else(|| format!("no function symbol for {name}"))?;
        if !start.is_multiple_of(4) || !end.is_multiple_of(4) {
            return Err(format!(
                "{name}: range {start:#x}..{end:#x} is not word aligned"
            ));
        }
        Ok((start / 4, end / 4))
    }
}

fn bytes(object: &[u8], at: usize, len: usize) -> Result<&[u8], String> {
    at.checked_add(len)
        .and_then(|end| object.get(at..end))
        .ok_or_else(|| format!("object truncated at {at:#x}+{len}"))
}
fn u16_at(object: &[u8], at: usize) -> Result<u16, String> {
    Ok(u16::from_le_bytes(
        bytes(object, at, 2)?.try_into().unwrap(),
    ))
}
fn u32_at(object: &[u8], at: usize) -> Result<u32, String> {
    Ok(u32::from_le_bytes(
        bytes(object, at, 4)?.try_into().unwrap(),
    ))
}
fn u64_at(object: &[u8], at: usize) -> Result<usize, String> {
    usize::try_from(u64::from_le_bytes(
        bytes(object, at, 8)?.try_into().unwrap(),
    ))
    .map_err(|_| format!("64-bit field at {at:#x} does not fit"))
}
fn c_string(table: &[u8], at: usize) -> Result<String, String> {
    let rest = table
        .get(at..)
        .ok_or_else(|| format!("string offset {at:#x} outside its table"))?;
    let end = rest
        .iter()
        .position(|&byte| byte == 0)
        .ok_or("unterminated string")?;
    String::from_utf8(rest[..end].to_vec()).map_err(|error| error.to_string())
}

fn text_image(object: &[u8]) -> Result<TextImage, String> {
    let (offset, len, starts) = if object.starts_with(b"\x7fELF") {
        elf_text(object)?
    } else if object.starts_with(&0xfeed_facf_u32.to_le_bytes()) {
        macho_text(object)?
    } else {
        return Err("neither ELF nor Mach-O".into());
    };
    if len % 4 != 0 {
        return Err("code section is not word sized".into());
    }
    let words = bytes(object, offset, len)?
        .as_chunks::<4>()
        .0
        .iter()
        .map(|word| u32::from_le_bytes(*word))
        .collect();
    let mut sorted: Vec<(usize, Option<usize>, String)> = starts;
    sorted.sort();
    let mut functions = BTreeMap::new();
    for (index, (start, size, name)) in sorted.iter().enumerate() {
        let next = sorted
            .get(index + 1)
            .map_or(len, |(following, _, _)| *following);
        let end = size.map_or(next, |size| start + size);
        if *start > len || end > next || end < *start {
            return Err(format!("{name}: bad range {start:#x}..{end:#x}"));
        }
        if functions.insert(name.clone(), (*start, end)).is_some() {
            return Err(format!("duplicate function symbol {name}"));
        }
    }
    Ok(TextImage {
        offset,
        words,
        functions,
    })
}

/// `.text` file offset and size, and its STT_FUNC symbols (offset, size, name).
#[allow(clippy::type_complexity)]
fn elf_text(object: &[u8]) -> Result<(usize, usize, Vec<(usize, Option<usize>, String)>), String> {
    if bytes(object, 4, 2)? != b"\x02\x01" || u16_at(object, 18)? != 183 {
        return Err("not ELF64 little-endian AArch64".into());
    }
    let table = u64_at(object, 0x28)?;
    let entry = usize::from(u16_at(object, 0x3a)?);
    let count = usize::from(u16_at(object, 0x3c)?);
    let header = |index: usize| table + index * entry;
    let names_header = header(usize::from(u16_at(object, 0x3e)?));
    let names = bytes(
        object,
        u64_at(object, names_header + 0x18)?,
        u64_at(object, names_header + 0x20)?,
    )?;
    let mut text = None;
    let mut symtab = None;
    for index in 0..count {
        let at = header(index);
        let name = c_string(names, u32_at(object, at)? as usize)?;
        if name == ".text" && text.replace(index).is_some() {
            return Err("duplicate .text".into());
        }
        if u32_at(object, at + 4)? == 2 && symtab.replace(index).is_some() {
            return Err("duplicate SHT_SYMTAB".into());
        }
    }
    let text = text.ok_or("no .text")?;
    let symtab = symtab.ok_or("no SHT_SYMTAB")?;
    let text_at = header(text);
    let offset = u64_at(object, text_at + 0x18)?;
    let len = u64_at(object, text_at + 0x20)?;
    let sym_at = header(symtab);
    let strings_at = header(u32_at(object, sym_at + 0x28)? as usize);
    let strings = bytes(
        object,
        u64_at(object, strings_at + 0x18)?,
        u64_at(object, strings_at + 0x20)?,
    )?;
    let symbols = u64_at(object, sym_at + 0x18)?;
    let symbols_len = u64_at(object, sym_at + 0x20)?;
    let mut starts = Vec::new();
    for at in (symbols..symbols + symbols_len).step_by(24) {
        let kind = bytes(object, at + 4, 1)?[0] & 0xf;
        let section = usize::from(u16_at(object, at + 6)?);
        if kind != 2 || section != text {
            continue;
        }
        let size = u64_at(object, at + 16)?;
        starts.push((
            u64_at(object, at + 8)?,
            (size != 0).then_some(size),
            c_string(strings, u32_at(object, at)? as usize)?,
        ));
    }
    Ok((offset, len, starts))
}

/// `__TEXT,__text` file offset and size, and its external symbols with the C
/// `_` prefix removed (offset, no size, name).
#[allow(clippy::type_complexity)]
fn macho_text(
    object: &[u8],
) -> Result<(usize, usize, Vec<(usize, Option<usize>, String)>), String> {
    if u32_at(object, 4)? != 0x0100_000c || u32_at(object, 12)? != 1 {
        return Err("not an arm64 MH_OBJECT".into());
    }
    let commands = u32_at(object, 16)? as usize;
    let mut at = 32;
    let mut section_number = 0;
    let mut text = None;
    let mut symtab = None;
    for _ in 0..commands {
        let command = u32_at(object, at)?;
        let size = u32_at(object, at + 4)? as usize;
        if command == 0x19 {
            for index in 0..u32_at(object, at + 64)? as usize {
                section_number += 1;
                let section = at + 72 + index * 80;
                let name = c_string(bytes(object, section, 16)?, 0).unwrap_or_default();
                let segment = c_string(bytes(object, section + 16, 16)?, 0).unwrap_or_default();
                if name == "__text" && segment == "__TEXT" {
                    let found = (
                        section_number,
                        u64_at(object, section + 32)?,
                        u64_at(object, section + 40)?,
                        u32_at(object, section + 48)? as usize,
                    );
                    if text.replace(found).is_some() {
                        return Err("duplicate __text".into());
                    }
                }
            }
        } else if command == 0x2 {
            symtab = Some((
                u32_at(object, at + 8)? as usize,
                u32_at(object, at + 12)? as usize,
                u32_at(object, at + 16)? as usize,
                u32_at(object, at + 20)? as usize,
            ));
        }
        at += size.max(8);
    }
    let (number, address, len, offset) = text.ok_or("no __text")?;
    let (symbols, count, strings_at, strings_len) = symtab.ok_or("no LC_SYMTAB")?;
    let strings = bytes(object, strings_at, strings_len)?;
    let mut starts = Vec::new();
    for index in 0..count {
        let entry = symbols + index * 16;
        let kind = bytes(object, entry + 4, 1)?[0];
        let section = usize::from(bytes(object, entry + 5, 1)?[0]);
        // External (N_EXT), defined in a section (N_SECT), not a stab.
        if kind & 0xe0 != 0 || kind & 0x0e != 0x0e || kind & 1 == 0 || section != number {
            continue;
        }
        let name = c_string(strings, u32_at(object, entry)? as usize)?;
        let value = u64_at(object, entry + 8)?;
        let start = value
            .checked_sub(address)
            .ok_or_else(|| format!("{name} precedes __text"))?;
        starts.push((
            start,
            None,
            name.strip_prefix('_').unwrap_or(&name).to_owned(),
        ));
    }
    Ok((offset, len, starts))
}

// ---------------------------------------------------------------------------
// LD1/ST1 post-index census
// ---------------------------------------------------------------------------

/// A decoded LD1/ST1 (one register, immediate post-index) word.
#[derive(Clone, Debug)]
struct PostWord {
    /// Word index in the code section.
    index: usize,
    function: String,
    load: bool,
    rn: u8,
}

impl PostWord {
    fn mnemonic(&self) -> &'static str {
        if self.load { "LD1" } else { "ST1" }
    }
}

/// The independent bit-mask classifier: `0 Q 0011001 L 0 11111 0111 size Rn Rt`
/// (Advanced SIMD load/store multiple structures, post-indexed by the
/// immediate, one register).
fn mask_is_ld1_st1_post(word: u32) -> bool {
    word & 0xbfbf_f000 == 0x0c9f_7000
}

/// Classify every code word with both decoders and attribute each LD1/ST1
/// post-index word to its function. Refuses decoder disagreement, a word
/// outside every function symbol, and any arrangement other than `.4S`.
fn post_index_words(image: &TextImage) -> Result<Vec<PostWord>, String> {
    let mut found = Vec::new();
    for (index, &word) in image.words.iter().enumerate() {
        let lifted = decode(word);
        let lift_says = matches!(lifted, Ok(Instruction::NeonLdStSinglePostImm(_)));
        if lift_says != mask_is_ld1_st1_post(word) {
            return Err(format!(
                "decoders disagree on word {index} ({word:#010x}): lift={lifted:?}"
            ));
        }
        let Ok(Instruction::NeonLdStSinglePostImm(form)) = lifted else {
            continue;
        };
        let at = index * 4;
        let function = image
            .functions
            .iter()
            .find(|&(_, &(start, end))| (start..end).contains(&at))
            .map(|(name, _)| name.clone())
            .ok_or_else(|| format!("LD1/ST1 post-index word {index} is outside every function"))?;
        let mnemonic = if form.load { "LD1" } else { "ST1" };
        if !form.q || form.size != 0b10 {
            return Err(format!(
                "{function}: {mnemonic} word {word:#010x} has Q={} size={:#04b}, not .4S",
                u8::from(form.q),
                form.size
            ));
        }
        if form.rn == 31 {
            return Err(format!("{function}: {mnemonic} word {index} is SP-based"));
        }
        found.push(PostWord {
            index,
            function,
            load: form.load,
            rn: form.rn,
        });
    }
    Ok(found)
}

/// The decode gate for a vectorizing level: every butterfly kernel holds
/// exactly two LD1 and two ST1 post-index words on four distinct base
/// registers (one walking pointer per stream). Returns the words per kernel.
fn require_butterfly_forms(object: &[u8]) -> Result<BTreeMap<&'static str, Vec<PostWord>>, String> {
    let image = text_image(object)?;
    let words = post_index_words(&image)?;
    let mut per_kernel = BTreeMap::new();
    for kernel in KERNELS {
        image.function(kernel.name)?;
        let mine: Vec<PostWord> = words
            .iter()
            .filter(|word| word.function == kernel.name)
            .cloned()
            .collect();
        let loads = mine.iter().filter(|word| word.load).count();
        let stores = mine.len() - loads;
        if (loads, stores) != (2, 2) {
            return Err(format!(
                "{}: LD1/ST1 post-index census LD1={loads} ST1={stores}, expected 2 and 2",
                kernel.name
            ));
        }
        let mut bases: Vec<u8> = mine.iter().map(|word| word.rn).collect();
        bases.sort_unstable();
        bases.dedup();
        if bases.len() != 4 {
            return Err(format!(
                "{}: the four LD1/ST1 words share base registers {bases:?}",
                kernel.name
            ));
        }
        per_kernel.insert(kernel.name, mine);
    }
    if let Some(stray) = words
        .iter()
        .find(|word| !KERNELS.iter().any(|kernel| kernel.name == word.function))
    {
        return Err(format!(
            "LD1/ST1 word {} in {}",
            stray.index, stray.function
        ));
    }
    Ok(per_kernel)
}

fn with_word(object: &[u8], image: &TextImage, index: usize, word: u32) -> Vec<u8> {
    let mut mutated = object.to_vec();
    let at = image.offset + index * 4;
    mutated[at..at + 4].copy_from_slice(&word.to_le_bytes());
    mutated
}

/// Mutations that change the transfer: the 64-bit (Q=0) form, whose implied
/// post-index is also 8, and removal of the instruction.
fn transfer_mutants(word: u32) -> [(&'static str, u32); 2] {
    [("narrowed", word ^ (1 << 30)), ("removed", NOP)]
}

/// Mutations that keep the transfer and change only the base-register update:
/// no writeback (`[Xn]`: bit 23 and Rm cleared) and register post-index by
/// `stride` (`[Xn], Xs`), a register holding a constant other than 16.
fn writeback_mutants(word: u32, stride: u8) -> [(&'static str, u32); 2] {
    [
        ("no writeback", word & !(1 << 23) & !(0x1f << 16)),
        (
            "wrong-stride register post-index",
            (word & !(0x1f << 16)) | (u32::from(stride) << 16),
        ),
    ]
}

// ---------------------------------------------------------------------------
// General-register effects of decoded words, and the liveness walk
// ---------------------------------------------------------------------------

/// What one decoded word does to X0-X30 (register 31, SP or ZR, is never a
/// tracked register) and to control flow.
#[derive(Clone, Copy, Debug, Default)]
struct Effect {
    reads: u32,
    writes: u32,
    /// Base register of a load or store.
    base: Option<u8>,
    /// A flag-setting compare/test that discards its result (`CMP`, `CMN`,
    /// `TST`).
    compare: bool,
    flow: Flow,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
enum Flow {
    #[default]
    Next,
    /// Unconditional branch by a word delta.
    Jump(i64),
    /// Conditional branch by a word delta, or fall through.
    Either(i64),
    /// Return or trap: the path ends and no register is live afterwards.
    End,
}

fn bit(register: u8) -> u32 {
    if register < 31 { 1 << register } else { 0 }
}

fn sign_extend(value: u32, width: u32) -> i64 {
    let shift = 64 - width;
    (i64::from(value) << shift) >> shift
}

/// Words trust-cg-lift does not decode that name SIMD/FP registers only:
/// REV64 (Advanced SIMD two-register miscellaneous,
/// `0 Q 0 01110 size 10000 00000 10 Rn Rd`), vector FMLA (three-same FP,
/// `0 Q 0 01110 0 sz 1 Rm 11001 1 Rn Rd`) and scalar FMADD/FMSUB/FNMADD/FNMSUB
/// (FP data-processing, three source, `0 0 0 11111 ...`).
fn mask_is_simd_only(word: u32) -> bool {
    word & 0xbf3f_fc00 == 0x0e20_0800
        || word & 0xbfa0_fc00 == 0x0e20_cc00
        || word & 0xff00_0000 == 0x1f00_0000
}

/// The general-register and control-flow effect of `word`. Refuses (instead
/// of guessing) every family whose effect the walk does not model.
fn effect(word: u32) -> Result<Effect, String> {
    let mut effect = Effect::default();
    let load_store = |effect: &mut Effect, vector: bool, store: bool, rt: u8, rn: u8| {
        effect.reads |= bit(rn);
        effect.base = Some(rn);
        if !vector {
            if store {
                effect.reads |= bit(rt);
            } else {
                effect.writes |= bit(rt);
            }
        }
    };
    let instruction = match decode(word) {
        Ok(instruction) => instruction,
        Err(_) if mask_is_simd_only(word) => return Ok(effect),
        Err(error) => return Err(format!("{word:#010x}: {error}")),
    };
    match instruction {
        Instruction::AddSubShiftedReg(op) => {
            effect.reads = bit(op.rn) | bit(op.rm);
            effect.writes = bit(op.rd);
            effect.compare = op.set_flags && op.rd == 31;
        }
        Instruction::LogicalShiftedReg(op) => {
            effect.reads = bit(op.rn) | bit(op.rm);
            effect.writes = bit(op.rd);
            effect.compare = op.opc == 0b11 && op.rd == 31;
        }
        Instruction::LogicalImm(op) => {
            effect.reads = bit(op.rn);
            effect.writes = bit(op.rd);
            effect.compare = op.opc == 0b11 && op.rd == 31;
        }
        Instruction::AddSubImm(op) => {
            effect.reads = bit(op.rn);
            effect.writes = bit(op.rd);
            effect.compare = op.set_flags && op.rd == 31;
        }
        Instruction::AddSubCarry(op) => {
            effect.reads = bit(op.rn) | bit(op.rm);
            effect.writes = bit(op.rd);
        }
        Instruction::MoveWide(op) => {
            // MOVK keeps the other halfwords of Rd.
            if op.opc == 0b11 {
                effect.reads = bit(op.rd);
            }
            effect.writes = bit(op.rd);
        }
        Instruction::BitfieldMove(op) => {
            // BFM keeps the unselected bits of Rd.
            effect.reads = bit(op.rn) | if op.opc == 0b01 { bit(op.rd) } else { 0 };
            effect.writes = bit(op.rd);
        }
        Instruction::PcRelAddress(op) => effect.writes = bit(op.rd),
        Instruction::CondBranch(op) => effect.flow = Flow::Either(sign_extend(op.imm19, 19)),
        Instruction::UncondBranch(op) if !op.link => {
            effect.flow = Flow::Jump(sign_extend(op.imm26, 26));
        }
        // RET.
        Instruction::BranchReg(op) if op.opc == 0b10 => {
            effect.reads = bit(op.rn);
            effect.flow = Flow::End;
        }
        Instruction::TestBranch(op) => {
            effect.reads = bit(op.rt);
            effect.flow = Flow::Either(sign_extend(u32::from(op.imm14), 14));
        }
        Instruction::CompareBranch(op) => {
            effect.reads = bit(op.rt);
            effect.flow = Flow::Either(sign_extend(op.imm19, 19));
        }
        Instruction::LoadStoreUnsignedImm(op) => {
            if !op.vector && op.size == 0b11 && op.opc == 0b10 {
                return Err(format!("{word:#010x}: PRFM is not modelled"));
            }
            load_store(&mut effect, op.vector, op.opc == 0, op.rt, op.rn);
        }
        Instruction::LoadStoreUnscaled(op) => {
            if !op.vector && op.size == 0b11 && op.opc == 0b10 {
                return Err(format!("{word:#010x}: PRFUM is not modelled"));
            }
            load_store(&mut effect, op.vector, op.opc == 0, op.rt, op.rn);
        }
        Instruction::LoadStoreIndexed(op) => {
            load_store(&mut effect, op.vector, op.opc == 0, op.rt, op.rn);
            effect.writes |= bit(op.rn);
        }
        Instruction::LoadStoreRegister(op) => {
            if !op.vector && op.size == 0b11 && op.opc == 0b10 {
                return Err(format!("{word:#010x}: PRFM is not modelled"));
            }
            load_store(&mut effect, op.vector, op.opc == 0, op.rt, op.rn);
            effect.reads |= bit(op.rm);
        }
        Instruction::LoadLiteral(op) => {
            if !op.vector {
                if op.opc == 0b11 {
                    return Err(format!("{word:#010x}: PRFM literal is not modelled"));
                }
                effect.writes = bit(op.rt);
            }
        }
        Instruction::LoadStorePair(op) => {
            effect.reads = bit(op.rn);
            effect.base = Some(op.rn);
            if !op.vector {
                let pair = bit(op.rt) | bit(op.rt2);
                if op.load {
                    effect.writes |= pair;
                } else {
                    effect.reads |= pair;
                }
            }
            if op.mode != LoadStorePairAddressMode::SignedOffset {
                effect.writes |= bit(op.rn);
            }
        }
        Instruction::DataProcessing2Source(op) => {
            effect.reads = bit(op.rn) | bit(op.rm);
            effect.writes = bit(op.rd);
        }
        Instruction::DataProcessing3Source(op) => {
            effect.reads = bit(op.rn) | bit(op.rm) | bit(op.ra);
            effect.writes = bit(op.rd);
        }
        Instruction::ConditionalSelect(op) => {
            effect.reads = bit(op.rn) | bit(op.rm);
            effect.writes = bit(op.rd);
        }
        Instruction::FpArith(_)
        | Instruction::FpCompare(_)
        | Instruction::FpUnary(_)
        | Instruction::FpPrecisionConvert(_)
        | Instruction::FpImmediate(_)
        | Instruction::Nop
        | Instruction::NeonIntVec3Same(_)
        | Instruction::NeonVecLogic(_)
        | Instruction::NeonFpVec3Same(_)
        | Instruction::NeonVecNot(_)
        | Instruction::NeonAcrossLanes(_)
        | Instruction::NeonDupElement(_)
        | Instruction::NeonMoviByte(_) => {}
        Instruction::NeonDupGeneral(op) => effect.reads = bit(op.rn),
        Instruction::NeonInsGeneral(op) => effect.reads = bit(op.rn),
        Instruction::NeonLdStSinglePostImm(op) => {
            effect.reads = bit(op.rn);
            effect.writes = bit(op.rn);
            effect.base = Some(op.rn);
        }
        Instruction::Brk(_) => effect.flow = Flow::End,
        other => return Err(format!("{word:#010x}: {other:?} is not modelled")),
    }
    Ok(effect)
}

/// Successor word indices of word `at` inside the function `[start, end)`.
fn successors(
    effect: &Effect,
    at: usize,
    (start, end): (usize, usize),
) -> Result<Vec<usize>, String> {
    let target = |delta: i64| -> Result<usize, String> {
        let target = at as i64 + delta;
        if target < start as i64 || target >= end as i64 {
            return Err(format!(
                "branch at word {at} leaves the function (to {target})"
            ));
        }
        Ok(target as usize)
    };
    let next = || -> Result<usize, String> {
        if at + 1 >= end {
            return Err(format!("word {at} falls off the end of the function"));
        }
        Ok(at + 1)
    };
    Ok(match effect.flow {
        Flow::Next => vec![next()?],
        Flow::Jump(delta) => vec![target(delta)?],
        Flow::Either(delta) => vec![target(delta)?, next()?],
        Flow::End => vec![],
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Liveness {
    /// The updated register is read by word `reader` on a path that takes the
    /// backward branch at word `back_edge` (if any) and on which no word
    /// between the writeback and `reader` writes it.
    Live {
        reader: usize,
        back_edge: Option<usize>,
        /// How `reader` reads it: as a load/store base or in a compare.
        as_base: bool,
    },
    /// Every path redefines the register or ends before reading it.
    Dead,
}

/// Is the value that word `at` leaves in `register` read later? Breadth-first
/// over the decoded control flow of `function`: a path stops at the first
/// word that reads the register (live) or writes it (killed) or ends.
fn writeback_liveness(
    words: &[u32],
    function: (usize, usize),
    at: usize,
    register: u8,
) -> Result<Liveness, String> {
    let wanted = bit(register);
    if wanted == 0 {
        return Err("SP/ZR is not a tracked register".into());
    }
    let mut parent: BTreeMap<usize, usize> = BTreeMap::new();
    let mut queue = VecDeque::new();
    for successor in successors(&effect(words[at])?, at, function)? {
        parent.entry(successor).or_insert(at);
        queue.push_back(successor);
    }
    let mut seen = std::collections::BTreeSet::new();
    while let Some(index) = queue.pop_front() {
        if !seen.insert(index) {
            continue;
        }
        let here = effect(words[index])?;
        if here.reads & wanted != 0 {
            let as_base = here.base == Some(register);
            if !as_base && !here.compare {
                return Err(format!(
                    "word {index} ({:#010x}) reads the register but is neither a load/store base \
                     nor a compare",
                    words[index]
                ));
            }
            // Walk the parent chain back to `at` (the reader may be `at`
            // itself, reached again through the loop) for the backward branch
            // nearest to the writeback.
            let mut back_edge = None;
            let mut node = index;
            loop {
                let from = parent[&node];
                if node <= from {
                    back_edge = Some(from);
                }
                if from == at {
                    break;
                }
                node = from;
            }
            return Ok(Liveness::Live {
                reader: index,
                back_edge,
                as_base,
            });
        }
        if here.writes & wanted != 0 {
            continue;
        }
        for successor in successors(&here, index, function)? {
            if !seen.contains(&successor) {
                parent.entry(successor).or_insert(index);
                queue.push_back(successor);
            }
        }
    }
    Ok(Liveness::Dead)
}

/// A register that provably holds the same constant (other than 0 and 16) at
/// every entry to word `loop_top`: its only definitions reaching the loop are
/// one `MOVZ`, found by a must-dataflow over the decoded control flow.
/// Returns the register and its value, preferring 8.
fn constant_stride_register(
    words: &[u32],
    function: (usize, usize),
    loop_top: usize,
) -> Result<Option<(u8, u64)>, String> {
    let (start, _) = function;
    // Only words reachable from the entry take part (alignment padding after
    // the return is not code the function runs).
    let mut effects: BTreeMap<usize, Effect> = BTreeMap::new();
    let mut predecessors: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    let mut queue = VecDeque::from([start]);
    while let Some(index) = queue.pop_front() {
        if effects.contains_key(&index) {
            continue;
        }
        let here = effect(words[index])?;
        for successor in successors(&here, index, function)? {
            predecessors.entry(successor).or_default().push(index);
            queue.push_back(successor);
        }
        effects.insert(index, here);
    }
    if !effects.contains_key(&loop_top) {
        return Err(format!("loop top word {loop_top} is unreachable"));
    }
    let mut candidates = Vec::new();
    for &index in effects.keys() {
        let Ok(Instruction::MoveWide(op)) = decode(words[index]) else {
            continue;
        };
        let value = u64::from(op.imm16) << (16 * u32::from(op.hw));
        if op.opc != 0b10 || op.sf != 1 || op.rd >= 31 || value == 0 || value == 16 {
            continue;
        }
        // Must-dataflow from the optimistic start: known[i] = the register
        // holds `value` on entry to reachable word i. The entry knows nothing.
        let register = op.rd;
        let mut known: BTreeMap<usize, bool> = effects.keys().map(|&i| (i, i != start)).collect();
        let out = |known: &BTreeMap<usize, bool>, i: usize| -> bool {
            if i == index {
                true
            } else if effects[&i].writes & bit(register) != 0 {
                false
            } else {
                known[&i]
            }
        };
        loop {
            let mut changed = false;
            for &i in effects.keys() {
                if i == start || !known[&i] {
                    continue;
                }
                if !predecessors[&i].iter().all(|&p| out(&known, p)) {
                    known.insert(i, false);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        if known[&loop_top] {
            candidates.push((register, value));
        }
    }
    candidates.sort_by_key(|&(register, value)| (value != 8, register));
    Ok(candidates.first().copied())
}

/// One kernel's liveness report at a vectorizing level.
struct KernelLiveness {
    kernel: &'static str,
    /// (post word, reader, back edge) per LD1/ST1.
    words: Vec<(PostWord, usize, usize)>,
    /// The first word of the vector loop (every writeback's reader).
    loop_top: usize,
    stride: (u8, u64),
}

/// The liveness gate: every butterfly LD1/ST1 writeback is read as the base
/// of the same word on the next iteration, on a path through the loop's
/// backward branch with no redefinition, and a register holds a wrong
/// constant stride at the loop top.
fn require_live_writebacks(object: &[u8]) -> Result<Vec<KernelLiveness>, String> {
    let per_kernel = require_butterfly_forms(object)?;
    let image = text_image(object)?;
    let mut reports = Vec::new();
    for kernel in KERNELS {
        let function = image.function(kernel.name)?;
        let mut words = Vec::new();
        for word in &per_kernel[kernel.name] {
            match writeback_liveness(&image.words, function, word.index, word.rn)? {
                // The same LD1/ST1 reads it as its base on the next iteration.
                Liveness::Live {
                    reader,
                    back_edge: Some(back_edge),
                    as_base: true,
                } if reader == word.index => words.push((word.clone(), reader, back_edge)),
                other => {
                    return Err(format!(
                        "{}: {} writeback of x{} at word {} is not loop-carried live: {other:?}",
                        kernel.name,
                        word.mnemonic(),
                        word.rn,
                        word.index
                    ));
                }
            }
        }
        let loop_top = words.iter().map(|(_, reader, _)| *reader).min().unwrap();
        let stride = constant_stride_register(&image.words, function, loop_top)?
            .ok_or_else(|| format!("{}: no register holds a wrong constant stride", kernel.name))?;
        reports.push(KernelLiveness {
            kernel: kernel.name,
            words,
            loop_top,
            stride,
        });
    }
    Ok(reports)
}

fn liveness_report(triple: &str, level: OptLevel, reports: &[KernelLiveness]) -> String {
    let mut text = String::new();
    for report in reports {
        for (word, reader, back_edge) in &report.words {
            text.push_str(&format!(
                "{triple}\t{level:?}\t{}\t{}\tword {}\tx{}\tread as base by word {reader} via \
                 backward branch at word {back_edge}\n",
                report.kernel,
                word.mnemonic(),
                word.index,
                word.rn
            ));
        }
        text.push_str(&format!(
            "{triple}\t{level:?}\t{}\tloop top word {}\tx{} holds {} at every loop entry\n",
            report.kernel, report.loop_top, report.stride.0, report.stride.1
        ));
    }
    text
}

// ---------------------------------------------------------------------------
// Host-neutral object controls (both containers, every host)
// ---------------------------------------------------------------------------

#[test]
fn vectorizing_levels_emit_live_ld1_st1_post_index_writebacks() {
    let butterflies = module();
    let control = fmap_control_module();
    for triple in [LINUX, DARWIN] {
        for level in LEVELS {
            let object = compile(triple, level, &butterflies, None);
            record(&format!("{triple}-{level:?}.o"), &object);
            let image = text_image(&object).unwrap();
            assert_eq!(image.words, native_host::text_words(&object), "{triple}");
            let words = post_index_words(&image)
                .unwrap_or_else(|error| panic!("{triple} {level:?}: {error}"));
            if VECTOR_LEVELS.contains(&level) {
                let reports = require_live_writebacks(&object)
                    .unwrap_or_else(|error| panic!("{triple} {level:?}: {error}"));
                let report = liveness_report(triple, level, &reports);
                record(
                    &format!("liveness-{triple}-{level:?}.tsv"),
                    report.as_bytes(),
                );
                print!("{report}");
                println!(
                    "NEON_BUTTERFLY_WRITEBACK_OBJECT {triple} {level:?}: {} code words, LD1 post=6 \
                     ST1 post=6 in 3/3 kernels on 4 distinct walking pointers each, both decoders \
                     agree; 12/12 writebacks read as a base on the next iteration before any \
                     redefinition",
                    image.words.len()
                );
                // Negative control: the same walk calls `neon_fmap`'s
                // remainder-loop writebacks dead (MADD recomputes them).
                let fmap = compile(triple, level, &control, None);
                record(&format!("fmap-control-{triple}-{level:?}.o"), &fmap);
                let fmap_image = text_image(&fmap).unwrap();
                let fmap_words = post_index_words(&fmap_image).unwrap();
                let function = fmap_image.function(FMAP_CONTROL).unwrap();
                assert_eq!(
                    (
                        fmap_words.iter().filter(|word| word.load).count(),
                        fmap_words.iter().filter(|word| !word.load).count()
                    ),
                    (1, 1),
                    "{triple} {level:?}: {fmap_words:?}"
                );
                for word in &fmap_words {
                    let liveness =
                        writeback_liveness(&fmap_image.words, function, word.index, word.rn)
                            .unwrap();
                    assert_eq!(liveness, Liveness::Dead, "{triple} {level:?} {word:?}");
                }
                println!(
                    "NEON_BUTTERFLY_WRITEBACK_CONTROL {triple} {level:?}: the walk reports both \
                     neon_fmap remainder LD1/ST1 writebacks dead"
                );
            } else {
                // O0/O1 schedule no NEON pass: scalar-only, refused.
                assert!(words.is_empty(), "{triple} {level:?}: {words:?}");
                let refusal = require_butterfly_forms(&object)
                    .expect_err("a scalar-only object must be refused");
                println!(
                    "NEON_BUTTERFLY_WRITEBACK_OBJECT {triple} {level:?}: scalar-only, refused: \
                     {refusal}"
                );
            }
        }
    }
}

#[test]
fn decode_and_liveness_gates_refuse_scalar_and_mutated_objects() {
    let butterflies = module();
    for triple in [LINUX, DARWIN] {
        // Same level with the pass disabled: scalar-only, refused.
        let scalar = compile(triple, OptLevel::O2, &butterflies, Some("neon_butterfly"));
        record(&format!("{triple}-O2-without-neon_butterfly.o"), &scalar);
        assert!(
            post_index_words(&text_image(&scalar).unwrap())
                .unwrap()
                .is_empty()
        );
        let refusal = require_butterfly_forms(&scalar).expect_err("neon_butterfly disabled");
        println!("NEON_BUTTERFLY_WRITEBACK_REFUSAL {triple} O2 without neon_butterfly: {refusal}");

        let object = compile(triple, OptLevel::O2, &butterflies, None);
        let image = text_image(&object).unwrap();
        let reports = require_live_writebacks(&object).unwrap();
        let mut refused = 0;
        for report in &reports {
            for (word, _, _) in &report.words {
                let original = image.words[word.index];
                for (label, mutated) in transfer_mutants(original)
                    .into_iter()
                    .chain(writeback_mutants(original, report.stride.0))
                {
                    let mutant = with_word(&object, &image, word.index, mutated);
                    let error = require_butterfly_forms(&mutant).expect_err(label);
                    assert!(error.contains(report.kernel), "{label}: {error}");
                    refused += 1;
                }
            }
        }
        assert_eq!(refused, 48);
        // Removing each kernel's backward branch leaves the four LD1/ST1
        // words intact, so the census still accepts the object, but no
        // writeback is read again: the liveness gate must refuse it.
        let mut dead = 0;
        for report in &reports {
            let back_edges: Vec<usize> = report.words.iter().map(|(_, _, edge)| *edge).collect();
            assert!(
                back_edges.windows(2).all(|pair| pair[0] == pair[1]),
                "{back_edges:?}"
            );
            let mutant = with_word(&object, &image, back_edges[0], NOP);
            require_butterfly_forms(&mutant).expect("the LD1/ST1 words are intact");
            let error = match require_live_writebacks(&mutant) {
                Err(error) => error,
                Ok(_) => panic!("{triple} {}: back edge removed but accepted", report.kernel),
            };
            assert!(error.contains(report.kernel), "{error}");
            let function = image.function(report.kernel).unwrap();
            let mutated = text_image(&mutant).unwrap();
            for (word, _, _) in &report.words {
                assert_eq!(
                    writeback_liveness(&mutated.words, function, word.index, word.rn).unwrap(),
                    Liveness::Dead,
                    "{triple} {} {word:?}",
                    report.kernel
                );
                dead += 1;
            }
        }
        assert_eq!(dead, 12);
        println!(
            "NEON_BUTTERFLY_WRITEBACK_REFUSAL {triple} O2: {refused}/48 mutated LD1/ST1 words \
             refused (narrowed, removed, no writeback, wrong-stride register post-index); \
             backward branch removed in 3/3 kernels: census accepts, liveness gate refuses, \
             {dead}/12 writebacks dead"
        );
    }
}

// ---------------------------------------------------------------------------
// Native execution against the C oracle
// ---------------------------------------------------------------------------

/// Trip counts `n = j - i0 + 1` run from each start `i0` (0, 1, 3): the
/// do-while's single iteration for `n <= 1`, every pair count up to twenty
/// with and without the odd scalar tail, and longer runs.
#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
fn counts() -> Vec<i64> {
    let mut counts: Vec<i64> = (-2..=40).collect();
    counts.extend([63, 64, 65, 127, 128, 129, 255, 256, 257, 300, 301]);
    counts
}

/// The C oracle. See the module header; `@COUNTS@` and `@LAYOUTS@` are filled
/// in from the Rust side. With an argument naming a kernel only that kernel
/// runs. Every call ends with a bit-for-bit comparison of the whole buffer.
/// Exit 0: no mismatch; 1: a mismatch; 2: usage or placement error.
#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
const DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef void (*kernel_fn)(const float *, float *, const float *, int64_t, int64_t,
                          int64_t, int64_t, int64_t);
#define DECLARE(N) extern void N(const float *, float *, const float *, int64_t, int64_t, \
                                 int64_t, int64_t, int64_t);
DECLARE(bfly_nested_e0) DECLARE(bfly_nested_e8) DECLARE(bfly_hoisted_e8)
struct kernel { const char *name; kernel_fn f; long e_off; };
static const struct kernel kernels[] = {
    {"bfly_nested_e0", bfly_nested_e0, 0},
    {"bfly_nested_e8", bfly_nested_e8, 8},
    {"bfly_hoisted_e8", bfly_hoisted_e8, 8},
};

/* Complex elements (8 bytes). Every stream fits in one region's payload. */
#define CAP 320
#define GUARD 8
#define REGION (CAP + 2 * GUARD)
#define REGIONS 6
#define ELEMENTS (REGIONS * REGION)
#define FLOATS (2 * ELEMENTS)
#define LAYOUTS @LAYOUTS@
#define K 3
#define P(r) ((long)(r) * REGION + GUARD)

static float buf[FLOATS] __attribute__((aligned(16)));
static float ref[FLOATS] __attribute__((aligned(16)));

#define F(address) (*(float *)(uintptr_t)(address))

/* One scalar A64 instruction per operation, operands in the loop's order. C
   compilers may commute the operands of `*`, `+` and fmaf's multiplicands,
   which changes which NaN propagates once FNEG has produced a NaN of the
   opposite sign; the asm pins the order. */
#define OP2(name, insn)                                                        \
    static float name(float a, float b) {                                      \
        float r;                                                               \
        __asm__ volatile(insn " %s0, %s1, %s2" : "=w"(r) : "w"(a), "w"(b));    \
        return r;                                                              \
    }
OP2(fadd_, "fadd") OP2(fsub_, "fsub") OP2(fmul_, "fmul")
static float fneg_(float a) {
    float r;
    __asm__ volatile("fneg %s0, %s1" : "=w"(r) : "w"(a));
    return r;
}
/* n * m + a with one rounding (FMADD Sd, Sn, Sm, Sa). */
static float fmadd_(float n, float m, float a) {
    float r;
    __asm__ volatile("fmadd %s0, %s1, %s2, %s3" : "=w"(r) : "w"(n), "w"(m), "w"(a));
    return r;
}

/* The trust-ir loop as written: a do-while from i0 that runs while the old i
   is below j; each statement reloads its operands after the previous store;
   one rounding per operation and one fused multiply-add per B field. */
static void reference(uintptr_t z, uintptr_t w, uintptr_t e, int64_t m, int64_t k,
                      int64_t kb, int64_t i0, int64_t j) {
    int64_t i = i0;
    for (;;) {
        uintptr_t pz = z + (uint64_t)i * 8, pzm = pz + (uint64_t)m * 8;
        uintptr_t pw = w + (uint64_t)i * 8;
        uintptr_t pa = pw + (uint64_t)k * 8, pb = pw + (uint64_t)kb * 8;
        float dr, di;
        F(pa) = fadd_(F(pz), F(pzm));
        F(pa + 4) = fadd_(F(pz + 4), F(pzm + 4));
        dr = fsub_(F(pz), F(pzm));
        di = fsub_(F(pz + 4), F(pzm + 4));
        F(pb) = fmadd_(F(e), dr, fmul_(F(e + 4), fneg_(di)));
        di = fsub_(F(pz + 4), F(pzm + 4));
        dr = fsub_(F(pz), F(pzm));
        F(pb + 4) = fmadd_(F(e), di, fmul_(F(e + 4), dr));
        if (!(i < j)) break;
        i = i + 1;
    }
}

/* Stream starts (complex indices) and the twiddle cell (a float index) for
   trip count t. 0-11 are admitted by the pass's seven-pair check (reads may
   overlap each other and the twiddle); 12-18 overlap a store range with a
   read range, the other store range or the twiddle cell. */
struct place { long s1, s2, a, b, ef; };
static int place(int layout, long t, struct place *p) {
    p->s1 = P(0); p->s2 = P(1); p->a = P(2); p->b = P(3); p->ef = 2 * P(4);
    switch (layout) {
    case 0: break;                                              /* disjoint */
    case 1: p->a = P(1); p->b = P(2); p->s2 = P(3); p->s1 = P(4);
            p->ef = 2 * P(1) - 2; break;          /* reversed; E touches A */
    case 2: p->s2 = p->s1 + 1; break;                           /* m = 1 */
    case 3: p->s2 = p->s1; break;                               /* m = 0 */
    case 4: p->s1 = P(0) + 1; p->s2 = P(0); break;              /* m = -1 */
    case 5: p->b = p->a + t; p->ef = 2 * P(5); break;           /* B after A */
    case 6: p->b = P(2); p->a = p->b + t; p->ef = 2 * P(5); break; /* A after B */
    case 7: p->a = p->s1 + t; p->s2 = P(4); p->b = p->s2 - t;
            p->ef = 2 * P(5); break;           /* A after S1, B before S2 */
    case 8: p->b = P(4); p->ef = 2 * (p->a + t); p->s2 = P(1); break; /* E after A */
    case 9: p->ef = 2 * p->b - 2; break;                        /* E before B */
    case 10: p->ef = 2 * (p->s1 + t / 2); break;                /* E inside S1 */
    case 11: p->ef = 2 * P(4) + 1; break;                  /* E straddles two */
    case 12: p->a = p->s1 + t - 1; p->ef = 2 * P(5); break; /* A over S1's last */
    case 13: p->s2 = p->s1 + t; p->a = p->s1; p->b = p->s2; break; /* in place */
    case 14: p->b = p->a + t - 1; p->ef = 2 * P(5); break;   /* B over A's last */
    case 15: p->ef = 2 * (p->a + (t - 1) / 2); break;           /* E inside A */
    case 16: p->ef = 2 * (p->b + t) - 1; break;       /* E over B's last word */
    case 17: p->s2 = P(3); p->a = p->s2 - t + 1; p->b = P(4);
             p->ef = 2 * P(5); break;                   /* A over S2's first */
    case 18: p->b = p->s1; break;                               /* B = S1 */
    default: return -1;
    }
    long streams[4] = {p->s1, p->s2, p->a, p->b};
    for (int s = 0; s < 4; ++s)
        if (streams[s] < 1 || streams[s] + t > ELEMENTS - 1) return -1;
    if (p->ef < 2 || p->ef + 2 > FLOATS - 2) return -1;
    return 0;
}

static int disjoint(uintptr_t x, uint64_t lx, uintptr_t y, uint64_t ly) {
    return x + lx <= y || y + ly <= x;
}

/* The pass's documented vector-path condition: 0 <= i0 < j < 2^31 and the
   two store ranges disjoint from both read ranges, from the 8-byte twiddle
   cell and from each other. 0: scalar path; else the number of vector
   pairs. */
static int64_t vector_pairs(int64_t i0, int64_t j, const struct place *p) {
    if (i0 < 0 || j < 0 || j >= (1LL << 31) || i0 >= j) return 0;
    uint64_t len = (uint64_t)(j - i0 + 1) * 8;
    uintptr_t base = (uintptr_t)buf;
    uintptr_t s1 = base + p->s1 * 8, s2 = base + p->s2 * 8, a = base + p->a * 8,
              b = base + p->b * 8, e = base + p->ef * 4;
    if (!(disjoint(a, len, s1, len) && disjoint(a, len, s2, len) && disjoint(a, len, e, 8) &&
          disjoint(b, len, s1, len) && disjoint(b, len, s2, len) && disjoint(b, len, e, 8) &&
          disjoint(a, len, b, len)))
        return 0;
    return (j - i0 + 1) / 2;
}

static const int64_t counts[] = {@COUNTS@};
static const int64_t starts[] = {0, 1, 3};
/* (i0, j) pairs at the magnitude gates: negative starts and bounds at or
   above 2^31 take the scalar loop; the largest admitted range is vector. */
static const int64_t specials[][2] = {
    {-2, 5}, {-(1LL << 40), -(1LL << 40) + 5}, {(1LL << 31) - 8, (1LL << 31) - 1},
    {(1LL << 31) - 7, (1LL << 31) - 1}, {(1LL << 31) - 1, (1LL << 31) + 4},
    {1LL << 31, (1LL << 31) + 3}, {1LL << 40, (1LL << 40) + 5},
};
static const uint32_t specials32[] = {
    0x00000000u, 0x80000000u, 0x7f800000u, 0xff800000u, 0x00000001u, 0x007fffffu,
    0x00800000u, 0x7f7fffffu, 0x3f800000u, 0xbfc00000u, 0x7fc00000u, 0x3eaaaaabu,
};

static uint64_t state;
static uint64_t next(void) {
    state = state * 6364136223846793005ull + 1442695040888963407ull;
    return state ^ (state >> 29);
}
/* 0: finite normals of mixed sign and magnitude; 1: IEEE specials with the
   default NaN; 2: raw bit patterns, every NaN replaced by one signaling NaN. */
static uint32_t bits32(int pattern) {
    uint64_t r = next();
    if (pattern == 0)
        return (uint32_t)(r & 1) << 31 | (uint32_t)(103 + (r >> 1) % 49) << 23 |
               ((uint32_t)(r >> 9) & 0x7fffffu);
    if (pattern == 1) return specials32[(r >> 7) % 12];
    uint32_t v = (uint32_t)(r >> 17);
    if ((v & 0x7f800000u) == 0x7f800000u && (v & 0x7fffffu)) v = 0x7f80beefu;
    return v;
}

int main(int argc, char **argv) {
    const char *only = argc > 1 ? argv[1] : 0;
    int ran = 0, failed = 0;
    const int count_n = (int)(sizeof counts / sizeof *counts);
    const int start_n = (int)(sizeof starts / sizeof *starts);
    const int special_n = (int)(sizeof specials / sizeof *specials);
    for (unsigned kn = 0; kn < sizeof kernels / sizeof *kernels; ++kn) {
        const struct kernel *kernel = &kernels[kn];
        if (only && strcmp(only, kernel->name)) continue;
        ++ran;
        /* calls, then per class (scalar, one vector pair, two or more pairs):
           calls and mismatching calls. */
        unsigned long long calls = 0, mismatched = 0, pairs = 0, tails = 0;
        unsigned long long cls[3] = {0, 0, 0}, bad[3] = {0, 0, 0};
        unsigned long long multi_p0 = 0, bad_multi_p0 = 0;
        int printed = 0;
        for (int pattern = 0; pattern < 3; ++pattern)
        for (int layout = 0; layout < LAYOUTS; ++layout)
        for (int c = 0; c < start_n * count_n + special_n; ++c) {
            int64_t i0, j;
            if (c < start_n * count_n) {
                i0 = starts[c / count_n];
                j = i0 + counts[c % count_n] - 1;
            } else {
                i0 = specials[c - start_n * count_n][0];
                j = specials[c - start_n * count_n][1];
            }
            long t = j >= i0 ? (long)(j - i0 + 1) : 1;
            struct place p;
            if (t > CAP || place(layout, t, &p)) {
                printf("PLACEMENT ERROR layout=%d t=%ld\n", layout, t);
                return 2;
            }
            state = 0x9e3779b97f4a7c15ull ^ ((uint64_t)kn << 56) ^ ((uint64_t)pattern << 48) ^
                    ((uint64_t)layout << 32) ^ (uint64_t)c;
            for (long i = 0; i < FLOATS; ++i) {
                uint32_t v = bits32(pattern);
                memcpy(&buf[i], &v, sizeof v);
            }
            memcpy(ref, buf, sizeof buf);
            int64_t m = p.s2 - p.s1, kb = p.b - p.a + K;
            uintptr_t B = (uintptr_t)buf, R = (uintptr_t)ref;
            uint64_t z = (uint64_t)(p.s1 - i0) * 8, w = (uint64_t)(p.a - i0 - K) * 8;
            uint64_t e = (uint64_t)p.ef * 4;
            kernel->f((const float *)(B + z), (float *)(B + w),
                      (const float *)(B + e - kernel->e_off), m, K, kb, i0, j);
            reference(R + z, R + w, R + e, m, K, kb, i0, j);
            int64_t vp = vector_pairs(i0, j, &p);
            int klass = vp == 0 ? 0 : vp == 1 ? 1 : 2;
            ++calls;
            ++cls[klass];
            pairs += (unsigned long long)vp;
            tails += vp && (j - i0 + 1) % 2;
            if (klass == 2 && pattern == 0) ++multi_p0;
            if (memcmp(buf, ref, sizeof buf)) {
                long at = 0;
                while (!memcmp(&buf[at], &ref[at], sizeof *buf)) ++at;
                ++mismatched;
                ++bad[klass];
                if (klass == 2 && pattern == 0) ++bad_multi_p0;
                if (!printed++) {
                    uint32_t got, want;
                    memcpy(&got, &buf[at], 4);
                    memcpy(&want, &ref[at], 4);
                    printf("MISMATCH %s pattern=%d layout=%d i0=%lld j=%lld class=%d float=%ld "
                           "got=%08x want=%08x\n", kernel->name, pattern, layout, (long long)i0,
                           (long long)j, klass, at, got, want);
                }
            }
        }
        printf("BUTTERFLY kernel=%s calls=%llu scalar=%llu vec_single=%llu vec_multi=%llu "
               "vector_pairs=%llu scalar_tails=%llu multi_p0=%llu mismatched=%llu "
               "mismatched_scalar=%llu mismatched_vec_single=%llu mismatched_vec_multi=%llu "
               "mismatched_multi_p0=%llu\n", kernel->name, calls, cls[0], cls[1], cls[2], pairs,
               tails, multi_p0, mismatched, bad[0], bad[1], bad[2], bad_multi_p0);
        failed |= mismatched != 0;
    }
    if (!ran) {
        printf("NO KERNEL %s\n", only);
        return 2;
    }
    return failed;
}
"#;

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
mod native {
    use std::path::{Path, PathBuf};
    use std::process::Command;
    use std::time::Duration;

    use super::*;

    /// Placements in `DRIVER`'s `place` (0-11 admitted, 12-18 overlapping).
    pub(super) const LAYOUTS: usize = 19;
    const PATTERNS: usize = 3;
    const STARTS: usize = 3;
    const SPECIALS: usize = 7;

    pub(super) fn driver_source() -> String {
        let counts: Vec<String> = counts().iter().map(i64::to_string).collect();
        DRIVER
            .replace("@COUNTS@", &counts.join(","))
            .replace("@LAYOUTS@", &LAYOUTS.to_string())
    }

    /// Calls the driver makes per kernel.
    pub(super) fn calls_per_kernel() -> u64 {
        (PATTERNS * LAYOUTS * (STARTS * counts().len() + SPECIALS)) as u64
    }

    /// `cc` with FP contraction off (the oracle's arithmetic is inline asm).
    fn cc() -> Command {
        let mut command = Command::new(native_host::C_COMPILER);
        command.arg("-O0").arg("-ffp-contract=off");
        command
    }

    fn checked(command: &mut Command, what: &str) {
        let result = process::command_output_with_timeout(command, Duration::from_secs(60))
            .unwrap_or_else(|error| panic!("{what}: {error}"));
        assert!(
            !result.timed_out && result.output.status.success(),
            "{what}: {:?}",
            result.output
        );
    }

    pub(super) struct Harness {
        pub(super) directory: tempfile::TempDir,
        driver: PathBuf,
    }

    impl Harness {
        pub(super) fn new() -> Self {
            let directory = tempfile::Builder::new()
                .prefix("trust-cg-butterfly-")
                .tempdir()
                .unwrap();
            let source = directory.path().join("driver.c");
            let driver = directory.path().join("driver.o");
            std::fs::write(&source, driver_source()).unwrap();
            record("driver.c", driver_source().as_bytes());
            checked(
                cc().arg("-c").arg(&source).arg("-o").arg(&driver),
                "compile the C oracle",
            );
            Self { directory, driver }
        }

        pub(super) fn link(&self, object: &[u8], tag: &str) -> PathBuf {
            let path = self.directory.path().join(format!("{tag}.o"));
            let executable = self.directory.path().join(tag);
            std::fs::write(&path, object).unwrap();
            checked(
                cc().arg(&self.driver)
                    .arg(&path)
                    .args(native_host::link_hardening_args())
                    .arg("-o")
                    .arg(&executable),
                &format!("link {tag}"),
            );
            executable
        }
    }

    /// One `BUTTERFLY kernel=...` summary line.
    #[derive(Clone, Debug, Default, PartialEq, Eq)]
    pub(super) struct Summary {
        pub(super) fields: BTreeMap<String, u64>,
    }

    impl Summary {
        pub(super) fn get(&self, key: &str) -> u64 {
            *self
                .fields
                .get(key)
                .unwrap_or_else(|| panic!("summary has no {key}: {self:?}"))
        }

        /// The path-class counts, which depend only on the placements.
        pub(super) fn classes(&self) -> [u64; 6] {
            [
                self.get("calls"),
                self.get("scalar"),
                self.get("vec_single"),
                self.get("vec_multi"),
                self.get("vector_pairs"),
                self.get("scalar_tails"),
            ]
        }
    }

    pub(super) struct Run {
        pub(super) status: Option<i32>,
        pub(super) timed_out: bool,
        pub(super) stdout: String,
        pub(super) summaries: BTreeMap<String, Summary>,
        pub(super) mismatch_lines: Vec<String>,
    }

    pub(super) fn run(executable: &Path, only: Option<&str>) -> Run {
        let mut command = Command::new(executable);
        if let Some(kernel) = only {
            command.arg(kernel);
        }
        let result = process::command_output_with_timeout(
            &mut command,
            process::exec_timeout(Duration::from_secs(60)),
        )
        .unwrap();
        let stdout = String::from_utf8_lossy(&result.output.stdout).into_owned();
        let mut summaries = BTreeMap::new();
        let mut mismatch_lines = Vec::new();
        for line in stdout.lines() {
            if line.starts_with("MISMATCH ") {
                mismatch_lines.push(line.to_owned());
                continue;
            }
            let Some(rest) = line.strip_prefix("BUTTERFLY ") else {
                panic!("unexpected driver line: {line}");
            };
            let mut kernel = None;
            let mut fields = BTreeMap::new();
            for pair in rest.split(' ') {
                let (key, value) = pair.split_once('=').expect("key=value");
                if key == "kernel" {
                    kernel = Some(value.to_owned());
                } else {
                    fields.insert(key.to_owned(), value.parse().expect("count"));
                }
            }
            summaries.insert(kernel.expect("kernel name"), Summary { fields });
        }
        Run {
            status: result.output.status.code(),
            timed_out: result.timed_out,
            stdout,
            summaries,
            mismatch_lines,
        }
    }
}

/// A clean run: exit 0, every kernel's summary with the expected call count,
/// no mismatch, all three path classes exercised, identical class counts for
/// every kernel. Returns the shared class counts.
#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
fn require_clean(run: &native::Run, kernels: &[Kernel], what: &str) -> [u64; 6] {
    assert!(
        !run.timed_out && run.status == Some(0) && run.mismatch_lines.is_empty(),
        "{what}: status={:?} timed_out={} stdout:\n{}",
        run.status,
        run.timed_out,
        run.stdout
    );
    assert_eq!(run.summaries.len(), kernels.len(), "{what}: {}", run.stdout);
    let mut classes = None;
    for kernel in kernels {
        let summary = &run.summaries[kernel.name];
        assert_eq!(summary.get("calls"), native::calls_per_kernel(), "{what}");
        assert_eq!(summary.get("mismatched"), 0, "{what}");
        for class in [
            "scalar",
            "vec_single",
            "vec_multi",
            "scalar_tails",
            "multi_p0",
        ] {
            assert!(
                summary.get(class) > 0,
                "{what} {}: no {class} call",
                kernel.name
            );
        }
        let these = summary.classes();
        assert_eq!(
            *classes.get_or_insert(these),
            these,
            "{what} {}",
            kernel.name
        );
    }
    classes.unwrap()
}

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[test]
fn native_objects_match_the_c_oracle_at_o0_through_o3() {
    let butterflies = module();
    let harness = native::Harness::new();
    let mut objects: Vec<(String, Vec<u8>, bool)> = LEVELS
        .iter()
        .map(|&level| {
            (
                format!("{level:?}"),
                compile(native_host::TRIPLE, level, &butterflies, None),
                VECTOR_LEVELS.contains(&level),
            )
        })
        .collect();
    objects.push((
        "O2-without-neon_butterfly".to_owned(),
        compile(
            native_host::TRIPLE,
            OptLevel::O2,
            &butterflies,
            Some("neon_butterfly"),
        ),
        false,
    ));
    for (tag, object, vector) in &objects {
        native_host::assert_native_object(object);
        record(&format!("native-{tag}.o"), object);
        let forms = if *vector {
            require_live_writebacks(object).unwrap_or_else(|error| panic!("{tag}: {error}"));
            "LD1 post=6 ST1 post=6, 12/12 writebacks live".to_owned()
        } else {
            require_butterfly_forms(object).expect_err("scalar-only object");
            "scalar-only".to_owned()
        };
        let executable = harness.link(object, tag);
        let run = native::run(&executable, None);
        let [calls, scalar, single, multi, pairs, tails] = require_clean(&run, &KERNELS, tag);
        println!(
            "NEON_BUTTERFLY_WRITEBACK_NATIVE {} {tag}: {forms}; 3 kernels x {calls} calls, every \
             one matched bit for bit over the whole buffer; per kernel the placements route \
             {scalar} calls to the scalar loop, {single} to exactly one vector pair and {multi} \
             to two or more ({pairs} vector pairs, {tails} odd scalar tails)",
            native_host::HOST
        );
    }
}

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[test]
fn c_oracle_fails_every_live_writeback_mutant() {
    let butterflies = module();
    let harness = native::Harness::new();
    for level in VECTOR_LEVELS {
        let object = compile(native_host::TRIPLE, level, &butterflies, None);
        let image = text_image(&object).unwrap();
        let reports = require_live_writebacks(&object).unwrap();
        let clean = harness.link(&object, &format!("{level:?}-clean"));
        let mut classes = None;
        for kernel in KERNELS {
            let run = native::run(&clean, Some(kernel.name));
            let these = require_clean(&run, &[kernel], &format!("{level:?} {}", kernel.name));
            assert_eq!(*classes.get_or_insert(these), these);
        }
        let [_, _, single_calls, multi_calls, _, _] = classes.unwrap();
        let mut outcomes = String::from(
            "serial\tkernel\tword\tbase\tmutation\toriginal\tmutated\tstatus\tdecode_gate\t\
             mismatched\tmismatched_scalar\tmismatched_vec_single\tmismatched_vec_multi\t\
             multi_p0\tmismatched_multi_p0\tfirst_line\n",
        );
        let mut failed: BTreeMap<String, usize> = BTreeMap::new();
        let mut serial = 0;
        for report in &reports {
            let kernel = report.kernel;
            for (word, _, _) in &report.words {
                let original = image.words[word.index];
                let mutations = transfer_mutants(original)
                    .map(|(label, mutated)| (label, mutated, false))
                    .into_iter()
                    .chain(
                        writeback_mutants(original, report.stride.0)
                            .map(|(label, mutated)| (label, mutated, true)),
                    );
                for (label, mutated, writeback_only) in mutations {
                    let mutant = with_word(&object, &image, word.index, mutated);
                    let gate = require_butterfly_forms(&mutant);
                    let executable = harness.link(&mutant, &format!("{level:?}-mutant-{serial}"));
                    let run = native::run(&executable, Some(kernel));
                    let summary = run.summaries.get(kernel).unwrap_or_else(|| {
                        panic!(
                            "{level:?} {kernel} {label} at word {}: status={:?} timed_out={} \
                             stdout:\n{}",
                            word.index, run.status, run.timed_out, run.stdout
                        )
                    });
                    let get = |key: &str| summary.get(key);
                    outcomes.push_str(&format!(
                        "{serial}\t{kernel}\t{}\tx{}\t{} {label}\t{original:#010x}\t\
                         {mutated:#010x}\t{:?}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                        word.index,
                        word.rn,
                        word.mnemonic(),
                        run.status,
                        if gate.is_ok() { "accepted" } else { "refused" },
                        get("mismatched"),
                        get("mismatched_scalar"),
                        get("mismatched_vec_single"),
                        get("mismatched_vec_multi"),
                        get("multi_p0"),
                        get("mismatched_multi_p0"),
                        run.mismatch_lines.first().map_or("", String::as_str),
                    ));
                    let context = format!(
                        "{level:?} {kernel} {} {label} at word {} (x{}): stdout:\n{}",
                        word.mnemonic(),
                        word.index,
                        word.rn,
                        run.stdout
                    );
                    gate.expect_err(&context);
                    // Every mutant fails the oracle, and never in a call the
                    // driver routes to the scalar loop.
                    assert!(
                        !run.timed_out
                            && run.status == Some(1)
                            && get("mismatched") > 0
                            && run.mismatch_lines.len() == 1
                            && run.mismatch_lines[0].starts_with(&format!("MISMATCH {kernel} ")),
                        "{context}"
                    );
                    assert_eq!(get("mismatched_scalar"), 0, "{context}");
                    // On finite inputs every call with two or more vector
                    // pairs fails.
                    assert_eq!(get("mismatched_multi_p0"), get("multi_p0"), "{context}");
                    if writeback_only {
                        // The writeback of the last vector iteration is dead:
                        // a one-pair call cannot observe it.
                        assert_eq!(get("mismatched_vec_single"), 0, "{context}");
                    } else {
                        assert!(get("mismatched_vec_single") > 0, "{context}");
                    }
                    assert!(get("mismatched_vec_multi") > 0, "{context}");
                    assert!(get("mismatched_vec_multi") <= multi_calls, "{context}");
                    assert!(get("mismatched_vec_single") <= single_calls, "{context}");
                    *failed
                        .entry(format!("{} {label}", word.mnemonic()))
                        .or_default() += 1;
                    std::fs::remove_file(executable).unwrap();
                    serial += 1;
                }
            }
        }
        record(&format!("mutants-{level:?}.tsv"), outcomes.as_bytes());
        for label in [
            "narrowed",
            "removed",
            "no writeback",
            "wrong-stride register post-index",
        ] {
            assert_eq!(failed[&format!("LD1 {label}")], 6, "{failed:?}");
            assert_eq!(failed[&format!("ST1 {label}")], 6, "{failed:?}");
        }
        assert_eq!(serial, 48);
        let strides: Vec<String> = reports
            .iter()
            .map(|report| format!("{} x{}={}", report.kernel, report.stride.0, report.stride.1))
            .collect();
        println!(
            "NEON_BUTTERFLY_WRITEBACK_MUTANTS {} {level:?}: 48/48 single-word mutants fail the C \
             oracle ({failed:?}); the 24 writeback-only ones (no writeback, and register \
             post-index by a register holding a wrong constant stride: {}) fail only in calls \
             with two or more vector pairs, never in the {single_calls} one-pair or the scalar \
             calls, and in every finite-input multi-pair call",
            native_host::HOST,
            strides.join(", ")
        );
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
