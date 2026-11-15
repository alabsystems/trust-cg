// trust-cg-codegen/tests/neon_ld1_st1_post_execution.rs
//
// NEON LD1/ST1 post-index (`NeonLd1Post`/`NeonSt1Post`) through the real
// trust-ir -> object pipeline, decoded and executed.
//
// Ten trust-ir f32/f64 elementwise map loops are compiled by `Compiler` at
// O0-O3. At O2 and O3 the scheduled `neon_fmap` pass vectorizes eight of
// them: a 16 x f32 / 8 x f64 main loop (LDP/STP Q), then a one-vector
// remainder loop whose loads and store are `LD1 {Vt.4S|.2D}, [Xn], #16` and
// `ST1 {Vt.4S|.2D}, [Xn], #16`, then the unchanged scalar loop for the last
// lanes. The eight cover the in-place map with no alias
// precondition (both loop shapes) and the rotated two- and three-array maps
// behind the pass's runtime range-disjointness check. The two remaining
// kernels are header-tested two- and three-array maps (`for_axpy_f32`,
// `for_diff_f64`): `neon_fmap` versions multi-array maps only on the rotated
// exit and the kernels carry no noalias authority, so they stay scalar at
// every level. O0 and O1 schedule no NEON pass, so their objects are
// scalar-only.
//
// Evidence, in order of strength:
// * decode: every word of the final object's code section is classified by
//   two independent decoders (trust-cg-lift and a bit mask written here);
//   they must agree, and each LD1/ST1 post-index word must sit in a named
//   kernel with that kernel's arrangement. The per-kernel counts are exact.
//   The same check refuses scalar-only objects (O0, O1, O2 with `neon_fmap`
//   disabled) and objects whose LD1/ST1 words were mutated;
// * execution: the host object is linked with `cc` against a C oracle that
//   runs the same loops with FP contraction off and compares the complete
//   buffer bit for bit after every call: every output element (main-loop,
//   remainder and scalar-tail lanes), the guard elements around it and the
//   unwritten inputs, over overlapping and disjoint layouts;
// * mutation: each LD1/ST1 post-index word is narrowed to 64 bits or removed,
//   and each vector FADD/FSUB/FMUL/FDIV is swapped for another; the C oracle
//   must report a mismatch for every such object.
//
// Boundary: the executed objects observe the LD1/ST1 transfer (address,
// width, arrangement and data), not the post-index base-register update.
// `neon_fmap`'s remainder loop recomputes every stream pointer and the store
// pointer with MADD on each step, so the `#16` writeback of all 20 executed
// words is dead: the register is redefined before any read. The test
// enforces that boundary rather than assuming it: each LD1/ST1 word rewritten
// to the no-writeback form `[Xn]` or to the register post-index form
// `[Xn], X1` must still PASS the C oracle, and the decode gate must REFUSE it.
// The post-index addressing form is therefore pinned by the decode gate only.
// The one scheduled emitter whose LD1/ST1 writeback is live is
// `neon_butterfly` (O2/Os/O3, walking pointers); it has no control here and
// is executed, with writeback-only mutants that must fail, by
// neon_butterfly_writeback_execution.rs.
//
// This is object and execution evidence for the admitted shapes and inputs;
// it is not a proof of the transform, of the encoder, or of other shapes.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::collections::BTreeMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_lift::disasm::aarch64::{Instruction, decode};
use trust_ir::{BinOp, CastOp, ICmpOp, Ty};
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
/// Levels whose default pipeline schedules `neon_fmap`.
const VECTOR_LEVELS: [OptLevel; 2] = [OptLevel::O2, OptLevel::O3];
const NOP: u32 = 0xd503_201f;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Shape {
    /// Guarded do-while with an i64 induction and an `iv + 1 == n` exit (the
    /// shape `neon_fmap` admits for runtime alias versioning).
    Rotated,
    /// Header-tested `for i in 0..n` with an i32 induction.
    Counted,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Op {
    /// `y[i] = a * y[i]`: one array, in place.
    Scale,
    /// `y[i] = a * x[i] + y[i]`: two arrays (FMUL then FADD, two roundings).
    Axpy,
    /// `y[i] = (x[i] - b[i]) / a`: three arrays.
    Diff,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Elem {
    F32,
    F64,
}

impl Elem {
    fn ty(self) -> Ty {
        match self {
            Self::F32 => Ty::F32,
            Self::F64 => Ty::F64,
        }
    }

    /// LD1/ST1 `size` field of the 128-bit arrangement (`.4S` or `.2D`).
    fn size_field(self) -> u8 {
        match self {
            Self::F32 => 0b10,
            Self::F64 => 0b11,
        }
    }

    fn arrangement(self) -> &'static str {
        match self {
            Self::F32 => ".4S",
            Self::F64 => ".2D",
        }
    }

    /// Lanes per main-loop iteration (four Q registers).
    #[cfg_attr(
        not(all(
            target_arch = "aarch64",
            any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
        )),
        allow(dead_code)
    )]
    fn main_lanes(self) -> i64 {
        match self {
            Self::F32 => 16,
            Self::F64 => 8,
        }
    }

    /// Lanes per remainder-loop iteration (one Q register).
    #[cfg_attr(
        not(all(
            target_arch = "aarch64",
            any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
        )),
        allow(dead_code)
    )]
    fn vector_lanes(self) -> i64 {
        match self {
            Self::F32 => 4,
            Self::F64 => 2,
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct Kernel {
    name: &'static str,
    shape: Shape,
    op: Op,
    elem: Elem,
    /// Whether O2/O3 must vectorize it.
    vector: bool,
}

impl Kernel {
    const fn new(name: &'static str, shape: Shape, op: Op, elem: Elem, vector: bool) -> Self {
        Self {
            name,
            shape,
            op,
            elem,
            vector,
        }
    }

    /// Distinct array streams read per element, one LD1 each in the remainder.
    fn streams(self) -> usize {
        match self.op {
            Op::Scale => 1,
            Op::Axpy | Op::Diff => 2,
        }
    }

    fn expected(self) -> FormCount {
        if self.vector {
            FormCount {
                ld1: self.streams(),
                st1: 1,
            }
        } else {
            FormCount::default()
        }
    }

    /// Pointer layouts the C oracle runs: the single-array map has one.
    #[cfg_attr(
        not(all(
            target_arch = "aarch64",
            any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
        )),
        allow(dead_code)
    )]
    fn layouts(self) -> usize {
        match self.op {
            Op::Scale => 1,
            Op::Axpy | Op::Diff => LAYOUTS,
        }
    }
}

const KERNELS: [Kernel; 10] = [
    Kernel::new(
        "ld1st1_rot_scale_f32",
        Shape::Rotated,
        Op::Scale,
        Elem::F32,
        true,
    ),
    Kernel::new(
        "ld1st1_rot_scale_f64",
        Shape::Rotated,
        Op::Scale,
        Elem::F64,
        true,
    ),
    Kernel::new(
        "ld1st1_rot_axpy_f32",
        Shape::Rotated,
        Op::Axpy,
        Elem::F32,
        true,
    ),
    Kernel::new(
        "ld1st1_rot_axpy_f64",
        Shape::Rotated,
        Op::Axpy,
        Elem::F64,
        true,
    ),
    Kernel::new(
        "ld1st1_rot_diff_f32",
        Shape::Rotated,
        Op::Diff,
        Elem::F32,
        true,
    ),
    Kernel::new(
        "ld1st1_rot_diff_f64",
        Shape::Rotated,
        Op::Diff,
        Elem::F64,
        true,
    ),
    Kernel::new(
        "ld1st1_for_scale_f32",
        Shape::Counted,
        Op::Scale,
        Elem::F32,
        true,
    ),
    Kernel::new(
        "ld1st1_for_scale_f64",
        Shape::Counted,
        Op::Scale,
        Elem::F64,
        true,
    ),
    // No noalias authority and no runtime versioning in this shape: scalar.
    Kernel::new(
        "ld1st1_for_axpy_f32",
        Shape::Counted,
        Op::Axpy,
        Elem::F32,
        false,
    ),
    Kernel::new(
        "ld1st1_for_diff_f64",
        Shape::Counted,
        Op::Diff,
        Elem::F64,
        false,
    ),
];

/// Pointer layouts for the two- and three-array kernels (see `DRIVER`).
#[cfg_attr(
    not(all(
        target_arch = "aarch64",
        any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
    )),
    allow(dead_code)
)]
const LAYOUTS: usize = 8;
#[cfg_attr(
    not(all(
        target_arch = "aarch64",
        any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
    )),
    allow(dead_code)
)]
const PATTERNS: usize = 3;
#[cfg_attr(
    not(all(
        target_arch = "aarch64",
        any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
    )),
    allow(dead_code)
)]
const OFFSETS: usize = 3;

/// Element counts: every residue of the main and remainder widths several
/// times over, empty and negative counts, and longer runs.
#[cfg_attr(
    not(all(
        target_arch = "aarch64",
        any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
    )),
    allow(dead_code)
)]
fn counts() -> Vec<i32> {
    let mut counts: Vec<i32> = (-3..=70).collect();
    counts.extend([97, 127, 128, 129, 255, 256, 257, 300]);
    counts
}

/// `f(y, x, b, a, n)` for one kernel.
fn build_kernel(mb: &mut ModuleBuilder, kernel: Kernel) {
    let fty = kernel.elem.ty();
    let ty = mb.add_func_type(
        vec![Ty::Ptr, Ty::Ptr, Ty::Ptr, fty.clone(), Ty::I32],
        vec![],
    );
    let mut fb = mb.function(kernel.name, ty);
    let entry = fb.create_block();
    let y = fb.add_block_param(entry, Ty::Ptr);
    let x = fb.add_block_param(entry, Ty::Ptr);
    let b = fb.add_block_param(entry, Ty::Ptr);
    let a = fb.add_block_param(entry, fty.clone());
    let n = fb.add_block_param(entry, Ty::I32);
    let exit = fb.create_block();
    // `back_edge` is the block the latch branches to; `index` the induction.
    let (back_edge, index) = match kernel.shape {
        Shape::Rotated => {
            let guard = fb.create_block();
            let body = fb.create_block();
            let iv = fb.add_block_param(body, Ty::I64);
            fb.switch_to_block(entry);
            let zero = fb.iconst(Ty::I32, 0);
            let positive = fb.icmp(ICmpOp::Sgt, Ty::I32, n, zero);
            fb.condbr(positive, guard, vec![], exit, vec![]);
            fb.switch_to_block(guard);
            let start = fb.iconst(Ty::I64, 0);
            fb.br(body, vec![start]);
            fb.switch_to_block(body);
            (body, iv)
        }
        Shape::Counted => {
            let header = fb.create_block();
            let iv = fb.add_block_param(header, Ty::I32);
            let body = fb.create_block();
            fb.switch_to_block(entry);
            let start = fb.iconst(Ty::I32, 0);
            fb.br(header, vec![start]);
            fb.switch_to_block(header);
            let more = fb.icmp(ICmpOp::Slt, Ty::I32, iv, n);
            fb.condbr(more, body, vec![], exit, vec![]);
            fb.switch_to_block(body);
            (header, iv)
        }
    };
    let py = fb.gep(fty.clone(), y, vec![index]);
    let value = match kernel.op {
        Op::Scale => {
            let old = fb.load(fty.clone(), py);
            fb.binop(BinOp::FMul, fty.clone(), a, old)
        }
        Op::Axpy => {
            let px = fb.gep(fty.clone(), x, vec![index]);
            let xv = fb.load(fty.clone(), px);
            let yv = fb.load(fty.clone(), py);
            let product = fb.binop(BinOp::FMul, fty.clone(), a, xv);
            fb.binop(BinOp::FAdd, fty.clone(), product, yv)
        }
        Op::Diff => {
            let px = fb.gep(fty.clone(), x, vec![index]);
            let xv = fb.load(fty.clone(), px);
            let pb = fb.gep(fty.clone(), b, vec![index]);
            let bv = fb.load(fty.clone(), pb);
            let difference = fb.binop(BinOp::FSub, fty.clone(), xv, bv);
            fb.binop(BinOp::FDiv, fty.clone(), difference, a)
        }
    };
    fb.store(fty.clone(), py, value);
    match kernel.shape {
        Shape::Rotated => {
            let one = fb.iconst(Ty::I64, 1);
            let next = fb.binop(BinOp::Add, Ty::I64, index, one);
            let bound = fb.cast(CastOp::ZExt, Ty::I32, Ty::I64, n);
            let done = fb.icmp(ICmpOp::Eq, Ty::I64, next, bound);
            fb.condbr(done, exit, vec![], back_edge, vec![next]);
        }
        Shape::Counted => {
            let one = fb.iconst(Ty::I32, 1);
            let next = fb.binop(BinOp::Add, Ty::I32, index, one);
            fb.br(back_edge, vec![next]);
        }
    }
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();
}

fn module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("neon_ld1_st1_post");
    for kernel in KERNELS {
        build_kernel(&mut mb, kernel);
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Compile the module for `triple` through the public `Compiler`, optionally
/// with `neon_fmap` disabled (the same-level scalar-only control). Serial
/// compilation keeps the thread-local environment edit in force.
fn compile(triple: &str, level: OptLevel, disable_fmap: bool) -> Vec<u8> {
    let module = module();
    let spec = TargetSpec::parse(triple).expect("target triple");
    trust_cg_codegen::env_lock::with_env_edits(|env| {
        if disable_fmap {
            env.set("TRUST_CG_DISABLE_PASSES", "neon_fmap");
        } else {
            env.remove("TRUST_CG_DISABLE_PASSES");
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
        let object = compiler
            .compile(&module)
            .unwrap_or_else(|error| panic!("{triple} {level:?}: {error:?}"))
            .object_code;
        assert!(!object.is_empty());
        object
    })
}

/// Opt-in retention of the objects and outcomes for an evidence archive:
/// with `TRUST_CG_LD1_ST1_RECORD_DIR` set, `contents` is written there as
/// `name`. Unset (as on the floors), it does nothing.
fn record(name: &str, contents: &[u8]) {
    if let Some(directory) = std::env::var_os("TRUST_CG_LD1_ST1_RECORD_DIR") {
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

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct FormCount {
    ld1: usize,
    st1: usize,
}

/// A decoded LD1/ST1 (one register, immediate post-index) word.
#[derive(Clone, Copy, Debug)]
struct PostWord {
    /// Word index in the code section.
    index: usize,
    kernel: Kernel,
    load: bool,
}

/// The independent bit-mask classifier: `0 Q 0011001 L 0 11111 0111 size Rn Rt`
/// (Advanced SIMD load/store multiple structures, post-indexed by the
/// immediate, one register).
fn mask_is_ld1_st1_post(word: u32) -> bool {
    word & 0xbfbf_f000 == 0x0c9f_7000
}

/// Classify every code word with both decoders and attribute each LD1/ST1
/// post-index word to its kernel, checking its arrangement. Refuses decoder
/// disagreement, a post-index word outside every kernel, a missing kernel
/// symbol, and any arrangement other than the kernel's 128-bit one.
fn post_index_words(image: &TextImage) -> Result<Vec<PostWord>, String> {
    let mut ranges = Vec::new();
    for kernel in KERNELS {
        let &(start, end) = image
            .functions
            .get(kernel.name)
            .ok_or_else(|| format!("no function symbol for {}", kernel.name))?;
        ranges.push((kernel, start, end));
    }
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
        let &(kernel, _, _) = ranges
            .iter()
            .find(|&&(_, start, end)| (start..end).contains(&at))
            .ok_or_else(|| format!("LD1/ST1 post-index word {index} is outside every kernel"))?;
        let mnemonic = if form.load { "LD1" } else { "ST1" };
        if !form.q || form.size != kernel.elem.size_field() {
            return Err(format!(
                "{}: {mnemonic} word {word:#010x} has Q={} size={:#04b}, not {}",
                kernel.name,
                u8::from(form.q),
                form.size,
                kernel.elem.arrangement()
            ));
        }
        found.push(PostWord {
            index,
            kernel,
            load: form.load,
        });
    }
    Ok(found)
}

fn form_counts(words: &[PostWord]) -> BTreeMap<&'static str, FormCount> {
    let mut counts: BTreeMap<&'static str, FormCount> = KERNELS
        .iter()
        .map(|kernel| (kernel.name, FormCount::default()))
        .collect();
    for word in words {
        let count = counts.get_mut(word.kernel.name).unwrap();
        if word.load {
            count.ld1 += 1;
        } else {
            count.st1 += 1;
        }
    }
    counts
}

/// The decode gate for a vectorizing level: every kernel carries exactly its
/// expected LD1/ST1 post-index words (and the scalar controls none).
fn require_ld1_st1(object: &[u8]) -> Result<FormCount, String> {
    let image = text_image(object)?;
    let words = post_index_words(&image)?;
    let counts = form_counts(&words);
    for kernel in KERNELS {
        let got = counts[kernel.name];
        if got != kernel.expected() {
            return Err(format!(
                "{}: LD1/ST1 post-index census {got:?}, expected {:?}",
                kernel.name,
                kernel.expected()
            ));
        }
    }
    let total = FormCount {
        ld1: counts.values().map(|count| count.ld1).sum(),
        st1: counts.values().map(|count| count.st1).sum(),
    };
    if total.ld1 == 0 || total.st1 == 0 {
        return Err("no LD1/ST1 post-index word".into());
    }
    Ok(total)
}

fn with_word(object: &[u8], image: &TextImage, index: usize, word: u32) -> Vec<u8> {
    let mut mutated = object.to_vec();
    let at = image.offset + index * 4;
    mutated[at..at + 4].copy_from_slice(&word.to_le_bytes());
    mutated
}

/// Semantics-changing LD1/ST1 mutations: the 64-bit (Q=0) transfer, and
/// removal of the transfer.
fn ld1_st1_mutants(word: u32) -> [(&'static str, u32); 2] {
    [("narrowed", word ^ (1 << 30)), ("removed", NOP)]
}

/// LD1/ST1 mutations that keep the transfer and change only the base-register
/// update: no writeback (`[Xn]`: bit 23 and Rm cleared) and register
/// post-index by X1 (`[Xn], X1`). The executed objects never read the updated
/// base, so the C oracle cannot tell these from the original; only the
/// decode gate refuses them.
fn writeback_mutants(word: u32) -> [(&'static str, u32); 2] {
    [
        ("no writeback", word & !(1 << 23) & !(0x1f << 16)),
        ("register post-index", (word & !(0x1f << 16)) | (1 << 16)),
    ]
}

/// Swap one vector FP operation for another allocated one: FADD<->FSUB,
/// FMUL->FADD, FDIV->FMUL.
#[cfg_attr(
    not(all(
        target_arch = "aarch64",
        any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
    )),
    allow(dead_code)
)]
fn swapped_fp_op(word: u32) -> Option<u32> {
    let Ok(Instruction::NeonFpVec3Same(op)) = decode(word) else {
        return None;
    };
    let mutated = match (op.u, op.bit23, op.opcode) {
        (false, false, 0b11_0101) => word | 1 << 23,
        (false, true, 0b11_0101) => word & !(1 << 23),
        (true, false, 0b11_0111) => word & !(1 << 29) & !(1 << 11),
        (true, false, 0b11_1111) => word & !(1 << 13),
        _ => return None,
    };
    let Ok(Instruction::NeonFpVec3Same(swapped)) = decode(mutated) else {
        panic!("{word:#010x} -> {mutated:#010x} is not a vector FP operation");
    };
    assert_ne!(
        (swapped.u, swapped.bit23, swapped.opcode),
        (op.u, op.bit23, op.opcode)
    );
    Some(mutated)
}

// ---------------------------------------------------------------------------
// Host-neutral object controls (both containers, every host)
// ---------------------------------------------------------------------------

#[test]
fn vectorizing_levels_emit_ld1_st1_post_index_in_every_admitted_kernel() {
    for triple in [LINUX, DARWIN] {
        for level in LEVELS {
            let object = compile(triple, level, false);
            record(&format!("{triple}-{level:?}.o"), &object);
            let image = text_image(&object).unwrap();
            assert_eq!(image.words, native_host::text_words(&object), "{triple}");
            let words = post_index_words(&image)
                .unwrap_or_else(|error| panic!("{triple} {level:?}: {error}"));
            let result = require_ld1_st1(&object);
            if VECTOR_LEVELS.contains(&level) {
                let total = result.unwrap_or_else(|error| panic!("{triple} {level:?}: {error}"));
                assert_eq!(total, FormCount { ld1: 12, st1: 8 }, "{triple} {level:?}");
                println!(
                    "NEON_LD1_ST1_POST_OBJECT {triple} {level:?}: {} code words, LD1 post={} ST1 post={} \
                     in 8/10 kernels (.4S and .2D), both decoders agree",
                    image.words.len(),
                    total.ld1,
                    total.st1
                );
            } else {
                // O0/O1 schedule no NEON pass: the objects are scalar-only
                // and the decode gate refuses them.
                assert!(words.is_empty(), "{triple} {level:?}: {words:?}");
                let refusal = result.expect_err("a scalar-only object must be refused");
                println!(
                    "NEON_LD1_ST1_POST_OBJECT {triple} {level:?}: scalar-only, refused: {refusal}"
                );
            }
        }
    }
}

#[test]
fn decode_gate_refuses_scalar_only_and_mutated_objects() {
    for triple in [LINUX, DARWIN] {
        // Same level with the vectorizer disabled: scalar-only, refused.
        let scalar = compile(triple, OptLevel::O2, true);
        record(&format!("{triple}-O2-without-neon_fmap.o"), &scalar);
        assert!(
            post_index_words(&text_image(&scalar).unwrap())
                .unwrap()
                .is_empty()
        );
        let refusal = require_ld1_st1(&scalar).expect_err("neon_fmap disabled");
        println!("NEON_LD1_ST1_POST_REFUSAL {triple} O2 without neon_fmap: {refusal}");

        let object = compile(triple, OptLevel::O2, false);
        let image = text_image(&object).unwrap();
        let words = post_index_words(&image).unwrap();
        assert_eq!(words.len(), 20);
        let mut refused = 0;
        for word in &words {
            let original = image.words[word.index];
            for (label, mutated) in ld1_st1_mutants(original)
                .into_iter()
                .chain(writeback_mutants(original))
            {
                let mutant = with_word(&object, &image, word.index, mutated);
                let error = require_ld1_st1(&mutant).expect_err(label);
                assert!(error.contains(word.kernel.name), "{label}: {error}");
                refused += 1;
            }
        }
        assert_eq!(refused, 80);
        println!(
            "NEON_LD1_ST1_POST_REFUSAL {triple} O2: {refused}/80 mutated LD1/ST1 words refused \
             (narrowed, removed, no writeback, register post-index)"
        );
    }
}

// ---------------------------------------------------------------------------
// Native execution against the C oracle
// ---------------------------------------------------------------------------

/// The C oracle. `y` sits in the middle of three regions; `x` and `b` are
/// placed by `layouts` relative to `y` in elements, so the two- and
/// three-array kernels run disjoint placements (in both address orders) and
/// overlapping ones, including loop-carried reads. After every call
/// the whole buffer, guards included, must equal the reference bit for bit.
/// Input NaNs within one pattern share a single encoding (the default NaN,
/// or one signaling NaN), so every operation's NaN result is independent of
/// operand order. With an argument naming a kernel, only that kernel runs and
/// the first mismatch exits 1.
#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
const DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define CAP 320
#define GUARD 16
#define REGION (CAP + 2 * GUARD)
#define TOTAL (3 * REGION)

typedef void (*kernel32)(float *, const float *, const float *, float, int32_t);
typedef void (*kernel64)(double *, const double *, const double *, double, int32_t);
#define D32(N) extern void N(float *, const float *, const float *, float, int32_t);
#define D64(N) extern void N(double *, const double *, const double *, double, int32_t);
D32(ld1st1_rot_scale_f32) D64(ld1st1_rot_scale_f64)
D32(ld1st1_rot_axpy_f32) D64(ld1st1_rot_axpy_f64)
D32(ld1st1_rot_diff_f32) D64(ld1st1_rot_diff_f64)
D32(ld1st1_for_scale_f32) D64(ld1st1_for_scale_f64)
D32(ld1st1_for_axpy_f32) D64(ld1st1_for_diff_f64)

/* The trust-ir loops as written: one rounding per operation, same operand
   order, sequential over i (so overlapping placements keep their meaning). */
#define REFERENCES(T, S)                                                   \
    static void ref_scale_##S(T *y, const T *x, const T *b, T a, int32_t n) { \
        (void)x; (void)b;                                                  \
        for (int32_t i = 0; i < n; i++) y[i] = a * y[i];                   \
    }                                                                      \
    static void ref_axpy_##S(T *y, const T *x, const T *b, T a, int32_t n) {  \
        (void)b;                                                           \
        for (int32_t i = 0; i < n; i++) { T p = a * x[i]; y[i] = p + y[i]; } \
    }                                                                      \
    static void ref_diff_##S(T *y, const T *x, const T *b, T a, int32_t n) {  \
        for (int32_t i = 0; i < n; i++) { T d = x[i] - b[i]; y[i] = d / a; } \
    }
REFERENCES(float, f32)
REFERENCES(double, f64)

enum { SCALE, AXPY, DIFF };
struct kernel { const char *name; int op; kernel32 f32; kernel64 f64; };
static const struct kernel kernels[] = {
    {"ld1st1_rot_scale_f32", SCALE, ld1st1_rot_scale_f32, 0},
    {"ld1st1_rot_scale_f64", SCALE, 0, ld1st1_rot_scale_f64},
    {"ld1st1_rot_axpy_f32", AXPY, ld1st1_rot_axpy_f32, 0},
    {"ld1st1_rot_axpy_f64", AXPY, 0, ld1st1_rot_axpy_f64},
    {"ld1st1_rot_diff_f32", DIFF, ld1st1_rot_diff_f32, 0},
    {"ld1st1_rot_diff_f64", DIFF, 0, ld1st1_rot_diff_f64},
    {"ld1st1_for_scale_f32", SCALE, ld1st1_for_scale_f32, 0},
    {"ld1st1_for_scale_f64", SCALE, 0, ld1st1_for_scale_f64},
    {"ld1st1_for_axpy_f32", AXPY, ld1st1_for_axpy_f32, 0},
    {"ld1st1_for_diff_f64", DIFF, 0, ld1st1_for_diff_f64},
};
static const kernel32 refs32[] = {ref_scale_f32, ref_axpy_f32, ref_diff_f32};
static const kernel64 refs64[] = {ref_scale_f64, ref_axpy_f64, ref_diff_f64};

static const int32_t counts[] = {@COUNTS@};
static const long offsets[] = {0, 1, 3};
/* {x - y, b - y} in elements. 0-1: disjoint in both address orders for
   every kernel; 5-6 are also disjoint for axpy, which never reads b; the
   rest overlap a read stream, including x or b one or more elements behind
   y. Which path the runtime range check chose is not observed here. */
static const long layouts[][2] = {
    {REGION, -REGION}, {-REGION, REGION}, {0, REGION}, {1, REGION},
    {-1, REGION}, {REGION, -2}, {REGION, 5}, {-3, 3},
};
/* Loop-invariant scalars (never NaN): 1.5, -3, 0.1, -0, a subnormal, +inf,
   2, 1. */
static const uint32_t scalars32[] = {
    0x3fc00000u, 0xc0400000u, 0x3dcccccdu, 0x80000000u,
    0x000116c2u, 0x7f800000u, 0x40000000u, 0x3f800000u,
};
static const uint64_t scalars64[] = {
    0x3ff8000000000000ull, 0xc008000000000000ull, 0x3fb999999999999aull,
    0x8000000000000000ull, 0x000000000116c2a5ull, 0x7ff0000000000000ull,
    0x4000000000000000ull, 0x3ff0000000000000ull,
};
static const uint32_t specials32[] = {
    0x00000000u, 0x80000000u, 0x7f800000u, 0xff800000u, 0x00000001u, 0x007fffffu,
    0x00800000u, 0x7f7fffffu, 0x3f800000u, 0xbfc00000u, 0x7fc00000u, 0x3eaaaaabu,
};
static const uint64_t specials64[] = {
    0x0000000000000000ull, 0x8000000000000000ull, 0x7ff0000000000000ull,
    0xfff0000000000000ull, 0x0000000000000001ull, 0x000fffffffffffffull,
    0x0010000000000000ull, 0x7fefffffffffffffull, 0x3ff0000000000000ull,
    0xbff8000000000000ull, 0x7ff8000000000000ull, 0x3fd5555555555555ull,
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
               (uint32_t)(r >> 9) & 0x7fffffu;
    if (pattern == 1) return specials32[(r >> 7) % 12];
    uint32_t v = (uint32_t)(r >> 17);
    if ((v & 0x7f800000u) == 0x7f800000u && (v & 0x7fffffu)) v = 0x7f80beefu;
    return v;
}
static uint64_t bits64(int pattern) {
    uint64_t r = next();
    if (pattern == 0)
        return (r & 1) << 63 | (uint64_t)(1023 - 40 + (r >> 1) % 81) << 52 |
               (next() & 0xfffffffffffffull);
    if (pattern == 1) return specials64[(r >> 7) % 12];
    uint64_t v = r;
    if ((v & 0x7ff0000000000000ull) == 0x7ff0000000000000ull && (v & 0xfffffffffffffull))
        v = 0x7ff000000000beefull;
    return v;
}

static float buf32[TOTAL], ref32[TOTAL];
static double buf64[TOTAL], ref64[TOTAL];

int main(int argc, char **argv) {
    const char *only = argc > 1 ? argv[1] : 0;
    unsigned long long cases = 0, elements = 0, errors = 0;
    int ran = 0;
    for (unsigned k = 0; k < sizeof kernels / sizeof *kernels; ++k) {
        const struct kernel *kn = &kernels[k];
        if (only && strcmp(only, kn->name)) continue;
        ++ran;
        unsigned layout_count = kn->op == SCALE ? 1 : sizeof layouts / sizeof *layouts;
        for (int pattern = 0; pattern < 3; ++pattern)
        for (unsigned l = 0; l < layout_count; ++l)
        for (unsigned o = 0; o < sizeof offsets / sizeof *offsets; ++o)
        for (unsigned c = 0; c < sizeof counts / sizeof *counts; ++c) {
            int32_t n = counts[c];
            long y = REGION + GUARD + offsets[o];
            long x = y + layouts[l][0], b = y + layouts[l][1];
            unsigned pick = (unsigned)(pattern * 7 + c + o + l) % 8;
            state = 0x9e3779b97f4a7c15ull ^ ((uint64_t)k << 48) ^ ((uint64_t)pattern << 40) ^
                    ((uint64_t)l << 32) ^ ((uint64_t)o << 24) ^ (uint64_t)c;
            long bad = -1;
            if (kn->f32) {
                float a;
                memcpy(&a, &scalars32[pick], sizeof a);
                for (long i = 0; i < TOTAL; ++i) {
                    uint32_t v = bits32(pattern);
                    memcpy(&buf32[i], &v, sizeof v);
                }
                memcpy(ref32, buf32, sizeof buf32);
                kn->f32(buf32 + y, buf32 + x, buf32 + b, a, n);
                refs32[kn->op](ref32 + y, ref32 + x, ref32 + b, a, n);
                if (memcmp(buf32, ref32, sizeof buf32))
                    for (long i = 0; i < TOTAL && bad < 0; ++i)
                        if (memcmp(&buf32[i], &ref32[i], sizeof *buf32)) bad = i;
                if (bad >= 0) {
                    uint32_t got, want;
                    memcpy(&got, &buf32[bad], 4);
                    memcpy(&want, &ref32[bad], 4);
                    printf("MISMATCH %s pattern=%d layout=%u offset=%ld n=%d element=%ld got=%08x want=%08x\n",
                           kn->name, pattern, l, offsets[o], n, bad - y, got, want);
                }
            } else {
                double a;
                memcpy(&a, &scalars64[pick], sizeof a);
                for (long i = 0; i < TOTAL; ++i) {
                    uint64_t v = bits64(pattern);
                    memcpy(&buf64[i], &v, sizeof v);
                }
                memcpy(ref64, buf64, sizeof buf64);
                kn->f64(buf64 + y, buf64 + x, buf64 + b, a, n);
                refs64[kn->op](ref64 + y, ref64 + x, ref64 + b, a, n);
                if (memcmp(buf64, ref64, sizeof buf64))
                    for (long i = 0; i < TOTAL && bad < 0; ++i)
                        if (memcmp(&buf64[i], &ref64[i], sizeof *buf64)) bad = i;
                if (bad >= 0) {
                    uint64_t got, want;
                    memcpy(&got, &buf64[bad], 8);
                    memcpy(&want, &ref64[bad], 8);
                    printf("MISMATCH %s pattern=%d layout=%u offset=%ld n=%d element=%ld got=%016llx want=%016llx\n",
                           kn->name, pattern, l, offsets[o], n, bad - y,
                           (unsigned long long)got, (unsigned long long)want);
                }
            }
            if (bad >= 0) {
                ++errors;
                if (only) return 1;
            }
            ++cases;
            elements += TOTAL;
        }
    }
    if (!ran) {
        printf("NO KERNEL %s\n", only);
        return 2;
    }
    printf("NEON_LD1_ST1_POST_CASES=%llu ELEMENTS=%llu\n", cases, elements);
    return errors ? 1 : 0;
}
"#;

/// Cases the driver runs over all kernels (one per call).
#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
fn expected_cases() -> usize {
    let per_layout = PATTERNS * OFFSETS * counts().len();
    KERNELS
        .iter()
        .map(|kernel| kernel.layouts() * per_layout)
        .sum()
}

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
mod native {
    use std::path::{Path, PathBuf};
    use std::process::Command;
    use std::time::Duration;

    use super::*;

    const TOTAL_ELEMENTS: usize = 3 * (320 + 2 * 16);

    pub(super) fn driver_source() -> String {
        let counts: Vec<String> = counts().iter().map(i32::to_string).collect();
        DRIVER.replace("@COUNTS@", &counts.join(","))
    }

    /// `cc` with FP contraction off, so the oracle rounds every operation.
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
                .prefix("trust-cg-ld1-st1-")
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

    pub(super) struct Run {
        pub(super) status: Option<i32>,
        pub(super) timed_out: bool,
        pub(super) stdout: String,
    }

    pub(super) fn run(executable: &Path, only: Option<&str>) -> Run {
        let mut command = Command::new(executable);
        if let Some(kernel) = only {
            command.arg(kernel);
        }
        let result = process::command_output_with_timeout(
            &mut command,
            process::exec_timeout(Duration::from_secs(30)),
        )
        .unwrap();
        Run {
            status: result.output.status.code(),
            timed_out: result.timed_out,
            stdout: String::from_utf8_lossy(&result.output.stdout).into_owned(),
        }
    }

    pub(super) fn expected_stdout() -> String {
        format!(
            "NEON_LD1_ST1_POST_CASES={} ELEMENTS={}\n",
            expected_cases(),
            expected_cases() * TOTAL_ELEMENTS
        )
    }

    /// The summary line of a clean run filtered to `kernel`.
    pub(super) fn expected_kernel_stdout(kernel: Kernel) -> String {
        let cases = kernel.layouts() * PATTERNS * OFFSETS * counts().len();
        format!(
            "NEON_LD1_ST1_POST_CASES={cases} ELEMENTS={}\n",
            cases * TOTAL_ELEMENTS
        )
    }

    /// Lanes of the vectorized kernels' layout 0-1 calls (disjoint for every
    /// kernel) that the vectorizer's documented partition assigns to the main
    /// loop, the LD1/ST1 remainder loop and the scalar tail. Derived from `n`,
    /// not measured; a lower bound for axpy, whose layouts 5-6 are also
    /// disjoint for its only read stream.
    pub(super) fn lane_partition() -> (i64, i64, i64) {
        let (mut main, mut remainder, mut tail) = (0, 0, 0);
        for kernel in KERNELS.iter().filter(|kernel| kernel.vector) {
            let calls = (PATTERNS * OFFSETS) as i64 * if kernel.op == Op::Scale { 1 } else { 2 };
            for n in counts().into_iter().map(i64::from).filter(|&n| n > 0) {
                let big = n / kernel.elem.main_lanes() * kernel.elem.main_lanes();
                let small = (n - big) / kernel.elem.vector_lanes() * kernel.elem.vector_lanes();
                main += calls * big;
                remainder += calls * small;
                tail += calls * (n - big - small);
            }
        }
        (main, remainder, tail)
    }
}

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[test]
fn native_objects_match_the_c_oracle_at_o0_through_o3() {
    let counts = counts();
    for elem in [Elem::F32, Elem::F64] {
        let (main, vector) = (elem.main_lanes(), elem.vector_lanes());
        // Main loop, every remainder trip count and every scalar tail length.
        for trips in 0..main / vector {
            for tail in 0..vector {
                let wanted = main + trips * vector + tail;
                assert!(counts.contains(&(wanted as i32)), "{wanted}");
            }
        }
    }
    let harness = native::Harness::new();
    let expected = native::expected_stdout();
    for level in LEVELS {
        let object = compile(native_host::TRIPLE, level, false);
        native_host::assert_native_object(&object);
        record(&format!("native-{level:?}.o"), &object);
        let census = require_ld1_st1(&object);
        let forms = if VECTOR_LEVELS.contains(&level) {
            let total = census.unwrap_or_else(|error| panic!("{level:?}: {error}"));
            format!("LD1 post={} ST1 post={}", total.ld1, total.st1)
        } else {
            census.expect_err("scalar-only level");
            "scalar-only".to_owned()
        };
        let executable = harness.link(&object, &format!("{level:?}"));
        let run = native::run(&executable, None);
        assert!(
            !run.timed_out && run.status == Some(0) && run.stdout == expected,
            "{level:?}: status={:?} timed_out={} stdout:\n{}",
            run.status,
            run.timed_out,
            run.stdout
        );
        println!(
            "NEON_LD1_ST1_POST_NATIVE {} {level:?}: {forms}; {}",
            native_host::HOST,
            run.stdout.trim()
        );
    }
    let (main, remainder, tail) = native::lane_partition();
    println!(
        "NEON_LD1_ST1_POST_NATIVE lanes of vectorized layout 0-1 calls per level (n-derived \
         partition, a lower bound for axpy): main={main} remainder={remainder} scalar-tail={tail}"
    );
}

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[test]
fn c_oracle_catches_every_mutated_vector_word() {
    let harness = native::Harness::new();
    for level in VECTOR_LEVELS {
        let object = compile(native_host::TRIPLE, level, false);
        let image = text_image(&object).unwrap();
        let words = post_index_words(&image).unwrap();
        // The unmutated object passes each kernel's filtered run.
        let clean = harness.link(&object, &format!("{level:?}-clean"));
        for kernel in KERNELS {
            let run = native::run(&clean, Some(kernel.name));
            assert!(
                !run.timed_out
                    && run.status == Some(0)
                    && run.stdout == native::expected_kernel_stdout(kernel),
                "{level:?} {}: status={:?} stdout:\n{}",
                kernel.name,
                run.status,
                run.stdout
            );
        }
        // (label, kernel, word index, mutated word, oracle must catch it).
        let mut mutants = Vec::new();
        for word in &words {
            for (label, mutated) in ld1_st1_mutants(image.words[word.index]) {
                let mnemonic = if word.load { "LD1" } else { "ST1" };
                mutants.push((
                    format!("{mnemonic} {label}"),
                    word.kernel,
                    word.index,
                    mutated,
                    true,
                ));
            }
        }
        for kernel in KERNELS.iter().filter(|kernel| kernel.vector) {
            let (start, end) = image.functions[kernel.name];
            for (offset, word) in image.words[start / 4..end / 4].iter().enumerate() {
                let index = start / 4 + offset;
                if let Some(mutated) = swapped_fp_op(*word) {
                    mutants.push(("FP op swapped".to_owned(), *kernel, index, mutated, true));
                }
            }
        }
        // The writeback-blind class, appended so the serials above are stable.
        for word in &words {
            for (label, mutated) in writeback_mutants(image.words[word.index]) {
                let mnemonic = if word.load { "LD1" } else { "ST1" };
                mutants.push((
                    format!("{mnemonic} {label}"),
                    word.kernel,
                    word.index,
                    mutated,
                    false,
                ));
            }
        }
        let mut caught: BTreeMap<String, usize> = BTreeMap::new();
        let mut blind: BTreeMap<String, usize> = BTreeMap::new();
        let mut outcomes = String::from(
            "serial\tkernel\tmutation\tword\toriginal\tmutated\tstatus\tfirst_line\tdecode_gate\toracle_expected\n",
        );
        for (serial, (label, kernel, index, mutated, observable)) in mutants.iter().enumerate() {
            let mutant = with_word(&object, &image, *index, *mutated);
            let gate = require_ld1_st1(&mutant);
            let executable = harness.link(&mutant, &format!("{level:?}-mutant-{serial}"));
            let run = native::run(&executable, Some(kernel.name));
            outcomes.push_str(&format!(
                "{serial}\t{}\t{label}\t{index}\t{:#010x}\t{mutated:#010x}\t{:?}\t{}\t{}\t{}\n",
                kernel.name,
                image.words[*index],
                run.status,
                run.stdout.lines().next().unwrap_or(""),
                if gate.is_ok() { "accepted" } else { "refused" },
                if *observable { "mismatch" } else { "pass" },
            ));
            if label == "FP op swapped" {
                // Every LD1/ST1 word is intact, so only the oracle catches it.
                gate.as_ref()
                    .unwrap_or_else(|error| panic!("{level:?} {label} at word {index}: {error}"));
            } else {
                let error = gate.expect_err(label);
                assert!(error.contains(kernel.name), "{level:?} {label}: {error}");
            }
            if *observable {
                assert!(
                    !run.timed_out
                        && run.status == Some(1)
                        && run
                            .stdout
                            .starts_with(&format!("MISMATCH {} ", kernel.name)),
                    "{level:?} {label} at word {index} of {}: status={:?} timed_out={} stdout:\n{}",
                    kernel.name,
                    run.status,
                    run.timed_out,
                    run.stdout
                );
                *caught.entry(label.clone()).or_default() += 1;
            } else {
                // The post-index base update is dead in these objects, so a
                // mutant that changes only the writeback must pass the oracle.
                // If it ever fails here, the writeback became observable and
                // the stated evidence boundary must be revisited.
                assert!(
                    !run.timed_out
                        && run.status == Some(0)
                        && run.stdout == native::expected_kernel_stdout(*kernel),
                    "{level:?} {label} at word {index} of {}: the oracle observed a writeback-only \
                     change: status={:?} timed_out={} stdout:\n{}",
                    kernel.name,
                    run.status,
                    run.timed_out,
                    run.stdout
                );
                *blind.entry(label.clone()).or_default() += 1;
            }
            std::fs::remove_file(executable).unwrap();
        }
        record(&format!("mutants-{level:?}.tsv"), outcomes.as_bytes());
        assert_eq!(caught["LD1 narrowed"], 12, "{caught:?}");
        assert_eq!(caught["LD1 removed"], 12, "{caught:?}");
        assert_eq!(caught["ST1 narrowed"], 8, "{caught:?}");
        assert_eq!(caught["ST1 removed"], 8, "{caught:?}");
        assert_eq!(caught["FP op swapped"], 60, "{caught:?}");
        for label in ["no writeback", "register post-index"] {
            assert_eq!(blind[&format!("LD1 {label}")], 12, "{blind:?}");
            assert_eq!(blind[&format!("ST1 {label}")], 8, "{blind:?}");
        }
        println!(
            "NEON_LD1_ST1_POST_MUTANTS {} {level:?}: {} of {} observable mutants reported MISMATCH \
             by the C oracle ({caught:?})",
            native_host::HOST,
            caught.values().sum::<usize>(),
            mutants.iter().filter(|mutant| mutant.4).count()
        );
        println!(
            "NEON_LD1_ST1_POST_WRITEBACK_BLIND {} {level:?}: {} writeback-only mutants pass the C \
             oracle and are refused by the decode gate ({blind:?}); the post-index base update is \
             dead in every executed LD1/ST1, so the addressing form is pinned by the decode gate only",
            native_host::HOST,
            blind.values().sum::<usize>()
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
