// trust-cg-codegen/tests/e2e_x86_64_sib_rmw.rs
//   x86-64 scaled-index (SIB) memory rows and memory-destination add/xor at
//   O2: each emitted in the object, then executed against clang
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The x86-64 body theorem (trust-cg-verify `x86_source_bound_body.rs`, ruling
// OD-227) states the scaled-index load and store rows and the
// read-modify-write `add`/`xor [m], r` rows that `X86Peephole`'s address folds
// and its RMW fusion produce at O1 and above, BEFORE register allocation. What
// runs after the theorem is trusted, not proved: frame-index elimination of a
// stack-slot SIB base, the slot prune and remap of SIB uses, register
// allocation's use-only reading of a SIB store's and an RMW row's operands,
// and the SIB presequencing replay. The per-compile `decode_check` compares
// the emitted bytes with the lowered rows only, so it cannot see a fault in
// those transforms (and does not check `movss`/`movsd` SIB loads at all).
//
// These tests are that lowering's execution check. Each fixture is the
// slice-25 fixture of the same name (`x86_source_bound_body_slice25_tests.rs`),
// compiled alone at O2 by the production `Compiler`; its object must contain
// the SIB or RMW instruction the fixture is for (decoded by the host's
// LLVM-family `objdump`, `common::disasm`), and every fixture is then linked
// with a C driver whose clang-compiled reference computes the same result on
// the same inputs. A slot fixture's SIB base is the stack pointer or frame
// pointer after frame-index elimination; an incoming fixture's is a register
// argument. A host without an x86-64 executor or an LLVM-family objdump
// prints a SKIP line for that leg only.

mod common;

use common::disasm::{DisasmInsn, ObjFormat, disassemble_x86_text, has_objdump_for};
use common::rosetta::{x86_64_cc, x86_64_link_run_or_skip};
use common::x86_64_object::assert_host_x86_64_object;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_ir::{BinOp, ICmpOp, Ty, ValueId};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

/// The host's object format, for the disassembler probe.
#[cfg(target_os = "macos")]
const HOST_FORMAT: ObjFormat = ObjFormat::MachO;
#[cfg(not(target_os = "macos"))]
const HOST_FORMAT: ObjFormat = ObjFormat::Elf;

/// The System V x86-64 triple of the host's object format. A module with a
/// bodyless external declaration (`panic_bounds`, `fill64`) is an FFI
/// boundary, so trust-ir requires its `target_info`, and it is compiled
/// through the matching `TargetSpec`.
const SUBJECT_TRIPLE: &str = if cfg!(target_os = "macos") {
    "x86_64-apple-darwin"
} else {
    "x86_64-unknown-linux-gnu"
};

fn subject_target_info() -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: SUBJECT_TRIPLE.into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        // `None`: derived from the triple; no claim beyond its own ABI.
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    }
}

/// One fixture: its function name, and the instruction its object must hold
/// (a predicate over the decoded stream, with its description).
struct Fixture {
    name: &'static str,
    form: &'static str,
    emitted: fn(&DisasmInsn) -> bool,
}

/// `(%base,%index,scale)` with any displacement: the operand text's SIB
/// part, `None` without one.
fn sib_of(operands: &str) -> Option<(String, String, u8)> {
    let open = operands.find('(')?;
    let close = operands[open..].find(')')? + open;
    let parts: Vec<&str> = operands[open + 1..close].split(',').collect();
    match parts.as_slice() {
        [base, index] if !index.is_empty() => {
            Some((base.trim().to_owned(), index.trim().to_owned(), 1))
        }
        [base, index, scale] => Some((
            base.trim().to_owned(),
            index.trim().to_owned(),
            scale.trim().parse().ok()?,
        )),
        _ => None,
    }
}

/// A load of `mnemonic` whose source is a SIB operand at `scale`, its base
/// not the stack or frame pointer (an incoming-memory row).
fn incoming_sib_load(insn: &DisasmInsn, mnemonic: &str, scale: u8) -> bool {
    insn.mnemonic == mnemonic
        && insn.operands.split_once("),").is_some_and(|(address, _)| {
            sib_of(&format!("{address})"))
                .is_some_and(|(base, _, s)| s == scale && base != "%rsp" && base != "%rbp")
        })
}

/// A store of `mnemonic` whose destination is a SIB operand at `scale`.
fn sib_store(insn: &DisasmInsn, mnemonic: &str, scale: u8) -> bool {
    insn.mnemonic == mnemonic
        && insn.operands.starts_with('%')
        && insn
            .operands
            .split_once(", ")
            .and_then(|(_, address)| sib_of(address))
            .is_some_and(|(_, _, s)| s == scale)
}

/// An access of `mnemonic` through a SIB operand whose base is the stack or
/// frame pointer (a stack-slot base after frame-index elimination), a store
/// when `store` (its source a register).
fn slot_sib_access(insn: &DisasmInsn, mnemonic: &str, store: bool) -> bool {
    insn.mnemonic == mnemonic
        && insn.operands.starts_with('%') == store
        && sib_of(&insn.operands).is_some_and(|(base, _, _)| base == "%rsp" || base == "%rbp")
}

/// `add`/`xor %r64, mem` (a memory destination), through a SIB operand at
/// `scale` or (`None`) through `[base + disp]`.
fn rmw(insn: &DisasmInsn, mnemonic: &str, scale: Option<u8>) -> bool {
    let Some((source, address)) = insn.operands.split_once(", ") else {
        return false;
    };
    insn.mnemonic == mnemonic
        && source.starts_with("%r")
        && address.contains('(')
        && match scale {
            Some(scale) => sib_of(address).is_some_and(|(_, _, s)| s == scale),
            None => sib_of(address).is_none(),
        }
}

const FIXTURES: &[Fixture] = &[
    Fixture {
        name: "e2e_byte_zext",
        form: "movzbl (%p,%i)",
        emitted: |insn| incoming_sib_load(insn, "movzbl", 1),
    },
    Fixture {
        name: "e2e_u64_scaled",
        form: "movq (%p,%i,8), %r",
        emitted: |insn| incoming_sib_load(insn, "movq", 8),
    },
    Fixture {
        name: "e2e_u32_scaled",
        form: "movl (%p,%i,4), %r",
        emitted: |insn| incoming_sib_load(insn, "movl", 4),
    },
    Fixture {
        name: "e2e_store_scaled",
        form: "movq %r, (%p,%i,8)",
        emitted: |insn| sib_store(insn, "movq", 8),
    },
    Fixture {
        name: "e2e_store_byte",
        form: "movb %r, (%p,%i)",
        emitted: |insn| sib_store(insn, "movb", 1),
    },
    Fixture {
        name: "e2e_slot_const",
        form: "movq (%rsp|%rbp,%k,8), %r",
        emitted: |insn| slot_sib_access(insn, "movq", false),
    },
    Fixture {
        name: "e2e_slot_guarded",
        form: "movzbl (%rsp|%rbp,%i)",
        emitted: |insn| slot_sib_access(insn, "movzbl", false),
    },
    Fixture {
        name: "e2e_slot_indexed_store",
        form: "movq %r, (%rsp|%rbp,%i)",
        emitted: |insn| slot_sib_access(insn, "movq", true),
    },
    Fixture {
        name: "e2e_add_into",
        form: "addq %r, (%p)",
        emitted: |insn| rmw(insn, "addq", None),
    },
    Fixture {
        name: "e2e_add_into_indexed",
        form: "addq %r, (%p,%i,8)",
        emitted: |insn| rmw(insn, "addq", Some(8)),
    },
    Fixture {
        name: "e2e_xor_into_indexed",
        form: "xorq %r, (%p,%i,8)",
        emitted: |insn| rmw(insn, "xorq", Some(8)),
    },
];

type V = ValueId;

/// `if index < bound { .. } else { panic_bounds(index, bound); trap }`, the
/// in-bounds block current.
fn bounds_check(f: &mut FunctionBuilder<'_>, panic: trust_ir::FuncId, index: V, bound: u64) {
    let (ok, fail) = (f.create_block(), f.create_block());
    let limit = f.iconst(Ty::U64, i128::from(bound));
    let test = f.icmp(ICmpOp::Ult, Ty::U64, index, limit);
    f.condbr(test, ok, vec![], fail, vec![]);
    f.switch_to_block(fail);
    f.call_void(panic, vec![index, limit]);
    f.unreachable();
    f.switch_to_block(ok);
}

/// The 16-byte local digit table, stored as two 8-byte constants.
fn digit_table(f: &mut FunctionBuilder<'_>, ty: Ty) -> V {
    let t = f.alloca(ty);
    let bytes = b"0123456789abcdef";
    for half in 0..2 {
        let word = u64::from_le_bytes(bytes[8 * half..8 * half + 8].try_into().unwrap());
        let value = f.iconst(Ty::U64, i128::from(word));
        let at = if half == 0 {
            t
        } else {
            f.gep_byte_offset(t, 8)
        };
        f.store(Ty::U64, at, value);
    }
    t
}

/// The module of fixture `name`: the slice-25 fixture's LIR, alone.
fn fixture_module(name: &str) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new_with_target_info(name, subject_target_info());
    let ptr = |ty: Ty| Ty::PtrMut(Box::new(ty));
    let element = |mb: &mut ModuleBuilder, ty: Ty, count: u64| {
        let ty = mb.add_type(ty);
        Ty::Array(ty, count)
    };
    let u8x16 = element(&mut mb, Ty::U8, 16);
    let u64x4 = element(&mut mb, Ty::U64, 4);
    let u64x16 = element(&mut mb, Ty::U64, 16);
    let panic_ty = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![]);
    let panic = mb.declare_function("panic_bounds", panic_ty);
    // `fill64` takes the slot's address, an untyped pointer (`alloca`'s).
    let fill64_ty = mb.add_func_type(vec![Ty::Ptr], vec![]);
    let fill64 = mb.declare_function("fill64", fill64_ty);
    let (params, results): (Vec<Ty>, Vec<Ty>) = match name {
        "e2e_byte_zext" => (vec![ptr(Ty::U8), Ty::U64], vec![Ty::U32]),
        "e2e_u64_scaled" => (vec![ptr(Ty::U64), Ty::U64, Ty::U64], vec![Ty::U64]),
        "e2e_u32_scaled" => (vec![ptr(Ty::U8), Ty::U64, Ty::U32], vec![Ty::U32]),
        "e2e_store_scaled" => (vec![ptr(Ty::U64), Ty::U64, Ty::U64, Ty::U64], vec![Ty::U64]),
        "e2e_store_byte" => (vec![ptr(Ty::U8), Ty::U64, Ty::U8], vec![]),
        "e2e_slot_const" => (vec![Ty::U64, Ty::U64], vec![Ty::U64]),
        "e2e_slot_guarded" => (vec![Ty::U64], vec![Ty::U8]),
        "e2e_slot_indexed_store" => (vec![Ty::U64, Ty::U64], vec![]),
        "e2e_add_into" => (vec![ptr(Ty::U64), Ty::U64], vec![]),
        "e2e_add_into_indexed" | "e2e_xor_into_indexed" => {
            (vec![ptr(Ty::U64), Ty::U64, Ty::U64], vec![])
        }
        other => unreachable!("no fixture {other}"),
    };
    let signature = mb.add_func_type(params.clone(), results);
    let mut f = mb.function(name.to_owned(), signature);
    let entry = f.create_block();
    let args: Vec<V> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    match name {
        "e2e_byte_zext" => {
            let at = f.gep(Ty::U8, args[0], vec![args[1]]);
            let byte = f.load(Ty::U8, at);
            let wide = f.zext(Ty::U8, Ty::U32, byte);
            f.ret(vec![wide]);
        }
        "e2e_u64_scaled" => {
            let at = f.gep(Ty::U64, args[0], vec![args[1]]);
            let value = f.load(Ty::U64, at);
            let sum = f.add(Ty::U64, value, args[2]);
            f.ret(vec![sum]);
        }
        "e2e_u32_scaled" => {
            let amount = f.iconst(Ty::U64, 2);
            let offset = f.binop(BinOp::Shl, Ty::U64, args[1], amount);
            let at = f.gep(Ty::U8, args[0], vec![offset]);
            let value = f.load(Ty::U32, at);
            let sum = f.add(Ty::U32, value, args[2]);
            f.ret(vec![sum]);
        }
        "e2e_store_scaled" => {
            let at = f.gep(Ty::U64, args[0], vec![args[1]]);
            f.store(Ty::U64, at, args[2]);
            let sum = f.add(Ty::U64, args[2], args[3]);
            f.ret(vec![sum]);
        }
        "e2e_store_byte" => {
            let at = f.gep(Ty::U8, args[0], vec![args[1]]);
            f.store(Ty::U8, at, args[2]);
            f.ret(vec![]);
        }
        "e2e_slot_const" => {
            let a = f.alloca(u64x4);
            let one = f.iconst(Ty::U64, 1);
            let two = f.iconst(Ty::U64, 2);
            let first = f.gep(Ty::U64, a, vec![one]);
            f.store(Ty::U64, first, args[0]);
            let second = f.gep(Ty::U64, a, vec![two]);
            f.store(Ty::U64, second, args[1]);
            let again = f.gep(Ty::U64, a, vec![one]);
            let value = f.load(Ty::U64, again);
            f.ret(vec![value]);
        }
        "e2e_slot_guarded" => {
            let t = digit_table(&mut f, u8x16);
            bounds_check(&mut f, panic, args[0], 16);
            let at = f.gep(Ty::U8, t, vec![args[0]]);
            let value = f.load(Ty::U8, at);
            f.ret(vec![value]);
        }
        "e2e_slot_indexed_store" => {
            let a = f.alloca(u64x16);
            f.call_void(fill64, vec![a]);
            bounds_check(&mut f, panic, args[0], 16);
            let at = f.gep(Ty::U64, a, vec![args[0]]);
            f.store(Ty::U64, at, args[1]);
            f.call_void(fill64, vec![a]);
            f.ret(vec![]);
        }
        "e2e_add_into" => {
            let old = f.load(Ty::U64, args[0]);
            let new = f.add(Ty::U64, old, args[1]);
            f.store(Ty::U64, args[0], new);
            f.ret(vec![]);
        }
        "e2e_add_into_indexed" | "e2e_xor_into_indexed" => {
            let at = f.gep(Ty::U64, args[0], vec![args[1]]);
            let old = f.load(Ty::U64, at);
            let op = if name == "e2e_xor_into_indexed" {
                BinOp::Xor
            } else {
                BinOp::Add
            };
            let new = f.binop(op, Ty::U64, old, args[2]);
            f.store(Ty::U64, at, new);
            f.ret(vec![]);
        }
        _ => unreachable!(),
    }
    f.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The fixture's O2 object from the production compiler.
fn object_at_o2(name: &str) -> Vec<u8> {
    let result = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O2,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(SUBJECT_TRIPLE).expect("the host x86-64 triple is a known triple"),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&fixture_module(name))
    .unwrap_or_else(|error| panic!("{name}: the O2 x86-64 object must compile: {error:?}"));
    assert!(!result.object_code.is_empty(), "{name}: empty object");
    result.object_code
}

/// The C driver: the fixtures' clang-compiled references, the runtime the
/// slot fixtures call (`panic_bounds` exits 3; `fill64` fills the slot on
/// its first call of a pair and records it on the second), and one `CASE
/// name k got ref` line per input.
const DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

uint32_t e2e_byte_zext(const uint8_t *p, uint64_t i);
uint64_t e2e_u64_scaled(const uint64_t *p, uint64_t i, uint64_t x);
uint32_t e2e_u32_scaled(const uint8_t *p, uint64_t i, uint32_t x);
uint64_t e2e_store_scaled(uint64_t *p, uint64_t i, uint64_t x, uint64_t y);
void e2e_store_byte(uint8_t *p, uint64_t i, uint8_t x);
uint64_t e2e_slot_const(uint64_t x, uint64_t y);
uint8_t e2e_slot_guarded(uint64_t i);
void e2e_slot_indexed_store(uint64_t i, uint64_t x);
void e2e_add_into(uint64_t *p, uint64_t x);
void e2e_add_into_indexed(uint64_t *p, uint64_t i, uint64_t x);
void e2e_xor_into_indexed(uint64_t *p, uint64_t i, uint64_t x);

void panic_bounds(uint64_t index, uint64_t bound) {
    printf("PANIC %llu %llu\n", (unsigned long long)index, (unsigned long long)bound);
    exit(3);
}

static unsigned fill64_calls;
static uint64_t fill64_seen[16];
static uint64_t pattern(unsigned k) { return 0x0123456789abcdefull * (k + 1) ^ 0x5a5a5a5a5a5a5a5aull; }
void fill64(uint64_t *a) {
    if (fill64_calls++ % 2 == 0) {
        for (unsigned k = 0; k < 16; k++) a[k] = pattern(k);
    } else {
        memcpy(fill64_seen, a, sizeof fill64_seen);
    }
}

static void check(const char *name, int k, unsigned long long got, unsigned long long ref) {
    printf("CASE %s %d %llx %llx\n", name, k, got, ref);
}

int main(void) {
    static const uint64_t idx[] = {0, 1, 2, 5, 7, 11, 14, 15};
    const int n = (int)(sizeof idx / sizeof idx[0]);
    uint8_t bytes[64];
    uint64_t words[16];
    for (int k = 0; k < 64; k++) bytes[k] = (uint8_t)(0x93 * k + 0x21);
    for (int k = 0; k < 16; k++) words[k] = 0x9e3779b97f4a7c15ull * (uint64_t)(k + 3);
    const char *digits = "0123456789abcdef";
    for (int k = 0; k < n; k++) {
        uint64_t i = idx[k];
        check("byte_zext", k, e2e_byte_zext(bytes, i), (uint32_t)bytes[i]);
        check("u64_scaled", k, e2e_u64_scaled(words, i, 0x1111 * i + 7), words[i] + 0x1111 * i + 7);
        uint32_t w32; memcpy(&w32, bytes + (i << 2), 4);
        check("u32_scaled", k, e2e_u32_scaled(bytes, i, 0xabcd0000u + (uint32_t)i), w32 + 0xabcd0000u + (uint32_t)i);
        uint64_t out[16]; memcpy(out, words, sizeof out);
        uint64_t sum = e2e_store_scaled(out, i, 0xfeed0000ull + i, 0x77);
        check("store_scaled", k, out[i] ^ sum, (0xfeed0000ull + i) ^ (0xfeed0000ull + i + 0x77));
        check("store_scaled_rest", k, memcmp(out, words, 8 * i) == 0 && memcmp(out + i + 1, words + i + 1, 8 * (15 - i)) == 0, 1);
        uint8_t b[64]; memcpy(b, bytes, sizeof b);
        e2e_store_byte(b, i, (uint8_t)(0xc3 ^ i));
        check("store_byte", k, b[i], (uint8_t)(0xc3 ^ i));
        check("store_byte_rest", k, memcmp(b, bytes, i) == 0 && memcmp(b + i + 1, bytes + i + 1, 63 - i) == 0, 1);
        check("slot_const", k, e2e_slot_const(0x1000 + i, 0x2000 + i), 0x1000 + i);
        check("slot_guarded", k, e2e_slot_guarded(i), (uint8_t)digits[i]);
        e2e_slot_indexed_store(i, 0xdead0000beefull + i);
        for (unsigned m = 0; m < 16; m++) {
            check("slot_indexed_store", k * 16 + (int)m, fill64_seen[m], m == i ? 0xdead0000beefull + i : pattern(m));
        }
        uint64_t cell = 0x8000000000000000ull + i;
        e2e_add_into(&cell, 0x8000000000000001ull * (i + 1));
        check("add_into", k, cell, 0x8000000000000000ull + i + 0x8000000000000001ull * (i + 1));
        memcpy(out, words, sizeof out);
        e2e_add_into_indexed(out, i, 0x0f0f0f0f0f0f0f0full + i);
        check("add_into_indexed", k, out[i], words[i] + 0x0f0f0f0f0f0f0f0full + i);
        check("add_into_indexed_rest", k, memcmp(out, words, 8 * i) == 0 && memcmp(out + i + 1, words + i + 1, 8 * (15 - i)) == 0, 1);
        memcpy(out, words, sizeof out);
        e2e_xor_into_indexed(out, i, 0xf0f0f0f0f0f0f0f0ull ^ i);
        check("xor_into_indexed", k, out[i], words[i] ^ 0xf0f0f0f0f0f0f0f0ull ^ i);
        check("xor_into_indexed_rest", k, memcmp(out, words, 8 * i) == 0 && memcmp(out + i + 1, words + i + 1, 8 * (15 - i)) == 0, 1);
    }
    printf("DONE\n");
    return 0;
}
"#;

/// Every fixture compiles at O2 into an object that defines it and holds the
/// SIB or RMW instruction it is for.
#[test]
fn every_fixture_emits_its_sib_or_rmw_instruction_at_o2() {
    let decodes = has_objdump_for(HOST_FORMAT);
    if !decodes {
        eprintln!(
            "SKIP: every_fixture_emits_its_sib_or_rmw_instruction_at_o2: the instruction leg not \
             run: no objdump on this host decodes the host object format"
        );
    }
    for fixture in FIXTURES {
        let object = object_at_o2(fixture.name);
        assert_host_x86_64_object(fixture.name, &object, &[fixture.name], &[]);
        if !decodes {
            continue;
        }
        let insns = disassemble_x86_text(&object)
            .unwrap_or_else(|| panic!("{}: the object does not decode", fixture.name));
        assert!(
            insns.iter().any(fixture.emitted),
            "{}: no `{}` in its O2 object:\n{}",
            fixture.name,
            fixture.form,
            insns
                .iter()
                .map(|insn| format!("  {:#x}: {} {}", insn.offset, insn.mnemonic, insn.operands))
                .collect::<Vec<_>>()
                .join("\n")
        );
    }
}

/// Every fixture's O2 object, linked with the C driver and executed, gives
/// the clang reference's result on every input.
#[test]
fn every_fixture_executes_as_its_clang_reference_at_o2() {
    let test = "every_fixture_executes_as_its_clang_reference_at_o2";
    let objects: Vec<(&str, Vec<u8>)> = FIXTURES
        .iter()
        .map(|fixture| (fixture.name, object_at_o2(fixture.name)))
        .collect();
    if !x86_64_link_run_or_skip(test, "link and run") {
        return;
    }
    let scratch = tempfile::Builder::new()
        .prefix("trust_cg_x86_sib_rmw-")
        .tempdir()
        .unwrap();
    let dir = scratch.path();
    let driver = dir.join("driver.c");
    std::fs::write(&driver, DRIVER).unwrap();
    let binary = dir.join("sib_rmw");
    let mut cc = x86_64_cc();
    cc.args(["-O1", "-o"]).arg(&binary).arg(&driver);
    for (name, object) in &objects {
        let path = dir.join(format!("{name}.o"));
        std::fs::write(&path, object).unwrap();
        cc.arg(&path);
    }
    let link = cc.output().expect("cc spawns");
    assert!(
        link.status.success(),
        "link failed: {}",
        String::from_utf8_lossy(&link.stderr)
    );
    let run = std::process::Command::new(&binary)
        .output()
        .expect("the linked fixture runs");
    let stdout = String::from_utf8_lossy(&run.stdout).to_string();
    assert!(
        run.status.success() && stdout.lines().last() == Some("DONE"),
        "the run failed (status {:?}):\n{stdout}\n{}",
        run.status,
        String::from_utf8_lossy(&run.stderr)
    );
    let mut cases = 0usize;
    let mut wrong = Vec::new();
    for line in stdout.lines().filter(|line| line.starts_with("CASE ")) {
        let fields: Vec<&str> = line.split_whitespace().collect();
        let [_, _, _, got, reference] = fields.as_slice() else {
            panic!("malformed line {line:?}");
        };
        cases += 1;
        if got != reference {
            wrong.push(line.to_owned());
        }
    }
    // 8 indices: 14 single checks and the 16 slot words each.
    assert_eq!(cases, 8 * (14 + 16), "{stdout}");
    assert!(wrong.is_empty(), "wrong results:\n{}", wrong.join("\n"));
}
