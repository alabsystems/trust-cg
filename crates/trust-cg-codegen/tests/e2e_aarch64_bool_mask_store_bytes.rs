// trust-cg-codegen/tests/e2e_aarch64_bool_mask_store_bytes.rs
//
// The BYTE IMAGE of a `<N x bool>` logical mask at a memory boundary, measured
// on this AArch64 host against trust-ir's normative interpreter
// (`docs/SPEC_RATIFICATIONS.md` §4 in trust-ir).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The referee stores a `<N x bool>` as N bytes, one per lane, `0xFF` for a
// true lane and `0x00` for a false one (`crates/trust-ir/src/interpret.rs`,
// `encode_value`'s bool-mask arm; `byte_size(Vector) = lanes * byte_size(elem)`
// with `byte_size(Bool) = 1`), and decodes any non-zero byte as `true`.
// trust-cg carries the mask in the register class its PRODUCER chose — a
// `<8 x bool>` from a `<8 x i16>` compare is a V128 of eight 16-bit lanes, a
// `<8 x bool>` from a `<8 x i8>` compare is a V64 of eight byte lanes — and a
// `Store` used to write that carrier verbatim (`translate_store`: "a vector
// store's WIDTH follows the stored value's LIR type").
//
// Measured 2026-09-22 on aarch64-darwin, trust-cg 017781483 BEFORE the refusal
// landed (`out` is 32 bytes of 0xAA sentinel, printed as four LE u64):
//
//   <8 x bool> from <8 x i16> sge [0,-1,2,-3,4,-5,6,-7] >= 0
//     referee : 00ff00ff00ff00ff aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa
//     trust-cg: 0000ffff0000ffff 0000ffff0000ffff aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa
//   <8 x bool> from <8 x i8> sge (same lanes)
//     referee : 00ff00ff00ff00ff aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa
//     trust-cg: not measurable from constants — `Constant::Vector` of
//               `<8 x i8>` is refused ("lowers to unsupported LIR type V64");
//               with loaded operands the V64 mask (`translate_v8i8_icmp`:
//               "per-byte 0x00/0xFF") would have been stored as 8 bytes
//               (`str d`), the one carrier whose image is the referee's by
//               coincidence of lane width
//   <4 x bool> from <4 x i32> sge [0,-1,2,-3] >= 0
//     referee : aaaaaaaa00ff00ff aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa
//     trust-cg: 00000000ffffffff 00000000ffffffff aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa
//   <2 x bool> from <2 x i64> sge [0,-1] >= 0
//     referee : aaaaaaaaaaaa00ff aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa
//     trust-cg: ffffffffffffffff 0000000000000000 aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa
//   <16 x bool> from <16 x i8> sge (lanes 0..16 alternating)
//     referee : 00ff00ff00ff00ff 00ff00ff00ff00ff aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa
//     trust-cg: 00ff00ff00ff00ff 00ff00ff00ff00ff aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa
//   Load <8 x bool> from [01 00 01 00 01 00 01 00 | bb x 24], Store to out
//     referee : 00ff00ff00ff00ff aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa
//     trust-cg: 0001000100010001 bbbbbbbbbbbbbbbb aaaaaaaaaaaaaaaa aaaaaaaaaaaaaaaa
//
// Two of the six agree by coincidence of lane width only; the other four write
// a different number of bytes at different offsets, and the load copies raw
// bytes the referee canonicalises. Since 2026-09-22 the adapter refuses every
// memory-layout use of a bool-lane vector by name
// (`AdapterError::BoolLaneLayoutNotAdmitted`, `trust-cg-lower/src/adapter.rs`),
// so this file now pins (1) the referee's image on every host and (2) the
// compile-time refusal on every host, with (3) a native non-vacuity control —
// the physical `<8 x i16>` mask stored as its own type still compiles, links
// and runs, writing the sixteen bytes the register holds.

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{CompileError, Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_lower::adapter::AdapterError;

use trust_ir::{
    Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction, ICmpOp,
    Inst, InstrNode, Interpreter, Module as TrustIrModule, Ty, ValueId,
};

#[path = "common/native_host.rs"]
mod native_host;

const SENTINEL: u64 = 0xAAAA_AAAA_AAAA_AAAA;

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn vec_ty(elem: Ty, lanes: u32) -> Ty {
    Ty::Vector(Box::new(elem), lanes)
}

fn bool_ty(lanes: u32) -> Ty {
    vec_ty(Ty::Bool, lanes)
}

/// Lane values `0, -1, 2, -3, ...`: `>= 0` at the even lanes.
fn alternating(lanes: u32) -> Vec<Constant> {
    (0..lanes)
        .map(|lane| {
            let lane = i128::from(lane);
            Constant::Int(if lane % 2 == 0 { lane } else { -lane })
        })
        .collect()
}

/// `mask = <N x elem> sge alternating, zeros` — the compare that PRODUCES the
/// bool mask, appended to `body`, returning the mask's ValueId.
fn push_compare(body: &mut Vec<InstrNode>, elem: Ty, lanes: u32, next: &mut u32) -> ValueId {
    let ty = vec_ty(elem, lanes);
    let a = v(*next);
    let b = v(*next + 1);
    let mask = v(*next + 2);
    *next += 3;
    body.push(
        InstrNode::new(Inst::Const {
            ty: ty.clone(),
            value: Constant::Vector(alternating(lanes)),
        })
        .with_result(a),
    );
    body.push(
        InstrNode::new(Inst::Const {
            ty: ty.clone(),
            value: Constant::Vector(vec![Constant::Int(0); lanes as usize]),
        })
        .with_result(b),
    );
    body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Sge,
            ty,
            lhs: a,
            rhs: b,
        })
        .with_result(mask),
    );
    mask
}

/// The native side: `fn name(out: ptr) { *out = (<N x elem> sge ..) as <N x bool> }`
/// when `store_ty` is the bool type, or the physical control when it is the
/// compare's own integer vector type — the alternating constant stored as
/// itself, a mask-free store of the same width through the same store path.
fn build_native_store(name: &str, elem: Ty, lanes: u32, store_ty: Ty) -> TrustIrModule {
    let mut module = TrustIrModule::new(name);
    let ft = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(0), name, ft, BlockId::new(0));
    let mut body = Vec::new();
    let mut next = 1;
    let value = if store_ty == bool_ty(lanes) {
        push_compare(&mut body, elem, lanes, &mut next)
    } else {
        // Physical control: store the alternating integer vector itself.
        let a = v(next);
        next += 1;
        body.push(
            InstrNode::new(Inst::Const {
                ty: store_ty.clone(),
                value: Constant::Vector(alternating(lanes)),
            })
            .with_result(a),
        );
        a
    };
    let _ = next;
    body.push(InstrNode::new(Inst::Store {
        ty: store_ty,
        ptr: v(0),
        value,
        volatile: false,
        align: None,
    }));
    body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(v(0), Ty::Ptr)],
        body,
    }];
    module
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    module
}

/// The native round trip: `fn name(in: ptr, out: ptr) { *out = *in as <N x bool> }`.
fn build_native_roundtrip(name: &str, lanes: u32) -> TrustIrModule {
    let mut module = TrustIrModule::new(name);
    let ft = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(0), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(v(0), Ty::Ptr), (v(1), Ty::Ptr)],
        body: vec![
            InstrNode::new(Inst::Load {
                ty: bool_ty(lanes),
                ptr: v(0),
                volatile: false,
                align: None,
            })
            .with_result(v(2)),
            InstrNode::new(Inst::Store {
                ty: bool_ty(lanes),
                ptr: v(1),
                value: v(2),
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    }];
    module
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    module
}

/// The referee side of [`build_native_store`]: a 32-byte stack buffer filled
/// with the sentinel, the same compare and store, then the four u64 words
/// read back and returned.
fn build_referee_store(elem: Ty, lanes: u32) -> TrustIrModule {
    let mut module = TrustIrModule::new("referee_store");
    let ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U64; 4],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(0), "referee", ft, BlockId::new(0));
    let mut body = Vec::new();
    let mut next = 0;
    let buf = push_sentinel_buffer(&mut body, &mut next, SENTINEL);
    let mask = push_compare(&mut body, elem, lanes, &mut next);
    body.push(InstrNode::new(Inst::Store {
        ty: bool_ty(lanes),
        ptr: buf,
        value: mask,
        volatile: false,
        align: None,
    }));
    let words = push_read_words(&mut body, &mut next, buf);
    body.push(InstrNode::new(Inst::Return { values: words }));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body,
    }];
    module
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    module
}

/// The referee side of [`build_native_roundtrip`]: `in` holds `input` (four
/// LE u64 words), `out` the sentinel; load `<N x bool>` from `in`, store to
/// `out`, return `out`'s words.
fn build_referee_roundtrip(lanes: u32, input: [u64; 4]) -> TrustIrModule {
    let mut module = TrustIrModule::new("referee_roundtrip");
    let ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U64; 4],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(0), "referee", ft, BlockId::new(0));
    let mut body = Vec::new();
    let mut next = 0;
    let out = push_sentinel_buffer(&mut body, &mut next, SENTINEL);
    let inp = push_words_buffer(&mut body, &mut next, input);
    let loaded = v(next);
    next += 1;
    body.push(
        InstrNode::new(Inst::Load {
            ty: bool_ty(lanes),
            ptr: inp,
            volatile: false,
            align: None,
        })
        .with_result(loaded),
    );
    body.push(InstrNode::new(Inst::Store {
        ty: bool_ty(lanes),
        ptr: out,
        value: loaded,
        volatile: false,
        align: None,
    }));
    let words = push_read_words(&mut body, &mut next, out);
    body.push(InstrNode::new(Inst::Return { values: words }));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body,
    }];
    module
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    module
}

fn push_sentinel_buffer(body: &mut Vec<InstrNode>, next: &mut u32, fill: u64) -> ValueId {
    push_words_buffer(body, next, [fill; 4])
}

/// `Alloca [u64; 4]` (as `Alloca { ty: U64, count: 4 }`) with the four words
/// stored through `GEP` over a `u64` pointee; returns the base pointer.
fn push_words_buffer(body: &mut Vec<InstrNode>, next: &mut u32, words: [u64; 4]) -> ValueId {
    let count = v(*next);
    let buf = v(*next + 1);
    *next += 2;
    body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(4),
        })
        .with_result(count),
    );
    body.push(
        InstrNode::new(Inst::Alloca {
            ty: Ty::U64,
            count: Some(count),
            align: Some(16),
        })
        .with_result(buf),
    );
    for (index, word) in words.iter().enumerate() {
        let idx = v(*next);
        let ptr = v(*next + 1);
        let val = v(*next + 2);
        *next += 3;
        body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(index as i128),
            })
            .with_result(idx),
        );
        body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::U64,
                base: buf,
                indices: vec![idx],
                inbounds: true,
            })
            .with_result(ptr),
        );
        body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(*word as i128),
            })
            .with_result(val),
        );
        body.push(InstrNode::new(Inst::Store {
            ty: Ty::U64,
            ptr,
            value: val,
            volatile: false,
            align: None,
        }));
    }
    buf
}

fn push_read_words(body: &mut Vec<InstrNode>, next: &mut u32, buf: ValueId) -> Vec<ValueId> {
    let mut words = Vec::with_capacity(4);
    for index in 0..4u32 {
        let idx = v(*next);
        let ptr = v(*next + 1);
        let word = v(*next + 2);
        *next += 3;
        body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(i128::from(index)),
            })
            .with_result(idx),
        );
        body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::U64,
                base: buf,
                indices: vec![idx],
                inbounds: true,
            })
            .with_result(ptr),
        );
        body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::U64,
                ptr,
                volatile: false,
                align: None,
            })
            .with_result(word),
        );
        words.push(word);
    }
    words
}

fn referee_words(module: &TrustIrModule) -> [u64; 4] {
    let outcome = Interpreter::with_module(module)
        .execute_func(FuncId::new(0), [])
        .expect("the referee executes the bool-mask memory image");
    let mut words = [0u64; 4];
    for (slot, value) in words.iter_mut().zip(&outcome.returns) {
        *slot =
            u64::try_from(value.as_int().expect("u64 word").as_unsigned()).expect("u64 word fits");
    }
    words
}

fn hex_words(words: &[u64; 4]) -> String {
    words
        .iter()
        .map(|w| format!("{w:016x}"))
        .collect::<Vec<_>>()
        .join(" ")
}

/// Referee image of a `<N x bool>` mask with `true` at the even lanes: one
/// `0xFF`/`0x00` byte per lane, the sentinel untouched after byte N.
fn expected_referee_store(lanes: u32) -> [u64; 4] {
    let mut bytes = [0xAAu8; 32];
    for (lane, byte) in bytes.iter_mut().enumerate().take(lanes as usize) {
        *byte = if lane % 2 == 0 { 0xFF } else { 0x00 };
    }
    words_of(&bytes)
}

fn words_of(bytes: &[u8; 32]) -> [u64; 4] {
    let mut words = [0u64; 4];
    for (i, word) in words.iter_mut().enumerate() {
        *word = u64::from_le_bytes(bytes[i * 8..i * 8 + 8].try_into().unwrap());
    }
    words
}

/// The producers of a `<N x bool>` value the adapter admits: `(elem, lanes)`
/// of the compare and the referee's canonical image after the store.
fn producers() -> Vec<(Ty, u32)> {
    vec![
        (Ty::I16, 8),
        (Ty::I8, 8),
        (Ty::I32, 4),
        (Ty::I64, 2),
        (Ty::I8, 16),
    ]
}

/// (1) The referee's byte image, on every host: N bytes, one per lane,
/// `0xFF` / `0x00`, nothing written past byte N — regardless of the compare's
/// lane width.
#[test]
fn referee_stores_one_byte_per_lane_for_every_admitted_producer() {
    for (elem, lanes) in producers() {
        let words = referee_words(&build_referee_store(elem.clone(), lanes));
        assert_eq!(
            words,
            expected_referee_store(lanes),
            "<{lanes} x bool> from <{lanes} x {elem:?}>: referee image {}",
            hex_words(&words)
        );
    }
}

/// (1b) The referee's load canonicalises: a `0x01` byte lane reads back as a
/// true lane and is re-stored as `0xFF`; the store writes exactly N bytes.
#[test]
fn referee_load_store_round_trip_canonicalises_to_all_ones_per_lane() {
    let input = words_of(&{
        let mut bytes = [0xBBu8; 32];
        for (lane, byte) in bytes.iter_mut().enumerate().take(8) {
            *byte = if lane % 2 == 0 { 0x01 } else { 0x00 };
        }
        bytes
    });
    let words = referee_words(&build_referee_roundtrip(8, input));
    assert_eq!(
        words,
        expected_referee_store(8),
        "referee round trip image {}",
        hex_words(&words)
    );
}

fn compile_error(module: &TrustIrModule) -> CompileError {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O0,
        ..CompilerConfig::default()
    })
    .with_codegen_license(permit_unlicensed());
    compiler
        .compile(module)
        .expect_err("a bool-lane vector at a memory boundary must not compile")
}

fn assert_bool_lane_refusal(module: &TrustIrModule, lanes: u32, site: &str) {
    let err = compile_error(module);
    let CompileError::Adapter(AdapterError::BoolLaneLayoutNotAdmitted { ty, location, .. }) = &err
    else {
        panic!("{site}: expected AdapterError::BoolLaneLayoutNotAdmitted, got {err:?}");
    };
    assert_eq!(ty, &bool_ty(lanes), "{site}: refused type");
    assert!(
        location.contains(site),
        "{site}: refusal location `{location}` must name the boundary"
    );
}

/// (2) Every producer's `Store { ty: <N x bool> }` is refused by name at the
/// adapter, on every host, so the carrier bytes never reach memory. The
/// `<8 x i8>` producer's `Constant::Vector` operands lower now (they were
/// refused first by a V64-constant gate), so it is driven from constants to
/// the same gate as every other producer; it is also covered with loaded
/// operands by `trust-cg-lower/tests/bool_lane_layout_refusal.rs`.
#[test]
fn store_of_a_bool_lane_vector_is_refused_by_name_for_every_producer() {
    for (elem, lanes) in producers() {
        let module = build_native_store("_store_bool", elem, lanes, bool_ty(lanes));
        assert_bool_lane_refusal(&module, lanes, "Store");
    }
}

/// (2b) The load side of the round trip is refused the same way.
#[test]
fn load_of_a_bool_lane_vector_is_refused_by_name() {
    assert_bool_lane_refusal(&build_native_roundtrip("_roundtrip_bool", 8), 8, "Load");
}

const CONTROL_DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
#include <string.h>

extern void _store_v8i16(uint64_t *out);

int main(void) {
    uint64_t out[4];
    memset(out, 0xAA, sizeof out);
    _store_v8i16(out);
    printf("%016llx %016llx %016llx %016llx\n",
           (unsigned long long)out[0], (unsigned long long)out[1],
           (unsigned long long)out[2], (unsigned long long)out[3]);
    return 0;
}
"#;

fn link_run_stdout(tag: &str, obj: &[u8], driver: &str) -> Option<String> {
    if !native_host::NATIVE {
        eprintln!("SKIP: link-and-run requires an AArch64 Linux GNU or macOS host");
        return None;
    }
    let dir = std::env::temp_dir().join(format!("trust_cg_{tag}_e2e_{}", std::process::id()));
    let _ = fs::create_dir_all(&dir);
    let obj_path = dir.join(format!("{tag}.o"));
    let drv_path = dir.join("driver.c");
    let bin_path = dir.join(format!("{tag}_bin"));
    fs::write(&obj_path, obj).expect("write .o");
    fs::write(&drv_path, driver).expect("write driver");
    let link = Command::new("cc")
        .args([
            drv_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
            "-o",
            bin_path.to_str().unwrap(),
        ])
        .args(native_host::c_math_library_args())
        .output()
        .expect("cc available");
    assert!(
        link.status.success(),
        "link failed:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );
    let run = Command::new(bin_path.to_str().unwrap())
        .output()
        .expect("run binary");
    assert!(
        run.status.success(),
        "driver exited {:?}",
        run.status.code()
    );
    let _ = fs::remove_dir_all(&dir);
    Some(String::from_utf8_lossy(&run.stdout).trim().to_string())
}

/// (3) Non-vacuity control, native on an AArch64 host: the PHYSICAL `<8 x
/// i16>` vector stored as its own type compiles, links and runs, and writes
/// the sixteen bytes the register holds — the store path itself is live, so
/// the refusal above is the bool-lane gate and nothing else. The physical
/// image is also what the referee stores for `<8 x i16>` (lane-by-lane LE).
#[test]
fn physical_i16_vector_store_control_compiles_and_matches_referee() {
    let lanes = 8;
    let physical = vec_ty(Ty::I16, lanes);
    let module = build_native_store("_store_v8i16", Ty::I16, lanes, physical.clone());
    let compiler = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O0,
        ..CompilerConfig::default()
    })
    .with_codegen_license(permit_unlicensed());
    let result = compiler
        .compile(&module)
        .expect("NON-VACUITY: the physical <8 x i16> store of the same shape must compile");
    assert!(!result.object_code.is_empty());

    // Referee: the same integer vector stored lane-by-lane, little-endian.
    let mut bytes = [0xAAu8; 32];
    for (lane, chunk) in bytes
        .as_chunks_mut::<2>()
        .0
        .iter_mut()
        .enumerate()
        .take(lanes as usize)
    {
        let lane = lane as i16;
        let value = if lane % 2 == 0 { lane } else { -lane };
        *chunk = value.to_le_bytes();
    }
    let expected = words_of(&bytes);

    let Some(stdout) = link_run_stdout("bool_mask_control", &result.object_code, CONTROL_DRIVER)
    else {
        return;
    };
    let got: Vec<u64> = stdout
        .split_whitespace()
        .map(|w| u64::from_str_radix(w, 16).expect("hex word"))
        .collect();
    assert_eq!(
        got,
        expected.to_vec(),
        "physical <8 x i16> store: native {stdout} vs referee {}",
        hex_words(&expected)
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
