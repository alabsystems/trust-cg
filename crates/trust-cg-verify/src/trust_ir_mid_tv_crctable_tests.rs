// trust-cg-verify/trust_ir_mid_tv_crctable_tests.rs - tests of the CRC-table checker
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The bit-serial CRC-32 step over one byte (eight shift-xor diamonds, as
//! full unrolling leaves `for _ in 0..8 { c = if c & 1 != 0 { P ^ (c >> 1) }
//! else { c >> 1 } }`) becomes a load from a 256-entry table: accepted, the
//! table is the standard reflected CRC-32 table, and the target agrees with
//! the source in the reference interpreter on every byte and on seeded
//! states. Refused: a region that xors two different constants (not one
//! polynomial), one that loads (not a pure function of its input), a claimed
//! polynomial the region does not xor, a table with one entry off, a table
//! built for another polynomial, an input over more than 8 bits, an input
//! whose range is not derived, a region value used after the join, a region
//! still rolled as a loop, a region whose join is its own block, a name that
//! is not fresh, and a global the rewrite does not append or that no region
//! names.
//!
//! The witness types (`CrcTableWitness`, `CrcTable`, `CRC_TABLE_ENTRIES`,
//! the `PassWitness::CrcTable` variant and `MidTvError::NotCrcTable`) are
//! provisional surfaces pending the owner's sign-off
//! (`docs/wasm32_perf_roadmap.md`, "Pending owner sign-off").

use super::super::{
    DifferentialBudget, MidTvError, PassWitness, check_pass, compare_samples, run_samples,
    seeded_inputs,
};
use super::*;

const HEADER: &str = "; TrustIr text format v1\nmodule \"crctable\"\n\
                      target \"wasm32-unknown-unknown\" 4 little\n\n";

const CRC32: u32 = 0xEDB8_8320;

fn module(body: &str) -> Module {
    trust_ir::parser::parse_module(&format!("{HEADER}{body}"))
        .unwrap_or_else(|e| panic!("test module failed to parse: {e}\n{body}"))
}

fn f(m: &Module) -> &Function {
    m.functions.iter().find(|f| f.name == "f").expect("f")
}

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

/// `f(state, byte)`: `c = (state ^ byte) & mask`, eight unrolled rounds of
/// `c = c & 1 != 0 ? poly ^ (c >> 1) : c >> 1` (round `r` branches in block
/// `bb(10 + 3r)` or the first block, its arms are `bb(11 + 3r)` and
/// `bb(12 + 3r)`, its join `bb(13 + 3r)`), then `c ^ (state >> 8)`.
/// `rounds` may differ from 8; `xor_of(r)` is the constant round `r` xors.
fn crc_program(mask: &str, rounds: u32, xor_of: &dyn Fn(u32) -> u32, tail: &str) -> String {
    let mut text = String::new();
    let mut consts = String::new();
    for r in 0..rounds {
        consts.push_str(&format!("\x20   %{} = const u32 {}\n", 500 + r, xor_of(r)));
    }
    let mut cur = 5u32;
    for r in 0..rounds {
        let (even, odd, join) = (11 + 3 * r, 12 + 3 * r, 13 + 3 * r);
        let bit = 100 + 10 * r;
        if r > 0 {
            text.push_str(&format!("bb{}(%{cur}: u32):\n", 10 + 3 * r));
        }
        text.push_str(&format!(
            "\x20   %{bit} = and u32 %{cur}, %6\n\
             \x20   switch %{bit} [ 0: bb{even} default: bb{odd} ]\n\
             bb{even}:\n\
             \x20   %{a} = lshr u32 %{cur}, %6\n\
             \x20   br bb{join}(%{a})\n\
             bb{odd}:\n\
             \x20   %{b} = lshr u32 %{cur}, %6\n\
             \x20   %{c} = xor u32 %{p}, %{b}\n\
             \x20   br bb{join}(%{c})\n",
            a = bit + 1,
            b = bit + 2,
            c = bit + 3,
            p = 500 + r,
        ));
        cur = bit + 4;
    }
    let last = 10 + 3 * rounds;
    format!(
        "functy.0 = (u32, u8) -> (u32)\n\n\
fn @f(functy.0) {{\n\
bb0(%0: u32, %1: u8):\n\
\x20   br bb1\n\
bb1:\n\
\x20   %2 = zext u8 %1 to u32\n\
\x20   %3 = xor u32 %0, %2\n\
\x20   %4 = const u32 {mask}\n\
\x20   %5 = and u32 %3, %4\n\
\x20   %6 = const u32 1\n\
{consts}\
{text}\
bb{last}(%{cur}: u32):\n\
\x20   %7 = const u32 8\n\
\x20   %8 = lshr u32 %0, %7\n\
\x20   %9 = xor u32 %{cur}, %8\n\
{tail}\
\x20   ret %9\n\
}}\n"
    )
}

fn standard(mask: &str) -> String {
    crc_program(mask, 8, &|_| CRC32, "")
}

/// The index of the region's first instruction in `bb1` (the first round's
/// `and`): after the casts, the mask, `%6` and the eight constants.
const START: usize = 13;

/// The witness for the standard program on `m`, with `entries` as the
/// table's bytes.
fn witness_with(m: &Module, polynomial: u128, data: Vec<u8>) -> CrcTableWitness {
    let (new_types, elem) = match m.types.iter().position(|t| *t == Ty::U8) {
        Some(i) => (Vec::new(), trust_ir::TyId::new(i as u32)),
        None => (vec![Ty::U8], trust_ir::TyId::new(m.types.len() as u32)),
    };
    CrcTableWitness {
        tables: vec![CrcTable {
            block: BlockId::new(1),
            start: START,
            exit: BlockId::new(34),
            input: v(5),
            polynomial,
            global: GlobalId::new(m.globals.len() as u32),
            values: (900..906).map(v).collect(),
        }],
        new_types,
        new_globals: vec![Global {
            name: "f.crc_table".to_string(),
            ty: Ty::Array(elem, data.len() as u64),
            mutable: false,
            initializer: Some(Constant::Bytes { data, utf8: false }),
            linkage: trust_ir::Linkage::Internal,
            tls: None,
            align: Some(4),
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
        }],
    }
}

/// The reflected CRC table of `poly`, little-endian.
fn table_bytes(poly: u32) -> Vec<u8> {
    let mut data = Vec::new();
    for byte in 0..256u32 {
        let mut c = byte;
        for _ in 0..8 {
            c = if c & 1 != 0 { poly ^ (c >> 1) } else { c >> 1 };
        }
        data.extend_from_slice(&c.to_le_bytes());
    }
    data
}

/// The claim is refused as not the region's table lookup, for a reason
/// whose text contains `why`.
fn refused_region(m: &Module, w: &CrcTableWitness, why: &str) {
    match rebuild_crc_table(m, 32, f(m), w) {
        Err(MidTvError::NotCrcTable { why: found, .. }) => {
            assert!(found.contains(why), "refused for `{found}`, not `{why}`");
        }
        other => panic!("not refused as a region: {:?}", other.map(|_| ())),
    }
}

fn refused_global(m: &Module, w: &CrcTableWitness) {
    let r = rebuild_crc_table(m, 32, f(m), w);
    assert!(
        matches!(r, Err(MidTvError::BadGlobal { .. })),
        "{:?}",
        r.map(|_| ())
    );
}

#[test]
fn the_unrolled_crc_byte_step_becomes_a_table_lookup_and_agrees() {
    let m = module(&standard("255"));
    let src = f(&m);
    let w = witness_with(&m, u128::from(CRC32), table_bytes(CRC32));
    let (out, verdict) = rebuild_crc_table(&m, 32, src, &w).expect("accepted");
    assert_eq!(verdict.exact, 1);
    check_pass(&m, 32, src, &out, &PassWitness::CrcTable(w.clone())).expect("check_pass");
    // Every round's block is gone: the entry, the region's block and the join.
    assert_eq!(out.blocks.len(), 3, "{out}");
    assert!(
        out.blocks.iter().flat_map(|b| &b.body).any(|n| matches!(
            n.inst,
            Inst::Load {
                ty: Ty::U32,
                align: Some(4),
                ..
            }
        )),
        "{out}"
    );
    // The standard reflected CRC-32 table.
    let Some(Constant::Bytes { data, .. }) = &w.new_globals[0].initializer else {
        panic!("bytes");
    };
    let entry = |i: usize| u32::from_le_bytes(data[4 * i..4 * i + 4].try_into().expect("4"));
    assert_eq!(entry(0), 0);
    assert_eq!(entry(1), 0x7707_3096);
    assert_eq!(entry(128), CRC32);
    assert_eq!(entry(255), 0x2D02_EF8D);
    // The target, run with the table appended, agrees with the source on
    // every byte and on seeded states.
    let mut with_table = m.clone();
    with_table.types.extend(w.new_types.iter().cloned());
    with_table.globals.extend(w.new_globals.iter().cloned());
    let mut inputs = seeded_inputs(&m, src, 32, 64, 11).expect("scalar parameters");
    for byte in 0..=255u8 {
        let mut input = inputs[0].clone();
        input[1] = trust_ir::InterpretValue::int(Ty::U8, i128::from(byte)).expect("u8");
        inputs.push(input);
    }
    let (a, _) = run_samples(&m, src, &inputs, DifferentialBudget::default());
    let (t, _) = run_samples(&with_table, &out, &inputs, DifferentialBudget::default());
    let report = compare_samples(&a, &t);
    assert!(report.mismatch.is_none(), "{:?}", report.mismatch);
    assert_eq!(report.compared, inputs.len(), "every input is compared");
}

#[test]
fn regions_that_are_not_one_byte_crc_steps_are_refused() {
    let base = standard("255");
    let good = |m: &Module| witness_with(m, u128::from(CRC32), table_bytes(CRC32));
    // The control is accepted.
    {
        let m = module(&base);
        rebuild_crc_table(&m, 32, f(&m), &good(&m)).expect("control");
    }
    // Not a CRC: the rounds xor two different constants.
    {
        let m = module(&crc_program(
            "255",
            8,
            &|r| if r == 3 { 0x04C1_1DB7 } else { CRC32 },
            "",
        ));
        refused_region(&m, &good(&m), "two different constants");
    }
    // Not a pure function of the input: a round loads.
    {
        let m = module(&base.replace(
            "\x20   %112 = lshr u32 %104, %6\n",
            "\x20   %600 = const usize 0\n\x20   %601 = inttoptr usize %600 to ptr\n\
             \x20   %112 = load u32, ptr %601\n",
        ));
        refused_region(&m, &good(&m), "not a pure integer operation");
    }
    // A loop over more than 8 bits: the input is masked to 9 bits.
    {
        let m = module(&standard("511"));
        refused_region(&m, &good(&m), "reaches 511");
    }
    // An input whose range is not derived from its definition.
    {
        let m = module(&base.replace("%5 = and u32 %3, %4", "%5 = or u32 %3, %4"));
        refused_region(&m, &good(&m), "range is not derived");
    }
    // A value of the region used after the join.
    {
        let m = module(&standard("255").replace(
            "\x20   %9 = xor u32 %174, %8\n",
            "\x20   %9 = xor u32 %170, %8\n",
        ));
        refused_region(&m, &good(&m), "used outside it");
    }
    // A region whose join is its own block.
    {
        let m = module(&base);
        let mut w = good(&m);
        w.tables[0].exit = BlockId::new(1);
        refused_region(&m, &w, "its exit");
    }
    // A name that is not fresh.
    {
        let m = module(&base);
        let mut w = good(&m);
        w.tables[0].values[3] = v(8);
        refused_region(&m, &w, "not fresh");
    }
}

#[test]
fn a_rolled_bit_loop_is_not_a_region() {
    // The same step still rolled: `bb2` loops eight times. The region from
    // `bb1` reaches the loop's cycle and is refused.
    let m = module(
        "functy.0 = (u32, u8) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32, %1: u8):\n\
\x20   br bb1\n\
bb1:\n\
\x20   %2 = zext u8 %1 to u32\n\
\x20   %3 = xor u32 %0, %2\n\
\x20   %4 = const u32 255\n\
\x20   %5 = and u32 %3, %4\n\
\x20   %6 = const u32 1\n\
\x20   %7 = const u32 3988292384\n\
\x20   %10 = const u32 0\n\
\x20   %11 = const u32 8\n\
\x20   br bb2(%5, %10)\n\
bb2(%20: u32, %21: u32):\n\
\x20   %22 = icmp ult u32 %21, %11\n\
\x20   condbr %22, bb3, bb5(%20)\n\
bb3:\n\
\x20   %23 = and u32 %20, %6\n\
\x20   %24 = lshr u32 %20, %6\n\
\x20   %25 = xor u32 %7, %24\n\
\x20   %26 = icmp ne u32 %23, %10\n\
\x20   %27 = select u32 %26, %25, %24\n\
\x20   %28 = add u32 %21, %6\n\
\x20   br bb2(%27, %28)\n\
bb5(%30: u32):\n\
\x20   %31 = lshr u32 %0, %11\n\
\x20   %32 = xor u32 %30, %31\n\
\x20   ret %32\n\
}\n",
    );
    let mut w = witness_with(&m, u128::from(CRC32), table_bytes(CRC32));
    w.tables[0].start = 8;
    w.tables[0].exit = BlockId::new(5);
    refused_region(&m, &w, "cycle");
}

#[test]
fn tables_and_polynomials_off_the_region_are_refused() {
    let m = module(&standard("255"));
    // The claimed polynomial is not the one the region xors.
    let w = witness_with(&m, 0x04C1_1DB7, table_bytes(CRC32));
    refused_region(&m, &w, "the polynomial is 0xedb88320");
    // A table with one entry off by one.
    let mut data = table_bytes(CRC32);
    data[4 * 77] ^= 1;
    refused_global(&m, &witness_with(&m, u128::from(CRC32), data));
    // A table built for another polynomial.
    refused_global(
        &m,
        &witness_with(&m, u128::from(CRC32), table_bytes(0x82F6_3B78)),
    );
    // A table one entry short.
    let mut short = table_bytes(CRC32);
    short.truncate(255 * 4);
    refused_global(&m, &witness_with(&m, u128::from(CRC32), short));
    // A region naming a global the rewrite does not append, which leaves
    // the appended one unnamed.
    let mut w = witness_with(&m, u128::from(CRC32), table_bytes(CRC32));
    w.tables[0].global = GlobalId::new(7);
    refused_global(&m, &w);
    w.new_globals.push(w.new_globals[0].clone());
    w.tables[0].global = GlobalId::new(m.globals.len() as u32 + 5);
    refused_global(&m, &w);
    // A target that loads another entry size is not the claimed rewrite.
    let src = f(&m);
    let w = witness_with(&m, u128::from(CRC32), table_bytes(CRC32));
    let (mut out, _) = rebuild_crc_table(&m, 32, src, &w).expect("accepted");
    for node in out.blocks.iter_mut().flat_map(|b| &mut b.body) {
        if let Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(k @ 4),
        } = &mut node.inst
        {
            *k = 8;
        }
    }
    assert!(matches!(
        check_pass(&m, 32, src, &out, &PassWitness::CrcTable(w)),
        Err(MidTvError::TargetDiffers { .. })
    ));
}
