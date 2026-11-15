// Copyright 2026 Andrew Yates | Apache-2.0
//! Finite native observation of the actual private spill-reload CSE transform.
//! This is not allocator, source-lowering, or formal-proof qualification.
//! Included by pipeline only for Linux AArch64 GNU unit tests.

use super::*;
use sha2::{Digest, Sha256};
use std::fmt::Write as _;
use std::fs;
use std::io::Read;
use std::path::Path;
use std::process::Command;
use trust_cg_ir::function::Type;
use trust_cg_ir::regs::{V18, X0, X1};

#[path = "../tests/common/rosetta.rs"]
mod process;

const CASES: usize = 24;
const CALLS: usize = CASES * 4;
const CHECKS: usize = CALLS * 3 * 96;

#[derive(Clone, Copy, Debug)]
struct Case {
    reg: PReg,
    other: PReg,
    bank: char,
    bytes: usize,
    fp: bool,
    load_origin: bool,
    cross: bool,
}

fn cases() -> Vec<Case> {
    let mut rows = Vec::new();
    for (reg, other, bank, bytes, fp) in [
        (W16, W17, 'w', 4, false),
        (H16, H17, 'h', 2, true),
        (S16, S17, 's', 4, true),
        (D16, D17, 'd', 8, true),
        (X16, X17, 'x', 8, false),
        (V16, V17, 'q', 16, true),
    ] {
        for load_origin in [false, true] {
            for cross in [false, true] {
                rows.push(Case {
                    reg,
                    other,
                    bank,
                    bytes,
                    fp,
                    load_origin,
                    cross,
                });
            }
        }
    }
    assert_eq!(rows.len(), CASES);
    rows
}

fn append(func: &mut IrMachFunction, block: BlockId, inst: IrMachInst) -> InstId {
    let id = func.push_inst(inst);
    func.append_inst(block, id);
    id
}

fn memory(op: IrOpcode, reg: PReg, base: PReg, offset: i64) -> IrMachInst {
    IrMachInst::new(
        op,
        vec![
            IrOperand::PReg(reg),
            IrOperand::PReg(base),
            IrOperand::Imm(offset),
        ],
    )
}

fn slot(op: IrOpcode, reg: PReg, id: u32) -> IrMachInst {
    IrMachInst::new(
        op,
        vec![IrOperand::PReg(reg), IrOperand::StackSlot(StackSlotId(id))],
    )
}

fn fixture(case: Case, name: &str) -> (IrMachFunction, InstId) {
    // void fn(const unsigned char seed[32], unsigned char snapshot[64]);
    let mut func = IrMachFunction::new(
        name.into(),
        IrSignature::new(vec![Type::Ptr, Type::Ptr], vec![]),
    );
    // Equal-sized/aligned slots let the frame layout establish actual adjacent
    // redzones without exposing any slot address to the CSE pass.
    for _ in 0..3 {
        func.alloc_stack_slot(IrStackSlot::new(16, 16));
    }
    let entry = func.entry;
    append(
        &mut func,
        entry,
        memory(IrOpcode::LdrRI, if case.fp { V16 } else { X16 }, X0, 0),
    );
    append(&mut func, entry, memory(IrOpcode::LdrRI, V17, X0, 16));
    for id in 0..3 {
        append(&mut func, entry, slot(IrOpcode::StrRI, V17, id));
    }
    if case.load_origin {
        // Initializer and first reload have distinct architectural registers:
        // the initializer cannot accidentally forward into that first reload.
        append(
            &mut func,
            entry,
            memory(IrOpcode::LdrRI, if case.fp { V17 } else { X17 }, X0, 0),
        );
        append(&mut func, entry, slot(IrOpcode::StrRI, case.other, 1));
        append(&mut func, entry, slot(IrOpcode::LdrRI, case.reg, 1));
    } else {
        append(&mut func, entry, slot(IrOpcode::StrRI, case.reg, 1));
    }
    let tail = if case.cross {
        let next = func.create_block();
        append(
            &mut func,
            entry,
            IrMachInst::new(IrOpcode::B, vec![IrOperand::Block(next)]),
        );
        func.blocks[entry.0 as usize].succs.push(next);
        func.blocks[next.0 as usize].preds.push(entry);
        next
    } else {
        entry
    };
    let reload = append(&mut func, tail, slot(IrOpcode::LdrRI, case.reg, 1));
    if case.fp {
        append(&mut func, tail, memory(IrOpcode::StrRI, V16, X1, 0));
    } else {
        append(&mut func, tail, memory(IrOpcode::StrRI, X16, X1, 0));
        append(&mut func, tail, memory(IrOpcode::StrRI, XZR, X1, 8));
    }
    // Capture all bytes of the target slot, including bytes outside a narrow
    // store, and both adjacent slots. These accesses do not name their addresses.
    for (id, output) in [(1, 16), (0, 32), (2, 48)] {
        append(&mut func, tail, slot(IrOpcode::LdrRI, V18, id));
        append(&mut func, tail, memory(IrOpcode::StrRI, V18, X1, output));
    }
    append(&mut func, tail, IrMachInst::new(IrOpcode::Ret, vec![]));
    (func, reload)
}

fn encode_actual(
    pipeline: &Pipeline,
    func: &mut IrMachFunction,
    transcript: &mut String,
) -> Vec<u8> {
    pipeline
        .validate_aarch64_mach_function_for_profile(func)
        .unwrap();
    let layout = pipeline.run_frame_lowering(func).unwrap();
    let offsets = crate::frame::stack_slot_frame_offsets(func, &layout);
    assert_eq!(offsets.len(), 3);
    let target = offsets[1].unwrap();
    assert_eq!(offsets[0], Some(target + 16));
    assert_eq!(offsets[2], Some(target - 16));
    writeln!(
        transcript,
        "FRAME {} offsets={offsets:?} layout={layout:#?}",
        func.name
    )
    .unwrap();
    resolve_branches(func).unwrap();
    pipeline.recheck_aarch64_post_regalloc(func).unwrap();
    writeln!(transcript, "ENCODED_IR {} {func:#?}", func.name).unwrap();
    let bytes = encode_function(func).unwrap();
    let mut word_index = 0;
    let mut branches = 0;
    for &block in &func.block_order {
        for &id in &func.block(block).insts {
            let inst = func.inst(id);
            if inst.is_pseudo() {
                continue;
            }
            if inst.opcode == IrOpcode::B {
                // The successor starts immediately after this B. Verify the
                // actual encoded branch, not only the input CFG metadata.
                assert_eq!(inst.operands, vec![IrOperand::Imm(1)]);
                assert_eq!(
                    &bytes[word_index * 4..word_index * 4 + 4],
                    &0x1400_0001_u32.to_le_bytes()
                );
                branches += 1;
            }
            word_index += 1;
        }
    }
    assert_eq!(word_index * 4, bytes.len());
    assert_eq!(branches, usize::from(func.blocks.len() == 2));
    bytes
}

fn cg_wrapper(assembly: &mut String, name: &str, bytes: &[u8]) {
    assert!(!bytes.is_empty() && bytes.len().is_multiple_of(4));
    writeln!(
        assembly,
        ".p2align 2\n.global {name}\n.type {name},%function\n{name}:"
    )
    .unwrap();
    for word in bytes.as_chunks::<4>().0 {
        writeln!(assembly, ".inst 0x{:08x}", u32::from_le_bytes(*word)).unwrap();
    }
    writeln!(assembly, ".size {name},.-{name}").unwrap();
}

fn reference_wrapper(assembly: &mut String, id: usize, case: Case) {
    // Independent GNU assembly: no encoder helpers or generated words. A
    // 64-byte active aligned frame contains guard/target/guard at 0/16/32.
    // No calls, SP pivot, or callee-saved register clobbers occur in this leaf.
    let name = format!("reference_{id}");
    let full = if case.fp { "q" } else { "x" };
    let lane = case.bank;
    writeln!(assembly, ".p2align 2\n.global {name}\n.type {name},%function\n{name}:\nsub sp,sp,#64\nldr {full}16,[x0]\nldr q17,[x0,#16]\nstr q17,[sp]\nstr q17,[sp,#16]\nstr q17,[sp,#32]").unwrap();
    if case.load_origin {
        writeln!(
            assembly,
            "ldr {full}17,[x0]\nstr {lane}17,[sp,#16]\nldr {lane}16,[sp,#16]"
        )
        .unwrap();
    } else {
        writeln!(assembly, "str {lane}16,[sp,#16]").unwrap();
    }
    if case.cross {
        writeln!(assembly, "b .L{name}_tail\n.L{name}_tail:").unwrap();
    }
    writeln!(assembly, "ldr {lane}16,[sp,#16]").unwrap();
    if case.fp {
        assembly.push_str("str q16,[x1]\n");
    } else {
        assembly.push_str("stp x16,xzr,[x1]\n");
    }
    writeln!(assembly, "ldr q18,[sp,#16]\nstr q18,[x1,#16]\nldr q18,[sp]\nstr q18,[x1,#32]\nldr q18,[sp,#32]\nstr q18,[x1,#48]\nadd sp,sp,#64\nret\n.size {name},.-{name}").unwrap();
}

fn snapshot(directory: &Path) {
    let mut rows = Vec::new();
    for entry in fs::read_dir(directory).unwrap() {
        let path = entry.unwrap().path();
        if path.file_name().unwrap() == "SHA256SUMS" {
            continue;
        }
        assert!(fs::symlink_metadata(&path).unwrap().is_file());
        let mut input = fs::File::open(&path).unwrap();
        let mut hash = Sha256::new();
        let mut buffer = [0; 65536];
        loop {
            let n = input.read(&mut buffer).unwrap();
            if n == 0 {
                break;
            }
            hash.update(&buffer[..n]);
        }
        rows.push(format!(
            "{:x}  {}\n",
            hash.finalize(),
            path.file_name().unwrap().to_str().unwrap()
        ));
    }
    rows.sort();
    fs::write(directory.join("SHA256SUMS"), rows.concat()).unwrap();
}

fn run(
    directory: &Path,
    label: &str,
    command: &mut Command,
    timeout: Duration,
) -> Result<process::TimedCommandOutput, String> {
    fs::write(
        directory.join(format!("{label}.argv")),
        format!("{command:?}\ntimeout={timeout:?}\n"),
    )
    .unwrap();
    let result = process::command_output_with_timeout(command, timeout);
    match &result {
        Ok(result) => {
            fs::write(
                directory.join(format!("{label}.stdout")),
                &result.output.stdout,
            )
            .unwrap();
            fs::write(
                directory.join(format!("{label}.stderr")),
                &result.output.stderr,
            )
            .unwrap();
            fs::write(
                directory.join(format!("{label}.status")),
                format!(
                    "status={}\ntimed_out={}\n",
                    result.output.status, result.timed_out
                ),
            )
            .unwrap();
        }
        Err(error) => {
            fs::write(
                directory.join(format!("{label}.spawn-error")),
                error.to_string(),
            )
            .unwrap();
        }
    }
    snapshot(directory);
    result.map_err(|error| error.to_string())
}

#[cfg(not(target_endian = "little"))]
compile_error!("native spill/reload fixtures require a little-endian target");

#[test]
fn native_spill_reload_cse_preserves_full_register_and_slot_state() {
    assert!(
        std::env::var_os("TCG_SPILL_RELOAD_CSE_OFF").is_none(),
        "required transform must not be disabled"
    );
    // Removed when this test ends, passed or failed, unless
    // `TRUST_CG_KEEP_TEST_OBJECTS` is set, which keeps the evidence (the
    // fixture, the assembly, the objects and each run's outputs).
    let directory_scratch = tempfile::Builder::new()
        .prefix("trust-cg-spill-reload-native-")
        .tempdir()
        .unwrap();
    let directory = directory_scratch.path().to_path_buf();
    let _directory_scratch = if std::env::var_os("TRUST_CG_KEEP_TEST_OBJECTS").is_some() {
        let kept = directory_scratch.keep();
        eprintln!(
            "spill-reload native evidence={kept:?} (kept: TRUST_CG_KEEP_TEST_OBJECTS is set)"
        );
        None
    } else {
        Some(directory_scratch)
    };
    fs::write(
        directory.join("fixture.rs"),
        include_bytes!("pipeline_spill_reload_native_tests.rs"),
    )
    .unwrap();
    let pipeline = Pipeline::new(PipelineConfig {
        target_triple: "aarch64-unknown-linux-gnu".into(),
        ..Default::default()
    });
    let mut assembly = String::from(".text\n");
    let mut driver = String::from(DRIVER);
    let mut transcript = String::new();
    let mut byte_rows = String::from("function\tlength\tsha256\thex\n");
    let mut rows = Vec::new();
    let mut transform_failures = Vec::new();
    let mut transforms = String::from("case\tbank\tload_origin\tcross\tremoved\treload_retained\n");
    for (id, case) in cases().into_iter().enumerate() {
        let (mut before, reload) = fixture(case, &format!("before_{id}"));
        let mut after = before.clone();
        after.name = format!("after_{id}");
        writeln!(transcript, "ORIGINAL case={id} {case:?}\n{before:#?}").unwrap();
        let slots = BTreeSet::from([StackSlotId(1)]);
        if case.cross {
            assert!(cross_block_spill_facts(&after, &slots).is_some());
        }
        let removed = elide_redundant_spill_slot_reloads_scoped(&mut after, &slots, case.cross);
        let retained = after
            .blocks
            .iter()
            .any(|block| block.insts.contains(&reload));
        let may_elide = case.load_origin || case.bytes == if case.fp { 16 } else { 8 };
        if removed != u32::from(may_elide) || retained == may_elide {
            transform_failures.push(format!(
                "case{id} {case:?}: removed={removed}, retained={retained}"
            ));
        }
        writeln!(
            transforms,
            "{id}\t{}\t{}\t{}\t{removed}\t{retained}",
            case.bank, case.load_origin, case.cross
        )
        .unwrap();
        writeln!(transcript, "AFTER_CSE case={id}\n{after:#?}").unwrap();
        for func in [&mut before, &mut after] {
            let bytes = encode_actual(&pipeline, func, &mut transcript);
            let hex = bytes
                .iter()
                .map(|byte| format!("{byte:02x}"))
                .collect::<String>();
            writeln!(
                byte_rows,
                "{}\t{}\t{:x}\t{hex}",
                func.name,
                bytes.len(),
                Sha256::digest(&bytes)
            )
            .unwrap();
            cg_wrapper(&mut assembly, &func.name, &bytes);
        }
        reference_wrapper(&mut assembly, id, case);
        writeln!(driver, "extern void before_{id}(const unsigned char*,unsigned char*);\nextern void after_{id}(const unsigned char*,unsigned char*);\nextern void reference_{id}(const unsigned char*,unsigned char*);").unwrap();
        rows.push(format!(
            "{{{{before_{id},after_{id},reference_{id}}},{},{}}}",
            case.bytes,
            u8::from(case.fp)
        ));
    }
    assert_eq!(rows.len(), CASES);
    assembly.push_str(".section .note.GNU-stack,\"\",%progbits\n");
    writeln!(
        driver,
        "static const struct Case cases[]={{ {} }};",
        rows.join(",\n")
    )
    .unwrap();
    driver.push_str(MAIN);
    for (name, bytes) in [
        ("words.S", assembly),
        ("driver.c", driver),
        ("machir.txt", transcript),
        ("machine-bytes.tsv", byte_rows),
        ("transforms.tsv", transforms),
    ] {
        fs::write(directory.join(name), bytes).unwrap();
    }
    snapshot(&directory);
    let executable = directory.join("native");
    let link = run(
        &directory,
        "link",
        Command::new("cc")
            .args(["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror"])
            .arg(directory.join("driver.c"))
            .arg(directory.join("words.S"))
            .arg("-o")
            .arg(&executable),
        process::codegen_link_timeout(),
    )
    .expect("native link process must start");
    assert!(
        !link.timed_out && link.output.status.code() == Some(0),
        "link failed: {directory:?}: {}",
        String::from_utf8_lossy(&link.output.stderr)
    );
    assert!(link.output.stdout.is_empty() && link.output.stderr.is_empty());
    // After an observed normal exit, attempt the poison before comparison
    // assertions, even for a baseline wrong answer (normal1, never success).
    // An abnormal/incomplete run supplies no cleanup assurance for another run.
    let normal = run(
        &directory,
        "native",
        &mut Command::new(&executable),
        process::codegen_run_timeout(),
    );
    let poison = if matches!(&normal, Ok(output) if !output.timed_out && output.output.status.code().is_some())
    {
        run(
            &directory,
            "poison",
            Command::new(&executable).arg("--poison"),
            process::codegen_run_timeout(),
        )
    } else {
        let reason =
            "poison not run: native process did not complete with an observed normal exit\n";
        fs::write(directory.join("poison.unrun"), reason).unwrap();
        Err(reason.to_string())
    };
    let mut failures = transform_failures;
    let expected = format!(
        "SPILL_RELOAD_NATIVE cases={CASES} calls_before={CALLS} calls_after={CALLS} calls_reference={CALLS} checks={CHECKS} mismatches_before=0 mismatches_after=0 mismatches_reference=0\n"
    );
    match normal {
        Ok(output)
            if !output.timed_out
                && output.output.status.code() == Some(0)
                && output.output.stdout == expected.as_bytes()
                && output.output.stderr.is_empty() => {}
        other => failures.push(format!(
            "native comparison failed; receipt={directory:?}/native.status; launched={}",
            other.is_ok()
        )),
    }
    match poison {
        Ok(output)
            if !output.timed_out
                && output.output.status.code() == Some(97)
                && output.output.stdout.is_empty()
                && output.output.stderr == b"EXPECTED_STATE_MISMATCH case=0 route=0 byte=0\n" => {}
        other => failures.push(format!(
            "poison control failed; receipt={directory:?}/poison.status; launched={}",
            other.is_ok()
        )),
    }
    snapshot(&directory);
    assert!(
        failures.is_empty(),
        "{} failures; evidence={directory:?}\n{}",
        failures.len(),
        failures.join("\n")
    );
}

const DRIVER: &str = r#"
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
typedef void (*Fn)(const unsigned char*,unsigned char*);
struct Case { Fn route[3]; unsigned bytes,fp; };
struct Output { unsigned char before[16],data[64],after[16]; };
_Static_assert(sizeof(struct Output)==96 && offsetof(struct Output,data)==16 && offsetof(struct Output,after)==80,"snapshot layout");
static _Alignas(16) unsigned char seed[32];
static unsigned long calls[3],mismatches[3],checks;
"#;

const MAIN: &str = r#"
int main(int argc,char **argv) {
    const int poison=argc==2 && strcmp(argv[1],"--poison")==0;
    if(argc!=1 && !poison) return 96;
    if(sizeof(cases)/sizeof(cases[0])!=24) return 98;
    for(size_t i=0;i<24;++i) {
        const struct Case *c=&cases[i];
        if(c->bytes>16 || c->bytes==0 || (!c->fp && c->bytes>8)) return 98;
        for(unsigned pattern=0;pattern<4;++pattern) {
            // Every seed has nonzero dirty upper X/Q bytes. Low lanes also
            // include 0/1/sign/all-one byte boundaries without FP interpretation.
            const unsigned char low[]={0,1,0x80,0xff};
            for(unsigned j=0;j<16;++j) seed[j]=j<2?low[pattern]:(unsigned char)(0x81+((j*13+pattern*29)%0x7e));
            for(unsigned j=16;j<32;++j) seed[j]=(unsigned char)(0x35+j*7+pattern*19);
            for(unsigned route=0;route<3;++route) {
                struct Output wanted,actual;
                memset(&wanted,0xa6,sizeof(wanted));
                memset(&actual,0xa6,sizeof(actual));
                memset(wanted.data,0,16);
                memcpy(wanted.data,seed,c->bytes);
                memcpy(wanted.data+16,seed+16,16);
                memcpy(wanted.data+16,seed,c->bytes);
                memcpy(wanted.data+32,seed+16,16);
                memcpy(wanted.data+48,seed+16,16);
                if(poison && i==0 && pattern==0 && route==0) wanted.data[0]^=1;
                c->route[route](seed,actual.data); ++calls[route];
                const unsigned char *a=(const unsigned char*)&actual,*w=(const unsigned char*)&wanted;
                unsigned bad=0,first=0;
                for(unsigned j=0;j<96;++j) {
                    ++checks;
                    if(a[j]!=w[j]) { if(!bad) first=j; ++bad; }
                }
                if(bad) {
                    if(poison && i==0 && pattern==0 && route==0 && first==16 && bad==1) {
                        fprintf(stderr,"EXPECTED_STATE_MISMATCH case=0 route=0 byte=0\n"); return 97;
                    }
                    ++mismatches[route];
                    fprintf(stderr,"STATE_MISMATCH case=%zu pattern=%u route=%u snapshot_byte=%u\n",i,pattern,route,first);
                }
            }
        }
    }
    if(poison || calls[0]!=96 || calls[1]!=96 || calls[2]!=96 || checks!=27648) return 98;
    printf("SPILL_RELOAD_NATIVE cases=24 calls_before=%lu calls_after=%lu calls_reference=%lu checks=%lu mismatches_before=%lu mismatches_after=%lu mismatches_reference=%lu\n",calls[0],calls[1],calls[2],checks,mismatches[0],mismatches[1],mismatches[2]);
    return (mismatches[0] || mismatches[1] || mismatches[2])?1:0;
}
"#;
