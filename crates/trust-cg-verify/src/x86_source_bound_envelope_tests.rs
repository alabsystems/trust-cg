// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Tests of the x86-64 System V ABI envelope owner. The Rust-level tests need
//! no solver; the qualification tests at the end replay through the admitted
//! AY and Clean and fail without them, naming what is missing
//! (`x86_source_bound_body::tests::replay_environment`).

use super::*;
use trust_cg_lower::function::{BasicBlock, Signature};
use trust_cg_lower::instructions::{Block, Instruction, Value};

const SYSV: Option<X86SourceBoundAbi> = Some(X86SourceBoundAbi::SystemV);

/// `push rbp; mov rbp, rsp; pop rbp; ret`, measured from the JIT.
const VOID: &[u8] = &[0x55, 0x48, 0x89, 0xe5, 0x5d, 0xc3];
/// `push rbp; mov rbp, rsp; call rel32; ud2`, measured from the JIT.
const DIVERGING: &[u8] = &[0x55, 0x48, 0x89, 0xe5, 0xe8, 0, 0, 0, 0, 0x0f, 0x0b];

fn instruction(opcode: L, args: Vec<Value>, results: Vec<Value>) -> Instruction {
    Instruction {
        opcode,
        args,
        results,
    }
}

/// A `subject` whose chain is `jumps` unconditional jumps then `tail`.
fn source(params: Vec<Type>, returns: Vec<Type>, jumps: u32, tail: Vec<Instruction>) -> Function {
    let mut function = Function::new(
        "subject",
        Signature {
            params: params.clone(),
            returns,
        },
    );
    function.entry_block = Block(0);
    let mut order = Vec::new();
    for block in 0..=jumps {
        let instructions = if block == jumps {
            tail.clone()
        } else {
            vec![instruction(
                L::Jump {
                    dest: Block(block + 1),
                },
                vec![],
                vec![],
            )]
        };
        let block_params = if block == 0 {
            params
                .iter()
                .enumerate()
                .map(|(i, ty)| (Value(i as u32), ty.clone()))
                .collect()
        } else {
            vec![]
        };
        function.blocks.insert(
            Block(block),
            BasicBlock {
                params: block_params,
                instructions,
                source_locs: vec![],
            },
        );
        order.push(Block(block));
    }
    function.block_order = order;
    function
}

fn void_source(jumps: u32) -> Function {
    source(
        vec![],
        vec![],
        jumps,
        vec![instruction(L::Return, vec![], vec![])],
    )
}

fn diverging_source(jumps: u32, callee: &str, binding: DirectCallBinding) -> Function {
    source(
        vec![],
        vec![],
        jumps,
        vec![
            instruction(
                L::Call {
                    name: callee.into(),
                    binding,
                },
                vec![],
                vec![],
            ),
            instruction(L::Trap, vec![], vec![]),
        ],
    )
}

fn abort_source() -> Function {
    diverging_source(0, "abort_probe", DirectCallBinding::Interposable)
}

/// The manifest encoding, spelled out independently of the parser.
fn encode(rows: &[X86FixupRow]) -> Vec<u8> {
    let mut out = X86_SYMBOLIC_FIXUP_MANIFEST_MAGIC.to_vec();
    out.extend_from_slice(&(rows.len() as u64).to_be_bytes());
    for row in rows {
        let (offset, kind, label, name, flag): (u64, u8, &[u8], &str, u8) = match row {
            X86FixupRow::Call {
                offset,
                callee,
                exact_module,
            } => (*offset, 0, b"callee", callee, u8::from(*exact_module)),
            X86FixupRow::Symbol {
                offset,
                symbol,
                kind,
            } => (*offset, 1, b"symbol", symbol, *kind),
        };
        out.extend_from_slice(&offset.to_be_bytes());
        out.push(kind);
        out.extend_from_slice(&(label.len() as u64).to_be_bytes());
        out.extend_from_slice(label);
        out.extend_from_slice(&(name.len() as u64).to_be_bytes());
        out.extend_from_slice(name.as_bytes());
        out.push(flag);
    }
    out
}

fn call_row(offset: u64) -> X86FixupRow {
    X86FixupRow::Call {
        offset,
        callee: "abort_probe".into(),
        exact_module: false,
    }
}

fn no_rows() -> Vec<u8> {
    encode(&[])
}

fn abort_rows() -> Vec<u8> {
    encode(&[call_row(5)])
}

fn build(source: &Function, code: &[u8], manifest: &[u8]) -> Result<(), X86EnvelopeRefusal> {
    source_bound_x86_envelope(source, "subject", code, manifest, SYSV).map(|_| ())
}

fn refusal(source: &Function, code: &[u8], manifest: &[u8]) -> X86EnvelopeRefusal {
    match source_bound_x86_envelope(source, "subject", code, manifest, SYSV) {
        Ok(_) => panic!("{code:02x?} built an envelope"),
        Err(refusal) => refusal,
    }
}

#[test]
fn owner_builds_for_the_pinned_void_and_diverging_bytes() {
    for jumps in [0, 1, 3] {
        let source = void_source(jumps);
        let rows = no_rows();
        let owner = source_bound_x86_envelope(&source, "subject", VOID, &rows, SYSV)
            .expect("the JIT's empty void body builds");
        assert_eq!(owner.shape(), &X86EnvelopeShape::VoidReturn);
        assert_eq!(owner.statement().name, X86_VOID_RETURN_ENVELOPE_NAME);
        assert_eq!(owner.terminator_offset(), 5);
        assert!(!owner.statement().is_degenerate());
        // return target and RBP split per byte, RSP and memory whole.
        assert_eq!(owner.parts().len(), 18);
        assert!(owner.parts().iter().all(|part| {
            is_x86_envelope_part_name(&part.name)
                && part.preconditions == owner.statement().preconditions
                && !part.is_degenerate()
        }));

        let source = diverging_source(jumps, "abort_probe", DirectCallBinding::Interposable);
        let rows = abort_rows();
        let owner = source_bound_x86_envelope(&source, "subject", DIVERGING, &rows, SYSV)
            .expect("the JIT's panic entry builds");
        assert_eq!(
            owner.shape(),
            &X86EnvelopeShape::DivergingCall {
                callee: "abort_probe".into(),
                exact_module: false
            }
        );
        assert_eq!(owner.statement().name, X86_DIVERGING_CALL_ENVELOPE_NAME);
        assert_eq!(owner.terminator_offset(), 9);
        // alignment and memory whole, the return slot per byte.
        assert_eq!(owner.parts().len(), 10);
    }
    // An exact-module callee is bound by its flag.
    let exact = diverging_source(
        0,
        "local",
        DirectCallBinding::ExactModuleFunction { function: 1 },
    );
    let rows = encode(&[X86FixupRow::Call {
        offset: 5,
        callee: "local".into(),
        exact_module: true,
    }]);
    build(&exact, DIVERGING, &rows).expect("an exact-module callee builds");
    // Frames with callee-saved pushes and a local area are in the closed set.
    let framed = [
        0x55, 0x48, 0x89, 0xe5, 0x53, 0x41, 0x54, 0x48, 0x83, 0xec, 0x10, 0x48, 0x83, 0xc4, 0x10,
        0x41, 0x5c, 0x5b, 0x5d, 0xc3,
    ];
    build(&void_source(0), &framed, &no_rows()).expect("a framed body with saves builds");
}

/// The replayed queries are shape-constant: every function with these bytes
/// replays the same parts (so AY's caches dedupe), and a change to the
/// builder shows up here. A golden holds every part's exact query, in replay
/// order, each after a `; part <name>` line. `TCG_X86_ENVELOPE_GOLDEN_WRITE=1`
/// rewrites them.
#[test]
fn envelope_theorems_match_their_goldens() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("src")
        .join("x86_source_bound_envelope_golden");
    for (file, source, code, manifest) in [
        ("void_return.smt2", void_source(0), VOID, no_rows()),
        (
            "diverging_call.smt2",
            abort_source(),
            DIVERGING,
            abort_rows(),
        ),
    ] {
        let owner = source_bound_x86_envelope(&source, "subject", code, &manifest, SYSV).unwrap();
        let mut smt2 = String::new();
        for part in owner.parts() {
            let query = crate::ay_bridge::generate_smt2_query_raw(
                part,
                &crate::ay_bridge::AYConfig::default(),
            );
            assert!(
                !query.contains("Array"),
                "{file}: the theorem is array-free"
            );
            assert!(query.contains("QF_BV"), "{file}: {query}");
            smt2.push_str(&format!("; part {}\n{query}", part.name));
        }
        let path = dir.join(file);
        if std::env::var_os("TCG_X86_ENVELOPE_GOLDEN_WRITE").is_some() {
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(&path, &smt2).unwrap();
        }
        let golden = std::fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("{}: {error}", path.display()));
        assert_eq!(smt2, golden, "{file}");
        // Another function name, same bytes: the same query.
        let mut renamed = source.clone();
        renamed.name = "other".into();
        let other = source_bound_x86_envelope(&renamed, "other", code, &manifest, SYSV).unwrap();
        assert_eq!(other.parts(), owner.parts());
    }
}

#[test]
fn source_outside_the_envelope_is_unsupported() {
    let unsupported = |source: &Function, abi| {
        assert!(!source_admits_x86_envelope_owner(source, abi));
        matches!(
            source_bound_x86_envelope(source, &source.name, VOID, &no_rows(), abi),
            Err(X86EnvelopeRefusal::Unsupported(_))
        )
    };
    // A call WITH arguments is the x86 body lane's (slice 3) territory.
    let with_args = source(
        vec![Type::I64],
        vec![],
        0,
        vec![
            instruction(
                L::Call {
                    name: "abort_probe".into(),
                    binding: DirectCallBinding::Interposable,
                },
                vec![Value(0)],
                vec![],
            ),
            instruction(L::Trap, vec![], vec![]),
        ],
    );
    assert!(unsupported(&with_args, SYSV));
    // A returned value.
    let returns = source(
        vec![Type::I64],
        vec![Type::I64],
        0,
        vec![instruction(L::Return, vec![Value(0)], vec![])],
    );
    assert!(unsupported(&returns, SYSV));
    // A jump that passes a block argument to a block with a parameter.
    let mut block_args = void_source(1);
    block_args.blocks.get_mut(&Block(1)).unwrap().params = vec![(Value(7), Type::I64)];
    assert!(unsupported(&block_args, SYSV));
    // `call f; ret` and a trap-only body.
    let call_ret = source(
        vec![],
        vec![],
        0,
        vec![
            instruction(
                L::Call {
                    name: "abort_probe".into(),
                    binding: DirectCallBinding::Interposable,
                },
                vec![],
                vec![],
            ),
            instruction(L::Return, vec![], vec![]),
        ],
    );
    assert!(unsupported(&call_ret, SYSV));
    let trap_only = source(
        vec![],
        vec![],
        0,
        vec![instruction(L::Trap, vec![], vec![])],
    );
    assert!(unsupported(&trap_only, SYSV));
    // A native dependency binding.
    let native = diverging_source(
        0,
        "abort_probe",
        DirectCallBinding::DeclaredExternalFunction { function: 3 },
    );
    assert!(unsupported(&native, SYSV));
    // A block off the chain (every LIR block must be on it).
    let mut orphan = void_source(0);
    orphan.blocks.insert(
        Block(9),
        BasicBlock {
            params: vec![],
            instructions: vec![instruction(L::Return, vec![], vec![])],
            source_locs: vec![],
        },
    );
    orphan.block_order.push(Block(9));
    assert!(unsupported(&orphan, SYSV));
    // Windows x64 and no ABI.
    assert!(unsupported(
        &void_source(0),
        Some(X86SourceBoundAbi::WindowsX64)
    ));
    assert!(unsupported(&void_source(0), None));
    // The machine function must be the LIR function's own.
    assert!(matches!(
        source_bound_x86_envelope(&void_source(0), "other", VOID, &no_rows(), SYSV),
        Err(X86EnvelopeRefusal::Mismatch(
            X86EnvelopeMismatch::Pairing { .. }
        ))
    ));
}

/// Forms outside the closed set, including the RSP-writing PUSH/POP and the
/// profile-counter forms the JIT patches inside the range after
/// certification.
#[test]
fn excluded_encodings_are_unsupported() {
    let counter_prefix: Vec<u8> = [
        &[0x50, 0x9c, 0x48, 0xb8][..],
        &[0; 8],
        &[0xf0, 0x48, 0xff, 0x00, 0x9d, 0x58],
    ]
    .concat();
    let cases: Vec<(&str, Vec<u8>, usize)> = vec![
        ("pop rsp", vec![0x55, 0x48, 0x89, 0xe5, 0x5c, 0xc3], 4),
        ("push rsp", vec![0x54, 0x48, 0x89, 0xe5, 0x5d, 0xc3], 0),
        (
            "call-counter trampoline",
            [&counter_prefix[..], VOID].concat(),
            1,
        ),
        (
            "movabs + lock inc (block counter)",
            [
                &[0x55, 0x48, 0x89, 0xe5, 0x48, 0xb8][..],
                &[0; 8],
                &[0xf0, 0x48, 0xff, 0x00, 0x5d, 0xc3],
            ]
            .concat(),
            4,
        ),
        ("lock inc", vec![0xf0, 0x48, 0xff, 0x00, 0xc3], 0),
        (
            "dead parameter copy",
            vec![0x55, 0x48, 0x89, 0xe5, 0x48, 0x89, 0xf8, 0x5d, 0xc3],
            4,
        ),
        ("nop", vec![0x90, 0x55, 0x48, 0x89, 0xe5, 0x5d, 0xc3], 0),
        (
            "jmp",
            vec![0xeb, 0x00, 0x55, 0x48, 0x89, 0xe5, 0x5d, 0xc3],
            0,
        ),
        (
            "rex.w push",
            vec![0x48, 0x55, 0x48, 0x89, 0xe5, 0x5d, 0xc3],
            0,
        ),
        (
            "sub rsp, negative imm8",
            vec![0x55, 0x48, 0x89, 0xe5, 0x48, 0x83, 0xec, 0xf8, 0x5d, 0xc3],
            4,
        ),
        (
            "truncated call",
            vec![0x55, 0x48, 0x89, 0xe5, 0xe8, 0, 0],
            4,
        ),
    ];
    // The battery asserts its own cardinality, so a case cannot vanish.
    assert_eq!(cases.len(), 11);
    for (label, code, at) in cases {
        match refusal(&void_source(0), &code, &no_rows()) {
            X86EnvelopeRefusal::Unsupported(X86EnvelopeUnsupported::Bytes { offset, .. }) => {
                assert_eq!(offset, at, "{label}")
            }
            other => panic!("{label}: {other}"),
        }
    }
    // PUSH/POP R12 (41 54 / 41 5C) are NOT the RSP forms.
    build(
        &void_source(0),
        &[0x55, 0x48, 0x89, 0xe5, 0x41, 0x54, 0x41, 0x5c, 0x5d, 0xc3],
        &no_rows(),
    )
    .expect("push r12; pop r12 is admitted");
}

#[test]
fn manifest_parser_is_exact() {
    let rows = vec![
        call_row(5),
        X86FixupRow::Symbol {
            offset: 12,
            symbol: "g".into(),
            kind: 3,
        },
    ];
    assert_eq!(
        parse_x86_symbolic_fixup_manifest(&encode(&rows)),
        Ok(rows.clone())
    );
    assert_eq!(parse_x86_symbolic_fixup_manifest(&no_rows()), Ok(vec![]));
    let mut trailing = encode(&rows);
    trailing.push(0);
    assert!(parse_x86_symbolic_fixup_manifest(&trailing).is_err());
    let mut magic = encode(&rows);
    magic[0] ^= 1;
    assert!(parse_x86_symbolic_fixup_manifest(&magic).is_err());
    let mut count = encode(&rows);
    let at = X86_SYMBOLIC_FIXUP_MANIFEST_MAGIC.len();
    count[at..at + 8].copy_from_slice(&u64::MAX.to_be_bytes());
    assert!(parse_x86_symbolic_fixup_manifest(&count).is_err());
    let mut kind = encode(&[call_row(5)]);
    kind[at + 16] = 2;
    assert!(parse_x86_symbolic_fixup_manifest(&kind).is_err());
    let mut flag = encode(&[call_row(5)]);
    *flag.last_mut().unwrap() = 2;
    assert!(parse_x86_symbolic_fixup_manifest(&flag).is_err());
    let mut label = encode(&[call_row(5)]);
    label[at + 25] = b'x';
    assert!(parse_x86_symbolic_fixup_manifest(&label).is_err());
    let truncated = &encode(&rows)[..encode(&rows).len() - 1];
    assert!(parse_x86_symbolic_fixup_manifest(truncated).is_err());
}

/// Every row the linker will patch must be the one judged hole.
#[test]
fn manifest_completeness_refuses_every_extra_or_misplaced_row() {
    let symbol = |offset, kind| X86FixupRow::Symbol {
        offset,
        symbol: "g".into(),
        kind,
    };
    let manifest_mismatch = |refusal: X86EnvelopeRefusal| {
        matches!(
            refusal,
            X86EnvelopeRefusal::Mismatch(X86EnvelopeMismatch::Manifest(_))
        )
    };
    for kind in 0..=3 {
        assert!(manifest_mismatch(refusal(
            &abort_source(),
            DIVERGING,
            &encode(&[call_row(5), symbol(1, kind)])
        )));
        assert!(manifest_mismatch(refusal(
            &void_source(0),
            VOID,
            &encode(&[symbol(1, kind)])
        )));
        assert!(manifest_mismatch(refusal(
            &abort_source(),
            DIVERGING,
            &encode(&[symbol(5, kind)])
        )));
    }
    assert!(manifest_mismatch(refusal(
        &abort_source(),
        DIVERGING,
        &encode(&[call_row(5), call_row(5)])
    )));
    assert!(manifest_mismatch(refusal(
        &abort_source(),
        DIVERGING,
        &no_rows()
    )));
    assert!(manifest_mismatch(refusal(
        &void_source(0),
        VOID,
        &encode(&[call_row(1)])
    )));
    let mut trailing = abort_rows();
    trailing.push(0);
    assert!(manifest_mismatch(refusal(
        &abort_source(),
        DIVERGING,
        &trailing
    )));
    for hole in [0, 4, 6, 9, 100] {
        assert!(matches!(
            refusal(&abort_source(), DIVERGING, &encode(&[call_row(hole)])),
            X86EnvelopeRefusal::Mismatch(X86EnvelopeMismatch::HolePlacement { .. })
        ));
    }
}

/// (label, source, bytes, manifest, the expected named refusal)
type NamedMutant<'s> = (
    &'static str,
    &'s Function,
    Vec<u8>,
    Vec<u8>,
    fn(&X86EnvelopeMismatch) -> bool,
);

/// (label, source, bytes, manifest, the items a counter-assignment falsifies)
type FalsifiedMutant<'s> = (
    &'static str,
    &'s Function,
    Vec<u8>,
    Vec<u8>,
    &'static [&'static str],
);

/// Each named Rust refusal, on bytes a wrong lowering could produce.
#[test]
fn walk_refuses_each_mutant_by_name() {
    use X86EnvelopeMismatch as M;
    let void = void_source(0);
    let div = abort_source();
    let cases: Vec<NamedMutant<'_>> = vec![
        (
            "missing pop",
            &void,
            vec![0x55, 0x48, 0x89, 0xe5, 0xc3],
            no_rows(),
            |m| matches!(m, M::StackImbalance { rsp_offset: -8, .. }),
        ),
        (
            "pop rbx for pop rbp",
            &void,
            vec![0x55, 0x48, 0x89, 0xe5, 0x5b, 0xc3],
            no_rows(),
            |m| matches!(m, M::PreservedWrite { .. }),
        ),
        (
            "extra pop",
            &void,
            vec![0x55, 0x48, 0x89, 0xe5, 0x5d, 0x5d, 0xc3],
            no_rows(),
            |m| matches!(m, M::StackImbalance { rsp_offset: 8, .. }),
        ),
        (
            "sub rsp without add",
            &void,
            vec![0x48, 0x83, 0xec, 0x08, 0xc3],
            no_rows(),
            |m| matches!(m, M::StackImbalance { .. }),
        ),
        (
            "push rbx; pop r12",
            &void,
            vec![0x55, 0x48, 0x89, 0xe5, 0x53, 0x41, 0x5c, 0x5d, 0xc3],
            no_rows(),
            |m| {
                matches!(
                    m,
                    M::PreservedWrite {
                        register: "r12",
                        ..
                    }
                )
            },
        ),
        (
            "write above rsp0",
            &void,
            vec![
                0x48, 0x83, 0xc4, 0x10, 0x55, 0x48, 0x89, 0xe5, 0x5d, 0x48, 0x83, 0xec, 0x10, 0xc3,
            ],
            no_rows(),
            |m| matches!(m, M::CallerMemoryWrite { .. }),
        ),
        (
            "frameless call (misaligned)",
            &div,
            vec![0xe8, 0, 0, 0, 0, 0x0f, 0x0b],
            encode(&[call_row(1)]),
            |m| {
                matches!(
                    m,
                    M::Misaligned {
                        callee_entry_offset: -8,
                        ..
                    }
                )
            },
        ),
        (
            "extra push before the call",
            &div,
            vec![0x55, 0x48, 0x89, 0xe5, 0x53, 0xe8, 0, 0, 0, 0, 0x0f, 0x0b],
            encode(&[call_row(6)]),
            |m| {
                matches!(
                    m,
                    M::Misaligned {
                        callee_entry_offset: -24,
                        ..
                    }
                )
            },
        ),
        (
            "rbx clobbered before the call",
            &div,
            vec![
                0x55, 0x55, 0x5b, 0x48, 0x89, 0xe5, 0xe8, 0, 0, 0, 0, 0x0f, 0x0b,
            ],
            encode(&[call_row(7)]),
            |m| {
                matches!(
                    m,
                    M::PreservedWrite {
                        register: "rbx",
                        ..
                    }
                )
            },
        ),
        (
            "renamed callee",
            &div,
            DIVERGING.to_vec(),
            encode(&[X86FixupRow::Call {
                offset: 5,
                callee: "other".into(),
                exact_module: false,
            }]),
            |m| matches!(m, M::CallTarget { .. }),
        ),
        (
            "exact flag flipped",
            &div,
            DIVERGING.to_vec(),
            encode(&[X86FixupRow::Call {
                offset: 5,
                callee: "abort_probe".into(),
                exact_module: true,
            }]),
            |m| matches!(m, M::CallMetadata { .. }),
        ),
        (
            "hole at the wrong offset",
            &div,
            DIVERGING.to_vec(),
            encode(&[call_row(6)]),
            |m| {
                matches!(
                    m,
                    M::HolePlacement {
                        hole: 6,
                        expected: 5,
                        ..
                    }
                )
            },
        ),
        (
            "non-zero rel32",
            &div,
            vec![0x55, 0x48, 0x89, 0xe5, 0xe8, 1, 0, 0, 0, 0x0f, 0x0b],
            abort_rows(),
            |m| matches!(m, M::NonZeroPlaceholder { .. }),
        ),
        (
            "ret for a trapping source",
            &div,
            VOID.to_vec(),
            no_rows(),
            |m| matches!(m, M::Control { .. }),
        ),
        (
            "ud2 for a returning source",
            &void,
            vec![0x55, 0x48, 0x89, 0xe5, 0x0f, 0x0b],
            no_rows(),
            |m| matches!(m, M::Control { .. }),
        ),
        (
            "call f; ret for call f; trap",
            &div,
            vec![0x55, 0x48, 0x89, 0xe5, 0xe8, 0, 0, 0, 0, 0x5d, 0xc3],
            abort_rows(),
            |m| matches!(m, M::TrapMissing { offset: 9 }),
        ),
        (
            "call in a returning body",
            &void,
            vec![0x55, 0x48, 0x89, 0xe5, 0xe8, 0, 0, 0, 0, 0x5d, 0xc3],
            abort_rows(),
            |m| matches!(m, M::CallCount { expected: 0, .. }),
        ),
        (
            "bytes after the ret",
            &void,
            vec![0x55, 0x48, 0x89, 0xe5, 0x5d, 0xc3, 0xc3],
            no_rows(),
            |m| matches!(m, M::Control { offset: 6, .. }),
        ),
        (
            "bytes after the ud2",
            &div,
            [DIVERGING, &[0x0f, 0x0b]].concat(),
            abort_rows(),
            |m| matches!(m, M::Control { offset: 11, .. }),
        ),
        (
            "no terminator",
            &void,
            vec![0x55, 0x48, 0x89, 0xe5, 0x5d],
            no_rows(),
            |m| matches!(m, M::Control { .. }),
        ),
        (
            "return slot overwritten through a partial overlap",
            &void,
            vec![0x48, 0x83, 0xc4, 0x04, 0x55, 0x48, 0x83, 0xc4, 0x04, 0xc3],
            no_rows(),
            |m| matches!(m, M::CallerMemoryWrite { rsp_offset: -4, .. }),
        ),
        (
            "an instruction between the call and the trap",
            &div,
            vec![0x55, 0x48, 0x89, 0xe5, 0xe8, 0, 0, 0, 0, 0x5d, 0x0f, 0x0b],
            abort_rows(),
            |m| matches!(m, M::TrapMissing { offset: 9 }),
        ),
        (
            "a ret between the call and the trap",
            &div,
            vec![0x55, 0x48, 0x89, 0xe5, 0xe8, 0, 0, 0, 0, 0xc3, 0x0f, 0x0b],
            abort_rows(),
            |m| matches!(m, M::Control { offset: 9, .. }),
        ),
        (
            "the call's push overwrites the caller's return address",
            &div,
            vec![0x58, 0xe8, 0, 0, 0, 0, 0x0f, 0x0b],
            encode(&[call_row(2)]),
            |m| {
                matches!(
                    m,
                    M::CallerMemoryWrite {
                        offset: 1,
                        rsp_offset: 0
                    }
                )
            },
        ),
    ];
    // The battery asserts its own cardinality, so a case cannot vanish.
    assert_eq!(cases.len(), 24);
    for (label, source, code, manifest, expected) in cases {
        match refusal(source, &code, &manifest) {
            X86EnvelopeRefusal::Mismatch(found) => assert!(expected(&found), "{label}: {found}"),
            other => panic!("{label}: {other}"),
        }
    }
}

fn premise_holding_assignments(theorem: &EnvelopeTheorem) -> Vec<HashMap<String, u64>> {
    let mut out = Vec::new();
    for rsp0 in [
        0x0000_7ffe_0000_1008u64,
        0x0000_0000_0010_0008,
        0xffff_ffff_ffff_fff8,
    ] {
        for obs_delta in [0i64, 1, 3, 4, 7, 8, 12, 15, 16, -8, -1] {
            let obs = rsp0.wrapping_add(obs_delta as u64);
            let env = witness(theorem, rsp0, obs);
            let (premises, _) = evaluate(theorem, &env).unwrap();
            if premises {
                out.push(env);
            }
        }
    }
    out
}

/// The indices of the items some premise-satisfying assignment falsifies.
fn refuted_items(theorem: &EnvelopeTheorem) -> Vec<usize> {
    let mut refuted = HashSet::new();
    for env in premise_holding_assignments(theorem) {
        let (_, items) = evaluate(theorem, &env).unwrap();
        refuted.extend(
            items
                .iter()
                .enumerate()
                .filter(|(_, holds)| !**holds)
                .map(|(i, _)| i),
        );
    }
    let mut refuted: Vec<usize> = refuted.into_iter().collect();
    refuted.sort_unstable();
    refuted
}

fn item_kinds(theorem: &EnvelopeTheorem) -> Vec<String> {
    theorem
        .items
        .iter()
        .map(|item| match item {
            E::Or { .. } => "memory".to_owned(),
            E::Eq { rhs, .. } => match rhs.as_ref() {
                E::Var { name, .. } => name.clone(),
                E::BvConst { width: 4, .. } => "alignment".to_owned(),
                E::BvAdd { lhs, .. } if matches!(lhs.as_ref(), E::Var { name, .. } if name == "rsp0") => {
                    "rsp".to_owned()
                }
                E::BvAdd { .. } => "return_slot".to_owned(),
                E::Concat { .. } => "rip".to_owned(),
                other => format!("{other}"),
            },
            other => format!("{other}"),
        })
        .collect()
}

/// The theorem itself carries every semantic refusal: with the Rust walk's
/// refusal removed, a premise-satisfying assignment falsifies exactly the
/// items the defect breaks. (Evaluation only; the solver-level refutation is
/// `mutant_envelope_theorems_are_refuted_by_ay`.)
#[test]
fn theorem_without_walk_refusal_is_falsified_for_each_semantic_mutant() {
    let void = void_source(0);
    let div = abort_source();
    let cases: Vec<FalsifiedMutant<'_>> = vec![
        (
            "missing pop",
            &void,
            vec![0x55, 0x48, 0x89, 0xe5, 0xc3],
            no_rows(),
            &["rip", "rsp", "rbp_0"],
        ),
        (
            "pop rbx for pop rbp",
            &void,
            vec![0x55, 0x48, 0x89, 0xe5, 0x5b, 0xc3],
            no_rows(),
            &["rbx_0", "rbp_0"],
        ),
        (
            "extra pop",
            &void,
            vec![0x55, 0x48, 0x89, 0xe5, 0x5d, 0x5d, 0xc3],
            no_rows(),
            &["rip", "rsp", "rbp_0"],
        ),
        (
            "push rbx; pop r12",
            &void,
            vec![0x55, 0x48, 0x89, 0xe5, 0x53, 0x41, 0x5c, 0x5d, 0xc3],
            no_rows(),
            &["r12_0"],
        ),
        (
            "write above rsp0 (only memory breaks)",
            &void,
            vec![
                0x48, 0x83, 0xc4, 0x10, 0x55, 0x48, 0x89, 0xe5, 0x5d, 0x48, 0x83, 0xec, 0x10, 0xc3,
            ],
            no_rows(),
            &["memory"],
        ),
        (
            "partial overlap of the return slot (byte-granular)",
            &void,
            vec![0x48, 0x83, 0xc4, 0x04, 0x55, 0x48, 0x83, 0xc4, 0x04, 0xc3],
            no_rows(),
            &["rip", "memory"],
        ),
        (
            "frameless call (misaligned)",
            &div,
            vec![0xe8, 0, 0, 0, 0, 0x0f, 0x0b],
            encode(&[call_row(1)]),
            &["alignment"],
        ),
        (
            "extra push before the call",
            &div,
            vec![0x55, 0x48, 0x89, 0xe5, 0x53, 0xe8, 0, 0, 0, 0, 0x0f, 0x0b],
            encode(&[call_row(6)]),
            &["alignment"],
        ),
        (
            "rbx clobbered before the call",
            &div,
            vec![
                0x55, 0x55, 0x5b, 0x48, 0x89, 0xe5, 0xe8, 0, 0, 0, 0, 0x0f, 0x0b,
            ],
            encode(&[call_row(7)]),
            &["rbx_0"],
        ),
        (
            "an instruction between the call and the trap (return slot)",
            &div,
            vec![0x55, 0x48, 0x89, 0xe5, 0xe8, 0, 0, 0, 0, 0x5d, 0x0f, 0x0b],
            abort_rows(),
            &["return_slot"],
        ),
        (
            "the call's push overwrites the caller's return address",
            &div,
            vec![0x58, 0xe8, 0, 0, 0, 0, 0x0f, 0x0b],
            encode(&[call_row(2)]),
            &["memory"],
        ),
    ];
    // The battery asserts its own cardinality, so a case cannot vanish.
    assert_eq!(cases.len(), 11);
    let mut falsified: HashSet<(bool, String)> = HashSet::new();
    for (label, source, code, manifest, expected) in cases {
        let theorem = theorem_without_walk_refusal(source, "subject", &code, &manifest, SYSV)
            .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
        check_envelope_structure(&theorem).unwrap();
        check_envelope_parts(&theorem).unwrap();
        let kinds = item_kinds(&theorem);
        let refuted: Vec<&str> = refuted_items(&theorem)
            .into_iter()
            .map(|i| kinds[i].as_str())
            .collect();
        assert_eq!(refuted, expected, "{label}: items {kinds:?}");
        let returns = std::ptr::eq(source, &void);
        falsified.extend(refuted.iter().map(|kind| (returns, (*kind).to_owned())));
    }
    // The correct bodies falsify nothing under any probed assignment, and
    // every item they state is one some mutant above falsifies: no item holds
    // whatever bytes the builder accepts.
    for (source, code, manifest) in [(&void, VOID, no_rows()), (&div, DIVERGING, abort_rows())] {
        let theorem = theorem_of(source, "subject", code, &manifest, SYSV).unwrap();
        assert!(refuted_items(&theorem).is_empty());
        assert!(!premise_holding_assignments(&theorem).is_empty());
        let returns = std::ptr::eq(source, &void);
        for kind in item_kinds(&theorem) {
            assert!(
                falsified.contains(&(returns, kind.clone())),
                "no mutant falsifies the correct theorem's `{kind}` item"
            );
        }
    }
}

/// The return-slot item is stated against the UD2's RECOGNIZED offset, not
/// against the address the CALL pushes, so it is not a read-back of the
/// walk's own write: with a byte between the CALL and the UD2 the slot holds
/// `code_base + 9` and the item demands `code_base + 10`. The old reading
/// (compare the slot with the pushed address) holds for that wrong body under
/// every assignment, which is exactly why it said nothing.
#[test]
fn return_slot_item_is_stated_against_the_recognized_trap() {
    let div = abort_source();
    let between = [0x55, 0x48, 0x89, 0xe5, 0xe8, 0, 0, 0, 0, 0x5d, 0x0f, 0x0b];
    let theorem =
        theorem_without_walk_refusal(&div, "subject", &between, &abort_rows(), SYSV).unwrap();
    let slot = item_kinds(&theorem)
        .iter()
        .position(|kind| kind == "return_slot")
        .expect("the diverging theorem states the return slot");
    let E::Eq { lhs: read, rhs } = &theorem.items[slot] else {
        panic!("the slot item is an equation");
    };
    let code_base = E::var("code_base", 64);
    assert_eq!(**rhs, code_base.clone().bvadd(E::bv_const(10, 64)));
    let pushed = read
        .as_ref()
        .clone()
        .eq_expr(code_base.bvadd(E::bv_const(9, 64)));
    for env in premise_holding_assignments(&theorem) {
        assert!(!theorem.items[slot].try_eval(&env).unwrap().as_bool());
        assert!(pushed.try_eval(&env).unwrap().as_bool());
    }
    // The walk refuses the same body by name before any theorem is built.
    assert!(matches!(
        refusal(&div, &between, &abort_rows()),
        X86EnvelopeRefusal::Mismatch(X86EnvelopeMismatch::TrapMissing { offset: 9 })
    ));
}

/// Alignment is stated at CALLEE ENTRY (RSP after the CALL's push) against
/// the ABI rule `RSP + 8 = 0 (mod 16)`. The other reading (the pre-CALL RSP
/// congruent to rsp0) would accept the frameless misaligned body and refuse
/// the correct framed one; both readings are evaluated on both bodies.
#[test]
fn alignment_is_stated_at_callee_entry_against_the_abi_rule() {
    let div = abort_source();
    let correct = theorem_of(&div, "subject", DIVERGING, &abort_rows(), SYSV).unwrap();
    let frameless = theorem_without_walk_refusal(
        &div,
        "subject",
        &[0xe8, 0, 0, 0, 0, 0x0f, 0x0b],
        &encode(&[call_row(1)]),
        SYSV,
    )
    .unwrap();
    let callee_entry = |theorem: &EnvelopeTheorem| -> E {
        let E::Eq { lhs, .. } = &theorem.items[0] else {
            panic!("item 0 is the alignment item");
        };
        let E::Extract { operand, .. } = lhs.as_ref() else {
            panic!("alignment extracts the low nibble");
        };
        let E::BvAdd { lhs: rsp, .. } = operand.as_ref() else {
            panic!("alignment adds 8 to callee-entry RSP");
        };
        rsp.as_ref().clone()
    };
    let other_reading = |theorem: &EnvelopeTheorem| {
        let pre_call = callee_entry(theorem).bvadd(E::bv_const(8, 64));
        pre_call
            .extract(3, 0)
            .eq_expr(E::var("rsp0", 64).extract(3, 0))
    };
    let decide = |theorem: &EnvelopeTheorem, item: &E| {
        premise_holding_assignments(theorem)
            .iter()
            .all(|env| item.try_eval(env).unwrap().as_bool())
    };
    assert!(decide(&correct, &correct.items[0]));
    assert!(!decide(&frameless, &frameless.items[0]));
    assert!(!decide(&correct, &other_reading(&correct)));
    assert!(decide(&frameless, &other_reading(&frameless)));
    // The correct framed body enters the callee at rsp0 - 16.
    assert_eq!(
        callee_entry(&correct),
        E::var("rsp0", 64)
            .bvsub(E::bv_const(8, 64))
            .bvsub(E::bv_const(8, 64))
    );
}

#[test]
fn non_vacuity_guards_reject_identity_items_and_foreign_premises() {
    let theorem = theorem_of(&void_source(0), "subject", VOID, &no_rows(), SYSV).unwrap();
    check_envelope_structure(&theorem).unwrap();
    assert_eq!(
        item_kinds(&theorem),
        ["rip", "rsp", "rbp_0", "memory"],
        "the void envelope states return target, stack, RBP and memory"
    );
    let rebuild = |mut theorem: EnvelopeTheorem| {
        theorem.obligation.aarch64_expr = theorem
            .items
            .iter()
            .cloned()
            .rev()
            .reduce(|tail, item| item.and_expr(tail))
            .unwrap();
        check_envelope_structure(&theorem)
    };
    // Each item replaced by an identity, one at a time, is refused.
    for index in 0..theorem.items.len() {
        let mut mutated = theorem.clone();
        mutated.items[index] = match &theorem.items[index] {
            E::Or { lhs, rhs } => {
                let E::Eq { rhs: base, .. } = rhs.as_ref() else {
                    unreachable!()
                };
                lhs.as_ref()
                    .clone()
                    .or_expr(base.as_ref().clone().eq_expr(base.as_ref().clone()))
            }
            E::Eq { rhs, .. } => rhs.as_ref().clone().eq_expr(rhs.as_ref().clone()),
            other => other.clone(),
        };
        let error = rebuild(mutated).expect_err("an identity item must be refused");
        assert!(error.contains("identity"), "{index}: {error}");
    }
    // A single item is refused.
    let mut single = theorem.clone();
    single.items.truncate(1);
    assert!(rebuild(single).is_err());
    // A premise outside the permitted forms is refused.
    for foreign in [
        E::var("rsp0", 64).eq_expr(E::bv_const(0x1008, 64)),
        E::var("mem_0", 8).eq_expr(E::var("mem_1", 8)),
        E::bool_const(false),
    ] {
        let mut mutated = theorem.clone();
        mutated.obligation.preconditions.push(foreign);
        assert!(check_envelope_structure(&mutated).is_err());
    }
    // A duplicated Ackermann pair or a second alignment premise is refused.
    let mut duplicated = theorem.clone();
    let ack = duplicated
        .obligation
        .preconditions
        .iter()
        .find(|p| matches!(p, E::Or { .. }))
        .cloned()
        .expect("the void theorem has Ackermann premises");
    duplicated.obligation.preconditions.push(ack);
    assert!(check_envelope_structure(&duplicated).is_err());
    let mut twice = theorem.clone();
    twice
        .obligation
        .preconditions
        .push(aligned_entry(E::var("rsp0", 64)));
    assert!(check_envelope_structure(&twice).is_err());
    // The replayed parts must be exactly the split of the statement.
    check_envelope_parts(&theorem).unwrap();
    assert_eq!(
        theorem
            .parts
            .iter()
            .map(|part| part
                .name
                .rsplit(X86_ENVELOPE_PART_SEPARATOR)
                .next()
                .unwrap())
            .filter(|label| !label.contains(" byte "))
            .collect::<Vec<_>>(),
        ["RSP after the return", "caller memory at or above rsp0"]
    );
    let mut dropped = theorem.clone();
    dropped.parts.pop();
    assert!(check_envelope_parts(&dropped).is_err());
    let mut weakened = theorem.clone();
    weakened.parts[0].aarch64_expr = E::bool_const(true);
    assert!(check_envelope_parts(&weakened).is_err());
    let mut premise_free = theorem.clone();
    premise_free.parts[3].preconditions.clear();
    assert!(check_envelope_parts(&premise_free).is_err());
    let mut identity = theorem.clone();
    let byte = E::var("mem_0", 8);
    identity.parts[1].aarch64_expr = byte.clone().eq_expr(byte);
    assert!(check_envelope_parts(&identity).is_err());
    // A frameless body is degenerate, never built.
    {
        let found = refusal(&void_source(0), &[0xc3], &no_rows());
        assert!(
            matches!(
                found,
                X86EnvelopeRefusal::Unsupported(X86EnvelopeUnsupported::Degenerate(_))
            ),
            "frameless ret: {found}"
        );
        let found = format!("{found}");
        assert!(
            found.contains("degenerate") || found.contains("identity"),
            "{found}"
        );
    }
}

/// The verifier entry builds the theorem and, with replay refused, credits
/// nothing: no verdict, no export, no reusable identity. Mismatches and
/// unsupported inputs pass through by name.
#[test]
fn verify_abi_envelope_without_replay_builds_but_credits_nothing() {
    use crate::lowering_proof::VerificationConfig;
    use crate::provenance_xcheck::ProvenanceXCheckMode;
    let verifier =
        crate::X86FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
    trust_cg_process_env::with_env_edits(|env| {
        env.set("TCG_REFINE_SOLVER", "0");
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        for (source, code, manifest, name) in [
            (
                void_source(0),
                VOID,
                no_rows(),
                X86_VOID_RETURN_ENVELOPE_NAME,
            ),
            (
                abort_source(),
                DIVERGING,
                abort_rows(),
                X86_DIVERGING_CALL_ENVELOPE_NAME,
            ),
        ] {
            let report =
                verifier.verify_abi_envelope(&source, "subject", code, &manifest, SYSV, &request);
            match report.outcome() {
                X86EnvelopeOutcome::Built {
                    theorem_name,
                    parts,
                    exports,
                } if !parts.is_empty()
                    && parts.iter().all(|part| part.verdict.is_none())
                    && exports.is_empty() =>
                {
                    assert_eq!(*theorem_name, name)
                }
                other => panic!("{name}: {other:?}"),
            }
            let (first, valid) = report.outcome().first_unproven_part().unwrap();
            assert_eq!(valid, 0);
            assert!(first.name.starts_with(name), "{}", first.name);
            assert!(!report.is_valid());
            assert!(!report.reusable_for(&request));
            assert!(report.matches_input(&source, "subject", code, &manifest, SYSV));
            assert!(
                !report.matches_input(&source, "subject", code, &no_rows(), SYSV)
                    || manifest == no_rows()
            );
        }
        let report = verifier.verify_abi_envelope(
            &void_source(0),
            "subject",
            &[0x55, 0x48, 0x89, 0xe5, 0xc3],
            &no_rows(),
            SYSV,
            &request,
        );
        assert!(matches!(
            report.outcome(),
            X86EnvelopeOutcome::Mismatch(X86EnvelopeMismatch::StackImbalance { .. })
        ));
        let report = verifier.verify_abi_envelope(
            &void_source(0),
            "subject",
            &[0x55, 0x48, 0x89, 0xe5, 0x5c, 0xc3],
            &no_rows(),
            SYSV,
            &request,
        );
        assert!(matches!(
            report.outcome(),
            X86EnvelopeOutcome::Unsupported(X86EnvelopeUnsupported::Bytes { offset: 4, .. })
        ));
    });
    // A request that does not enforce provenance never replays.
    let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Warn);
    let report =
        verifier.verify_abi_envelope(&void_source(0), "subject", VOID, &no_rows(), SYSV, &request);
    assert!(matches!(
        report.outcome(),
        X86EnvelopeOutcome::Built { parts, exports, .. }
            if parts.iter().all(|part| part.verdict.is_none()) && exports.is_empty()
    ));
}

fn verify_request() -> crate::FunctionVerificationRequest {
    use crate::lowering_proof::VerificationConfig;
    use crate::provenance_xcheck::ProvenanceXCheckMode;
    crate::X86FunctionVerifier::with_config(VerificationConfig::for_proof_promotion())
        .capture_request_with_mode(ProvenanceXCheckMode::Enforce)
}

type InjectedVerdict = (Option<crate::verify::VerificationResult>, Option<String>);

fn all_valid(n: usize) -> Vec<InjectedVerdict> {
    (0..n)
        .map(|_| (Some(crate::verify::VerificationResult::Valid), None))
        .collect()
}

fn exports_of(report: &X86EnvelopeReport) -> Vec<crate::SourceBoundArithmeticObligation> {
    match report.outcome() {
        X86EnvelopeOutcome::Built { exports, .. } => exports.clone(),
        other => panic!("not built: {other:?}"),
    }
}

/// THE CREDIT RULE is "every part", not "any part". The verifier's own report
/// assembly ([`envelope_report`], which `verify_abi_envelope` calls) is fed
/// injected verdicts, so no solver is needed: all parts Valid and bound is
/// credit, with one export per part and a reusable identity; the same verdicts
/// with ANY ONE part not Valid (none, inconclusive or refuted, at every
/// position) is no credit, no export, no identity. The rule is also checked
/// apart from the assembly: a report whose outcome carries one export per part
/// but one non-Valid part is still not valid and not reusable.
#[test]
fn envelope_credit_requires_a_valid_replay_of_every_part() {
    use crate::verify::VerificationResult as V;
    let request = verify_request().with_reuse_identity([7; 32]);
    for (source, code, manifest) in [
        (void_source(0), VOID, no_rows()),
        (abort_source(), DIVERGING, abort_rows()),
    ] {
        let owner = source_bound_x86_envelope(&source, "subject", code, &manifest, SYSV).unwrap();
        let n = owner.parts().len();
        assert!(n >= 2);
        let input =
            crate::function_request::x86_envelope_input(&source, "subject", code, &manifest, SYSV);
        let credited = envelope_report("subject", &owner, input, all_valid(n), true, &request);
        assert!(credited.is_valid() && credited.outcome().is_credited());
        assert!(credited.reusable_for(&request));
        let full_exports = exports_of(&credited);
        assert_eq!(full_exports.len(), n);
        for missing in 0..n {
            for other in [
                None,
                Some(V::Unknown {
                    reason: "incomplete".into(),
                }),
                Some(V::Invalid {
                    counterexample: "rsp0 = 0".into(),
                }),
            ] {
                let mut verdicts = all_valid(n);
                verdicts[missing] = (other.clone(), Some("probe".into()));
                let report = envelope_report("subject", &owner, input, verdicts, true, &request);
                let label = format!("part {missing} of {n} is {other:?}");
                assert!(!report.is_valid(), "{label}");
                assert!(!report.outcome().is_credited(), "{label}");
                assert!(!report.reusable_for(&request), "{label}");
                assert!(exports_of(&report).is_empty(), "{label}");
                let X86EnvelopeOutcome::Built {
                    theorem_name,
                    parts,
                    ..
                } = report.outcome()
                else {
                    unreachable!()
                };
                let (first, valid) = report.outcome().first_unproven_part().unwrap();
                assert_eq!(first.name, owner.parts()[missing].name, "{label}");
                assert_eq!(first.detail.as_deref(), Some("probe"), "{label}");
                assert_eq!(valid, n - 1, "{label}");
                let forged = X86EnvelopeReport::new(
                    "subject",
                    X86EnvelopeOutcome::Built {
                        theorem_name,
                        parts: parts.clone(),
                        exports: full_exports.clone(),
                    },
                    input,
                    Some([7; 32]),
                );
                assert!(!forged.is_valid(), "{label}");
                assert!(!forged.outcome().is_credited(), "{label}");
                assert!(!forged.reusable_for(&request), "{label}");
            }
        }
    }
}

/// GAP 8 on the real report, on every host: a Valid envelope is served from
/// a cache only to a request of the authority its replays were bound to. A
/// Valid replay that was not bound (a fresh-path solve), a Valid replay bound
/// to another authority, and a Valid replay assembled under a request that
/// may not reuse carry no identity for this request, although each is Valid
/// and exports every part.
#[test]
fn envelope_report_reuse_is_bound_to_the_replay_authority() {
    let a = verify_request().with_reuse_identity([1; 32]);
    let b = verify_request().with_reuse_identity([2; 32]);
    let recording = a.clone().captured_while_recording();
    for (source, code, manifest) in [
        (void_source(0), VOID, no_rows()),
        (abort_source(), DIVERGING, abort_rows()),
    ] {
        let owner = source_bound_x86_envelope(&source, "subject", code, &manifest, SYSV).unwrap();
        let n = owner.parts().len();
        let input =
            crate::function_request::x86_envelope_input(&source, "subject", code, &manifest, SYSV);
        let assemble = |bound: bool, request: &crate::FunctionVerificationRequest| {
            let report = envelope_report("subject", &owner, input, all_valid(n), bound, request);
            assert!(report.is_valid());
            assert_eq!(exports_of(&report).len(), n);
            report
        };
        let bound_to_a = assemble(true, &a);
        assert!(bound_to_a.reusable_for(&a));
        assert!(!bound_to_a.reusable_for(&b));
        assert!(!bound_to_a.reusable_for(&recording));
        let unbound = assemble(false, &a);
        assert!(!unbound.reusable_for(&a));
        assert!(!unbound.reusable_for(&b));
        let no_reuse = assemble(true, &recording);
        assert!(!no_reuse.reusable_for(&a));
        assert!(!no_reuse.reusable_for(&recording));
        // The same checks on reports that carry the identity directly.
        let valid_outcome = bound_to_a.outcome().clone();
        let with_identity =
            |identity| X86EnvelopeReport::new("subject", valid_outcome.clone(), input, identity);
        assert!(!with_identity(None).reusable_for(&a));
        assert!(!with_identity(Some([2; 32])).reusable_for(&a));
        assert!(with_identity(Some([2; 32])).reusable_for(&b));
        assert!(!with_identity(Some([1; 32])).reusable_for(&recording));
    }
}

/// The split into parts is checked SEMANTICALLY, not only by recomputing it
/// with the function that produced it: under every probed assignment (the
/// premise-holding witnesses and arbitrary ones), the conjunction of the
/// parts' goals has the statement's value, for the correct theorems and for
/// mutant theorems. Every part keeps the statement's premises, inputs and
/// `true` right-hand side, and for the correct theorems both values of the
/// statement are observed, so the comparison is not vacuous. A split that paired byte k of a read with
/// byte 7-k, or dropped a byte, fails here.
#[test]
fn envelope_parts_conjoin_to_the_statement_under_every_probed_assignment() {
    fn mix(seed: u64, name: &str) -> u64 {
        name.bytes().fold(
            seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ 0x243f_6a88,
            |h, b| {
                (h ^ u64::from(b))
                    .wrapping_mul(0x100_0000_01b3)
                    .rotate_left(29)
            },
        )
    }
    let void = void_source(0);
    let div = abort_source();
    let framed = vec![
        0x55, 0x48, 0x89, 0xe5, 0x53, 0x41, 0x54, 0x48, 0x83, 0xec, 0x10, 0x48, 0x83, 0xc4, 0x10,
        0x41, 0x5c, 0x5b, 0x5d, 0xc3,
    ];
    let cases: Vec<(&str, &Function, Vec<u8>, Vec<u8>)> = vec![
        ("void_return", &void, VOID.to_vec(), no_rows()),
        ("diverging_call", &div, DIVERGING.to_vec(), abort_rows()),
        ("void_return_saves", &void, framed, no_rows()),
        (
            "missing pop",
            &void,
            vec![0x55, 0x48, 0x89, 0xe5, 0xc3],
            no_rows(),
        ),
        (
            "partial overlap",
            &void,
            vec![0x48, 0x83, 0xc4, 0x04, 0x55, 0x48, 0x83, 0xc4, 0x04, 0xc3],
            no_rows(),
        ),
        (
            "instruction between call and trap",
            &div,
            vec![0x55, 0x48, 0x89, 0xe5, 0xe8, 0, 0, 0, 0, 0x5d, 0x0f, 0x0b],
            abort_rows(),
        ),
        (
            "rbx clobbered before the call",
            &div,
            vec![
                0x55, 0x55, 0x5b, 0x48, 0x89, 0xe5, 0xe8, 0, 0, 0, 0, 0x0f, 0x0b,
            ],
            encode(&[call_row(7)]),
        ),
    ];
    for (label, source, code, manifest) in cases {
        let theorem = theorem_without_walk_refusal(source, "subject", &code, &manifest, SYSV)
            .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
        let statement = &theorem.obligation;
        assert!(
            theorem.parts.len() > theorem.items.len(),
            "{label}: nothing was split"
        );
        for part in &theorem.parts {
            assert_eq!(part.trust_ir_expr, E::bool_const(true), "{label}");
            assert_eq!(part.preconditions, statement.preconditions, "{label}");
            assert_eq!(part.inputs, statement.inputs, "{label}");
            assert_eq!(part.category, statement.category, "{label}");
        }
        let mut envs = premise_holding_assignments(&theorem);
        for seed in 0..64u64 {
            let mut env = witness(&theorem, 0x0000_7ffe_0000_1008, 0x0000_7ffe_0000_1008);
            for (name, width) in &statement.inputs {
                let mask = if *width >= 64 {
                    u64::MAX
                } else {
                    (1u64 << width) - 1
                };
                // Half the seeds keep the witness memory and move registers
                // only; the rest move everything.
                if seed % 2 == 0 || !name.starts_with("mem_") {
                    env.insert(name.clone(), mix(seed, name) & mask);
                }
            }
            envs.push(env);
        }
        let mut seen = HashSet::new();
        for env in &envs {
            let whole = holds(&statement.aarch64_expr, env).unwrap();
            let conjoined = theorem
                .parts
                .iter()
                .map(|part| holds(&part.aarch64_expr, env))
                .collect::<Result<Vec<_>, _>>()
                .unwrap()
                .into_iter()
                .all(|holds| holds);
            assert_eq!(
                conjoined, whole,
                "{label}: parts disagree with the statement"
            );
            seen.insert(whole);
        }
        assert!(
            seen.contains(&false),
            "{label}: no probe falsifies the statement"
        );
        let correct = label.starts_with("void_return") || label == "diverging_call";
        assert!(
            !correct || seen.contains(&true),
            "{label}: the statement never holds"
        );
    }
}

/// The export and the report bind every input: a change to any byte, the
/// manifest, the function name, the calling convention or the LIR changes the
/// digest, so neither can be reused for another function.
#[test]
fn envelope_input_digest_binds_every_input() {
    use crate::function_request::x86_envelope_input;
    let source = abort_source();
    let manifest = abort_rows();
    let base = x86_envelope_input(&source, "subject", DIVERGING, &manifest, SYSV);
    let mut digests = HashSet::new();
    digests.insert(base);
    for index in 0..DIVERGING.len() {
        let mut code = DIVERGING.to_vec();
        code[index] ^= 0x01;
        assert!(digests.insert(x86_envelope_input(
            &source, "subject", &code, &manifest, SYSV
        )));
    }
    assert!(digests.insert(x86_envelope_input(
        &source,
        "subject",
        DIVERGING,
        &encode(&[X86FixupRow::Call {
            offset: 5,
            callee: "abort_probf".into(),
            exact_module: false,
        }]),
        SYSV
    )));
    assert!(digests.insert(x86_envelope_input(
        &source, "other", DIVERGING, &manifest, SYSV
    )));
    assert!(digests.insert(x86_envelope_input(
        &source,
        "subject",
        DIVERGING,
        &manifest,
        Some(X86SourceBoundAbi::WindowsX64)
    )));
    let renamed_callee = diverging_source(0, "abort_probf", DirectCallBinding::Interposable);
    assert!(digests.insert(x86_envelope_input(
        &renamed_callee,
        "subject",
        DIVERGING,
        &manifest,
        SYSV
    )));
    let export = crate::SourceBoundArithmeticObligation::x86_envelope(
        base,
        "subject",
        9,
        theorem_of(&source, "subject", DIVERGING, &manifest, SYSV)
            .unwrap()
            .parts
            .remove(0),
    );
    assert_eq!(export.kind(), crate::SourceBoundObligationKind::X86Envelope);
    assert_eq!(export.instruction_index(), 9);
    assert!(export.matches_x86_envelope_input(&source, "subject", DIVERGING, &manifest, SYSV));
    assert!(!export.matches_x86_envelope_input(&source, "subject", VOID, &manifest, SYSV));
    assert!(!export.matches_x86_input(
        &trust_cg_lower::x86_64_isel::X86ISelFunction::new(
            "subject".into(),
            Signature {
                params: vec![],
                returns: vec![],
            }
        ),
        Some(&source),
        SYSV
    ));
}

// ---------------------------------------------------------------------------
// Host qualification (tool-gated: the admitted AY + a capable Clean)
// ---------------------------------------------------------------------------

/// The parts of item `index`: its one goal, or its eight byte goals.
fn parts_of_item(theorem: &EnvelopeTheorem, index: usize) -> Vec<&ProofObligation> {
    let whole = format!(
        "{}{X86_ENVELOPE_PART_SEPARATOR}{}",
        theorem.obligation.name, theorem.labels[index]
    );
    let bytes = format!("{whole} byte ");
    theorem
        .parts
        .iter()
        .filter(|part| part.name == whole || part.name.starts_with(&bytes))
        .collect()
}

/// `result` without the per-run temporary proof path AY reports.
fn stable_outcome(result: &crate::ay_bridge::AYResult) -> String {
    format!("{result:?}")
        .split(' ')
        .map(|word| {
            if word.starts_with("path=") {
                "path=<tmp>"
            } else {
                word
            }
        })
        .collect::<Vec<_>>()
        .join(" ")
}

/// Correct envelope theorems an admitted AY did NOT certify, measured on the
/// arm64 macOS development host with the exact outcome of the first part
/// that did not certify (never credit; a recorded row only stops the
/// qualification test from demanding a proof the pair cannot produce). Keyed
/// by the admitted AY's SHA-256:
/// - `40e852cc...` is the Trust pack 9192 toolchain AY, `ay 0.26.0 build 9624`
///   (Clean: aterm store pack 8606). It computes UNSAT for the first part of
///   each theorem, but its Alethe certificate carries an unproved step (or
///   its own strict check rejects a hole step), so no part is credited.
///
/// No row is recorded for the local overlay AY `ay 0.27.0 build 11378`
/// (commit `0b670d840`, Clean `5390f432b` with carcara-verify): it certifies
/// every part of all three theorems, and Clean fully verifies each proof.
/// A row that starts certifying (or changes outcome) fails the test until
/// the table is reviewed.
const KNOWN_UNCERTIFIED: &[(&str, &str, &str)] = &[
    (
        "40e852cc7fa3a3289f17a47b5a8d6d1a5218177b4a95087538ff2c3d702ac7a8",
        "void_return",
        "return target byte 0: Unknown(\"incomplete AY proof certificate: c ay.proof.certificate path=<tmp> unproved_steps=1 foreign_assumes=no trust_free=no ay_self_checkable=yes\")",
    ),
    (
        "40e852cc7fa3a3289f17a47b5a8d6d1a5218177b4a95087538ff2c3d702ac7a8",
        "diverging_call",
        "callee-entry alignment: Unknown(\"incomplete AY proof certificate: c ay.proof.certificate path=<tmp> unproved_steps=1 foreign_assumes=no trust_free=no ay_self_checkable=yes\")",
    ),
    (
        "40e852cc7fa3a3289f17a47b5a8d6d1a5218177b4a95087538ff2c3d702ac7a8",
        "void_return_saves",
        "return target byte 0: Unknown(\"(:reason-unknown (incomplete self-check-rejected))\")",
    ),
];

/// Every part of every correct envelope theorem is proven by the admitted AY
/// and its proof is accepted by Clean (`AYResult::Verified`), except the exact
/// recorded [`KNOWN_UNCERTIFIED`] outcomes of that AY. Fails without
/// authority.
#[test]
fn envelope_theorems_certify_on_the_admitted_pair() {
    use crate::ay_bridge::{AYConfig, AYResult};
    let test = "envelope_theorems_certify_on_the_admitted_pair";
    let edits = crate::x86_source_bound_body::tests::replay_environment(test);
    let config = AYConfig {
        solver: None,
        timeout_ms: 30_000,
        produce_models: true,
    };
    let framed = [
        0x55, 0x48, 0x89, 0xe5, 0x53, 0x41, 0x54, 0x48, 0x83, 0xec, 0x10, 0x48, 0x83, 0xc4, 0x10,
        0x41, 0x5c, 0x5b, 0x5d, 0xc3,
    ];
    let cases: Vec<(&str, Function, Vec<u8>, Vec<u8>)> = vec![
        ("void_return", void_source(0), VOID.to_vec(), no_rows()),
        (
            "diverging_call",
            abort_source(),
            DIVERGING.to_vec(),
            abort_rows(),
        ),
        (
            "void_return_saves",
            void_source(0),
            framed.to_vec(),
            no_rows(),
        ),
    ];
    let ay_sha = crate::x86_source_bound_body::tests::with_edits(&edits, || {
        crate::ay_bridge::admitted_proof_solver().map(|ay| ay.identity().sha256().to_owned())
    })
    .expect("replay_environment admitted an AY");
    let mut unexpected = Vec::new();
    for (label, source, code, manifest) in cases {
        let owner = source_bound_x86_envelope(&source, "subject", &code, &manifest, SYSV).unwrap();
        // Replay part by part, as the verifier does, up to the first part
        // that does not certify.
        let mut outcome = "Verified".to_owned();
        for part in owner.parts() {
            let result = crate::x86_source_bound_body::tests::with_edits(&edits, || {
                crate::ay_bridge::verify_with_cli_raw_attributed(part, &config).result
            });
            if !matches!(result, AYResult::Verified) {
                let part_label = part
                    .name
                    .rsplit(X86_ENVELOPE_PART_SEPARATOR)
                    .next()
                    .unwrap_or_default();
                outcome = format!("{part_label}: {}", stable_outcome(&result));
                break;
            }
        }
        let recorded = KNOWN_UNCERTIFIED
            .iter()
            .find(|(sha, row, _)| *sha == ay_sha && *row == label)
            .map(|(_, _, outcome)| *outcome);
        eprintln!(
            "X86_ENVELOPE_QUALIFICATION {label} parts={} result={outcome} recorded={}",
            owner.parts().len(),
            recorded.unwrap_or("-")
        );
        if outcome != recorded.unwrap_or("Verified") {
            unexpected.push(format!("{label}: {outcome} (recorded: {recorded:?})"));
        }
    }
    assert!(
        unexpected.is_empty(),
        "a correct envelope changed outcome on the admitted pair (ay sha256 {ay_sha}); \
         review KNOWN_UNCERTIFIED: {unexpected:#?}"
    );
}

/// The replayed SMT, not only the Rust walk, carries each semantic check:
/// for the theorem of every mutant built without the walk's refusal, AY
/// refutes a part of an item the evaluator says the defect breaks (so the
/// theorem, the conjunction of its parts, is refuted). Fails without
/// authority.
#[test]
fn mutant_envelope_theorems_are_refuted_by_ay() {
    use crate::ay_bridge::{AYConfig, AYResult};
    let test = "mutant_envelope_theorems_are_refuted_by_ay";
    let edits = crate::x86_source_bound_body::tests::replay_environment(test);
    let config = AYConfig {
        solver: None,
        timeout_ms: 30_000,
        produce_models: true,
    };
    let void = void_source(0);
    let div = abort_source();
    let cases: Vec<(&str, &Function, Vec<u8>, Vec<u8>)> = vec![
        (
            "missing pop",
            &void,
            vec![0x55, 0x48, 0x89, 0xe5, 0xc3],
            no_rows(),
        ),
        (
            "extra pop",
            &void,
            vec![0x55, 0x48, 0x89, 0xe5, 0x5d, 0x5d, 0xc3],
            no_rows(),
        ),
        (
            "pop rbx",
            &void,
            vec![0x55, 0x48, 0x89, 0xe5, 0x5b, 0xc3],
            no_rows(),
        ),
        (
            "push rbx; pop r12",
            &void,
            vec![0x55, 0x48, 0x89, 0xe5, 0x53, 0x41, 0x5c, 0x5d, 0xc3],
            no_rows(),
        ),
        (
            "write above rsp0",
            &void,
            vec![
                0x48, 0x83, 0xc4, 0x10, 0x55, 0x48, 0x89, 0xe5, 0x5d, 0x48, 0x83, 0xec, 0x10, 0xc3,
            ],
            no_rows(),
        ),
        (
            "partial overlap",
            &void,
            vec![0x48, 0x83, 0xc4, 0x04, 0x55, 0x48, 0x83, 0xc4, 0x04, 0xc3],
            no_rows(),
        ),
        (
            "frameless call",
            &div,
            vec![0xe8, 0, 0, 0, 0, 0x0f, 0x0b],
            encode(&[call_row(1)]),
        ),
        (
            "extra push before the call",
            &div,
            vec![0x55, 0x48, 0x89, 0xe5, 0x53, 0xe8, 0, 0, 0, 0, 0x0f, 0x0b],
            encode(&[call_row(6)]),
        ),
        (
            "an instruction between the call and the trap",
            &div,
            vec![0x55, 0x48, 0x89, 0xe5, 0xe8, 0, 0, 0, 0, 0x5d, 0x0f, 0x0b],
            abort_rows(),
        ),
        (
            "the call's push overwrites the caller's return address",
            &div,
            vec![0x58, 0xe8, 0, 0, 0, 0, 0x0f, 0x0b],
            encode(&[call_row(2)]),
        ),
    ];
    // The battery asserts its own cardinality, so a case cannot vanish.
    assert_eq!(cases.len(), 10);
    let mut unrefuted = Vec::new();
    for (label, source, code, manifest) in cases {
        let theorem =
            theorem_without_walk_refusal(source, "subject", &code, &manifest, SYSV).unwrap();
        let broken = refuted_items(&theorem);
        assert!(
            !broken.is_empty(),
            "{label}: the evaluator falsifies no item"
        );
        let mut refuted = None;
        'items: for &item in &broken {
            for part in parts_of_item(&theorem, item) {
                let result = crate::x86_source_bound_body::tests::with_edits(&edits, || {
                    crate::ay_bridge::verify_with_cli_raw_attributed(part, &config).result
                });
                if matches!(result, AYResult::CounterExample(_)) {
                    refuted = Some(part.name.clone());
                    break 'items;
                }
            }
        }
        eprintln!("X86_ENVELOPE_QUALIFICATION mutant={label} refuted_part={refuted:?}");
        if refuted.is_none() {
            unrefuted.push(label);
        }
    }
    assert!(
        unrefuted.is_empty(),
        "every mutant's theorem must be refuted: {unrefuted:#?}"
    );
}
