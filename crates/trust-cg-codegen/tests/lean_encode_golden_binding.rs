// trust-cg-codegen/tests/lean_encode_golden_binding.rs
//
// ENC-4 — GOLDEN-VECTOR BINDING of the Lean byte encoder to the real backend encoder.
//
// WHAT THIS GUARDS
// ----------------
// The Lean forward-simulation model (formal/lean, ENC-1) has its OWN byte-level x86-64 emitter
// `Trust.Model.Encoder.encode`.  Its keystone `x86Step_decode` (a theorem of the model's
// fetch/decode/execute `x86Step`, no longer an axiom) is only end-to-end meaningful if those MODEL
// bytes are the bytes the REAL backend (`x86_64/encode.rs`) actually writes; it says nothing about
// what x86-64 hardware does with them.  Nothing mechanically forces the two encoders to agree —
// the Lean model can drift and keep proving things about an encoding the backend no longer
// produces, silently voiding the guarantee.
//
// THE BINDING (single shared anchor)
// ----------------------------------
//   formal/lean/Trust/Model/EncoderGolden.lean pins, for the keystone-reachable b64 reg/reg ALU
//   forms, exact byte lists that are KERNEL-CHECKED by `decide` against the Lean model's `encode`
//   (lake build fails closed on model drift).  THIS test parses that very file and asserts the real
//   `encode.rs` emits byte-for-byte the SAME lists.  Transitively:
//
//         encode.rs  ==  EncoderGolden.lean literals  ==  Lean model `encode`.
//
//   A drift on EITHER leg fails a gate:
//     * Lean model `encode` changes    -> lake `by decide` in EncoderGolden.lean fails.
//     * backend `encode.rs` changes     -> THIS test fails (encoder != parsed golden).
//     * a golden byte is hand-edited    -> lake fails (model != literal) AND/OR this test fails.
//     * an instruction is dropped from  -> the coverage assertion below fails (parsed-key set !=
//       one side                            the bound table).
//
// This is sound-in-isolation: a golden test can only ADD constraints; it never relaxes one.

use std::path::PathBuf;

use trust_cg_codegen::x86_64::{X86Encoder, X86InstOperands};
use trust_cg_ir::x86_64_ops::X86CondCode;
use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_ir::x86_64_regs::X86PReg;
use trust_cg_ir::x86_64_regs::{R8, R9, R15, RAX, RCX, RDX};

/// Path to the Lean golden module (the single source of the anchored bytes).
fn golden_lean_path() -> PathBuf {
    // CARGO_MANIFEST_DIR = <repo>/crates/trust-cg-codegen
    let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    p.pop(); // crates
    p.pop(); // <repo>
    p.push("formal/lean/Trust/Model/EncoderGolden.lean");
    p
}

/// One parsed golden line: `theorem g_<op>_<pair> : encode (...) = ([bytes] : List UInt8) ...`
#[derive(Debug)]
struct Golden {
    op: String,
    pair: String,
    bytes: Vec<u8>,
}

/// Parse the rigid one-theorem-per-line golden format.  Robust to whitespace but expects the
/// `theorem g_<op>_<pair>` name token and a `([ ... ] : List UInt8)` byte list on the same line.
fn parse_goldens(text: &str) -> Vec<Golden> {
    let mut out = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        if !line.starts_with("theorem g_") {
            continue;
        }
        // key = the token after "theorem g_", up to the next whitespace or ':'.
        let after = &line["theorem g_".len()..];
        let key_end = after
            .find(|c: char| c.is_whitespace() || c == ':')
            .unwrap_or(after.len());
        let key = &after[..key_end];
        // key is <op>_<pair>; pair is the LAST two underscore-joined tokens (e.g. rax_rcx).
        let parts: Vec<&str> = key.split('_').collect();
        assert!(
            parts.len() == 3,
            "golden key `{key}` must be <op>_<regA>_<regB>"
        );
        let op = parts[0].to_string();
        let pair = format!("{}_{}", parts[1], parts[2]);
        // bytes = inside the first `[ ... ]`.
        let lb = line.find('[').expect("golden line missing `[`");
        let rb = line.find(']').expect("golden line missing `]`");
        let inner = &line[lb + 1..rb];
        let bytes: Vec<u8> = inner
            .split(',')
            .map(|t| {
                let t = t.trim();
                let hex = t
                    .strip_prefix("0x")
                    .or_else(|| t.strip_prefix("0X"))
                    .unwrap_or(t);
                u8::from_str_radix(hex, 16)
                    .unwrap_or_else(|_| panic!("bad golden byte `{t}` in line: {line}"))
            })
            .collect();
        assert!(!bytes.is_empty(), "empty byte list in golden line: {line}");
        out.push(Golden { op, pair, bytes });
    }
    out
}

/// Lean op-mnemonic -> backend opcode (the keystone-reachable b64 reg/reg ALU set).
fn opcode_of(op: &str) -> Option<X86Opcode> {
    Some(match op {
        "movRR" => X86Opcode::MovRR,
        "addRR" => X86Opcode::AddRR,
        "adcRR" => X86Opcode::AdcRR,
        "subRR" => X86Opcode::SubRR,
        "sbbRR" => X86Opcode::SbbRR,
        "cmpRR" => X86Opcode::CmpRR,
        "testRR" => X86Opcode::TestRR,
        "andRR" => X86Opcode::AndRR,
        "orRR" => X86Opcode::OrRR,
        "xorRR" => X86Opcode::XorRR,
        _ => return None,
    })
}

/// Lean pair name -> (dst, src) physical registers.
fn regs_of(pair: &str) -> Option<(X86PReg, X86PReg)> {
    Some(match pair {
        "rax_rcx" => (RAX, RCX),
        "r8_rdx" => (R8, RDX),
        "rdx_r9" => (RDX, R9),
        "r15_r8" => (R15, R8),
        _ => return None,
    })
}

fn encode_backend(op: X86Opcode, dst: X86PReg, src: X86PReg) -> Vec<u8> {
    let mut enc = X86Encoder::new();
    enc.encode_instruction(op, &X86InstOperands::rr(dst, src))
        .expect("backend encode_instruction failed");
    enc.finish()
}

/// Bind all condition codes and signed/byte-order displacement boundaries.
#[test]
fn backend_matches_lean_near_branch_goldens() {
    use X86CondCode::*;
    use std::collections::BTreeMap;
    let conditions = [
        ("o", O),
        ("no", NO),
        ("b", B),
        ("ae", AE),
        ("e", E),
        ("ne", NE),
        ("be", BE),
        ("a", A),
        ("s", S),
        ("ns", NS),
        ("p", P),
        ("np", NP),
        ("l", L),
        ("ge", GE),
        ("le", LE),
        ("g", G),
    ];
    let displacements = [
        ("one", 1),
        ("minus_one", -1),
        ("min", i32::MIN as i64),
        ("max", i32::MAX as i64),
        ("bytes", 0x1234_5678),
    ];
    let mut expected = BTreeMap::new();
    for (name, condition) in conditions {
        expected.insert(
            format!("jcc_{name}_zero"),
            (X86Opcode::Jcc, X86InstOperands::jcc(condition, 0)),
        );
    }
    for (name, displacement) in displacements {
        expected.insert(
            format!("jcc_e_{name}"),
            (X86Opcode::Jcc, X86InstOperands::jcc(E, displacement)),
        );
        expected.insert(
            format!("jmp_{name}"),
            (X86Opcode::Jmp, X86InstOperands::rel(displacement)),
        );
    }
    expected.insert("jmp_zero".into(), (X86Opcode::Jmp, X86InstOperands::rel(0)));
    let text = std::fs::read_to_string(golden_lean_path()).expect("read Lean branch goldens");
    let mut count = 0;
    for line in text
        .lines()
        .filter_map(|line| line.trim().strip_prefix("theorem branch_"))
    {
        let (name, body) = line.split_once(" : ").expect("branch theorem name");
        let (opcode, operands) = expected.remove(name).expect("unique bound branch key");
        let bytes = body
            .split_once("([")
            .expect("branch byte list")
            .1
            .split_once(']')
            .expect("branch byte list end")
            .0;
        let bytes: Vec<u8> = bytes
            .split(',')
            .map(|byte| {
                u8::from_str_radix(byte.trim().strip_prefix("0x").expect("hex byte"), 16)
                    .expect("valid byte")
            })
            .collect();
        let mut encoder = X86Encoder::new();
        encoder
            .encode_instruction(opcode, &operands)
            .expect("encode branch");
        assert_eq!(encoder.finish(), bytes, "branch encoder drift: {name}");
        count += 1;
    }
    assert_eq!(count, 27);
    assert!(
        expected.is_empty(),
        "missing branch goldens: {:?}",
        expected.keys()
    );
}

#[test]
fn lean_golden_file_present_and_nonempty() {
    let path = golden_lean_path();
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("cannot read Lean golden {}: {e}", path.display()));
    let goldens = parse_goldens(&text);
    assert!(
        goldens.len() >= 40,
        "expected >= 40 golden vectors in {}, found {}",
        path.display(),
        goldens.len()
    );
}

/// THE BINDING: every Lean golden byte list is reproduced EXACTLY by the real `encode.rs`.
#[test]
fn backend_matches_lean_golden_bytes() {
    let path = golden_lean_path();
    let text = std::fs::read_to_string(&path).expect("read Lean golden");
    let goldens = parse_goldens(&text);
    assert!(
        !goldens.is_empty(),
        "no goldens parsed from {}",
        path.display()
    );

    for g in &goldens {
        let op = opcode_of(&g.op).unwrap_or_else(|| {
            panic!(
                "Lean golden references op `{}` with no backend binding — DRIFT: add it to \
                 opcode_of() or remove the golden",
                g.op
            )
        });
        let (dst, src) = regs_of(&g.pair).unwrap_or_else(|| {
            panic!(
                "Lean golden references reg pair `{}` with no backend binding — DRIFT: add it to \
                 regs_of() or remove the golden",
                g.pair
            )
        });
        let got = encode_backend(op, dst, src);
        assert_eq!(
            got, g.bytes,
            "ENCODER DRIFT for `{}_{}`: backend encode.rs emitted {:02X?} but the Lean model's \
             golden (kernel-checked in EncoderGolden.lean) is {:02X?}. The Lean forward-sim proof \
             now describes bytes the backend does NOT emit. Reconcile encode.rs and the Lean \
             `encode` model, then update the golden.",
            g.op, g.pair, got, g.bytes
        );
    }
}

/// COVERAGE / drift-of-set: the parsed golden key set must equal the bound (op x pair) matrix —
/// so an instruction added to (or dropped from) EITHER the Lean goldens or this binding table is a
/// hard failure, not a silent gap.
#[test]
fn golden_key_set_matches_binding_table() {
    let path = golden_lean_path();
    let text = std::fs::read_to_string(&path).expect("read Lean golden");
    let goldens = parse_goldens(&text);

    let ops = [
        "movRR", "addRR", "adcRR", "subRR", "sbbRR", "cmpRR", "testRR", "andRR", "orRR", "xorRR",
    ];
    let pairs = ["rax_rcx", "r8_rdx", "rdx_r9", "r15_r8"];

    let mut expected: Vec<String> = Vec::new();
    for p in &pairs {
        for o in &ops {
            expected.push(format!("{o}_{p}"));
        }
    }
    let mut found: Vec<String> = goldens
        .iter()
        .map(|g| format!("{}_{}", g.op, g.pair))
        .collect();
    found.sort();
    let mut expected_sorted = expected.clone();
    expected_sorted.sort();

    // Every bound key has a golden, and every golden binds (both directions).
    for k in &expected_sorted {
        assert!(
            found.binary_search(k).is_ok(),
            "missing Lean golden for bound key `{k}` — an instruction was dropped from the Lean \
             side (drift)"
        );
    }
    for k in &found {
        assert!(
            expected_sorted.binary_search(k).is_ok(),
            "Lean golden `{k}` has no entry in the binding table — an instruction was added on the \
             Lean side without a backend binding (drift)"
        );
    }
    assert_eq!(
        found.len(),
        expected.len(),
        "golden count {} != bound-matrix size {}",
        found.len(),
        expected.len()
    );
}

/// Bind the full-width mask loads needed by the SWAR execution proof.
#[test]
fn backend_matches_lean_movabs_goldens() {
    use std::collections::BTreeMap;
    use trust_cg_ir::x86_64_regs::*;
    let registers = [
        ("rax", RAX),
        ("rcx", RCX),
        ("rdx", RDX),
        ("rbx", RBX),
        ("rsp", RSP),
        ("rbp", RBP),
        ("rsi", RSI),
        ("rdi", RDI),
        ("r8", R8),
        ("r9", R9),
        ("r10", R10),
        ("r11", R11),
        ("r12", R12),
        ("r13", R13),
        ("r14", R14),
        ("r15", R15),
    ];
    let values = [
        ("m1", 0x5555_5555_5555_5555_u64),
        ("m2", 0x3333_3333_3333_3333),
        ("m4", 0x0f0f_0f0f_0f0f_0f0f),
        ("mixed", 0x0123_4567_89ab_cdef),
        ("high", 0x8000_0000_0000_0000),
        ("ones", u64::MAX),
    ];
    let path = golden_lean_path().with_file_name("MovabsGolden.lean");
    let text = std::fs::read_to_string(path).expect("read movabs golden module");
    let mut parsed = BTreeMap::new();
    for golden in parse_goldens(&text) {
        assert_eq!(golden.op, "movabsRI");
        assert!(
            parsed.insert(golden.pair, golden.bytes).is_none(),
            "duplicate golden"
        );
    }
    assert_eq!(parsed.len(), registers.len() * values.len());
    for (name, register) in registers {
        for (label, immediate) in values {
            let key = format!("{name}_{label}");
            let expected = parsed.remove(&key).expect("missing movabs golden");
            let mut encoder = X86Encoder::new();
            encoder
                .encode_instruction(
                    X86Opcode::MovRI,
                    &X86InstOperands::ri(register, immediate as i64),
                )
                .expect("encode movabs");
            assert_eq!(encoder.finish(), expected, "{key}");
        }
    }
    assert!(parsed.is_empty(), "unbound golden keys");
}

/// Anchor every register prefix, then cover all 256 raw immediate bytes.
/// Lean's encode_shrRI_immediate proves this prefix/suffix decomposition.
#[test]
fn backend_matches_lean_shr_all_immediates() {
    use std::collections::BTreeMap;
    use trust_cg_ir::x86_64_regs::*;
    let registers = [
        ("rax", RAX),
        ("rcx", RCX),
        ("rdx", RDX),
        ("rbx", RBX),
        ("rsp", RSP),
        ("rbp", RBP),
        ("rsi", RSI),
        ("rdi", RDI),
        ("r8", R8),
        ("r9", R9),
        ("r10", R10),
        ("r11", R11),
        ("r12", R12),
        ("r13", R13),
        ("r14", R14),
        ("r15", R15),
    ];
    let path = golden_lean_path().with_file_name("ShrGolden.lean");
    let text = std::fs::read_to_string(path).expect("read SHR golden module");
    let mut prefixes = BTreeMap::new();
    for golden in parse_goldens(&text) {
        assert_eq!(golden.op, "shrRI");
        assert_eq!(golden.bytes.len(), 4);
        assert_eq!(golden.bytes[3], 0);
        assert!(
            prefixes
                .insert(golden.pair, golden.bytes[..3].to_vec())
                .is_none(),
            "duplicate SHR prefix"
        );
    }
    assert_eq!(prefixes.len(), registers.len());
    for (name, register) in registers {
        let prefix = prefixes
            .remove(&format!("{name}_zero"))
            .expect("missing register prefix");
        for immediate in 0..=u8::MAX {
            let mut expected = prefix.clone();
            expected.push(immediate);
            let mut encoder = X86Encoder::new();
            encoder
                .encode_instruction(
                    X86Opcode::ShrRI,
                    &X86InstOperands::ri(register, i64::from(immediate)),
                )
                .expect("encode SHR");
            assert_eq!(encoder.finish(), expected, "{name} imm={immediate}");
        }
    }
    assert!(prefixes.is_empty(), "unexpected register prefix");
}

/// Exercise the Trust-minted mask over all raw byte inputs, through real constructors.
#[test]
fn clean_register_bits_cover_every_input_byte() {
    use trust_cg_codegen::x86_64::ModRM;
    for reg in 0..=u8::MAX {
        for rm in 0..=u8::MAX {
            let fields = ((reg & 7) << 3) | (rm & 7);
            assert_eq!(ModRM::reg_reg(reg, rm).encode(), 0xc0 | fields);
            assert_eq!(ModRM::ext_reg(reg, rm).encode(), 0xc0 | fields);
            assert_eq!(ModRM::indirect(reg, rm).encode(), fields);
            assert_eq!(ModRM::indirect_disp8(reg, rm).encode(), 0x40 | fields);
            assert_eq!(ModRM::indirect_disp32(reg, rm).encode(), 0x80 | fields);
        }
    }
}
