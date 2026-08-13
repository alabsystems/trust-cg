// trust-cg-codegen/tests/lean_encode_golden_binding.rs
//
// ENC-4 — GOLDEN-VECTOR BINDING of the Lean byte encoder to the real backend encoder.
//
// WHAT THIS GUARDS
// ----------------
// The Lean forward-simulation model (formal/lean, ENC-1) has its OWN byte-level x86-64 emitter
// `Trust.Model.Encoder.encode`.  Its keystone axiom `x86Step_decode` is only end-to-end meaningful
// if those MODEL bytes are the bytes the REAL backend (`x86_64/encode.rs`) actually writes.  Nothing
// mechanically forces the two encoders to agree — the Lean model can drift and keep proving things
// about an encoding the backend no longer produces, silently voiding the guarantee.
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
