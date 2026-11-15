// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
use trust_cg_lower::instructions::{Block, DirectCallBinding, Opcode};
fn invoke(binding: DirectCallBinding) -> Opcode {
    Opcode::Invoke {
        name: "owned_entry".into(),
        binding,
        normal_dest: Block(1),
        unwind_dest: Block(2),
    }
}
#[test]
fn old_unbound_serde_invoke_remains_interposable_and_exact_carrier_roundtrips() {
    let old: Opcode =
        serde_json::from_str(r#"{"Invoke":{"name":"old","normal_dest":1,"unwind_dest":2}}"#)
            .unwrap();
    assert!(matches!(
        old,
        Opcode::Invoke {
            binding: DirectCallBinding::Interposable,
            ..
        }
    ));
    let exact = invoke(DirectCallBinding::ExactModuleFunction { function: 17 });
    let encoded = serde_json::to_string(&exact).unwrap();
    assert_eq!(serde_json::from_str::<Opcode>(&encoded).unwrap(), exact);
    let pending = invoke(DirectCallBinding::DeclaredExternalFunction { function: 17 });
    assert_ne!(serde_json::to_string(&pending).unwrap(), encoded);
}
