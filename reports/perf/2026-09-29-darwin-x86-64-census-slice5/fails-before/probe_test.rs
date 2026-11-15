
/// Fails-before probe: the outcome of the owner on every slice-5 fixture and
/// on the new-rule mutants, through API present before and after slice 5.
#[test]
fn slice_five_fails_before_probe() {
    let outcome = |source: &Function, machine: &X86ISelFunction| match source_bound_x86_body(
        source, machine, SYSV,
    ) {
        Ok(owner) => format!(
            "THEOREM built, {} bound rows, refuted on samples: {}",
            owner.bound_rows().len(),
            refuted_on_samples(owner.obligation())
        ),
        Err(refusal) => format!("REFUSED {refusal}"),
    };
    for shape in SLICE_FIVE {
        let (source, machine) = slice5_pair(shape);
        println!("PROBE fixture {shape:?}: {}", outcome(&source, &machine));
    }
    let mut mutants: Vec<(&str, Function, X86ISelFunction)> = Vec::new();
    let (source, mut machine) = slice5_pair(PairShape::PairSwap);
    let (rax, rdx) = (return_move(&machine, RAX), return_move(&machine, RDX));
    let (first, second) = (
        inst(&machine, rax).operands[1].clone(),
        inst(&machine, rdx).operands[1].clone(),
    );
    inst_mut(&mut machine, rax).operands[1] = second;
    inst_mut(&mut machine, rdx).operands[1] = first;
    mutants.push(("swapped pair halves", source, machine));
    let (source, mut machine) = slice5_pair(PairShape::PairSwap);
    remove_at(&mut machine, rdx);
    mutants.push(("missing RDX write", source, machine));
    let (source, mut machine) = slice5_pair(PairShape::PairCallArgs);
    let call = rows_with(&machine, X86Opcode::Call)[0];
    inst_mut(&mut machine, call + 1).operands[1] = preg(RDX);
    mutants.push(("RDX read after a one-result call", source, machine));
    let (source, mut machine) = slice5_pair(PairShape::PairCallSum);
    let call = rows_with(&machine, X86Opcode::Call)[0];
    inst_mut(&mut machine, call).call_result_regs =
        Some(vec![X86CallResultReg::new(X86PReg::new(RAX), 64)]);
    mutants.push(("pair call RDX lane dropped", source, machine));
    let (source, mut machine) = slice5_pair(PairShape::GlobalAddr);
    let lea = rows_with(&machine, X86Opcode::LeaRip)[0];
    inst_mut(&mut machine, lea).operands[1] = O::Symbol("s5_b".into());
    mutants.push(("an unreferenced symbol", source, machine));
    let (source, mut machine) = slice5_pair(PairShape::GlobalAddr);
    inst_mut(&mut machine, lea).opcode = X86Opcode::MovRipRel;
    inst_mut(&mut machine, lea).flags = X86Opcode::MovRipRel.default_flags();
    mutants.push(("GOT load of a direct reference", source, machine));
    let (source, mut machine) = slice5_pair(PairShape::TwoGlobals);
    let leas = rows_with(&machine, X86Opcode::LeaRip);
    let (first, second) = (
        inst(&machine, leas[0]).operands[1].clone(),
        inst(&machine, leas[1]).operands[1].clone(),
    );
    inst_mut(&mut machine, leas[0]).operands[1] = second;
    inst_mut(&mut machine, leas[1]).operands[1] = first;
    mutants.push(("symbols swapped", source, machine));
    let (source, mut machine) = slice5_pair(PairShape::CmpEqU64);
    let cmp = rows_with(&machine, X86Opcode::CmpRR)[0];
    remove_at(&mut machine, cmp);
    mutants.push(("setcc of the entry flags", source, machine));
    let (source, mut machine) = slice5_pair(PairShape::CmpEqU64);
    let movzx = rows_with(&machine, X86Opcode::Movzx)[0];
    remove_at(&mut machine, movzx);
    mutants.push(("setcc without movzx", source, machine));
    let (source, mut machine) = slice5_pair(PairShape::CmpSltI64);
    let setcc = rows_with(&machine, X86Opcode::Setcc)[0];
    inst_mut(&mut machine, setcc).operands[1] = O::CondCode(trust_cg_ir::X86CondCode::B);
    mutants.push(("unsigned order for a signed compare", source, machine));
    for (label, source, machine) in &mutants {
        println!("PROBE mutant {label}: {}", outcome(source, machine));
    }
}
