
/// The machine-side controls of `wrong_control_is_named_or_refused`, as
/// pairs (the same mutations, in the same order).
fn probe_controls() -> Vec<(&'static str, Function, X86ISelFunction)> {
    use trust_cg_ir::X86CondCode as C;
    let mut cases = Vec::new();
    let (source, mut machine) = slice6_pair(FlowShape::MinU64);
    let jcc = nth(&machine, X86Opcode::Jcc, 0);
    insert_at(
        &mut machine,
        jcc,
        X86ISelInst::new(X86Opcode::MovRI, vec![vreg(90), O::Imm(0)]),
    );
    insert_at(
        &mut machine,
        jcc + 1,
        X86ISelInst::new(X86Opcode::AddRI, vec![vreg(90), vreg(90), O::Imm(1)]),
    );
    cases.push(("flag clobber between cmp and jcc", source, machine));
    let (source, mut machine) = slice6_pair(FlowShape::SelectU64);
    let cmov = nth(&machine, X86Opcode::Cmovcc, 0);
    insert_at(
        &mut machine,
        cmov,
        X86ISelInst::new(X86Opcode::AndRI, vec![vreg(4), vreg(4), O::Imm(1)]),
    );
    cases.push(("flag clobber between cmp and cmov", source, machine));
    let (source, mut machine) = slice6_pair(FlowShape::TwoDiamonds);
    let second = nth(&machine, X86Opcode::Jcc, 1);
    let cmp = (0..second)
        .rev()
        .find(|row| inst(&machine, *row).opcode == X86Opcode::CmpRI)
        .unwrap();
    remove_at(&mut machine, cmp);
    cases.push(("flags an ALU row wrote before a jump", source, machine));
    let (source, mut machine) = slice6_pair(FlowShape::TwoDiamonds);
    let second = nth(&machine, X86Opcode::Jcc, 1);
    let block = block_of(&machine, second);
    let first = (0..second)
        .find(|row| block_of(&machine, *row) == block)
        .unwrap();
    for row in (first..second).rev() {
        remove_at(&mut machine, row);
    }
    cases.push(("flags from another block", source, machine));
    let (source, mut machine) = slice6_pair(FlowShape::CallThenBranch);
    let jcc = nth(&machine, X86Opcode::Jcc, 0);
    let first = nth(&machine, X86Opcode::CmpRR, 0);
    for row in (first..jcc).rev() {
        remove_at(&mut machine, row);
    }
    cases.push(("jump on flags a call left undefined", source, machine));
    let (source, mut machine) = slice6_pair(FlowShape::CallThenBranch);
    let jcc = nth(&machine, X86Opcode::Jcc, 0);
    let first = nth(&machine, X86Opcode::CmpRR, 0);
    for row in (first..jcc).rev() {
        remove_at(&mut machine, row);
    }
    let call = nth(&machine, X86Opcode::Call, 0);
    let argument = inst(&machine, 0).operands[0].clone();
    insert_at(
        &mut machine,
        call,
        X86ISelInst::new(X86Opcode::CmpRI, vec![argument, O::Imm(0)]),
    );
    cases.push(("jump on flags set before a call", source, machine));
    let (source, mut machine) = slice6_pair(FlowShape::SelectU64);
    let cmov = nth(&machine, X86Opcode::Cmovcc, 0);
    let kept = inst(&machine, cmov).operands[0].clone();
    let init = (0..cmov)
        .rev()
        .find(|row| {
            let row = inst(&machine, *row);
            row.opcode == X86Opcode::MovRR && row.operands[0] == kept
        })
        .unwrap();
    remove_at(&mut machine, init);
    cases.push(("cmov into an undefined register", source, machine));
    let (source, mut machine) = slice6_pair(FlowShape::TrapArm);
    let ud2 = nth(&machine, X86Opcode::Ud2, 0);
    *inst_mut(&mut machine, ud2) = X86ISelInst::new(X86Opcode::Ret, vec![]);
    cases.push(("returns where the source traps", source, machine));
    let (source, mut machine) = slice6_pair(FlowShape::PanicArm);
    let ud2 = nth(&machine, X86Opcode::Ud2, 0);
    remove_at(&mut machine, ud2);
    cases.push(("a trap removed", source, machine));
    let (source, mut machine) = slice6_pair(FlowShape::EarlyReturn);
    let ret = nth(&machine, X86Opcode::Ret, 0);
    *inst_mut(&mut machine, ret) = X86ISelInst::new(X86Opcode::Ud2, vec![]);
    cases.push(("traps where the source returns", source, machine));
    let (source, mut machine) = slice6_pair(FlowShape::MinU64);
    let b = entry_copy(&machine, RSI);
    let arm_copy = join_copy(&machine, 0);
    inst_mut(&mut machine, arm_copy).operands[1] = b;
    cases.push(("wrong arm value", source, machine));
    let (source, mut machine) = slice6_pair(FlowShape::MinU64);
    let extra = Block(source.blocks.keys().map(|block| block.0).max().unwrap() + 1);
    machine.ensure_block(extra);
    machine
        .blocks
        .get_mut(&extra)
        .unwrap()
        .insts
        .push(X86ISelInst::new(X86Opcode::Ret, vec![]));
    let jcc = nth(&machine, X86Opcode::Jcc, 0);
    insert_jump(&mut machine, jcc, C::O, extra);
    cases.push(("a jump to a machine-only block", source, machine));
    let (source, mut machine) = slice6_pair(FlowShape::MinU64);
    let extra = Block(source.blocks.keys().map(|block| block.0).max().unwrap() + 1);
    machine.ensure_block(extra);
    machine
        .blocks
        .get_mut(&extra)
        .unwrap()
        .insts
        .push(X86ISelInst::new(X86Opcode::Ret, vec![]));
    cases.push(("a dead laid-out block", source, machine));
    let (source, mut machine) = slice6_pair(FlowShape::MinU64);
    let jcc = nth(&machine, X86Opcode::Jcc, 0);
    let then_block = match &inst(&machine, jcc).operands[1] {
        O::Block(block) => *block,
        other => panic!("{other:?}"),
    };
    let else_block = match &inst(&machine, jcc + 1).operands[0] {
        O::Block(block) => *block,
        other => panic!("{other:?}"),
    };
    inst_mut(&mut machine, jcc).operands[1] = O::Block(else_block);
    let entry = block_of(&machine, jcc);
    machine.blocks.get_mut(&entry).unwrap().successors = vec![else_block];
    cases.push(("both edges to one arm", source, machine));
    let (source, mut machine) = slice6_pair(FlowShape::MinU64);
    let jcc = nth(&machine, X86Opcode::Jcc, 0);
    let entry = block_of(&machine, jcc);
    machine.blocks.get_mut(&entry).unwrap().successors = vec![then_block];
    cases.push(("a recorded edge missing", source, machine));
    let (source, mut machine) = slice6_pair(FlowShape::MinU64);
    let jcc = nth(&machine, X86Opcode::Jcc, 0);
    inst_mut(&mut machine, jcc + 1).operands[0] = O::Block(then_block);
    let entry = block_of(&machine, jcc);
    machine.blocks.get_mut(&entry).unwrap().successors = vec![then_block];
    cases.push(("a jump whose fallthrough reaches its target", source, machine));
    let (source, mut machine) = slice6_pair(FlowShape::MinU64);
    let else_copy = join_copy(&machine, 1);
    let else_arm = block_of(&machine, else_copy);
    *inst_mut(&mut machine, else_copy + 1) = X86ISelInst::new(X86Opcode::Ret, vec![]);
    machine.blocks.get_mut(&else_arm).unwrap().successors.clear();
    cases.push(("a return before the path ends", source, machine));
    let (mut source, _) = slice6_pair(FlowShape::Switch3);
    for block in source.blocks.values_mut() {
        if let Some(last) = block.instructions.last_mut()
            && let L::Switch { cases, default } = &mut last.opcode
        {
            cases[1].1 = *default;
        }
    }
    let machine = select(&source, X86CallAbi::SystemV);
    cases.push(("a switch with two edges to one block", source, machine));
    let (source, machine) = slice6_pair(FlowShape::MinU64);
    let (_, selected) = slice6_pair(FlowShape::SelectU64);
    let mut converted = selected.clone();
    converted.name = machine.name.clone();
    converted.sig = machine.sig.clone();
    cases.push(("if-converted diamond", source, converted));
    let looped = counting_loop();
    let machine = select(&looped, X86CallAbi::SystemV);
    cases.push(("a loop", looped, machine));
    cases
}

/// Fails-before probe (temporary, never committed as a test): the slice-6
/// fixtures, variants, refutation mutants and controls, judged by whichever
/// owner this tree has, through API present before and after slice 6.
#[test]
#[ignore]
fn fails_before_probe() {
    let outcome = |source: &Function, machine: &X86ISelFunction| {
        match source_bound_x86_body(source, machine, SYSV) {
            Ok(owner) => format!("BUILT bound_rows={}", owner.bound_rows().len()),
            Err(refusal) => format!("REFUSED {}", refusal.to_string().replace('\n', " | ")),
        }
    };
    let mut lines = Vec::new();
    for shape in SLICE_SIX {
        let (source, machine) = slice6_pair(shape);
        lines.push(format!("fixture\t{shape:?}\t{}", outcome(&source, &machine)));
    }
    for (label, source, machine) in slice_six_variants() {
        lines.push(format!("variant\t{label}\t{}", outcome(&source, &machine)));
    }
    for (label, source, machine) in slice_six_refutations() {
        lines.push(format!("refutation\t{label}\t{}", outcome(&source, &machine)));
    }
    for (label, source, machine) in probe_controls() {
        lines.push(format!("control\t{label}\t{}", outcome(&source, &machine)));
    }
    let out = std::env::var("TCG_FB_OUT").expect("TCG_FB_OUT names the output file");
    std::fs::write(out, lines.join("\n") + "\n").unwrap();
}
