// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Concrete evaluation is regression evidence, never universal proof discharge.
use super::super::cell_source::values::Call;
use super::*;
use std::collections::{BTreeMap, HashMap};
use std::hash::{Hash, Hasher};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Memory {
    seed: u64,
    writes: BTreeMap<u64, u8>,
}
impl Memory {
    fn default_byte(&self, address: u64) -> u8 {
        address
            .wrapping_mul(0x9e3779b97f4a7c15)
            .rotate_left(17)
            .wrapping_add(self.seed) as u8
    }
    fn read(&self, address: u64) -> u8 {
        self.writes
            .get(&address)
            .copied()
            .unwrap_or_else(|| self.default_byte(address))
    }
    fn write(&mut self, address: u64, value: u8) {
        if value == self.default_byte(address) {
            self.writes.remove(&address);
        } else {
            self.writes.insert(address, value);
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Value {
    Bits(u64),
    Bool(bool),
    Memory(Memory),
}
impl Value {
    fn bits(self) -> u64 {
        let Self::Bits(v) = self else {
            panic!("expected bits")
        };
        v
    }
    fn boolean(self) -> bool {
        let Self::Bool(v) = self else {
            panic!("expected boolean")
        };
        v
    }
    fn memory(self) -> Memory {
        let Self::Memory(v) = self else {
            panic!("expected memory")
        };
        v
    }
}

// Interpret the emitted AST, including full array equality, independently of
// the obligation builder. The callback replaces arbitrary public memory; it
// is deliberately neither cell-only nor an identity transformation.
fn eval(e: &E, env: &HashMap<String, Value>) -> Value {
    let bits = |e: &E| eval(e, env).bits();
    let boolean = |e: &E| eval(e, env).boolean();
    let mask = |v: u64, width: u32| {
        if width == 64 {
            v
        } else {
            v & ((1 << width) - 1)
        }
    };
    match e {
        E::Var { name, .. } => env[name].clone(),
        E::BvConst { value, .. } => Value::Bits(*value),
        E::BoolConst(v) => Value::Bool(*v),
        E::BvAdd { lhs, rhs, width } => {
            Value::Bits(mask(bits(lhs).wrapping_add(bits(rhs)), *width))
        }
        E::BvSub { lhs, rhs, width } => {
            Value::Bits(mask(bits(lhs).wrapping_sub(bits(rhs)), *width))
        }
        E::BvAnd { lhs, rhs, .. } => Value::Bits(bits(lhs) & bits(rhs)),
        E::BvXor { lhs, rhs, .. } => Value::Bits(bits(lhs) ^ bits(rhs)),
        E::BvUlt { lhs, rhs, .. } => Value::Bool(bits(lhs) < bits(rhs)),
        E::BvUge { lhs, rhs, .. } => Value::Bool(bits(lhs) >= bits(rhs)),
        E::Extract {
            operand,
            low,
            width,
            ..
        } => Value::Bits(mask(bits(operand) >> low, *width)),
        E::Concat { hi, lo, .. } => Value::Bits((bits(hi) << lo.bv_width()) | bits(lo)),
        E::Eq { lhs, rhs } => Value::Bool(eval(lhs, env) == eval(rhs, env)),
        E::Not { operand } => Value::Bool(!boolean(operand)),
        E::And { lhs, rhs } => Value::Bool(boolean(lhs) & boolean(rhs)),
        E::Or { lhs, rhs } => Value::Bool(boolean(lhs) | boolean(rhs)),
        E::Select { array, index } => {
            Value::Bits(u64::from(eval(array, env).memory().read(bits(index))))
        }
        E::Store {
            array,
            index,
            value,
        } => {
            let mut memory = eval(array, env).memory();
            memory.write(bits(index), bits(value) as u8);
            Value::Memory(memory)
        }
        E::UF { name, args, .. } if args.is_empty() => env
            .get(name)
            .unwrap_or_else(|| panic!("unbound or forward definition {name}"))
            .clone(),
        E::UF { name, args, .. } => {
            assert_eq!(args.len(), 3);
            let mut hash = std::collections::hash_map::DefaultHasher::new();
            name.hash(&mut hash);
            args.iter()
                .map(|arg| eval(arg, env))
                .collect::<Vec<_>>()
                .hash(&mut hash);
            Value::Memory(Memory {
                seed: hash.finish(),
                writes: BTreeMap::new(),
            })
        }
        other => panic!("unsupported test expression {other:?}"),
    }
}

fn sample(ob: &ProofObligation, sp: u64, observe: u64, seed: u64) -> bool {
    let mut env: HashMap<_, _> = ob
        .inputs
        .iter()
        .enumerate()
        .map(|(i, (name, width))| {
            let value = seed.wrapping_mul(0x517cc1b727220a95).rotate_left(i as u32);
            (
                name.clone(),
                Value::Bits(if *width == 64 {
                    value
                } else {
                    value & 0xffff_ffff
                }),
            )
        })
        .collect();
    env.insert("entry_sp".into(), Value::Bits(sp));
    env.insert("observe".into(), Value::Bits(observe));
    env.insert(
        "entry_memory".into(),
        Value::Memory(Memory {
            seed,
            writes: BTreeMap::new(),
        }),
    );
    for guard in &ob.preconditions[..2] {
        assert!(eval(guard, &env).boolean());
    }
    for definition in &ob.preconditions[2..] {
        let E::Eq { lhs, rhs } = definition else {
            panic!("expected definition")
        };
        let E::UF {
            name,
            args,
            ret_sort,
        } = &**lhs
        else {
            panic!("expected fresh array")
        };
        assert!(args.is_empty());
        assert_eq!(*ret_sort, memory_sort());
        let value = eval(rhs, &env); // Fails on a cycle or forward reference.
        assert!(
            env.insert(name.clone(), value).is_none(),
            "duplicate definition"
        );
    }
    eval(&ob.trust_ir_expr, &env) == eval(&ob.aarch64_expr, &env)
}

fn contract(width: usize, count: usize) -> Contract {
    let parameters = |p| {
        (0..width)
            .map(|b| Byte::Parameter(p, b))
            .collect::<Vec<_>>()
    };
    let result = |c| (0..width).map(|b| Byte::Call(c, b)).collect::<Vec<_>>();
    Contract {
        width,
        parameters: 2,
        calls: (0..count)
            .map(|i| Call {
                name: if i % 2 == 0 {
                    "callback|\\ α"
                } else {
                    "other"
                }
                .into(),
                cell_before: if i == 0 {
                    let mut initial = parameters(0);
                    initial[width - 1] = Byte::Constant(0x80);
                    initial
                } else {
                    result(i - 1)
                },
                argument: if i == 0 { parameters(1) } else { result(i - 1) },
            })
            .collect(),
        cell_after: result(count - 1),
        // Retain an earlier value independently of the final cell.
        result: if count == 1 { parameters(1) } else { result(0) },
    }
}

#[test]
fn complete_memory_queries_evaluate_with_acyclic_definitions_at_trace_bounds() {
    let mut samples = 0;
    for width in [4, 8] {
        for count in [1, 2, 16] {
            let ob = obligation(&contract(width, count));
            let query = crate::ay_bridge::generate_smt2_query_raw(&ob, &Default::default());
            // The maintained serializer selects ALL for arrays plus UFs.
            // This is a valid logic selection; no formula rewrite is needed.
            assert!(query.contains("(set-logic ALL)"));
            println!(
                "CELL_MEMORY_QUERY_BEGIN synthetic-cell{width}-calls{count}\n{query}CELL_MEMORY_QUERY_END synthetic-cell{width}-calls{count}"
            );
            assert!(query.len() < 400_000, "{} bytes", query.len());
            assert_eq!(query.matches("(declare-fun cell_callback_").count(), count);
            for sp in [48, 4096, u64::MAX - 15] {
                for observe in [0, sp - 48, sp - 40, sp - 33, sp - 32, sp - 1, sp, u64::MAX] {
                    for seed in [0, 1, 0x7ff8_0000_0000_0001, u64::MAX] {
                        assert!(
                            sample(&ob, sp, observe, seed),
                            "width={width} calls={count} sp={sp} observe={observe} seed={seed}"
                        );
                        samples += 1;
                    }
                }
            }
        }
    }
    assert_eq!(samples, 576);
    println!("CELL_MEMORY samples={samples} proof_discharge=false");
}

#[test]
fn memory_queries_detect_changed_callback_and_private_or_public_effects() {
    let mut rejected = 0;
    for width in [4, 8] {
        let ob = obligation(&contract(width, 2));
        for mutation in 0..7 {
            let mut bad = ob.clone();
            // The first machine callback has its own definition. Locate it by
            // its application, so this control does not depend on save count.
            if mutation < 4 {
                let mut seen = false;
                for definition in &mut bad.preconditions {
                    let E::Eq { rhs, .. } = definition else {
                        continue;
                    };
                    let E::UF { name, args, .. } = std::sync::Arc::make_mut(rhs) else {
                        continue;
                    };
                    if args.is_empty() {
                        continue;
                    }
                    if !seen {
                        seen = true;
                        continue;
                    }
                    match mutation {
                        0 => name.push_str("00"),
                        1 => args[1] = args[1].clone().bvadd(E::bv_const(1, 64)),
                        2 => args[2] = args[2].clone().bvxor(E::bv_const(1, (width * 8) as u32)),
                        _ => args[0] = E::uf("entry_memory", vec![], memory_sort()),
                    }
                    break;
                }
            } else {
                let E::Eq { rhs, .. } = bad.preconditions.last_mut().unwrap() else {
                    unreachable!()
                };
                // Flip a final private save, cell, or distant public byte.
                let address = match mutation {
                    4 => below(24),
                    5 => below(33),
                    _ => E::var("observe", 64),
                };
                *rhs = E::store(
                    (**rhs).clone(),
                    address.clone(),
                    E::select((**rhs).clone(), address).bvxor(E::bv_const(1, 8)),
                )
                .into();
            }
            assert!(
                (0..8).any(|seed| !sample(&bad, 4096, 9000, seed)),
                "undetected mutation {mutation} width {width}"
            );
            let query = crate::ay_bridge::generate_smt2_query_raw(&bad, &Default::default());
            println!(
                "CELL_MEMORY_QUERY_BEGIN mutant-cell{width}-case{mutation}\n{query}CELL_MEMORY_QUERY_END mutant-cell{width}-case{mutation}"
            );
            rejected += 1;
        }
    }
    assert_eq!(rejected, 14);
    println!("CELL_MEMORY mutations_rejected={rejected} proof_discharge=false");
}
