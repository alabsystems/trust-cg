#![no_std]
#![allow(dead_code)]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Op {
    Push(i64),
    PushF(f32),
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Dup,
    Swap,
    Over,
    Drop,
    Neg,
    Jz(u8),
    Jmp(u8),
    Lt,
    Shl(u8),
    Load(u8),
    Store(u8),
    ToF,
    FAdd,
    FToI,
    Halt,
}

#[derive(Debug, PartialEq, Clone, Copy)]
enum Val {
    I(i64),
    F(u32),
}

#[derive(Debug, PartialEq)]
enum VmErr {
    Underflow,
    Overflow,
    DivZero,
    Type(u8),
    Steps,
    Pc(usize),
}

struct Vm {
    stack: [i64; 16],
    tags: [u8; 16],
    sp: usize,
    regs: [i64; 4],
}

impl Vm {
    #[inline(never)]
    fn pop(&mut self) -> Result<Val, VmErr> {
        if self.sp == 0 {
            return Err(VmErr::Underflow);
        }
        self.sp -= 1;
        let raw = self.stack[self.sp];
        if self.tags[self.sp] == 0 {
            Ok(Val::I(raw))
        } else {
            Ok(Val::F(raw as u32))
        }
    }
    #[inline(never)]
    fn popi(&mut self) -> Result<i64, VmErr> {
        match self.pop()? {
            Val::I(x) => Ok(x),
            Val::F(_) => Err(VmErr::Type(self.sp as u8)),
        }
    }
    #[inline(never)]
    fn push(&mut self, v: Val) -> Result<(), VmErr> {
        if self.sp == self.stack.len() {
            return Err(VmErr::Overflow);
        }
        let (t, raw) = match v {
            Val::I(x) => (0u8, x),
            Val::F(b) => (1u8, b as i64),
        };
        self.stack[self.sp] = raw;
        self.tags[self.sp] = t;
        self.sp += 1;
        Ok(())
    }
}

#[inline(never)]
fn run(prog: &[Op], init: i64) -> Result<Val, VmErr> {
    let mut vm = Vm {
        stack: [0; 16],
        tags: [0; 16],
        sp: 0,
        regs: [init, 0, 0, 0],
    };
    let mut pc = 0usize;
    let mut steps = 0;
    loop {
        steps += 1;
        if steps > 500 {
            return Err(VmErr::Steps);
        }
        let op = *prog.get(pc).ok_or(VmErr::Pc(pc))?;
        pc += 1;
        match op {
            Op::Push(v) => vm.push(Val::I(v))?,
            Op::PushF(f) => vm.push(Val::F(f.to_bits()))?,
            Op::Add => {
                let b = vm.popi()?;
                let a = vm.popi()?;
                vm.push(Val::I(a.wrapping_add(b)))?
            }
            Op::Sub => {
                let b = vm.popi()?;
                let a = vm.popi()?;
                vm.push(Val::I(a.wrapping_sub(b)))?
            }
            Op::Mul => {
                let b = vm.popi()?;
                let a = vm.popi()?;
                vm.push(Val::I(a.wrapping_mul(b)))?
            }
            Op::Div => {
                let b = vm.popi()?;
                let a = vm.popi()?;
                let r = a.checked_div(b).ok_or(VmErr::DivZero)?;
                vm.push(Val::I(r))?
            }
            Op::Rem => {
                let b = vm.popi()?;
                let a = vm.popi()?;
                let r = a.checked_rem_euclid(b).ok_or(VmErr::DivZero)?;
                vm.push(Val::I(r))?
            }
            Op::Dup => {
                let a = vm.pop()?;
                vm.push(a)?;
                vm.push(a)?
            }
            Op::Swap => {
                let b = vm.pop()?;
                let a = vm.pop()?;
                vm.push(b)?;
                vm.push(a)?
            }
            Op::Over => {
                let b = vm.pop()?;
                let a = vm.pop()?;
                vm.push(a)?;
                vm.push(b)?;
                vm.push(a)?
            }
            Op::Drop => {
                vm.pop()?;
            }
            Op::Neg => {
                let a = vm.popi()?;
                vm.push(Val::I(a.wrapping_neg()))?
            }
            Op::Jz(t) => {
                if vm.popi()? == 0 {
                    pc = t as usize;
                }
            }
            Op::Jmp(t) => pc = t as usize,
            Op::Lt => {
                let b = vm.popi()?;
                let a = vm.popi()?;
                vm.push(Val::I((a < b) as i64))?
            }
            Op::Shl(k) => {
                let a = vm.popi()?;
                vm.push(Val::I(a.wrapping_shl(k as u32)))?
            }
            Op::Load(r) => {
                let v = vm.regs[(r & 3) as usize];
                vm.push(Val::I(v))?
            }
            Op::Store(r) => {
                let v = vm.popi()?;
                vm.regs[(r & 3) as usize] = v;
            }
            Op::ToF => {
                let a = vm.popi()?;
                vm.push(Val::F((a as f32).to_bits()))?
            }
            Op::FAdd => {
                let b = vm.pop()?;
                let a = vm.pop()?;
                match (a, b) {
                    (Val::F(x), Val::F(y)) => {
                        vm.push(Val::F((f32::from_bits(x) + f32::from_bits(y)).to_bits()))?
                    }
                    (Val::F(x), Val::I(y)) | (Val::I(y), Val::F(x)) => {
                        vm.push(Val::F((f32::from_bits(x) + y as f32).to_bits()))?
                    }
                    _ => return Err(VmErr::Type(99)),
                }
            }
            Op::FToI => match vm.pop()? {
                Val::F(x) => vm.push(Val::I(f32::from_bits(x) as i64))?,
                v => vm.push(v)?,
            },
            Op::Halt => return vm.pop(),
        }
    }
}

#[inline(never)]
fn enc(r: Result<Val, VmErr>) -> i64 {
    match r {
        Ok(Val::I(x)) => x,
        Ok(Val::F(f)) => 0x7000_0000_0000_0000 | f as i64,
        Err(VmErr::Underflow) => -1,
        Err(VmErr::Overflow) => -2,
        Err(VmErr::DivZero) => -3,
        Err(VmErr::Type(k)) => -100 - k as i64,
        Err(VmErr::Steps) => -5,
        Err(VmErr::Pc(p)) => -1000 - p as i64,
    }
}

// sum 1..=n via loop: r0 = n, r1 = acc
#[no_mangle]
pub extern "C" fn vm_sum(n: i64) -> i64 {
    let n = n % 50;
    let prog = [
        Op::Push(0),
        Op::Store(1),
        // loop at 2
        Op::Load(0),
        Op::Jz(12),
        Op::Load(1),
        Op::Load(0),
        Op::Add,
        Op::Store(1),
        Op::Load(0),
        Op::Push(1),
        Op::Sub,
        Op::Store(0),
        Op::Jmp(2),
    ];
    let mut p2 = [Op::Halt; 16];
    p2[..13].copy_from_slice(&prog);
    p2[12] = Op::Jmp(2);
    p2[3] = Op::Jz(13);
    p2[13] = Op::Load(1);
    p2[14] = Op::Halt;
    enc(run(&p2, n))
}

#[no_mangle]
pub extern "C" fn vm_arith(a: i64, b: i64) -> i64 {
    let prog = [
        Op::Push(a),
        Op::Push(b),
        Op::Over,
        Op::Over,
        Op::Div,
        Op::Swap,
        Op::Drop,
        Op::Swap,
        Op::Push(7),
        Op::Rem,
        Op::Add,
        Op::Shl((a & 63) as u8),
        Op::Halt,
    ];
    enc(run(&prog, 0))
}

#[no_mangle]
pub extern "C" fn vm_float(a: i32, b: i32) -> i64 {
    let prog = [
        Op::Push(a as i64),
        Op::ToF,
        Op::PushF(b as f32 * 0.25),
        Op::FAdd,
        Op::Push(3),
        Op::FAdd,
        Op::Dup,
        Op::FAdd,
        if a & 1 == 0 { Op::FToI } else { Op::Dup },
        Op::Halt,
    ];
    enc(run(&prog, 0))
}

#[no_mangle]
pub extern "C" fn vm_fuzz(seed: u32, len: u32) -> i64 {
    let mut prog = [Op::Halt; 24];
    let mut s = seed | 1;
    let len = (len % 24) as usize;
    for i in 0..len {
        s ^= s << 13;
        s ^= s >> 17;
        s ^= s << 5;
        prog[i] = match s % 22 {
            0 => Op::Push((s >> 8) as i64 - 1000),
            1 => Op::PushF((s >> 12) as f32 / 3.0),
            2 => Op::Add,
            3 => Op::Sub,
            4 => Op::Mul,
            5 => Op::Div,
            6 => Op::Rem,
            7 => Op::Dup,
            8 => Op::Swap,
            9 => Op::Over,
            10 => Op::Drop,
            11 => Op::Neg,
            12 => Op::Jz(((s >> 5) % 24) as u8),
            13 => Op::Jmp(((s >> 5) % 30) as u8),
            14 => Op::Lt,
            15 => Op::Shl((s >> 20) as u8),
            16 => Op::Load((s >> 3) as u8),
            17 => Op::Store((s >> 3) as u8),
            18 => Op::ToF,
            19 => Op::FAdd,
            20 => Op::FToI,
            _ => Op::Push(s as i64),
        };
    }
    enc(run(&prog, seed as i64))
}

#[no_mangle]
pub extern "C" fn op_size() -> u32 {
    (core::mem::size_of::<Op>() * 100
        + core::mem::size_of::<Val>() * 10
        + core::mem::size_of::<Result<Val, VmErr>>()) as u32
}
