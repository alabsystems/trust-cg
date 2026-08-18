// trust-cg-codegen/src/interpreter.rs - trust_ir direct interpreter for golden truth validation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// This module provides a direct interpreter for trust_ir programs. It evaluates
// trust_ir instructions without any codegen, lowering, or optimization — serving
// as a golden truth oracle for differential testing against compiled binaries.
//
// If the interpreter and the compiled binary produce the same result for a
// given trust_ir program, we have strong evidence the compiler is correct.
//
// Reference: CompCert's reference interpreter (Cminor → Clight semantics)

use std::collections::HashMap;

use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, Constant, FuncId, Function as TrustIrFunction, ICmpOp,
    Inst, Module as TrustIrModule, Ty, UnOp, ValueId,
};

// ---------------------------------------------------------------------------
// Interpreter value
// ---------------------------------------------------------------------------

/// Runtime value in the interpreter.
///
/// All integer types are widened to i128 for uniform handling. This avoids
/// sign-extension and truncation bugs while preserving exact semantics for
/// all bit-widths (i8..i128). Float types are stored as f64.
#[derive(Debug, Clone)]
pub enum InterpreterValue {
    /// Integer value (covers i8, i16, i32, i64, i128).
    Int(i128),
    /// Floating-point value (covers f32 and f64).
    Float(f64),
    /// Boolean value.
    Bool(bool),
    /// Undefined value (from Undef instruction).
    Undef,
}

impl InterpreterValue {
    /// Extract as i128, or error.
    pub fn as_int(&self) -> Result<i128, InterpreterError> {
        match self {
            InterpreterValue::Int(v) => Ok(*v),
            InterpreterValue::Bool(b) => Ok(if *b { 1 } else { 0 }),
            _ => Err(InterpreterError::TypeMismatch(format!(
                "expected Int, got {:?}",
                self
            ))),
        }
    }

    /// Extract as f64, or error.
    pub fn as_float(&self) -> Result<f64, InterpreterError> {
        match self {
            InterpreterValue::Float(v) => Ok(*v),
            _ => Err(InterpreterError::TypeMismatch(format!(
                "expected Float, got {:?}",
                self
            ))),
        }
    }

    /// Extract as bool, or error.
    pub fn as_bool(&self) -> Result<bool, InterpreterError> {
        match self {
            InterpreterValue::Bool(b) => Ok(*b),
            InterpreterValue::Int(v) => Ok(*v != 0),
            _ => Err(InterpreterError::TypeMismatch(format!(
                "expected Bool, got {:?}",
                self
            ))),
        }
    }
}

fn int_mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

fn unsigned_bits(value: i128, width: u32) -> u128 {
    (value as u128) & int_mask(width)
}

fn normalize_signed(value: i128, width: u32) -> i128 {
    let bits = unsigned_bits(value, width);
    if width == 0 || width >= 128 {
        bits as i128
    } else {
        let sign_bit = 1u128 << (width - 1);
        if bits & sign_bit != 0 {
            (bits | !int_mask(width)) as i128
        } else {
            bits as i128
        }
    }
}

fn normalize_unsigned(bits: u128, ty: &Ty, width: u32) -> i128 {
    let masked = bits & int_mask(width);
    if ty.is_signed() {
        normalize_signed(masked as i128, width)
    } else {
        masked as i128
    }
}

fn normalize_int(value: i128, ty: &Ty, width: u32) -> i128 {
    normalize_unsigned(value as u128, ty, width)
}

fn shift_amount(value: i128, width: u32) -> u32 {
    let width = width.max(1);
    (value as u128 % u128::from(width)) as u32
}

/// Trust-IR `FMin` semantics: return the non-NaN operand when exactly one
/// operand is NaN, independent of the host Rust/LLVM lowering of `f64::min`.
/// The signed-zero rule follows IEEE 754-2019 `minimum`
/// (`minimum(-0.0, +0.0) = -0.0`) EXPLICITLY: `f64::min` lowers to LLVM
/// `minnum`, which treats `-0.0` and `+0.0` as equal with an UNSPECIFIED
/// (platform/optimization-dependent) result, so delegating the zero case to it
/// is non-deterministic. Pick the correctly-signed zero by sign bit instead.
fn minimum_number_f64(lhs: f64, rhs: f64) -> f64 {
    if lhs.is_nan() {
        if rhs.is_nan() {
            quiet_nan_f64(lhs)
        } else {
            rhs
        }
    } else if rhs.is_nan() {
        lhs
    } else if lhs == 0.0 && rhs == 0.0 {
        // Both are ±0.0 (equal under `==`). `minimum` returns -0.0 if either
        // operand is -0.0, else +0.0.
        if lhs.is_sign_negative() || rhs.is_sign_negative() {
            -0.0
        } else {
            0.0
        }
    } else {
        lhs.min(rhs)
    }
}

/// Trust-IR `FMax` counterpart to [`minimum_number_f64`]
/// (`maximum(-0.0, +0.0) = +0.0`; same non-determinism caveat for `f64::max`).
fn maximum_number_f64(lhs: f64, rhs: f64) -> f64 {
    if lhs.is_nan() {
        if rhs.is_nan() {
            quiet_nan_f64(lhs)
        } else {
            rhs
        }
    } else if rhs.is_nan() {
        lhs
    } else if lhs == 0.0 && rhs == 0.0 {
        // Both are ±0.0. `maximum` returns +0.0 if either operand is +0.0,
        // else -0.0.
        if lhs.is_sign_positive() || rhs.is_sign_positive() {
            0.0
        } else {
            -0.0
        }
    } else {
        lhs.max(rhs)
    }
}

fn quiet_nan_f64(value: f64) -> f64 {
    debug_assert!(value.is_nan());
    f64::from_bits(value.to_bits() | 0x0008_0000_0000_0000)
}

/// Inclusive signed bounds `[min, max]` for a `width`-bit two's-complement
/// integer, matching the reference `trust_ir` interpreter.
fn signed_bounds(width: u32) -> (i128, i128) {
    if width == 0 {
        return (0, 0);
    }
    if width >= 128 {
        return (i128::MIN, i128::MAX);
    }
    let sign = 1u128 << (width - 1);
    (-(sign as i128), (sign - 1) as i128)
}

/// Compute the overflow bit for a checked add/sub/mul, mirroring the reference
/// `trust_ir` interpreter (and therefore Rust's `checked_*`/`overflowing_*`
/// semantics) for both signed and unsigned `width`-bit integers.
///
/// Signedness is taken from the IR type: `I8..=I128` are signed, `U8..=U128`
/// are unsigned.
fn eval_overflow_flag(op: trust_ir::OverflowOp, ty: &Ty, width: u32, lhs: i128, rhs: i128) -> bool {
    use trust_ir::OverflowOp;
    if ty.is_signed() {
        let (min, max) = signed_bounds(width);
        let lhs = normalize_signed(lhs, width);
        let rhs = normalize_signed(rhs, width);
        let checked = match op {
            OverflowOp::AddOverflow => lhs.checked_add(rhs),
            OverflowOp::SubOverflow => lhs.checked_sub(rhs),
            OverflowOp::MulOverflow => lhs.checked_mul(rhs),
        };
        !matches!(checked, Some(value) if value >= min && value <= max)
    } else {
        let mask = int_mask(width);
        let lhs = unsigned_bits(lhs, width);
        let rhs = unsigned_bits(rhs, width);
        match op {
            OverflowOp::AddOverflow => {
                let (sum, overflow) = lhs.overflowing_add(rhs);
                overflow || sum > mask
            }
            OverflowOp::SubOverflow => lhs < rhs,
            OverflowOp::MulOverflow => {
                let (product, overflow) = lhs.overflowing_mul(rhs);
                overflow || product > mask || (rhs != 0 && lhs > mask / rhs)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors that can occur during interpretation.
#[derive(Debug, Clone)]
pub enum InterpreterError {
    /// Function not found in module.
    FunctionNotFound(String),
    /// Block not found in function.
    BlockNotFound(BlockId),
    /// Value not found in register file.
    ValueNotFound(ValueId),
    /// Type mismatch during operation.
    TypeMismatch(String),
    /// Division by zero.
    DivisionByZero,
    /// Fuel exhausted (step limit reached).
    FuelExhausted(u64),
    /// Unsupported instruction.
    Unsupported(String),
    /// Assertion failed.
    AssertionFailed,
    /// Argument count mismatch.
    ArityMismatch { expected: usize, got: usize },
    /// Call stack depth exceeded.
    StackOverflow(usize),
}

impl std::fmt::Display for InterpreterError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::FunctionNotFound(name) => write!(f, "function not found: {}", name),
            Self::BlockNotFound(id) => write!(f, "block not found: {:?}", id),
            Self::ValueNotFound(id) => write!(f, "value not found: {:?}", id),
            Self::TypeMismatch(msg) => write!(f, "type mismatch: {}", msg),
            Self::DivisionByZero => write!(f, "division by zero"),
            Self::FuelExhausted(limit) => write!(f, "fuel exhausted after {} steps", limit),
            Self::Unsupported(msg) => write!(f, "unsupported: {}", msg),
            Self::AssertionFailed => write!(f, "assertion failed"),
            Self::ArityMismatch { expected, got } => {
                write!(f, "arity mismatch: expected {} args, got {}", expected, got)
            }
            Self::StackOverflow(depth) => write!(f, "stack overflow at depth {}", depth),
        }
    }
}

impl std::error::Error for InterpreterError {}

// ---------------------------------------------------------------------------
// Interpreter
// ---------------------------------------------------------------------------

/// Configuration for the interpreter.
pub struct InterpreterConfig {
    /// Maximum number of instructions to execute before aborting.
    pub fuel: u64,
    /// Maximum call stack depth.
    pub max_call_depth: usize,
}

impl Default for InterpreterConfig {
    fn default() -> Self {
        Self {
            fuel: 1_000_000,
            max_call_depth: 256,
        }
    }
}

/// trust_ir direct interpreter.
///
/// Evaluates trust_ir programs instruction-by-instruction without any compilation.
/// This is intentionally simple and unoptimized — correctness over speed.
struct Interpreter<'m> {
    module: &'m TrustIrModule,
    config: InterpreterConfig,
    steps: u64,
    call_depth: usize,
}

impl<'m> Interpreter<'m> {
    fn new(module: &'m TrustIrModule, config: InterpreterConfig) -> Self {
        Self {
            module,
            config,
            steps: 0,
            call_depth: 0,
        }
    }

    /// Execute a function by FuncId with the given arguments.
    fn call_func(
        &mut self,
        func_id: FuncId,
        args: &[InterpreterValue],
    ) -> Result<Vec<InterpreterValue>, InterpreterError> {
        let func = self
            .module
            .functions
            .iter()
            .find(|f| f.id == func_id)
            .ok_or_else(|| {
                InterpreterError::FunctionNotFound(format!("FuncId({})", func_id.index()))
            })?;

        self.execute_function(func, args)
    }

    /// Execute a function with the given arguments.
    fn execute_function(
        &mut self,
        func: &TrustIrFunction,
        args: &[InterpreterValue],
    ) -> Result<Vec<InterpreterValue>, InterpreterError> {
        if self.call_depth >= self.config.max_call_depth {
            return Err(InterpreterError::StackOverflow(self.call_depth));
        }
        self.call_depth += 1;

        // Find entry block.
        let entry_block = self.find_block(func, func.entry)?;

        // Validate argument count matches entry block params.
        if args.len() != entry_block.params.len() {
            self.call_depth -= 1;
            return Err(InterpreterError::ArityMismatch {
                expected: entry_block.params.len(),
                got: args.len(),
            });
        }

        // Initialize register file: bind args to entry block params.
        let mut regs: HashMap<ValueId, InterpreterValue> = HashMap::new();
        for (i, (vid, _ty)) in entry_block.params.iter().enumerate() {
            regs.insert(*vid, args[i].clone());
        }

        // Execute starting from entry block.
        let result = self.execute_block(func, func.entry, &mut regs);
        self.call_depth -= 1;
        result
    }

    /// Execute instructions in a block, following control flow until Return.
    fn execute_block(
        &mut self,
        func: &TrustIrFunction,
        mut block_id: BlockId,
        regs: &mut HashMap<ValueId, InterpreterValue>,
    ) -> Result<Vec<InterpreterValue>, InterpreterError> {
        loop {
            let block = self.find_block(func, block_id)?;

            for node in &block.body {
                self.steps += 1;
                if self.steps > self.config.fuel {
                    return Err(InterpreterError::FuelExhausted(self.config.fuel));
                }

                match &node.inst {
                    // --- Constants ---
                    Inst::Const { ty: _, value } => {
                        let result_vid = node.results[0];
                        let val = self.eval_constant(value);
                        regs.insert(result_vid, val);
                    }

                    // --- Binary operations ---
                    Inst::BinOp { op, ty, lhs, rhs } => {
                        let result_vid = node.results[0];
                        let lhs_val = self.get_reg(regs, *lhs)?;
                        let rhs_val = self.get_reg(regs, *rhs)?;
                        let result = self.eval_binop(*op, ty, &lhs_val, &rhs_val)?;
                        regs.insert(result_vid, result);
                    }

                    // --- Unary operations ---
                    Inst::UnOp { op, ty, operand } => {
                        let result_vid = node.results[0];
                        let src = self.get_reg(regs, *operand)?;
                        let result = self.eval_unop(*op, ty, &src)?;
                        regs.insert(result_vid, result);
                    }

                    // --- Integer comparisons ---
                    Inst::ICmp {
                        op,
                        ty: _,
                        lhs,
                        rhs,
                    } => {
                        let result_vid = node.results[0];
                        let lhs_val = self.get_reg(regs, *lhs)?.as_int()?;
                        let rhs_val = self.get_reg(regs, *rhs)?.as_int()?;
                        let result = self.eval_icmp(*op, lhs_val, rhs_val);
                        regs.insert(result_vid, InterpreterValue::Bool(result));
                    }

                    // --- Float comparisons ---
                    Inst::FCmp {
                        op,
                        ty: _,
                        lhs,
                        rhs,
                    } => {
                        let result_vid = node.results[0];
                        let lhs_val = self.get_reg(regs, *lhs)?.as_float()?;
                        let rhs_val = self.get_reg(regs, *rhs)?.as_float()?;
                        let result = self.eval_fcmp(*op, lhs_val, rhs_val);
                        regs.insert(result_vid, InterpreterValue::Bool(result));
                    }

                    // --- Overflow ops (result + overflow flag) ---
                    Inst::Overflow { op, ty, lhs, rhs } => {
                        let width = ty.bit_width().unwrap_or(128);
                        let lhs_val = self.get_reg(regs, *lhs)?.as_int()?;
                        let rhs_val = self.get_reg(regs, *rhs)?.as_int()?;
                        let wrapped = match op {
                            trust_ir::OverflowOp::AddOverflow => lhs_val.wrapping_add(rhs_val),
                            trust_ir::OverflowOp::SubOverflow => lhs_val.wrapping_sub(rhs_val),
                            trust_ir::OverflowOp::MulOverflow => lhs_val.wrapping_mul(rhs_val),
                        };
                        // The truncated, width-correct result of the checked op.
                        let result = normalize_int(wrapped, ty, width);
                        let overflow = eval_overflow_flag(*op, ty, width, lhs_val, rhs_val);
                        if !node.results.is_empty() {
                            regs.insert(node.results[0], InterpreterValue::Int(result));
                        }
                        if node.results.len() > 1 {
                            regs.insert(node.results[1], InterpreterValue::Bool(overflow));
                        }
                    }

                    // --- Select ---
                    Inst::Select {
                        ty: _,
                        cond,
                        then_val,
                        else_val,
                    } => {
                        let result_vid = node.results[0];
                        let cond_val = self.get_reg(regs, *cond)?.as_bool()?;
                        let result = if cond_val {
                            self.get_reg(regs, *then_val)?
                        } else {
                            self.get_reg(regs, *else_val)?
                        };
                        regs.insert(result_vid, result);
                    }

                    // --- Copy ---
                    Inst::Copy { ty: _, operand } => {
                        let result_vid = node.results[0];
                        let val = self.get_reg(regs, *operand)?;
                        regs.insert(result_vid, val);
                    }

                    // --- Cast (simplified) ---
                    Inst::Cast {
                        op,
                        src_ty: _,
                        dst_ty: _,
                        operand,
                    } => {
                        let result_vid = node.results[0];
                        let src = self.get_reg(regs, *operand)?;
                        let result = self.eval_cast(*op, &src)?;
                        regs.insert(result_vid, result);
                    }

                    // --- NullPtr ---
                    Inst::NullPtr => {
                        let result_vid = node.results[0];
                        regs.insert(result_vid, InterpreterValue::Int(0));
                    }

                    // --- Undef ---
                    Inst::Undef { .. } => {
                        let result_vid = node.results[0];
                        regs.insert(result_vid, InterpreterValue::Undef);
                    }

                    // --- Assume/Assert ---
                    Inst::Assume { .. } => {}
                    Inst::Assert { cond } => {
                        if !self.get_reg(regs, *cond)?.as_bool()? {
                            return Err(InterpreterError::AssertionFailed);
                        }
                    }

                    // --- Unconditional branch ---
                    Inst::Br { target, args } => {
                        let arg_vals: Vec<InterpreterValue> = args
                            .iter()
                            .map(|vid| self.get_reg(regs, *vid))
                            .collect::<Result<Vec<_>, _>>()?;

                        // Bind args to target block params.
                        let target_block = self.find_block(func, *target)?;
                        for (i, (vid, _ty)) in target_block.params.iter().enumerate() {
                            regs.insert(*vid, arg_vals[i].clone());
                        }

                        block_id = *target;
                        break; // Restart from new block
                    }

                    // --- Conditional branch ---
                    Inst::CondBr {
                        cond,
                        then_target,
                        then_args,
                        else_target,
                        else_args,
                    } => {
                        let cond_val = self.get_reg(regs, *cond)?.as_bool()?;
                        let (target, branch_args) = if cond_val {
                            (*then_target, then_args)
                        } else {
                            (*else_target, else_args)
                        };

                        let arg_vals: Vec<InterpreterValue> = branch_args
                            .iter()
                            .map(|vid| self.get_reg(regs, *vid))
                            .collect::<Result<Vec<_>, _>>()?;

                        let target_block = self.find_block(func, target)?;
                        for (i, (vid, _ty)) in target_block.params.iter().enumerate() {
                            regs.insert(*vid, arg_vals[i].clone());
                        }

                        block_id = target;
                        break; // Restart from new block
                    }

                    // --- Switch ---
                    Inst::Switch {
                        value,
                        default,
                        default_args,
                        cases,
                        ..
                    } => {
                        let selector = self.get_reg(regs, *value)?.as_int()?;

                        // Find matching case.
                        let mut matched_target = *default;
                        let mut matched_args: &Vec<ValueId> = default_args;

                        for case in cases {
                            let case_val = match &case.value {
                                Constant::Int(v) => *v,
                                Constant::Bool(b) => {
                                    if *b {
                                        1
                                    } else {
                                        0
                                    }
                                }
                                _ => continue,
                            };
                            if selector == case_val {
                                matched_target = case.target;
                                matched_args = &case.args;
                                break;
                            }
                        }

                        let arg_vals: Vec<InterpreterValue> = matched_args
                            .iter()
                            .map(|vid| self.get_reg(regs, *vid))
                            .collect::<Result<Vec<_>, _>>()?;

                        let target_block = self.find_block(func, matched_target)?;
                        for (i, (vid, _ty)) in target_block.params.iter().enumerate() {
                            regs.insert(*vid, arg_vals[i].clone());
                        }

                        block_id = matched_target;
                        break;
                    }

                    // --- Return ---
                    Inst::Return { values } => {
                        let result: Vec<InterpreterValue> = values
                            .iter()
                            .map(|vid| self.get_reg(regs, *vid))
                            .collect::<Result<Vec<_>, _>>()?;
                        return Ok(result);
                    }

                    // --- Call ---
                    Inst::Call { callee, args } => {
                        let arg_vals: Vec<InterpreterValue> = args
                            .iter()
                            .map(|vid| self.get_reg(regs, *vid))
                            .collect::<Result<Vec<_>, _>>()?;

                        let results = self.call_func(*callee, &arg_vals)?;

                        // Bind results.
                        for (i, vid) in node.results.iter().enumerate() {
                            if i < results.len() {
                                regs.insert(*vid, results[i].clone());
                            }
                        }
                    }

                    // --- Unreachable ---
                    Inst::Unreachable => {
                        return Err(InterpreterError::Unsupported(
                            "reached unreachable instruction".to_string(),
                        ));
                    }

                    // --- Unsupported (memory, atomics, aggregates, etc.) ---
                    other => {
                        return Err(InterpreterError::Unsupported(format!("{:?}", other)));
                    }
                }
            }
            // If we reach end of block body without a terminator, something is wrong.
            // But the loop will continue to the next block_id iteration.
        }
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    fn find_block<'f>(
        &self,
        func: &'f TrustIrFunction,
        block_id: BlockId,
    ) -> Result<&'f TrustIrBlock, InterpreterError> {
        func.blocks
            .iter()
            .find(|b| b.id == block_id)
            .ok_or(InterpreterError::BlockNotFound(block_id))
    }

    fn get_reg(
        &self,
        regs: &HashMap<ValueId, InterpreterValue>,
        vid: ValueId,
    ) -> Result<InterpreterValue, InterpreterError> {
        regs.get(&vid)
            .cloned()
            .ok_or(InterpreterError::ValueNotFound(vid))
    }

    fn eval_constant(&self, c: &Constant) -> InterpreterValue {
        match c {
            Constant::Int(v) => InterpreterValue::Int(*v),
            Constant::Float(v) => InterpreterValue::Float(*v),
            Constant::Bool(b) => InterpreterValue::Bool(*b),
            Constant::Aggregate(_) | Constant::Array(_) | Constant::Vector(_) => {
                // Simplified aggregate/vector interpreter model.
                InterpreterValue::Undef
            }
            // trust_ir#30 aggregate/closure constants — this simplified
            // interpreter does not model set/sequence/record/closure runtime
            // representations yet. Its value model is also only i128-shaped,
            // so it cannot represent canonical U128 or Bytes constants. The
            // production lowering supports those constants; differential tests
            // that exercise them therefore need a different oracle.
            Constant::U128(_)
            | Constant::Bytes { .. }
            | Constant::Sequence(_)
            | Constant::Set(_)
            | Constant::Record(_)
            | Constant::Closure { .. }
            | Constant::FnDef(_)
            // A symbol address is only known at link time; the interpreter
            // cannot model it, so it is `Undef` here (the data-relocation path
            // is exercised by link+run differential testing instead).
            | Constant::SymbolAddr { .. }
            | Constant::PhantomData => InterpreterValue::Undef,
        }
    }

    fn eval_binop(
        &self,
        op: BinOp,
        ty: &Ty,
        lhs: &InterpreterValue,
        rhs: &InterpreterValue,
    ) -> Result<InterpreterValue, InterpreterError> {
        let int_width = ty.bit_width().unwrap_or(128);
        match op {
            // Integer arithmetic
            BinOp::Add => {
                let a = lhs.as_int()?;
                let b = rhs.as_int()?;
                Ok(InterpreterValue::Int(normalize_int(
                    a.wrapping_add(b),
                    ty,
                    int_width,
                )))
            }
            BinOp::Sub => {
                let a = lhs.as_int()?;
                let b = rhs.as_int()?;
                Ok(InterpreterValue::Int(normalize_int(
                    a.wrapping_sub(b),
                    ty,
                    int_width,
                )))
            }
            BinOp::Mul => {
                let a = lhs.as_int()?;
                let b = rhs.as_int()?;
                Ok(InterpreterValue::Int(normalize_int(
                    a.wrapping_mul(b),
                    ty,
                    int_width,
                )))
            }
            BinOp::UDiv => {
                let a = unsigned_bits(lhs.as_int()?, int_width);
                let b = unsigned_bits(rhs.as_int()?, int_width);
                if b == 0 {
                    return Err(InterpreterError::DivisionByZero);
                }
                Ok(InterpreterValue::Int(normalize_unsigned(
                    a / b,
                    ty,
                    int_width,
                )))
            }
            BinOp::SDiv => {
                let a = normalize_signed(lhs.as_int()?, int_width);
                let b = normalize_signed(rhs.as_int()?, int_width);
                if b == 0 {
                    return Err(InterpreterError::DivisionByZero);
                }
                Ok(InterpreterValue::Int(normalize_int(
                    a.wrapping_div(b),
                    ty,
                    int_width,
                )))
            }
            BinOp::URem => {
                let a = unsigned_bits(lhs.as_int()?, int_width);
                let b = unsigned_bits(rhs.as_int()?, int_width);
                if b == 0 {
                    return Err(InterpreterError::DivisionByZero);
                }
                Ok(InterpreterValue::Int(normalize_unsigned(
                    a % b,
                    ty,
                    int_width,
                )))
            }
            BinOp::SRem => {
                let a = normalize_signed(lhs.as_int()?, int_width);
                let b = normalize_signed(rhs.as_int()?, int_width);
                if b == 0 {
                    return Err(InterpreterError::DivisionByZero);
                }
                Ok(InterpreterValue::Int(normalize_int(
                    a.wrapping_rem(b),
                    ty,
                    int_width,
                )))
            }

            // Floating-point arithmetic
            BinOp::FAdd => {
                let a = lhs.as_float()?;
                let b = rhs.as_float()?;
                Ok(InterpreterValue::Float(a + b))
            }
            BinOp::FSub => {
                let a = lhs.as_float()?;
                let b = rhs.as_float()?;
                Ok(InterpreterValue::Float(a - b))
            }
            BinOp::FMul => {
                let a = lhs.as_float()?;
                let b = rhs.as_float()?;
                Ok(InterpreterValue::Float(a * b))
            }
            BinOp::FDiv => {
                let a = lhs.as_float()?;
                let b = rhs.as_float()?;
                Ok(InterpreterValue::Float(a / b))
            }
            BinOp::FRem => {
                let a = lhs.as_float()?;
                let b = rhs.as_float()?;
                Ok(InterpreterValue::Float(a % b))
            }
            // IEEE minimumNumber/maximumNumber semantics (NaN-propagating-away),
            // implemented explicitly so the trust-ir result does not depend on
            // the host rustc/LLVM handling of signaling NaNs.
            BinOp::FMin => {
                let a = lhs.as_float()?;
                let b = rhs.as_float()?;
                Ok(InterpreterValue::Float(minimum_number_f64(a, b)))
            }
            BinOp::FMax => {
                let a = lhs.as_float()?;
                let b = rhs.as_float()?;
                Ok(InterpreterValue::Float(maximum_number_f64(a, b)))
            }

            // Bitwise / shift operations
            BinOp::And => {
                let a = lhs.as_int()?;
                let b = rhs.as_int()?;
                Ok(InterpreterValue::Int(normalize_int(a & b, ty, int_width)))
            }
            BinOp::Or => {
                let a = lhs.as_int()?;
                let b = rhs.as_int()?;
                Ok(InterpreterValue::Int(normalize_int(a | b, ty, int_width)))
            }
            BinOp::Xor => {
                let a = lhs.as_int()?;
                let b = rhs.as_int()?;
                Ok(InterpreterValue::Int(normalize_int(a ^ b, ty, int_width)))
            }
            // Trust: the BOOLEAN connectives (trust-ir 4b06918). Evaluated as the
            // LOGICAL ops on the 0/1 carrier -- any nonzero operand counts as true --
            // which is byte-for-byte what `trust_ir::interpret`'s own `BAnd`/`BOr`/
            // `BXor` arms and `semIntBinOp` in the Lean semantics compute. Written as
            // `!= 0` rather than `== 1` for exactly that reason: it must stay total on
            // operands outside {0,1}, or the two interpreters would disagree about the
            // same program on inputs neither rejects.
            BinOp::BAnd => {
                let a = lhs.as_int()?;
                let b = rhs.as_int()?;
                Ok(InterpreterValue::Int(i128::from(a != 0 && b != 0)))
            }
            BinOp::BOr => {
                let a = lhs.as_int()?;
                let b = rhs.as_int()?;
                Ok(InterpreterValue::Int(i128::from(a != 0 || b != 0)))
            }
            BinOp::BXor => {
                let a = lhs.as_int()?;
                let b = rhs.as_int()?;
                Ok(InterpreterValue::Int(i128::from((a != 0) != (b != 0))))
            }
            BinOp::Shl => {
                let a = unsigned_bits(lhs.as_int()?, int_width);
                let b = shift_amount(rhs.as_int()?, int_width);
                Ok(InterpreterValue::Int(normalize_unsigned(
                    a.wrapping_shl(b),
                    ty,
                    int_width,
                )))
            }
            BinOp::LShr => {
                let a = unsigned_bits(lhs.as_int()?, int_width);
                let b = shift_amount(rhs.as_int()?, int_width);
                Ok(InterpreterValue::Int(normalize_unsigned(
                    a >> b,
                    ty,
                    int_width,
                )))
            }
            BinOp::AShr => {
                let a = normalize_signed(lhs.as_int()?, int_width);
                let b = shift_amount(rhs.as_int()?, int_width);
                Ok(InterpreterValue::Int(normalize_int(a >> b, ty, int_width)))
            }
        }
    }

    fn eval_unop(
        &self,
        op: UnOp,
        ty: &Ty,
        src: &InterpreterValue,
    ) -> Result<InterpreterValue, InterpreterError> {
        match op {
            UnOp::Neg => {
                let v = src.as_int()?;
                Ok(InterpreterValue::Int(v.wrapping_neg()))
            }
            UnOp::FNeg => {
                let v = src.as_float()?;
                Ok(InterpreterValue::Float(-v))
            }
            UnOp::FAbs => {
                let v = src.as_float()?;
                Ok(InterpreterValue::Float(v.abs()))
            }
            UnOp::FSqrt => {
                let v = src.as_float()?;
                Ok(InterpreterValue::Float(v.sqrt()))
            }
            UnOp::FFloor => {
                let v = src.as_float()?;
                Ok(InterpreterValue::Float(v.floor()))
            }
            UnOp::FCeil => {
                let v = src.as_float()?;
                Ok(InterpreterValue::Float(v.ceil()))
            }
            UnOp::FTrunc => {
                let v = src.as_float()?;
                Ok(InterpreterValue::Float(v.trunc()))
            }
            UnOp::Not => {
                let v = src.as_int()?;
                Ok(InterpreterValue::Int(!v))
            }
            UnOp::CtPop => {
                let width = ty.bit_width().unwrap_or(128);
                let v = unsigned_bits(src.as_int()?, width);
                Ok(InterpreterValue::Int(v.count_ones() as i128))
            }
        }
    }

    fn eval_icmp(&self, op: ICmpOp, lhs: i128, rhs: i128) -> bool {
        match op {
            ICmpOp::Eq => lhs == rhs,
            ICmpOp::Ne => lhs != rhs,
            ICmpOp::Slt => lhs < rhs,
            ICmpOp::Sle => lhs <= rhs,
            ICmpOp::Sgt => lhs > rhs,
            ICmpOp::Sge => lhs >= rhs,
            ICmpOp::Ult => (lhs as u128) < (rhs as u128),
            ICmpOp::Ule => (lhs as u128) <= (rhs as u128),
            ICmpOp::Ugt => (lhs as u128) > (rhs as u128),
            ICmpOp::Uge => (lhs as u128) >= (rhs as u128),
        }
    }

    fn eval_fcmp(&self, op: trust_ir::FCmpOp, lhs: f64, rhs: f64) -> bool {
        use trust_ir::FCmpOp;
        match op {
            // Ordered comparisons (false when NaN)
            FCmpOp::OEq => lhs == rhs,
            // Ordered not-equal: both operands must be non-NaN. Rust's `!=`
            // returns `true` when either operand is NaN, which would violate the
            // ordered predicate contract, so guard against NaN explicitly.
            FCmpOp::ONe => !lhs.is_nan() && !rhs.is_nan() && lhs != rhs,
            FCmpOp::OLt => lhs < rhs,
            FCmpOp::OLe => lhs <= rhs,
            FCmpOp::OGt => lhs > rhs,
            FCmpOp::OGe => lhs >= rhs,
            // Unordered comparisons (true when NaN)
            FCmpOp::UEq => lhs == rhs || lhs.is_nan() || rhs.is_nan(),
            FCmpOp::UNe => lhs != rhs || lhs.is_nan() || rhs.is_nan(),
            FCmpOp::ULt => lhs < rhs || lhs.is_nan() || rhs.is_nan(),
            FCmpOp::ULe => lhs <= rhs || lhs.is_nan() || rhs.is_nan(),
            FCmpOp::UGt => lhs > rhs || lhs.is_nan() || rhs.is_nan(),
            FCmpOp::UGe => lhs >= rhs || lhs.is_nan() || rhs.is_nan(),
        }
    }

    fn eval_cast(
        &self,
        op: trust_ir::CastOp,
        src: &InterpreterValue,
    ) -> Result<InterpreterValue, InterpreterError> {
        use trust_ir::CastOp;
        match op {
            CastOp::ZExt | CastOp::SExt | CastOp::Trunc => {
                // For the interpreter, all ints are i128, so extension/truncation
                // is a no-op at this level. Real semantics depend on bit-width,
                // but for golden truth testing of typical programs this suffices.
                Ok(InterpreterValue::Int(src.as_int()?))
            }
            // Host-Rust `as` on floats IS the saturating conversion (NaN -> 0,
            // clamp) — EXACT semantics for the Sat variants, and a sound
            // refinement for the raw FPToSI/FPToUI (whose out-of-range/NaN is
            // UB per trust-ir: any defined result refines UB).
            CastOp::FPToSI | CastOp::FPToSISat => {
                Ok(InterpreterValue::Int(src.as_float()? as i128))
            }
            CastOp::FPToUI | CastOp::FPToUISat => {
                Ok(InterpreterValue::Int(src.as_float()? as u128 as i128))
            }
            CastOp::SIToFP => Ok(InterpreterValue::Float(src.as_int()? as f64)),
            CastOp::UIToFP => Ok(InterpreterValue::Float(src.as_int()? as u128 as f64)),
            CastOp::FPExt | CastOp::FPTrunc => Ok(InterpreterValue::Float(src.as_float()?)),
            CastOp::Bitcast | CastOp::PtrToInt | CastOp::IntToPtr | CastOp::PtrToPtr => {
                // Pass through — simplified for integer-focused testing.
                match src {
                    InterpreterValue::Int(v) => Ok(InterpreterValue::Int(*v)),
                    InterpreterValue::Float(v) => Ok(InterpreterValue::Float(*v)),
                    other => Ok(other.clone()),
                }
            }
            CastOp::Transmute | CastOp::ReifyFnPointer => Err(InterpreterError::Unsupported(
                format!("cast op {:?} not supported by interpreter", op),
            )),
        }
    }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Interpret a trust_ir function by name with the given arguments.
///
/// This is the primary entry point for golden truth validation.
///
/// # Example
/// ```text
/// let module = build_some_trust_ir_module();
/// let result = interpret(&module, "add", &[InterpreterValue::Int(3), InterpreterValue::Int(5)]);
/// assert_eq!(result.unwrap()[0].as_int().unwrap(), 8);
/// ```
pub fn interpret(
    module: &TrustIrModule,
    func_name: &str,
    args: &[InterpreterValue],
) -> Result<Vec<InterpreterValue>, InterpreterError> {
    interpret_with_config(module, func_name, args, InterpreterConfig::default())
}

/// Interpret a trust_ir function with custom configuration.
pub fn interpret_with_config(
    module: &TrustIrModule,
    func_name: &str,
    args: &[InterpreterValue],
    config: InterpreterConfig,
) -> Result<Vec<InterpreterValue>, InterpreterError> {
    let func = module
        .functions
        .iter()
        .find(|f| f.name == func_name)
        .ok_or_else(|| InterpreterError::FunctionNotFound(func_name.to_string()))?;

    let mut interp = Interpreter::new(module, config);
    interp.execute_function(func, args)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{BinOp, Constant, ICmpOp, Module as TrustIrModule, Ty};
    use trust_ir_build::ModuleBuilder;

    /// Helper: extract single i128 result from interpreter output.
    fn result_int(results: &[InterpreterValue]) -> i128 {
        assert_eq!(results.len(), 1, "expected single return value");
        results[0].as_int().expect("expected Int result")
    }

    #[test]
    fn test_interpreter_vector_constant_is_undef_like_aggregate_constants() {
        let module = TrustIrModule::new("vector_constant");
        let interp = Interpreter::new(&module, InterpreterConfig::default());

        let value = interp.eval_constant(&Constant::Vector(vec![
            Constant::Int(-1),
            Constant::Int(0),
            Constant::Int(-1),
            Constant::Int(0),
        ]));

        assert!(matches!(value, InterpreterValue::Undef));
    }

    #[test]
    fn test_interpreter_float_minmax_nan_and_signed_zero_semantics() {
        let module = TrustIrModule::new("float_minmax_semantics");
        let interp = Interpreter::new(&module, InterpreterConfig::default());
        let eval = |op, lhs, rhs| {
            let result = interp
                .eval_binop(
                    op,
                    &Ty::F64,
                    &InterpreterValue::Float(lhs),
                    &InterpreterValue::Float(rhs),
                )
                .expect("float min/max must interpret");
            result.as_float().expect("float min/max must return Float")
        };

        let snan = f64::from_bits(0x7ff0_0000_0000_0001);
        let qnan = f64::from_bits(0x7ff8_0000_0000_0042);
        let other_qnan = f64::from_bits(0xfff8_0000_0000_0099);
        let one = 1.0f64;
        for op in [BinOp::FMin, BinOp::FMax] {
            assert_eq!(eval(op, snan, one).to_bits(), one.to_bits());
            assert_eq!(eval(op, one, snan).to_bits(), one.to_bits());
            assert_eq!(eval(op, qnan, one).to_bits(), one.to_bits());
            assert_eq!(eval(op, one, qnan).to_bits(), one.to_bits());
            assert_eq!(eval(op, qnan, other_qnan).to_bits(), qnan.to_bits());
            assert_eq!(
                eval(op, snan, other_qnan).to_bits(),
                snan.to_bits() | 0x0008_0000_0000_0000
            );
        }

        let negative_zero = (-0.0f64).to_bits();
        let positive_zero = 0.0f64.to_bits();
        assert_eq!(eval(BinOp::FMin, -0.0, 0.0).to_bits(), negative_zero);
        assert_eq!(eval(BinOp::FMin, 0.0, -0.0).to_bits(), negative_zero);
        assert_eq!(eval(BinOp::FMax, -0.0, 0.0).to_bits(), positive_zero);
        assert_eq!(eval(BinOp::FMax, 0.0, -0.0).to_bits(), positive_zero);
    }

    // -----------------------------------------------------------------------
    // Test 1: Simple addition — add(3, 5) == 8
    // -----------------------------------------------------------------------

    #[test]
    fn test_interpreter_add() {
        let mut mb = ModuleBuilder::new("test_add");
        let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("add", ty);

        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I64);
        let b = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let sum = fb.binop(BinOp::Add, Ty::I64, a, b);
        fb.ret(vec![sum]);
        fb.build();

        let module = mb.build();
        let result = interpret(
            &module,
            "add",
            &[InterpreterValue::Int(3), InterpreterValue::Int(5)],
        )
        .expect("interpret add");
        assert_eq!(result_int(&result), 8);
    }

    // -----------------------------------------------------------------------
    // Test 2: Fibonacci — fib(10) == 55 (loop with block params)
    //
    // fn fib(n: i64) -> i64 {
    //     a = 0, b = 1, i = 0
    //     while i < n { tmp = a + b; a = b; b = tmp; i += 1 }
    //     return a
    // }
    // -----------------------------------------------------------------------

    #[test]
    fn test_interpreter_fibonacci() {
        let mut mb = ModuleBuilder::new("test_fib");
        let ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("fib", ty);

        let entry = fb.create_block();
        let n = fb.add_block_param(entry, Ty::I64);

        let bb_loop = fb.create_block();
        let loop_a = fb.add_block_param(bb_loop, Ty::I64);
        let loop_b = fb.add_block_param(bb_loop, Ty::I64);
        let loop_i = fb.add_block_param(bb_loop, Ty::I64);

        let bb_body = fb.create_block();
        let bb_exit = fb.create_block();

        // entry: init a=0, b=1, i=0, jump to loop
        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::I64, 0);
        let one = fb.iconst(Ty::I64, 1);
        let i_init = fb.iconst(Ty::I64, 0);
        fb.br(bb_loop, vec![zero, one, i_init]);

        // loop header: if i < n -> body, else -> exit
        fb.switch_to_block(bb_loop);
        let cmp = fb.icmp(ICmpOp::Slt, Ty::I64, loop_i, n);
        fb.condbr(cmp, bb_body, vec![], bb_exit, vec![]);

        // body: tmp = a + b; a = b; b = tmp; i += 1; back to loop
        fb.switch_to_block(bb_body);
        let tmp = fb.binop(BinOp::Add, Ty::I64, loop_a, loop_b);
        let one2 = fb.iconst(Ty::I64, 1);
        let new_i = fb.binop(BinOp::Add, Ty::I64, loop_i, one2);
        fb.br(bb_loop, vec![loop_b, tmp, new_i]);

        // exit: return a
        fb.switch_to_block(bb_exit);
        fb.ret(vec![loop_a]);

        fb.build();
        let module = mb.build();

        let result =
            interpret(&module, "fib", &[InterpreterValue::Int(10)]).expect("interpret fib");
        assert_eq!(result_int(&result), 55);

        // Edge cases
        let r0 = interpret(&module, "fib", &[InterpreterValue::Int(0)]).unwrap();
        assert_eq!(result_int(&r0), 0);

        let r1 = interpret(&module, "fib", &[InterpreterValue::Int(1)]).unwrap();
        assert_eq!(result_int(&r1), 1);

        let r2 = interpret(&module, "fib", &[InterpreterValue::Int(2)]).unwrap();
        assert_eq!(result_int(&r2), 1);
    }

    // -----------------------------------------------------------------------
    // Test 3: GCD — gcd(12, 8) == 4 (loop with conditional)
    //
    // fn gcd(a: i64, b: i64) -> i64 {
    //     while b != 0 { tmp = b; b = a % b; a = tmp }
    //     return a
    // }
    // -----------------------------------------------------------------------

    #[test]
    fn test_interpreter_gcd() {
        let mut mb = ModuleBuilder::new("test_gcd");
        let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("gcd", ty);

        let entry = fb.create_block();
        let a_param = fb.add_block_param(entry, Ty::I64);
        let b_param = fb.add_block_param(entry, Ty::I64);

        let bb_loop = fb.create_block();
        let loop_a = fb.add_block_param(bb_loop, Ty::I64);
        let loop_b = fb.add_block_param(bb_loop, Ty::I64);

        let bb_body = fb.create_block();
        let bb_exit = fb.create_block();

        // entry: jump to loop(a, b)
        fb.switch_to_block(entry);
        fb.br(bb_loop, vec![a_param, b_param]);

        // loop header: if b != 0 -> body, else -> exit
        fb.switch_to_block(bb_loop);
        let zero = fb.iconst(Ty::I64, 0);
        let cmp = fb.icmp(ICmpOp::Ne, Ty::I64, loop_b, zero);
        fb.condbr(cmp, bb_body, vec![], bb_exit, vec![]);

        // body: new_b = a % b; a = b; back to loop(b, new_b)
        fb.switch_to_block(bb_body);
        let remainder = fb.binop(BinOp::SRem, Ty::I64, loop_a, loop_b);
        fb.br(bb_loop, vec![loop_b, remainder]);

        // exit: return a
        fb.switch_to_block(bb_exit);
        fb.ret(vec![loop_a]);

        fb.build();
        let module = mb.build();

        let result = interpret(
            &module,
            "gcd",
            &[InterpreterValue::Int(12), InterpreterValue::Int(8)],
        )
        .expect("interpret gcd");
        assert_eq!(result_int(&result), 4);

        let r2 = interpret(
            &module,
            "gcd",
            &[InterpreterValue::Int(48), InterpreterValue::Int(18)],
        )
        .unwrap();
        assert_eq!(result_int(&r2), 6);

        let r3 = interpret(
            &module,
            "gcd",
            &[InterpreterValue::Int(100), InterpreterValue::Int(75)],
        )
        .unwrap();
        assert_eq!(result_int(&r3), 25);
    }

    // -----------------------------------------------------------------------
    // Test 4: Sum to N — sum(100) == 5050
    //
    // fn sum_to(n: i64) -> i64 {
    //     sum = 0; i = 1
    //     while i <= n { sum += i; i += 1 }
    //     return sum
    // }
    // -----------------------------------------------------------------------

    #[test]
    fn test_interpreter_sum_to_n() {
        let mut mb = ModuleBuilder::new("test_sum");
        let ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("sum_to", ty);

        let entry = fb.create_block();
        let n = fb.add_block_param(entry, Ty::I64);

        let bb_loop = fb.create_block();
        let loop_sum = fb.add_block_param(bb_loop, Ty::I64);
        let loop_i = fb.add_block_param(bb_loop, Ty::I64);

        let bb_body = fb.create_block();
        let bb_exit = fb.create_block();

        // entry: sum=0, i=1, jump to loop
        fb.switch_to_block(entry);
        let sum_init = fb.iconst(Ty::I64, 0);
        let i_init = fb.iconst(Ty::I64, 1);
        fb.br(bb_loop, vec![sum_init, i_init]);

        // loop header: if i <= n -> body, else -> exit
        fb.switch_to_block(bb_loop);
        let cmp = fb.icmp(ICmpOp::Sle, Ty::I64, loop_i, n);
        fb.condbr(cmp, bb_body, vec![], bb_exit, vec![]);

        // body: sum += i; i += 1; back to loop
        fb.switch_to_block(bb_body);
        let new_sum = fb.binop(BinOp::Add, Ty::I64, loop_sum, loop_i);
        let one = fb.iconst(Ty::I64, 1);
        let new_i = fb.binop(BinOp::Add, Ty::I64, loop_i, one);
        fb.br(bb_loop, vec![new_sum, new_i]);

        // exit: return sum
        fb.switch_to_block(bb_exit);
        fb.ret(vec![loop_sum]);

        fb.build();
        let module = mb.build();

        let result =
            interpret(&module, "sum_to", &[InterpreterValue::Int(100)]).expect("interpret sum_to");
        assert_eq!(result_int(&result), 5050);

        let r0 = interpret(&module, "sum_to", &[InterpreterValue::Int(0)]).unwrap();
        assert_eq!(result_int(&r0), 0);

        let r10 = interpret(&module, "sum_to", &[InterpreterValue::Int(10)]).unwrap();
        assert_eq!(result_int(&r10), 55);
    }

    // -----------------------------------------------------------------------
    // Test 5: Factorial via recursive Call — factorial(10) == 3628800
    //
    // fn factorial(n: i64) -> i64 {
    //     if n <= 1 { return 1 }
    //     else { return n * factorial(n - 1) }
    // }
    // -----------------------------------------------------------------------

    #[test]
    fn test_interpreter_factorial() {
        let mut mb = ModuleBuilder::new("test_factorial");
        let ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("factorial", ty);

        let entry = fb.create_block();
        let n = fb.add_block_param(entry, Ty::I64);

        let bb_base = fb.create_block();
        let bb_recurse = fb.create_block();

        // entry: if n <= 1 -> base, else -> recurse
        fb.switch_to_block(entry);
        let one = fb.iconst(Ty::I64, 1);
        let cmp = fb.icmp(ICmpOp::Sle, Ty::I64, n, one);
        fb.condbr(cmp, bb_base, vec![], bb_recurse, vec![]);

        // base case: return 1
        fb.switch_to_block(bb_base);
        let base_val = fb.iconst(Ty::I64, 1);
        fb.ret(vec![base_val]);

        // recursive case: return n * factorial(n - 1)
        fb.switch_to_block(bb_recurse);
        let one2 = fb.iconst(Ty::I64, 1);
        let n_minus_1 = fb.binop(BinOp::Sub, Ty::I64, n, one2);
        let func_id = trust_ir::FuncId::new(0); // factorial is function 0
        let sub_result = fb.call(func_id, vec![n_minus_1]);
        let product = fb.binop(BinOp::Mul, Ty::I64, n, sub_result);
        fb.ret(vec![product]);

        fb.build();
        let module = mb.build();

        let result = interpret(&module, "factorial", &[InterpreterValue::Int(10)])
            .expect("interpret factorial");
        assert_eq!(result_int(&result), 3_628_800);

        let r0 = interpret(&module, "factorial", &[InterpreterValue::Int(0)]).unwrap();
        assert_eq!(result_int(&r0), 1);

        let r1 = interpret(&module, "factorial", &[InterpreterValue::Int(1)]).unwrap();
        assert_eq!(result_int(&r1), 1);

        let r5 = interpret(&module, "factorial", &[InterpreterValue::Int(5)]).unwrap();
        assert_eq!(result_int(&r5), 120);
    }

    // -----------------------------------------------------------------------
    // Test 6: Max — max(10, 20) == 20, max(20, 10) == 20
    //
    // fn max(a: i64, b: i64) -> i64 {
    //     if a > b { return a } else { return b }
    // }
    // -----------------------------------------------------------------------

    #[test]
    fn test_interpreter_max() {
        let mut mb = ModuleBuilder::new("test_max");
        let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("max", ty);

        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I64);
        let b = fb.add_block_param(entry, Ty::I64);

        let bb_then = fb.create_block();
        let bb_else = fb.create_block();

        // entry: if a > b -> then (return a), else (return b)
        fb.switch_to_block(entry);
        let cmp = fb.icmp(ICmpOp::Sgt, Ty::I64, a, b);
        fb.condbr(cmp, bb_then, vec![], bb_else, vec![]);

        fb.switch_to_block(bb_then);
        fb.ret(vec![a]);

        fb.switch_to_block(bb_else);
        fb.ret(vec![b]);

        fb.build();
        let module = mb.build();

        let r1 = interpret(
            &module,
            "max",
            &[InterpreterValue::Int(10), InterpreterValue::Int(20)],
        )
        .unwrap();
        assert_eq!(result_int(&r1), 20);

        let r2 = interpret(
            &module,
            "max",
            &[InterpreterValue::Int(20), InterpreterValue::Int(10)],
        )
        .unwrap();
        assert_eq!(result_int(&r2), 20);

        let r3 = interpret(
            &module,
            "max",
            &[InterpreterValue::Int(5), InterpreterValue::Int(5)],
        )
        .unwrap();
        assert_eq!(result_int(&r3), 5);

        let r4 = interpret(
            &module,
            "max",
            &[InterpreterValue::Int(-3), InterpreterValue::Int(-7)],
        )
        .unwrap();
        assert_eq!(result_int(&r4), -3);
    }

    // -----------------------------------------------------------------------
    // Test 7: Select instruction
    // -----------------------------------------------------------------------

    #[test]
    fn test_interpreter_select() {
        let mut mb = ModuleBuilder::new("test_select");
        let ty = mb.add_func_type(vec![Ty::I64, Ty::I64, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("select_max", ty);

        let entry = fb.create_block();
        let cond_param = fb.add_block_param(entry, Ty::I64); // nonzero = true
        let a = fb.add_block_param(entry, Ty::I64);
        let b = fb.add_block_param(entry, Ty::I64);

        fb.switch_to_block(entry);
        // Compare cond_param != 0 to get a Bool
        let zero = fb.iconst(Ty::I64, 0);
        let cond = fb.icmp(ICmpOp::Ne, Ty::I64, cond_param, zero);
        let result = fb.select(Ty::I64, cond, a, b);
        fb.ret(vec![result]);

        fb.build();
        let module = mb.build();

        // cond=1 -> select a=10
        let r1 = interpret(
            &module,
            "select_max",
            &[
                InterpreterValue::Int(1),
                InterpreterValue::Int(10),
                InterpreterValue::Int(20),
            ],
        )
        .unwrap();
        assert_eq!(result_int(&r1), 10);

        // cond=0 -> select b=20
        let r2 = interpret(
            &module,
            "select_max",
            &[
                InterpreterValue::Int(0),
                InterpreterValue::Int(10),
                InterpreterValue::Int(20),
            ],
        )
        .unwrap();
        assert_eq!(result_int(&r2), 20);
    }

    // -----------------------------------------------------------------------
    // Test 8: Bitwise operations — AND, OR, XOR
    // -----------------------------------------------------------------------

    #[test]
    fn test_interpreter_bitwise() {
        let mut mb = ModuleBuilder::new("test_bitwise");
        let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);

        // fn bit_and(a, b) -> a & b
        {
            let mut fb = mb.function("bit_and", ty);
            let entry = fb.create_block();
            let a = fb.add_block_param(entry, Ty::I64);
            let b = fb.add_block_param(entry, Ty::I64);
            fb.switch_to_block(entry);
            let result = fb.binop(BinOp::And, Ty::I64, a, b);
            fb.ret(vec![result]);
            fb.build();
        }

        // fn bit_or(a, b) -> a | b
        {
            let mut fb = mb.function("bit_or", ty);
            let entry = fb.create_block();
            let a = fb.add_block_param(entry, Ty::I64);
            let b = fb.add_block_param(entry, Ty::I64);
            fb.switch_to_block(entry);
            let result = fb.binop(BinOp::Or, Ty::I64, a, b);
            fb.ret(vec![result]);
            fb.build();
        }

        // fn bit_xor(a, b) -> a ^ b
        {
            let mut fb = mb.function("bit_xor", ty);
            let entry = fb.create_block();
            let a = fb.add_block_param(entry, Ty::I64);
            let b = fb.add_block_param(entry, Ty::I64);
            fb.switch_to_block(entry);
            let result = fb.binop(BinOp::Xor, Ty::I64, a, b);
            fb.ret(vec![result]);
            fb.build();
        }

        let module = mb.build();

        // AND: 0xFF & 0x0F == 0x0F
        let r_and = interpret(
            &module,
            "bit_and",
            &[InterpreterValue::Int(0xFF), InterpreterValue::Int(0x0F)],
        )
        .unwrap();
        assert_eq!(result_int(&r_and), 0x0F);

        // OR: 0xF0 | 0x0F == 0xFF
        let r_or = interpret(
            &module,
            "bit_or",
            &[InterpreterValue::Int(0xF0), InterpreterValue::Int(0x0F)],
        )
        .unwrap();
        assert_eq!(result_int(&r_or), 0xFF);

        // XOR: 0xFF ^ 0xFF == 0
        let r_xor = interpret(
            &module,
            "bit_xor",
            &[InterpreterValue::Int(0xFF), InterpreterValue::Int(0xFF)],
        )
        .unwrap();
        assert_eq!(result_int(&r_xor), 0);

        // XOR: 0xAA ^ 0x55 == 0xFF
        let r_xor2 = interpret(
            &module,
            "bit_xor",
            &[InterpreterValue::Int(0xAA), InterpreterValue::Int(0x55)],
        )
        .unwrap();
        assert_eq!(result_int(&r_xor2), 0xFF);
    }

    #[test]
    fn test_interpreter_ctpop_respects_declared_width() {
        let mut mb = ModuleBuilder::new("test_ctpop");
        let ty = mb.add_func_type(vec![Ty::I8], vec![Ty::I8]);
        let mut fb = mb.function("ctpop8", ty);

        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I8);
        fb.switch_to_block(entry);
        let result = fb.ctpop(Ty::I8, a);
        fb.ret(vec![result]);
        fb.build();

        let module = mb.build();
        let result =
            interpret(&module, "ctpop8", &[InterpreterValue::Int(-1)]).expect("interpret ctpop8");
        assert_eq!(result_int(&result), 8);
    }

    #[test]
    fn test_interpreter_lshr_oversized_shift_count_wraps_without_panic() {
        let mut mb = ModuleBuilder::new("test_lshr_oversized");
        let ty = mb.add_func_type(vec![Ty::I128, Ty::I128], vec![Ty::I128]);
        let mut fb = mb.function("lshr", ty);

        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I128);
        let b = fb.add_block_param(entry, Ty::I128);
        fb.switch_to_block(entry);
        let result = fb.binop(BinOp::LShr, Ty::I128, a, b);
        fb.ret(vec![result]);
        fb.build();

        let module = mb.build();

        let r_boundary = interpret(
            &module,
            "lshr",
            &[InterpreterValue::Int(-2), InterpreterValue::Int(128)],
        )
        .expect("lshr by 128 should not panic");
        assert_eq!(result_int(&r_boundary), -2);

        let r_boundary_plus_one = interpret(
            &module,
            "lshr",
            &[InterpreterValue::Int(-2), InterpreterValue::Int(129)],
        )
        .expect("lshr by 129 should not panic");
        assert_eq!(result_int(&r_boundary_plus_one), i128::MAX);
    }

    #[test]
    fn test_interpreter_i64_urem_lshr_uses_i64_width() {
        let mut mb = ModuleBuilder::new("test_i64_urem_lshr_width");
        let ty = mb.add_func_type(vec![Ty::I64, Ty::I64, Ty::I64, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("fuzz_fn", ty);

        let entry = fb.create_block();
        let a0 = fb.add_block_param(entry, Ty::I64);
        let _a1 = fb.add_block_param(entry, Ty::I64);
        let _a2 = fb.add_block_param(entry, Ty::I64);
        let a3 = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let xor = fb.binop(BinOp::Xor, Ty::I64, a3, a0);
        let rem = fb.binop(BinOp::URem, Ty::I64, a3, xor);
        let shifted = fb.binop(BinOp::LShr, Ty::I64, rem, rem);
        fb.ret(vec![shifted]);
        fb.build();

        let module = mb.build();
        let result = interpret(
            &module,
            "fuzz_fn",
            &[
                InterpreterValue::Int(-2_147_483_648),
                InterpreterValue::Int(-886_279_710),
                InterpreterValue::Int(-649_227_473),
                InterpreterValue::Int(-151_070_022),
            ],
        )
        .expect("interpret seed-7 reduction");

        assert_eq!(result_int(&result), 0);
    }

    #[test]
    fn test_interpreter_assert_false_fails() {
        let mut mb = ModuleBuilder::new("test_assert_false");
        let ty = mb.add_func_type(vec![], vec![Ty::I64]);
        let mut fb = mb.function("assert_false", ty);

        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let false_value = fb.iconst(Ty::Bool, 0);
        fb.assert(false_value);
        let zero = fb.iconst(Ty::I64, 0);
        fb.ret(vec![zero]);
        fb.build();

        let module = mb.build();
        let result = interpret(&module, "assert_false", &[]);
        assert!(matches!(result, Err(InterpreterError::AssertionFailed)));
    }

    // -----------------------------------------------------------------------
    // Test 9: Fuel exhaustion
    // -----------------------------------------------------------------------

    #[test]
    fn test_interpreter_fuel_exhaustion() {
        // Build an infinite loop: while true { }
        let mut mb = ModuleBuilder::new("test_inf");
        let ty = mb.add_func_type(vec![], vec![Ty::I64]);
        let mut fb = mb.function("infinite", ty);

        let entry = fb.create_block();
        let bb_loop = fb.create_block();

        fb.switch_to_block(entry);
        fb.br(bb_loop, vec![]);

        fb.switch_to_block(bb_loop);
        fb.br(bb_loop, vec![]);

        fb.build();
        let module = mb.build();

        let config = InterpreterConfig {
            fuel: 100,
            ..Default::default()
        };
        let result = interpret_with_config(&module, "infinite", &[], config);
        assert!(
            matches!(result, Err(InterpreterError::FuelExhausted(100))),
            "expected fuel exhaustion, got {:?}",
            result
        );
    }

    // -----------------------------------------------------------------------
    // Test 10: Function not found
    // -----------------------------------------------------------------------

    #[test]
    fn test_interpreter_function_not_found() {
        let mb = ModuleBuilder::new("empty");
        let module = mb.build();
        let result = interpret(&module, "nonexistent", &[]);
        assert!(matches!(result, Err(InterpreterError::FunctionNotFound(_))));
    }

    // -----------------------------------------------------------------------
    // Test 11: Arity mismatch
    // -----------------------------------------------------------------------

    #[test]
    fn test_interpreter_arity_mismatch() {
        let mut mb = ModuleBuilder::new("test_arity");
        let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("needs_two", ty);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I64);
        let _b = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        fb.ret(vec![a]);
        fb.build();

        let module = mb.build();
        let result = interpret(&module, "needs_two", &[InterpreterValue::Int(1)]);
        assert!(matches!(
            result,
            Err(InterpreterError::ArityMismatch {
                expected: 2,
                got: 1
            })
        ));
    }

    // -----------------------------------------------------------------------
    // Test 12: Ordered float comparisons are false when either operand is NaN.
    //
    // In particular `ONe` (ordered not-equal) must be FALSE on NaN, even
    // though Rust's `!=` would return `true`.
    // -----------------------------------------------------------------------

    #[test]
    fn test_eval_fcmp_one_is_false_with_nan() {
        use trust_ir::FCmpOp;
        let module = TrustIrModule::new("fcmp_one_nan");
        let interp = Interpreter::new(&module, InterpreterConfig::default());

        let nan = f64::NAN;

        // Ordered not-equal: false whenever an operand is NaN, regardless of
        // the other operand.
        assert!(!interp.eval_fcmp(FCmpOp::ONe, nan, 1.0));
        assert!(!interp.eval_fcmp(FCmpOp::ONe, 1.0, nan));
        assert!(!interp.eval_fcmp(FCmpOp::ONe, nan, nan));
        // Distinct, non-NaN operands are still ordered-not-equal.
        assert!(interp.eval_fcmp(FCmpOp::ONe, 1.0, 2.0));
        // Equal, non-NaN operands are not ordered-not-equal.
        assert!(!interp.eval_fcmp(FCmpOp::ONe, 1.0, 1.0));

        // Cross-check the predicate class: every ordered predicate must be
        // false on NaN, and every unordered predicate must be true on NaN.
        for op in [
            FCmpOp::OEq,
            FCmpOp::ONe,
            FCmpOp::OLt,
            FCmpOp::OLe,
            FCmpOp::OGt,
            FCmpOp::OGe,
        ] {
            assert!(!interp.eval_fcmp(op, nan, 1.0), "ordered {op:?} on NaN lhs");
            assert!(!interp.eval_fcmp(op, 1.0, nan), "ordered {op:?} on NaN rhs");
            assert!(!interp.eval_fcmp(op, nan, nan), "ordered {op:?} on NaN/NaN");
        }
        for op in [
            FCmpOp::UEq,
            FCmpOp::UNe,
            FCmpOp::ULt,
            FCmpOp::ULe,
            FCmpOp::UGt,
            FCmpOp::UGe,
        ] {
            assert!(
                interp.eval_fcmp(op, nan, 1.0),
                "unordered {op:?} on NaN lhs"
            );
            assert!(
                interp.eval_fcmp(op, 1.0, nan),
                "unordered {op:?} on NaN rhs"
            );
            assert!(
                interp.eval_fcmp(op, nan, nan),
                "unordered {op:?} on NaN/NaN"
            );
        }
    }

    // -----------------------------------------------------------------------
    // Test 13: Checked-arithmetic overflow flag tracks Rust's checked_*/
    // overflowing_* semantics for both signed and unsigned integer types.
    // -----------------------------------------------------------------------

    #[test]
    fn test_eval_overflow_flag_signed_and_unsigned() {
        use trust_ir::OverflowOp;

        // Signed i8 (width 8): bounds [-128, 127].
        // 127 + 1 overflows.
        assert!(eval_overflow_flag(
            OverflowOp::AddOverflow,
            &Ty::I8,
            8,
            127,
            1
        ));
        // 100 + 27 == 127, no overflow.
        assert!(!eval_overflow_flag(
            OverflowOp::AddOverflow,
            &Ty::I8,
            8,
            100,
            27
        ));
        // -128 - 1 overflows.
        assert!(eval_overflow_flag(
            OverflowOp::SubOverflow,
            &Ty::I8,
            8,
            -128,
            1
        ));
        // i8 MIN * -1 overflows (== 128, out of range).
        assert!(eval_overflow_flag(
            OverflowOp::MulOverflow,
            &Ty::I8,
            8,
            -128,
            -1
        ));

        // Unsigned u8 (width 8): bounds [0, 255].
        // 255 + 1 overflows.
        assert!(eval_overflow_flag(
            OverflowOp::AddOverflow,
            &Ty::U8,
            8,
            255,
            1
        ));
        // 200 + 55 == 255, no overflow.
        assert!(!eval_overflow_flag(
            OverflowOp::AddOverflow,
            &Ty::U8,
            8,
            200,
            55
        ));
        // Unsigned subtraction underflows when lhs < rhs.
        assert!(eval_overflow_flag(
            OverflowOp::SubOverflow,
            &Ty::U8,
            8,
            0,
            1
        ));
        assert!(!eval_overflow_flag(
            OverflowOp::SubOverflow,
            &Ty::U8,
            8,
            5,
            5
        ));
        // 16 * 16 == 256 overflows u8.
        assert!(eval_overflow_flag(
            OverflowOp::MulOverflow,
            &Ty::U8,
            8,
            16,
            16
        ));
        // 15 * 17 == 255, no overflow.
        assert!(!eval_overflow_flag(
            OverflowOp::MulOverflow,
            &Ty::U8,
            8,
            15,
            17
        ));

        // i64 (width 64): MAX + 1 overflows; large non-overflowing case is fine.
        assert!(eval_overflow_flag(
            OverflowOp::AddOverflow,
            &Ty::I64,
            64,
            i64::MAX as i128,
            1
        ));
        assert!(!eval_overflow_flag(
            OverflowOp::AddOverflow,
            &Ty::I64,
            64,
            i64::MAX as i128 - 1,
            1
        ));
    }

    // -----------------------------------------------------------------------
    // Test 14: The Overflow instruction reports the overflow bit end-to-end.
    // -----------------------------------------------------------------------

    #[test]
    fn test_interpreter_overflow_instruction_reports_flag() {
        let mut mb = ModuleBuilder::new("test_overflow_inst");
        let ty = mb.add_func_type(vec![Ty::I8, Ty::I8], vec![Ty::Bool]);
        let mut fb = mb.function("checked_add_i8", ty);

        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I8);
        let b = fb.add_block_param(entry, Ty::I8);
        fb.switch_to_block(entry);
        let (_sum, overflow) = fb.overflow(trust_ir::OverflowOp::AddOverflow, Ty::I8, a, b);
        fb.ret(vec![overflow]);
        fb.build();

        let module = mb.build();

        // 127 + 1 overflows i8.
        let overflowed = interpret(
            &module,
            "checked_add_i8",
            &[InterpreterValue::Int(127), InterpreterValue::Int(1)],
        )
        .expect("interpret checked_add_i8 (overflow)");
        assert_eq!(overflowed.len(), 1);
        assert!(overflowed[0].as_bool().expect("bool flag"));

        // 100 + 27 == 127, no overflow.
        let ok = interpret(
            &module,
            "checked_add_i8",
            &[InterpreterValue::Int(100), InterpreterValue::Int(27)],
        )
        .expect("interpret checked_add_i8 (no overflow)");
        assert_eq!(ok.len(), 1);
        assert!(!ok[0].as_bool().expect("bool flag"));
    }
}
