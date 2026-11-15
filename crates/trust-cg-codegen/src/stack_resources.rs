// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Cheap observations of the frame layout already produced by preparation.
//! These are not stack-limit certificates or whole-call-stack bounds.

use crate::{frame::FrameLayout, pipeline::PreparationMetrics};

/// The static component of one prepared function's stack layout.
///
/// This records existing frame-lowering output without scanning machine code
/// or requesting a U10 prologue check. It does not establish a stack bound,
/// source/native correspondence or permission to execute. Callee frames,
/// external-call allowances and signal-handler stack use are not included.
/// An absent report means unknown, never a zero-byte frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StaticStackFrameReport {
    /// Planned fixed-frame bytes: callee saves, spills/locals and outgoing
    /// stack arguments, including the layout's alignment padding. This is not
    /// an independently modeled maximum depth of the final instruction stream.
    pub static_frame_bytes: u32,
    /// Runtime-sized allocation is present. In that case the fixed component
    /// remains known, but the function's total stack consumption is unknown.
    pub has_dynamic_allocation: bool,
    /// The layout uses the target red zone. No platform red-zone allowance is
    /// added to `static_frame_bytes`; consumers must account for it separately.
    pub uses_red_zone: bool,
}

impl StaticStackFrameReport {
    pub(crate) fn from_layout(layout: &FrameLayout) -> Self {
        Self {
            static_frame_bytes: layout.total_frame_size,
            has_dynamic_allocation: layout.has_dynamic_alloc,
            uses_red_zone: layout.uses_red_zone,
        }
    }
}

impl PreparationMetrics {
    /// Observe the already-produced fixed frame without another machine/CFG
    /// scan. `None` means no layout was retained, not a zero-byte frame. Dynamic
    /// allocation and excluded callee/external costs remain explicit in the
    /// report; this does not grant a stack-limit certificate or bound.
    #[must_use]
    pub fn static_stack_frame(&self) -> Option<StaticStackFrameReport> {
        self.frame_layout
            .as_ref()
            .map(StaticStackFrameReport::from_layout)
    }
}

#[cfg(test)]
mod tests;
