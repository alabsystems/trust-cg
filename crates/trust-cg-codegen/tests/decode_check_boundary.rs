//! The arch-neutral gate must admit byte extents before calling any decoder.

use std::cell::Cell;
use trust_cg_codegen::decode_check::{
    DecodeCheck, DecodeCheckItem, DecodeCheckMode, DecodeCheckOutcome, FixupHole, run_decode_check,
};

#[derive(Default)]
struct PermissiveDecoder(Cell<usize>);

impl DecodeCheck for PermissiveDecoder {
    type Intent = ();

    fn arch(&self) -> &'static str {
        "extent-control"
    }

    fn label(&self, _: &()) -> String {
        "extent control".into()
    }

    fn check_one(&self, _: &(), _: &[u8], _: Option<&FixupHole>) -> DecodeCheckOutcome {
        self.0.set(self.0.get() + 1);
        DecodeCheckOutcome::Match
    }
}

fn item(start: usize, end: usize) -> DecodeCheckItem<()> {
    DecodeCheckItem {
        start,
        end,
        intent: (),
        hole: None,
    }
}

#[test]
fn empty_instruction_ranges_are_rejected_before_decoder_dispatch() {
    for offset in [0, 1, 2] {
        let decoder = PermissiveDecoder::default();
        assert!(
            run_decode_check(
                &decoder,
                &[item(offset, offset)],
                &[0x90, 0xc3],
                DecodeCheckMode::Enforce,
            )
            .is_err(),
            "empty extent at {offset} was accepted"
        );
        assert_eq!(decoder.0.get(), 0);
    }
}

#[test]
fn reversed_and_out_of_bounds_ranges_are_rejected_before_dispatch() {
    for (start, end) in [(2, 1), (0, 3), (usize::MAX, usize::MAX)] {
        let decoder = PermissiveDecoder::default();
        assert!(
            run_decode_check(
                &decoder,
                &[item(start, end)],
                &[0x90, 0xc3],
                DecodeCheckMode::Enforce,
            )
            .is_err()
        );
        assert_eq!(decoder.0.get(), 0);
    }
}

#[test]
fn exact_nonempty_ranges_reach_the_decoder() {
    let decoder = PermissiveDecoder::default();
    run_decode_check(
        &decoder,
        &[item(0, 1), item(1, 2)],
        &[0x90, 0xc3],
        DecodeCheckMode::Enforce,
    )
    .unwrap();
    assert_eq!(decoder.0.get(), 2);
}

#[test]
fn warn_reports_invalid_extents_without_dispatch_and_off_preserves_bypass() {
    for mode in [DecodeCheckMode::Warn, DecodeCheckMode::Off] {
        let decoder = PermissiveDecoder::default();
        run_decode_check(&decoder, &[item(0, 0)], &[], mode).unwrap();
        assert_eq!(decoder.0.get(), 0);
    }
}
