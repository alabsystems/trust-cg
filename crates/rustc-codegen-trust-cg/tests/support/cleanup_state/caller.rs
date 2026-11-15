extern crate cleanup_state_callee as callee;
extern crate cleanup_state_provider as provider;

use std::panic::{catch_unwind, AssertUnwindSafe};

fn check_outcome(result: Result<u64, Box<dyn std::any::Any + Send>>, panic_site: u8, value: u64) {
    if panic_site == 0 {
        assert_eq!(result.expect("normal path unwound"), value);
    } else {
        let payload = result.expect_err("requested panic returned normally");
        let actual = payload.downcast_ref::<provider::ProbePanic>().expect("wrong panic payload");
        assert_eq!(actual.0, panic_site);
    }
}
fn check_boxes(values: &[u64]) {
    assert_eq!(provider::observed_count(), values.len());
    for (index, expected) in values.iter().copied().enumerate() {
        let (pointer, observed, freed) = provider::box_observation(index);
        assert_ne!(pointer, 0);
        assert_eq!(pointer % std::mem::align_of::<u64>(), 0);
        assert_eq!(observed, expected, "LLVM provider read wrong pointee");
        assert_eq!(freed, 1, "selected buffer was not freed exactly once");
    }
    assert_eq!(provider::drop_observation(), (0, 0));
}
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let base = std::hint::black_box(100u64);
    let mut scenarios = 0;
    for branch in [false, true] {
        let branch_site = if branch { 1 } else { 2 };
        let expected = base + if branch { 11 } else { 21 };
        for site in [0, branch_site, 3] {
            provider::reset();
            let result = catch_unwind(AssertUnwindSafe(|| callee::box_join(branch, site, base)));
            check_outcome(result, site, expected);
            check_boxes(&[expected]);
            scenarios += 1;
        }
    }
    for site in 0..=4 {
        provider::reset();
        let result = catch_unwind(AssertUnwindSafe(|| callee::box_replace_call_result(site, base)));
        check_outcome(result, site, base + 21);
        let values: &[u64] = match site {
            1 => &[],
            2 | 3 => &[111],
            0 | 4 => &[111, 121],
            _ => unreachable!(),
        };
        check_boxes(values);
        scenarios += 1;
    }
    for branch in [false, true] {
        let branch_site = if branch { 1 } else { 2 };
        let expected = base + if branch { 31 } else { 41 };
        for site in [0, branch_site, 3] {
            provider::reset();
            let result = catch_unwind(AssertUnwindSafe(|| callee::scalar_join(branch, site, base)));
            check_outcome(result, site, expected);
            assert_eq!(provider::observed_count(), 0);
            assert_eq!(provider::drop_observation(), (1, expected));
            scenarios += 1;
        }
    }
    assert_eq!(scenarios, 17);
    println!("CLEANUP_STATE|scenarios=17|box_join=6|box_call_result=5|scalar_join=6");
}
