extern crate cleanup_cell_transport_callee as callee;
extern crate cleanup_cell_transport_provider as provider;
use std::panic::{catch_unwind,AssertUnwindSafe};
fn main() {
    std::panic::set_hook(Box::new(|_|{}));
    assert_eq!(callee::sum(83, false), 83);
    let error = catch_unwind(AssertUnwindSafe(||callee::sum(83, true))).unwrap_err();
    assert!(error.is::<provider::ProbePanic>());
    println!("SATURATING_LOCAL_TUPLE|scenarios=2");
}
