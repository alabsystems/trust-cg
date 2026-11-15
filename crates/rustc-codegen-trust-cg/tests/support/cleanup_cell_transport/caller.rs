extern crate cleanup_cell_transport_callee as callee;
extern crate cleanup_cell_transport_provider as provider;

fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let values = [11u64, 73u64];
    let mut scenarios = 0;
    for choose_b in [false, true] {
        for do_panic in [false, true] {
            provider::reset();
            let result = std::panic::catch_unwind(|| {
                callee::reference_copy(&values[0], &values[1], choose_b, do_panic)
            });
            if do_panic {
                assert!(result.unwrap_err().is::<provider::ProbePanic>());
            } else {
                assert_eq!(result.unwrap(), values[1]);
            }
            assert_eq!(provider::observation(),
                (&values[1] as *const u64 as usize, values[1], 1, values[1]));
            scenarios += 1;
        }
    }
    for do_panic in [false, true] {
        provider::reset();
        let result = std::panic::catch_unwind(|| callee::nested_scalar_tuple(11, 83, do_panic));
        if do_panic {
            assert!(result.unwrap_err().is::<provider::ProbePanic>());
        } else {
            assert_eq!(result.unwrap(), 90);
        }
        let (address, observed, drops, dropped) = provider::observation();
        assert_ne!(address, 0);
        assert_eq!(address % std::mem::align_of::<u64>(), 0);
        assert_eq!((observed, drops, dropped), (83, 1, 83));
        scenarios += 1;
    }
    assert_eq!(scenarios, 6);
    println!("CLEANUP_CELL_TRANSPORT|scenarios=6|reference_copy=4|nested_scalar_tuple=2");
}
