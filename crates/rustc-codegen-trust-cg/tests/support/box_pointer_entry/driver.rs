extern crate box_pointer_entry_callee as callee;
extern crate box_pointer_entry_provider as provider;

fn require_events(snapshot: &provider::Snapshot, expected: &[usize]) {
    assert_eq!(snapshot.event_count, expected.len(), "{snapshot:?}");
    assert_eq!(&snapshot.events[..expected.len()], expected, "{snapshot:?}");
    assert!(
        snapshot.events[expected.len()..]
            .iter()
            .all(|event| *event == 0)
    );
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    assert_eq!(arguments.len(), 3);
    let kind = arguments[0].as_str();
    let old_payload: i64 = arguments[1].parse().unwrap();
    let new_payload: i64 = arguments[2].parse().unwrap();
    assert_ne!(old_payload, new_payload);
    assert_eq!(provider::box_layout(), (8, 8));
    assert_eq!(std::mem::size_of::<i64>(), 8);
    assert_eq!(std::mem::align_of::<i64>(), 8);

    let old = provider::make_box(old_payload);
    assert_eq!(*old, old_payload);
    let old_address = provider::address(&old);
    let (result, expected_address, expected_payload, expected_frees, snapshot) = match kind {
        "untouched" => {
            provider::begin(old_address, 0);
            let result = callee::consume_untouched(old);
            let snapshot = provider::finish();
            assert_eq!(snapshot.retargets, 0, "{snapshot:?}");
            assert_eq!(snapshot.before, 0, "{snapshot:?}");
            assert_eq!(snapshot.after, 0, "{snapshot:?}");
            assert_eq!(snapshot.before_payload, 0, "{snapshot:?}");
            assert_eq!(snapshot.after_payload, 0, "{snapshot:?}");
            assert_eq!(snapshot.old_frees, 1, "{snapshot:?}");
            assert_eq!(snapshot.new_frees, 0, "{snapshot:?}");
            require_events(&snapshot, &[provider::READ, provider::FREE_OLD]);
            (result, old_address, old_payload, 1, snapshot)
        }
        "retargeted" => {
            let replacement = provider::make_box(new_payload);
            assert_eq!(*replacement, new_payload);
            let new_address = provider::address(&replacement);
            assert_ne!(old_address, new_address);
            provider::begin(old_address, new_address);
            let result = callee::consume_retargeted(old, replacement);
            let snapshot = provider::finish();
            assert_eq!(snapshot.retargets, 1, "{snapshot:?}");
            assert_eq!(snapshot.before, old_address, "{snapshot:?}");
            assert_eq!(snapshot.after, new_address, "{snapshot:?}");
            assert_eq!(snapshot.before_payload, old_payload, "{snapshot:?}");
            assert_eq!(snapshot.after_payload, new_payload, "{snapshot:?}");
            assert_eq!(snapshot.old_frees, 1, "{snapshot:?}");
            assert_eq!(snapshot.new_frees, 1, "{snapshot:?}");
            require_events(
                &snapshot,
                &[
                    provider::RETARGET_BEGIN,
                    provider::FREE_OLD,
                    provider::RETARGET_END,
                    provider::READ,
                    provider::FREE_NEW,
                ],
            );
            (result, new_address, new_payload, 2, snapshot)
        }
        _ => panic!("unknown mandatory case {kind}"),
    };
    assert_eq!(result, expected_payload, "{snapshot:?}");
    assert_eq!(snapshot.payload, expected_payload, "{snapshot:?}");
    assert_eq!(snapshot.observed, expected_address, "{snapshot:?}");
    assert_eq!(snapshot.reads, 1, "{snapshot:?}");
    assert_eq!(snapshot.bad_layout, 0, "{snapshot:?}");
    println!(
        "BOX_POINTER_ENTRY_ADDRESS kind={kind} expected={expected_address:#x} observed={:#x}",
        snapshot.observed
    );
    println!(
        "BOX_POINTER_ENTRY_CASE kind={kind} payload={expected_payload} address_match=1 reads=1 retargets={} drop_frees={expected_frees} bad_layout=0 events={}",
        snapshot.retargets, snapshot.event_count
    );
}
