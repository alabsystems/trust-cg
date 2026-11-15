use std::sync::Mutex;
static EVENTS: Mutex<Vec<(u64, usize)>> = Mutex::new(Vec::new());
unsafe extern "C-unwind" {
    fn zst_scope(enabled: u64) -> u64;
}
unsafe extern "C" {
    fn zst_by_value();
    fn zst_loop(count: u32) -> u64;
    fn zst_raw_local() -> u64;
}
#[unsafe(no_mangle)]
pub extern "C" fn note_address(kind: u64, address: usize) {
    EVENTS.lock().unwrap().push((kind, address));
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn maybe_panic(item: u64, enabled: u64) {
    if enabled != 0 && item == 2 {
        std::panic::panic_any(123_u64);
    }
}
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    for enabled in [0, 1] {
        EVENTS.lock().unwrap().clear();
        let result = std::panic::catch_unwind(|| unsafe { zst_scope(enabled) });
        if enabled == 0 {
            assert_eq!(result.unwrap(), 77);
        } else {
            assert_eq!(*result.unwrap_err().downcast::<u64>().unwrap(), 123);
        }
        let events = EVENTS.lock().unwrap();
        assert_eq!(
            events.iter().map(|row| row.0).collect::<Vec<_>>(),
            [1, 3, 4, 2]
        );
        assert_eq!(events[0].1, events[3].1);
        assert_eq!(events[1].1, events[2].1);
        assert_ne!(events[0].1, 0);
        assert_ne!(events[1].1, 0);
        assert_eq!(events[1].1 % 8, 0);
    }
    EVENTS.lock().unwrap().clear();
    unsafe {
        zst_by_value();
    }
    {
        let events = EVENTS.lock().unwrap();
        assert_eq!(
            events.iter().map(|row| row.0).collect::<Vec<_>>(),
            [2, 2, 2]
        );
        assert!(events.iter().all(|row| row.1 != 0));
    }
    EVENTS.lock().unwrap().clear();
    assert_eq!(unsafe { zst_raw_local() }, 16);
    {
        let events = EVENTS.lock().unwrap();
        assert_eq!(events.iter().map(|row| row.0).collect::<Vec<_>>(), [5, 6]);
        assert_eq!(events[0].1, events[1].1);
        assert_ne!(events[0].1, 0);
        assert_eq!(events[0].1 % 16, 0);
    }
    let mut checks = 21;
    for count in 0..=8 {
        EVENTS.lock().unwrap().clear();
        assert_eq!(unsafe { zst_loop(count) }, u64::from(count));
        let events = EVENTS.lock().unwrap();
        assert_eq!(events.len(), count as usize * 2);
        checks += 2;
        for pair in events.chunks_exact(2) {
            assert_eq!([pair[0].0, pair[1].0], [1, 2]);
            assert_eq!(pair[0].1, pair[1].1);
            assert_ne!(pair[0].1, 0);
            checks += 3;
        }
    }
    println!("PASS zero_sized_drop checks={checks}");
}
