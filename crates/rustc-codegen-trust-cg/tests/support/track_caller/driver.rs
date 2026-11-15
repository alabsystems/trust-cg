extern crate tracked;
use std::panic::Location;
use std::sync::Mutex;

static PANIC_SITE: Mutex<Option<(String, u32, u32)>> = Mutex::new(None);

fn verify(at: &Location<'_>, file: &str, line: u32, column: u32) {
    assert_eq!((at.file(), at.line(), at.column()), (file, line, column));
}

fn main() {
    let mut checks = 0;
    macro_rules! check {
        ($name:ident($($arg:expr),*)) => {{
            let at = tracked::$name($($arg),*);
            verify(at, file!(), line!(), column!());
            checks += 1;
        }};
    }
    macro_rules! check_pair {
        ($x:expr) => {{
            let x: u64 = $x;
            let (at, value) = tracked::many(x, 2, 3, 4, 5, 6, 7, 8, 9, !x);
            verify(at, file!(), line!(), column!());
            let expected = x
                ^ 2u64.rotate_left(1)
                ^ 3u64.rotate_left(2)
                ^ 4u64.rotate_left(3)
                ^ 5u64.rotate_left(4)
                ^ 6u64.rotate_left(5)
                ^ 7u64.rotate_left(6)
                ^ 8u64.rotate_left(7)
                ^ 9u64.rotate_left(8)
                ^ (!x).rotate_left(9);
            assert_eq!(value, expected);
            checks += 2;
            let (values, at) = tracked::buffered(x);
            verify(at, file!(), line!(), column!());
            assert_eq!(
                values,
                [x, x.wrapping_add(1), x.wrapping_add(2), x.wrapping_add(3)]
            );
            checks += 2;
        }};
    }
    for index in 0..128 {
        check!(leaf());
        check!(chain());
        check!(through_inline());
        check!(recursive(index % 8));
        check!(dynamic(&tracked::Marker));
        check!(external());
        check_pair!(u64::MAX.wrapping_mul(index as u64));
    }
    let corpus = concat!(env!("CORPUS_DIR"), "/corpus.rs");
    verify(tracked::boundary(), corpus, tracked::BOUNDARY_LINE, 5);
    verify(
        tracked::through_boundary(),
        corpus,
        tracked::INLINE_BOUNDARY_LINE,
        5,
    );
    // A function-pointer reification shim and a trait whose declaration is
    // untracked form location boundaries at the concrete function definition.
    verify(tracked::reify()(), corpus, tracked::LEAF_LINE, 1);
    verify(
        tracked::plain_dynamic(&tracked::Marker),
        corpus,
        tracked::PLAIN_IMPL_LINE,
        5,
    );
    checks += 4;

    std::panic::set_hook(Box::new(|info| {
        let at = info.location().unwrap();
        *PANIC_SITE.lock().unwrap() = Some((at.file().to_owned(), at.line(), at.column()));
    }));
    macro_rules! check_panic {
        ($name:ident($($arg:expr),*)) => {{
            assert!(std::panic::catch_unwind(|| tracked::$name($($arg),*)).is_err());
            let at = PANIC_SITE.lock().unwrap().take().unwrap();
            assert_eq!((at.0.as_str(), at.1, at.2), (file!(), line!(), column!()));
            checks += 1;
        }};
    }
    check_panic!(external_panic());
    check_panic!(local_panic());
    check_panic!(on_assert(0));
    assert!(std::panic::catch_unwind(|| tracked::plain_div(0)).is_err());
    let at = PANIC_SITE.lock().unwrap().take().unwrap();
    assert_eq!(
        (at.0.as_str(), at.1, at.2),
        (corpus, tracked::ASSERT_LINE, 5)
    );
    checks += 1;
    assert_eq!(checks, 1288);
    println!("PASS track_caller checks={checks}");
}
