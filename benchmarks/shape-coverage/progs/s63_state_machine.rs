// a small state machine: match (enum_state, input) -> new state, struct state
// mutated in a loop. Exercises discriminant of a projected fieldless enum (238a377a).
use std::hint::black_box as bb;
#[derive(Clone, Copy, PartialEq)] enum St { Idle, Run, Halt }
struct M { st: St, acc: u64, steps: u64 }
impl M {
    fn step(&mut self, input: u64) {
        self.st = match (self.st, input % 3) {
            (St::Idle, 0) => St::Run,
            (St::Run, 2) => St::Halt,
            (St::Halt, _) => St::Idle,
            (s, _) => s,
        };
        if self.st == St::Run { self.acc = self.acc.wrapping_add(input); }
        self.steps += 1;
    }
}
fn main() {
    let mut m = M { st: St::Idle, acc: 0, steps: 0 };
    let mut s = bb(0x1234u64);
    for _ in 0..bb(200u64) { s = s.wrapping_mul(6364136223846793005).wrapping_add(1); m.step(s >> 40); }
    std::process::exit(((m.acc ^ m.steps) % 241) as i32);
}
