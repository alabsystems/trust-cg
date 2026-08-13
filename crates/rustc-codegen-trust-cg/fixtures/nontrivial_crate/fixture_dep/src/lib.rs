enum DepChoice {
    Packed(u64),
    Raw,
}

use rustc_codegen_trust_cg_fixture_leaf::leaf_mix;

#[inline(never)]
pub fn dependency_mix(seed: u64, total: u64) -> u64 {
    let pair = (seed ^ 3, total | 1);
    let mut cells = [pair.0, pair.1, seed & 7];
    let cells_copy = cells;
    cells = [cells_copy[2], cells_copy[1], cells_copy[0]];
    let cells_len = cells.len() as u64;
    let mut choice = DepChoice::Packed(cells[0] ^ cells[2]);
    choice = DepChoice::Packed(match choice {
        DepChoice::Packed(value) => value & 15,
        DepChoice::Raw => total,
    });
    match choice {
        DepChoice::Packed(value) => leaf_mix(value ^ cells[1], cells_len),
        DepChoice::Raw => seed,
    }
}
