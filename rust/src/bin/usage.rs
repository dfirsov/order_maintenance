//! How much of the reserved memory a core uses: grow by random insertions and, at each checkpoint,
//! read the current core's record counts and list lengths from the machine arrays.
//!
//!     usage

use om::Om;

fn main() {
    let mut seed: u64 = 0x9E3779B97F4A7C15 | 1;
    let mut rnd = move || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
    let mut om = Om::new(4);
    let mut live: Vec<u64> = Vec::new();
    println!("{:>9} {:>9} | {:>8} {:>8} | {:>7} {:>9} | max list length: children table inTab side cin | cells: capacities, in use",
        "live", "N", "elements", "chunks", "nodes", "node cap");
    for &target in &[10_000usize, 100_000, 1_000_000, 4_000_000] {
        while live.len() < target {
            let h = if live.is_empty() { om.insert_first() } else {
                let x = live[(rnd() % live.len() as u64) as usize];
                om.insert_after(x)
            };
            live.push(h);
        }
        let p = om.m.peek(2000, 0).as_u64();
        let base = 1000 * p;
        let n = om.capacity();
        let sz = |t: u64| om.m.peek(base + 100 + t, 0).as_u64();
        let (ne, nc, nn) = (sz(0), sz(2), sz(3));
        let ncap = om.m.cap(base + 60);
        let maxlen = |k: u64, recs: u64| (0..recs as usize).map(|i| om.m.peek(base + 132 + 3 * k, i).as_u64()).max().unwrap_or(0);
        println!("{:>9} {:>9} | {:>8} {:>8} | {:>7} {:>9} | {:>8} {:>5} {:>5} {:>4} {:>3} | {} {}",
            live.len(), n, ne, nc, nn, ncap,
            maxlen(0, nn), maxlen(1, nn), maxlen(2, nn), maxlen(3, nn), maxlen(4, nc), om.m.cells(), om.m.resident());
    }
}
