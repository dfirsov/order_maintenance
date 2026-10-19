//! The most expensive operations: random insertions up to `n` elements; per decade, the five
//! operations with the most machine steps, and whether a rebuild started (`start`), finished
//! (`swap`) or was in progress (`copy`) during them, with the capacity of the current core and
//! the number of drains started (a drain start adds two top-structure nodes).
//!
//!     maxop N [seed]

use om::Om;

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let n: usize = a.get(1).map(|s| s.parse().unwrap()).unwrap_or(1_000_000);
    let mut seed: u64 = a.get(2).map(|s| s.parse().unwrap()).unwrap_or(1) * 0x9E3779B97F4A7C15 | 1;
    let mut rnd = move || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
    let mut om = Om::new(4);
    let mut live: Vec<u64> = vec![om.insert_first()];
    let mut from = 1usize;
    while live.len() < n {
        let to = (from * 10).min(n);
        let mut top: Vec<(u64, usize, &'static str, u64, u64)> = Vec::new();
        while live.len() < to {
            let nxt0 = om.m.peek(2001, 0).as_u64();
            let cap0 = om.capacity();
            let c0 = om.m.cost;
            // top-structure nodes in both slots (cell 0 of array 1000·p + 103)
            let nodes = |om: &Om| om.m.peek(103, 0).as_u64() + om.m.peek(1103, 0).as_u64();
            let nd0 = nodes(&om);
            let x = live[(rnd() % live.len() as u64) as usize];
            live.push(om.insert_after(x));
            let steps = om.m.cost - c0;
            let nxt1 = om.m.peek(2001, 0).as_u64();
            let what = match (nxt0, nxt1, om.capacity() != cap0) {
                (_, _, true) => "swap",
                (0, 1, _) => "start",
                (1, 1, _) => "copy",
                _ => "-",
            };
            let drains = nodes(&om).saturating_sub(nd0) / 2;
            top.push((steps, live.len(), what, cap0, drains));
            if top.len() > 64 {
                top.sort_unstable_by(|a, b| b.0.cmp(&a.0));
                top.truncate(5);
            }
        }
        top.sort_unstable_by(|a, b| b.0.cmp(&a.0));
        for (s, k, w, c, d) in top.iter().take(5) {
            println!("{from}-{to}: steps {s} at n={k} ({w}, N={c}), drains started {d}");
        }
        from = to;
    }
}
