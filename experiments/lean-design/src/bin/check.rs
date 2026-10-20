//! Differential check of `lean` against the list itself: after every operation the new element
//! must sit where the workload put it, and at checkpoints (geometric, plus every `EVERY`
//! operations) the full check of `Lean::check` runs (keys strictly increase along the list,
//! nesting, tags against stored paths).
//!
//!     check WORKLOAD N [L]     WORKLOAD: random hammer append front zigzag mixed all
//!
//! With `L`, groups and chunks use the size parameter `L` (small values stress splits and the
//! top structure) and the top height is sized for N.

use lean_design::lean::{Lean, Params, NIL};

fn run(wl: &str, n: usize, l: Option<u32>) {
    let p = match l { Some(l) => Params::profile(l, n as u64 + 1), None => Params::for_capacity(n as u64 + 1) };
    let mut s = Lean::with_params(n, p.clone(), false);
    let mut seed: u64 = 0x9E3779B97F4A7C15 | 1;
    let mut rnd = move || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
    // reference list: next pointers by handle; handles are dense indices (sentinel 0)
    let mut next: Vec<u32> = vec![NIL; n + 2];
    let head = 0u32;
    let mut live: Vec<u32> = vec![head];
    let mut last = head;
    let mut cp = 16usize;
    for k in 0..n {
        let x = match wl {
            "random" => live[(rnd() % live.len() as u64) as usize],
            "hammer" => if live.len() > 1 { live[1] } else { head },
            "append" => last,
            "front" => head,
            "zigzag" => live[if k % 2 == 0 { live.len() - 1 } else { (live.len() - 1) / 2 }],
            "mixed" => match rnd() % 4 { 0 => head, 1 => last, 2 => live[live.len() - 1 - (rnd() % live.len().min(64) as u64) as usize], _ => live[(rnd() % live.len() as u64) as usize] },
            _ => panic!("workload"),
        };
        let y = s.insert_after(x);
        assert_eq!(y as usize, live.len(), "handles are dense");
        next[y as usize] = next[x as usize];
        next[x as usize] = y;
        assert!(s.order(x, y) && !s.order(y, x), "new element not right after its anchor");
        if next[y as usize] != NIL {
            assert!(s.order(y, next[y as usize]), "new element not before its successor");
        }
        live.push(y);
        last = y;
        if k + 1 == cp || k + 1 == n || (k + 1) % 200_000 == 0 {
            let mut list = Vec::with_capacity(live.len());
            let mut e = head;
            while e != NIL { list.push(e); e = next[e as usize]; }
            s.check(&list);
            cp *= 2;
        }
    }
    println!("{wl}: n={n} L={} H={} G={} T={}: ok (drains {}, max table {})", p.l, p.h, p.g, p.t, s.drains, s.max_table);
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let wl = a.get(1).map(|s| s.as_str()).unwrap_or("all");
    let n: usize = a.get(2).map(|s| s.parse().unwrap()).unwrap_or(100_000);
    let l: Option<u32> = a.get(3).map(|s| s.parse().unwrap());
    if wl == "all" {
        for w in ["random", "hammer", "append", "front", "zigzag", "mixed"] { run(w, n, l); }
    } else {
        run(wl, n, l);
    }
}
