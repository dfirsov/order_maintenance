//! Real time per operation as the structure grows: random insertions up to `n` elements.
//! Every `w` operations prints a CSV row: operations so far, live elements, the current core's
//! capacity N and L = max(8, bit length of N), the mean nanoseconds per operation, the mean and
//! maximum machine steps per operation, and the peak bit length so far.
//!
//!     growth N [W] [seed]

use om::Om;
use std::time::Instant;

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let n: usize = a.get(1).map(|s| s.parse().unwrap()).unwrap_or(1_000_000);
    let w: usize = a.get(2).map(|s| s.parse().unwrap()).unwrap_or(20_000);
    let mut seed: u64 = a.get(3).map(|s| s.parse().unwrap()).unwrap_or(1) * 0x9E3779B97F4A7C15 | 1;
    let mut rnd = move || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
    let mut om = Om::new(4);
    let mut live: Vec<u64> = Vec::new();
    println!("ops,live,N,L,ns_per_op,mean_steps,max_steps,peak_bits");
    let mut k = 0;
    while k < n {
        let t0 = Instant::now();
        let c0 = om.m.cost;
        let mut maxs = 0;
        for _ in 0..w {
            let before = om.m.cost;
            let h = if live.is_empty() { om.insert_first() } else {
                let x = live[(rnd() % live.len() as u64) as usize];
                om.insert_after(x)
            };
            live.push(h);
            maxs = maxs.max(om.m.cost - before);
        }
        k += w;
        let dt = t0.elapsed().as_nanos() as f64 / w as f64;
        let cap = om.capacity();
        let l = (64 - cap.leading_zeros() as u64).max(8);
        println!("{k},{},{cap},{l},{dt:.0},{:.0},{maxs},{}", live.len(), (om.m.cost - c0) as f64 / w as f64, om.m.peak);
    }
}
