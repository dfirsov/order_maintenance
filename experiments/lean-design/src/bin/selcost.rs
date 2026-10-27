//! The cost of the work that `compare` used to time together with each random insertion (added for
//! revision 2026-10-27b): the random-number draw and the read of the vector of live handles at a
//! random index, without any data structure.
//!
//!     selcost FROM TO [REPS=3]
//!
//! The vector `live` (u64 handles, capacity `TO`) starts with `FROM` entries and grows by one entry
//! per step, as in `compare`'s `random` workload over the decade FROM..TO, with the same generator
//! and seed. Each step is timed exactly as `compare` times an operation (`Instant::now()` ...
//! `elapsed()`), for four bodies, each in its own pass over the decade:
//!
//! * `empty`: nothing (the timer's own floor, part of every measured operation);
//! * `rng`: one draw, `rnd() % live.len()`;
//! * `select`: one draw and the read `live[rnd() % live.len()]`;
//! * `old`: the old in-interval work exactly, `select` inside the match on the workload name
//!   (`match wl { "random" => ... }`, a string comparison).
//!
//! The push of the next handle is outside the timed interval. Per pass and run, one CSV row:
//!
//!   body,from,to,run,ops,mean_ns,p99_ns,p999_ns,p9999_ns,max_ns
//!
//! and per pass a row with `run` = `min`: the statistics of the per-step minima over the runs.
//! Without the structure, `live` shares the caches with nothing else, so at 10^7 entries (80 MB,
//! L3 36 MB) part of it stays cached, and the figure is a lower bound for the cost in `compare`.

use std::hint::black_box;
use std::time::Instant;

/// One pass; `B`: 0 empty, 1 rng, 2 select, 3 old (a constant, so no dispatch is timed).
fn pass<const B: u8>(from: usize, to: usize, times: &mut Vec<u32>) {
    let wl: &str = black_box("random");
    let first = 0u64;
    let mut seed: u64 = 0x9E3779B97F4A7C15 | 1;
    let mut rnd = move || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
    let mut live: Vec<u64> = Vec::with_capacity(to);
    // the handles 0..from, written now so that the pages are mapped, as they are in `compare`
    live.extend(0..from as u64);
    times.clear();
    while live.len() < to {
        let len = live.len() as u64;
        let t0 = Instant::now();
        match B {
            0 => {}
            1 => { black_box(rnd() % len); }
            2 => { black_box(live[(rnd() % len) as usize]); }
            _ => {
                black_box(match wl {
                    "random" => live[(rnd() % len) as usize],
                    "hammer" => first,
                    "append" => *live.last().unwrap(),
                    _ => panic!("workload"),
                });
            }
        }
        let dt = t0.elapsed().as_nanos();
        times.push(dt.min(u32::MAX as u128) as u32);
        live.push(len);
    }
    black_box(&live);
}

fn row(body: &str, from: usize, to: usize, run: &str, ts: &[u32]) {
    let (mean, p99, p999, p9999, max) = lean_design::tails::stats(ts).unwrap();
    println!("{body},{from},{to},{run},{},{mean:.1},{p99},{p999},{p9999},{max}", ts.len());
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let from: usize = a.get(1).map(|s| s.parse().unwrap()).unwrap_or(10_000_000);
    let to: usize = a.get(2).map(|s| s.parse().unwrap()).unwrap_or(100_000_000);
    let reps: usize = a.get(3).map(|s| s.parse().unwrap()).unwrap_or(3);
    assert!(from >= 1 && to > from);
    println!("body,from,to,run,ops,mean_ns,p99_ns,p999_ns,p9999_ns,max_ns");
    let mut times = Vec::with_capacity(to - from);
    for (b, body) in ["empty", "rng", "select", "old"].iter().enumerate() {
        let mut best: Vec<u32> = Vec::new();
        for r in 0..reps {
            match b {
                0 => pass::<0>(from, to, &mut times),
                1 => pass::<1>(from, to, &mut times),
                2 => pass::<2>(from, to, &mut times),
                _ => pass::<3>(from, to, &mut times),
            }
            row(body, from, to, &r.to_string(), &times);
            if r == 0 { best = times.clone(); } else {
                for (b, &t) in best.iter_mut().zip(times.iter()) { *b = (*b).min(t); }
            }
        }
        row(body, from, to, "min", &best);
    }
}
