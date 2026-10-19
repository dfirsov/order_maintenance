//! Per-operation time of the verified structure and of the amortized baseline (`om::baseline`),
//! on the same workloads.
//!
//!     compare (om|bender) (random|hammer|append|front) N [REPS]
//!
//! The workload runs `REPS` times (default 3), each time on a fresh structure. The workloads are
//! deterministic, so the k-th operation is the same in every run: its time is the minimum over
//! the runs (noise from the machine rarely hits the same operation in every run), and its work
//! must be the same in every run. Statistics per decade of the number of elements, as CSV rows:
//!
//!   impl,workload,from,to,ops,mean_ns,p99_ns,p9999_ns,max_ns,mean_work,max_work,work_of_slowest
//!
//! `max_ns` and the percentiles are over the per-operation minima; `mean_ns` is the median over
//! the runs of each run's mean. `work` is machine steps for `om`, and tags and labels written
//! plus groups scanned for `bender`.
//!
//! Workloads (insertions only): `random` inserts after a uniformly random element; `hammer`
//! always inserts right after the first element (every insertion lands at the same place);
//! `append` inserts after the last inserted element; `front` inserts a new first element.

use om::baseline::Bender;
use om::Om;
use std::time::Instant;

enum S {
    Om(Om),
    B(Bender),
}

impl S {
    fn work(&self) -> u64 {
        match self { S::Om(o) => o.m.cost, S::B(b) => b.work }
    }
    fn insert_first(&mut self) -> u64 {
        match self { S::Om(o) => o.insert_first(), S::B(b) => b.insert_first() as u64 }
    }
    fn insert_after(&mut self, x: u64) -> u64 {
        match self { S::Om(o) => o.insert_after(x), S::B(b) => b.insert_after(x as u32) as u64 }
    }
}

/// One run: the time and work of every insertion after the first.
fn run(imp: &str, wl: &str, n: usize, times: &mut Vec<u32>, works: &mut Vec<u32>) {
    let mut seed: u64 = 0x9E3779B97F4A7C15 | 1;
    let mut rnd = move || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
    let mut s = match imp {
        "om" => S::Om(Om::new(4)),
        "bender" => S::B(Bender::new(1.4, n + 1)),
        _ => panic!("impl: om or bender"),
    };
    let mut live: Vec<u64> = Vec::with_capacity(n);
    let first = s.insert_first();
    live.push(first);
    times.clear();
    works.clear();
    while live.len() < n {
        let w0 = s.work();
        let t0 = Instant::now();
        let h = match wl {
            "random" => { let x = live[(rnd() % live.len() as u64) as usize]; s.insert_after(x) }
            "hammer" => s.insert_after(first),
            "append" => { let x = *live.last().unwrap(); s.insert_after(x) }
            "front" => s.insert_first(),
            _ => panic!("workload"),
        };
        let dt = t0.elapsed().as_nanos();
        times.push(dt.min(u32::MAX as u128) as u32);
        works.push((s.work() - w0).min(u32::MAX as u64) as u32);
        live.push(h);
    }
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let imp = a.get(1).expect("impl").clone();
    let wl = a.get(2).expect("workload").clone();
    let n: usize = a.get(3).map(|s| s.parse().unwrap()).unwrap_or(1_000_000);
    let reps: usize = a.get(4).map(|s| s.parse().unwrap()).unwrap_or(3);
    let mut best: Vec<u32> = Vec::new();
    let mut work: Vec<u32> = Vec::new();
    let mut means: Vec<Vec<f64>> = Vec::new();
    let mut times = Vec::with_capacity(n);
    let mut works = Vec::with_capacity(n);
    // decades of elements: operation k (0-based) makes k + 2 elements
    let mut bounds = vec![1usize];
    while *bounds.last().unwrap() < n { bounds.push((bounds.last().unwrap() * 10).min(n)); }
    for r in 0..reps {
        run(&imp, &wl, n, &mut times, &mut works);
        if r == 0 {
            best = times.clone();
            work = works.clone();
        } else {
            assert_eq!(work, works, "the work differs between runs");
            for (b, &t) in best.iter_mut().zip(times.iter()) { *b = (*b).min(t); }
        }
        means.push(bounds.windows(2).map(|w| {
            let ts = &times[w[0] - 1..w[1] - 1];
            ts.iter().map(|&t| t as f64).sum::<f64>() / ts.len() as f64
        }).collect());
    }
    for (d, w) in bounds.windows(2).enumerate() {
        let (from, to) = (w[0], w[1]);
        let ts = &best[from - 1..to - 1];
        let ws = &work[from - 1..to - 1];
        let k = ts.len();
        let mut run_means: Vec<f64> = means.iter().map(|m| m[d]).collect();
        run_means.sort_by(|x, y| x.partial_cmp(y).unwrap());
        let mean_t = run_means[run_means.len() / 2];
        let mean_w = ws.iter().map(|&w| w as f64).sum::<f64>() / k as f64;
        let max_w = *ws.iter().max().unwrap();
        let slowest = (0..k).max_by_key(|&i| ts[i]).unwrap();
        let mut sorted = ts.to_vec();
        sorted.sort_unstable();
        let pct = |p: f64| sorted[((k as f64 * p) as usize).min(k - 1)];
        println!("{imp},{wl},{from},{to},{k},{mean_t:.0},{},{},{},{mean_w:.1},{max_w},{}",
            pct(0.99), pct(0.9999), sorted[k - 1], ws[slowest]);
    }
}
