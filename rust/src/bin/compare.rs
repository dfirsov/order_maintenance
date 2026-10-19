//! Per-operation time of the verified structure and of the amortized baseline (`om::baseline`),
//! on the same workloads.
//!
//!     compare (om|bender|avl) (random|hammer|append|front) N [REPS] [QPI]
//!
//! With `QPI` > 0, every insertion is followed by `QPI` order queries on uniformly random pairs of
//! elements, timed separately and reported in rows whose workload is `query-` and the workload.
//! The workload runs `REPS` times (default 3), each time on a fresh structure. The workloads are
//! deterministic, so the k-th operation is the same in every run: its time is the minimum over
//! the runs (noise from the machine rarely hits the same operation in every run), and its work
//! must be the same in every run. Statistics per decade of the number of elements, as CSV rows:
//!
//!   impl,workload,from,to,ops,mean_ns,p99_ns,p9999_ns,max_ns,mean_work,max_work,work_of_slowest
//!
//! `max_ns` and the percentiles are over the per-operation minima; `mean_ns` is the median over
//! the runs of each run's mean. `work` is machine steps for `om`, tags and labels written plus
//! groups scanned for `bender`, and nodes visited for `avl` (`om::avl`, the textbook O(log n)
//! balanced tree).
//!
//! Workloads (insertions only): `random` inserts after a uniformly random element; `hammer`
//! always inserts right after the first element (every insertion lands at the same place);
//! `append` inserts after the last inserted element; `front` inserts a new first element.

use om::avl::Avl;
use om::baseline::Bender;
use om::Om;
use std::time::Instant;

enum S {
    Om(Om),
    B(Bender),
    A(Avl),
}

impl S {
    fn work(&self) -> u64 {
        match self { S::Om(o) => o.m.cost, S::B(b) => b.work, S::A(t) => t.work }
    }
    fn insert_first(&mut self) -> u64 {
        match self { S::Om(o) => o.insert_first(), S::B(b) => b.insert_first() as u64, S::A(t) => t.insert_first() as u64 }
    }
    fn insert_after(&mut self, x: u64) -> u64 {
        match self { S::Om(o) => o.insert_after(x), S::B(b) => b.insert_after(x as u32) as u64, S::A(t) => t.insert_after(x as u32) as u64 }
    }
    fn order(&mut self, x: u64, y: u64) -> bool {
        match self { S::Om(o) => o.order(x, y), S::B(b) => b.order(x as u32, y as u32), S::A(t) => t.order(x as u32, y as u32) }
    }
}

/// One run: the time and work of every insertion after the first, and of every query.
fn run(imp: &str, wl: &str, n: usize, qpi: usize, times: &mut Vec<u32>, works: &mut Vec<u32>,
       qtimes: &mut Vec<u32>, qworks: &mut Vec<u32>) {
    let mut qseed: u64 = 0xD1B54A32D192ED03 | 1;
    let mut qrnd = move || { qseed ^= qseed << 13; qseed ^= qseed >> 7; qseed ^= qseed << 17; qseed };
    let mut seed: u64 = 0x9E3779B97F4A7C15 | 1;
    let mut rnd = move || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
    let mut s = match imp {
        "om" => S::Om(Om::new(4)),
        "bender" => S::B(Bender::new(1.4, n + 1)),
        "avl" => S::A(Avl::new(n + 1)),
        _ => panic!("impl: om, bender or avl"),
    };
    let mut live: Vec<u64> = Vec::with_capacity(n);
    let first = s.insert_first();
    live.push(first);
    times.clear();
    works.clear();
    qtimes.clear();
    qworks.clear();
    let mut sink = 0u64;
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
        for _ in 0..qpi {
            let (x, y) = (live[(qrnd() % live.len() as u64) as usize], live[(qrnd() % live.len() as u64) as usize]);
            let w0 = s.work();
            let t0 = Instant::now();
            let b = s.order(x, y);
            let dt = t0.elapsed().as_nanos();
            sink += b as u64;
            qtimes.push(dt.min(u32::MAX as u128) as u32);
            qworks.push((s.work() - w0).min(u32::MAX as u64) as u32);
        }
    }
    std::hint::black_box(sink);
}

/// Per decade of elements (operation k makes k + 2 elements; with queries, the k-th insertion's
/// queries are `k*qpi .. (k+1)*qpi`), print the statistics of `best` (per-operation minima).
fn report(imp: &str, wl: &str, bounds: &[usize], per: usize, best: &[u32], work: &[u32], means: &[Vec<f64>]) {
    for (d, w) in bounds.windows(2).enumerate() {
        let (from, to) = (w[0], w[1]);
        let ts = &best[(from - 1) * per..(to - 1) * per];
        let ws = &work[(from - 1) * per..(to - 1) * per];
        let k = ts.len();
        if k == 0 { continue; }
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

fn decade_means(bounds: &[usize], per: usize, times: &[u32]) -> Vec<f64> {
    bounds.windows(2).map(|w| {
        let ts = &times[(w[0] - 1) * per..(w[1] - 1) * per];
        if ts.is_empty() { 0.0 } else { ts.iter().map(|&t| t as f64).sum::<f64>() / ts.len() as f64 }
    }).collect()
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let imp = a.get(1).expect("impl").clone();
    let wl = a.get(2).expect("workload").clone();
    let n: usize = a.get(3).map(|s| s.parse().unwrap()).unwrap_or(1_000_000);
    let reps: usize = a.get(4).map(|s| s.parse().unwrap()).unwrap_or(3);
    let qpi: usize = a.get(5).map(|s| s.parse().unwrap()).unwrap_or(0);
    let (mut best, mut work, mut qbest, mut qwork) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
    let (mut means, mut qmeans): (Vec<Vec<f64>>, Vec<Vec<f64>>) = (Vec::new(), Vec::new());
    let (mut times, mut works) = (Vec::with_capacity(n), Vec::with_capacity(n));
    let (mut qtimes, mut qworks) = (Vec::with_capacity(n * qpi), Vec::with_capacity(n * qpi));
    // decades of elements: operation k (0-based) makes k + 2 elements
    let mut bounds = vec![1usize];
    while *bounds.last().unwrap() < n { bounds.push((bounds.last().unwrap() * 10).min(n)); }
    for r in 0..reps {
        run(&imp, &wl, n, qpi, &mut times, &mut works, &mut qtimes, &mut qworks);
        if r == 0 {
            best = times.clone();
            work = works.clone();
            qbest = qtimes.clone();
            qwork = qworks.clone();
        } else {
            assert_eq!(work, works, "the work differs between runs");
            assert_eq!(qwork, qworks, "the query work differs between runs");
            for (b, &t) in best.iter_mut().zip(times.iter()) { *b = (*b).min(t); }
            for (b, &t) in qbest.iter_mut().zip(qtimes.iter()) { *b = (*b).min(t); }
        }
        means.push(decade_means(&bounds, 1, &times));
        qmeans.push(decade_means(&bounds, qpi, &qtimes));
    }
    report(&imp, &wl, &bounds, 1, &best, &work, &means);
    if qpi > 0 {
        report(&imp, &format!("query-{wl}"), &bounds, qpi, &qbest, &qwork, &qmeans);
    }
}
