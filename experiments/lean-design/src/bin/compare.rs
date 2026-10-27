//! Copy of `rust/src/bin/compare.rs` with more implementations (`lean_design`, not verified):
//! `native`, the verified program's algorithm written natively (`Native<Wide>`); `lean`, the
//! `native-k1`, the same with the parameter profile K_R = 1 of `Lean` (`Params::for_capacity`), and
//! `native-k1-128`, also with 128-bit group labels; `core`, one core with the verified parameters
//! and label widths, of capacity 2N + 4 (no rebuilding: the verified program's core alone); `lean`, the fixed-capacity variant (`Lean`), and `lean-touch`, the same with all its memory mapped before
//! the run; `avl-touch`, the AVL baseline (`lean_design::avl`, a copy of `om::avl`) with its arrays
//! mapped before the run.
//!
//!     compare (om|bender|avl|avl-touch|lean|lean-touch|native|native-k1|native-k1-128|core) (random|hammer|append|front) N [REPS] [QPI]
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
//! With the environment variable `TAILS=PATH`, the statistics of each run on its own (maximum,
//! p99.9, p99.99, ...) are also appended to `PATH` (`lean_design::tails`); stdout is unchanged.
//!
//! `max_ns` and the percentiles are over the per-operation minima; `mean_ns` is the median over
//! the runs of each run's mean. `work` is machine steps for `om`, tags and labels written plus
//! groups scanned for `bender`, and nodes visited for `avl` (`om::avl`, the textbook O(log n)
//! balanced tree).
//!
//! Workloads (insertions only): `random` inserts after a uniformly random element; `hammer`
//! always inserts right after the first element (every insertion lands at the same place);
//! `append` inserts after the last inserted element; `front` inserts a new first element.
//!
//! Only the operation is timed: the element to insert after (and the pair to query) is chosen
//! before the timer starts, and the time and work are stored after it stops. (Until revision
//! 2026-10-27b the random choice of `random`, a random-number draw and a read of the vector of
//! live handles at a random index, was inside the timed interval; the operation sequence is
//! unchanged.) With the environment variable `SEED=k`, `random` uses another seed (see
//! `insertion_seed`); unset, the sequence is the published one.

use lean_design::avl::Avl;
use om::baseline::Bender;
use om::Om;
use lean_design::lean::{Core, Lean, Native, Params, Wide};
use std::time::Instant;

enum S {
    Om(Om),
    B(Bender),
    A(Avl),
    L(Lean),
    N(Native<Wide>),
    N1(Native<u128>),
    C(Core<Wide>),
}

impl S {
    fn work(&self) -> u64 {
        match self { S::Om(o) => o.m.cost, S::B(b) => b.work, S::A(t) => t.work, S::L(l) => l.work, S::N(v) => v.work(), S::N1(v) => v.work(), S::C(c) => c.work }
    }
    fn insert_first(&mut self) -> u64 {
        match self { S::Om(o) => o.insert_first(), S::B(b) => b.insert_first() as u64, S::A(t) => t.insert_first() as u64, S::L(l) => l.insert_first() as u64, S::N(v) => v.insert_first(), S::N1(v) => v.insert_first(), S::C(c) => c.insert_first() as u64 }
    }
    fn insert_after(&mut self, x: u64) -> u64 {
        match self { S::Om(o) => o.insert_after(x), S::B(b) => b.insert_after(x as u32) as u64, S::A(t) => t.insert_after(x as u32) as u64, S::L(l) => l.insert_after(x as u32) as u64, S::N(v) => v.insert_after(x), S::N1(v) => v.insert_after(x), S::C(c) => c.insert_after(x as u32) as u64 }
    }
    fn order(&mut self, x: u64, y: u64) -> bool {
        match self { S::Om(o) => o.order(x, y), S::B(b) => b.order(x as u32, y as u32), S::A(t) => t.order(x as u32, y as u32), S::L(l) => l.order(x as u32, y as u32), S::N(v) => v.order(x, y), S::N1(v) => v.order(x, y), S::C(c) => c.order(x as u32, y as u32) }
    }
}

#[derive(Clone, Copy)]
enum Wl { Random, Hammer, Append, Front }

/// The seed of the generator that picks the element to insert after (`random`): by default the
/// fixed seed of all published runs; with the environment variable `SEED=k` (k > 0), the
/// splitmix64 hash of k instead, a different but equally deterministic workload. `SEED` does not
/// change the query pairs.
fn insertion_seed() -> u64 {
    match std::env::var("SEED") {
        Err(_) => 0x9E3779B97F4A7C15 | 1,
        Ok(k) => {
            let k: u64 = k.parse().expect("SEED: a positive integer");
            assert!(k > 0, "SEED: a positive integer (unset for the default sequence)");
            let mut z = k.wrapping_add(0x9E3779B97F4A7C15);
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
            (z ^ (z >> 31)) | 1
        }
    }
}

/// One run: the time and work of every insertion after the first, and of every query.
fn run(imp: &str, wl: &str, n: usize, qpi: usize, times: &mut Vec<u32>, works: &mut Vec<u32>,
       qtimes: &mut Vec<u32>, qworks: &mut Vec<u32>) {
    let mut qseed: u64 = 0xD1B54A32D192ED03 | 1;
    let mut qrnd = move || { qseed ^= qseed << 13; qseed ^= qseed >> 7; qseed ^= qseed << 17; qseed };
    let mut seed: u64 = insertion_seed();
    let mut rnd = move || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
    let wl = match wl {
        "random" => Wl::Random,
        "hammer" => Wl::Hammer,
        "append" => Wl::Append,
        "front" => Wl::Front,
        _ => panic!("workload"),
    };
    let mut s = match imp {
        "om" => S::Om(Om::new(4)),
        "bender" => S::B(Bender::new(1.4, n + 1)),
        "avl" => S::A(Avl::new(n + 1)),
        "avl-touch" => S::A(Avl::new_touched(n + 1)),
        "lean" => S::L(Lean::new(n + 1, false)),
        "lean-touch" => S::L(Lean::new(n + 1, true)),
            "native" => S::N(Native::new(4, n + 1)),
        "native-k1" => S::N(Native::with_params(4, n + 1, Params::for_capacity)),
        "native-k1-128" => S::N1(Native::with_params(4, n + 1, Params::for_capacity)),
        "core" => S::C(Core::create(Params::verified(2 * n as u64 + 4), false, false)),
        _ => panic!("impl: om, bender, avl, avl-touch, lean, lean-touch, native, native-k1, native-k1-128 or core"),
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
        // the argument is chosen before the timed interval (revision 2026-10-27b: the random
        // choice, a read of `live` at a random index, used to be inside it)
        let x = match wl {
            Wl::Random => Some(live[(rnd() % live.len() as u64) as usize]),
            Wl::Hammer => Some(first),
            Wl::Append => Some(*live.last().unwrap()),
            Wl::Front => None,
        };
        let w0 = s.work();
        let t0 = Instant::now();
        let h = match x { Some(x) => s.insert_after(x), None => s.insert_first() };
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

/// With `TAILS=PATH`: per decade, the statistics of one run's times (or of the per-operation
/// minima, `run` = `min`) as rows of `PATH` (`lean_design::tails`).
fn tail_rows(f: &mut std::fs::File, imp: &str, wl: &str, bounds: &[usize], per: usize, ts: &[u32], run: &str) {
    for w in bounds.windows(2) {
        let (from, to) = (w[0], w[1]);
        lean_design::tails::row(f, &format!("{imp},{wl},{from},{to}"), run, &ts[(from - 1) * per..(to - 1) * per]);
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
    let mut tails = lean_design::tails::sink(&lean_design::tails::header("impl,workload,from,to"));
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
        if let Some(f) = tails.as_mut() {
            let r = r.to_string();
            tail_rows(f, &imp, &wl, &bounds, 1, &times, &r);
            if qpi > 0 { tail_rows(f, &imp, &format!("query-{wl}"), &bounds, qpi, &qtimes, &r); }
        }
    }
    if let Some(f) = tails.as_mut() {
        tail_rows(f, &imp, &wl, &bounds, 1, &best, "min");
        if qpi > 0 { tail_rows(f, &imp, &format!("query-{wl}"), &bounds, qpi, &qbest, "min"); }
    }
    report(&imp, &wl, &bounds, 1, &best, &work, &means);
    if qpi > 0 {
        report(&imp, &format!("query-{wl}"), &bounds, qpi, &qbest, &qwork, &qmeans);
    }
}
