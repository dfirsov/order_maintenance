//! Deletion timings (`lean_design`, not verified): the native implementation of the verified
//! algorithm (`Native<Wide>`) against the two baselines, the AVL tree (`lean_design::avl`) and the
//! amortized algorithm (`om::baseline::Bender`).
//!
//!     deletes (native|avl|bender) (random|fifo) N [REPS]
//!
//! Three phases on one structure:
//! * build: N insertions (not reported);
//! * churn: N rounds of one deletion and one insertion, so the list keeps N elements while the
//!   native version keeps rebuilding to get rid of tombstones;
//! * drain: N deletions, down to the empty list (the native version rebuilds into smaller cores).
//!
//! `random` inserts after a uniformly random live element and deletes a uniformly random live
//! element. `fifo` is a queue: it inserts after the newest element and deletes the oldest.
//!
//! As in `compare`, the workload runs `REPS` times (default 3), each time on a fresh structure, the
//! time of each operation is the minimum over the runs, and its work must be the same in every
//! run. CSV rows, one per phase and operation:
//!
//!   impl,workload,phase,n,ops,mean_ns,p99_ns,p9999_ns,max_ns,mean_work,max_work,work_of_slowest
//!
//! With the environment variable `TAILS=PATH`, the statistics of each run on its own are also
//! appended to `PATH` (`lean_design::tails`); stdout is unchanged.

use lean_design::avl::Avl;
use lean_design::lean::{Native, Wide};
use om::baseline::Bender;
use std::collections::VecDeque;
use std::time::Instant;

enum S {
    B(Bender),
    A(Avl),
    N(Native<Wide>),
}

impl S {
    fn work(&self) -> u64 {
        match self { S::B(b) => b.work, S::A(t) => t.work, S::N(v) => v.work() }
    }
    fn insert_first(&mut self) -> u64 {
        match self { S::B(b) => b.insert_first() as u64, S::A(t) => t.insert_first() as u64, S::N(v) => v.insert_first() }
    }
    fn insert_after(&mut self, x: u64) -> u64 {
        match self { S::B(b) => b.insert_after(x as u32) as u64, S::A(t) => t.insert_after(x as u32) as u64, S::N(v) => v.insert_after(x) }
    }
    fn delete(&mut self, x: u64) {
        match self { S::B(b) => b.delete(x as u32), S::A(t) => t.delete(x as u32), S::N(v) => v.delete(x) }
    }
}

/// The live elements: a random one is removed by swapping with the last (`random`), the oldest
/// is removed first (`fifo`).
struct Live {
    fifo: bool,
    q: VecDeque<u64>,
}

impl Live {
    fn pick_delete(&mut self, rnd: &mut impl FnMut() -> u64) -> u64 {
        if self.fifo {
            self.q.pop_front().unwrap()
        } else {
            let i = (rnd() % self.q.len() as u64) as usize;
            self.q.swap_remove_back(i).unwrap()
        }
    }
    fn pick_insert(&self, rnd: &mut impl FnMut() -> u64) -> Option<u64> {
        if self.q.is_empty() {
            None
        } else if self.fifo {
            self.q.back().copied()
        } else {
            Some(self.q[(rnd() % self.q.len() as u64) as usize])
        }
    }
}

/// Times and work of the operations of one phase.
#[derive(Default, Clone)]
struct Phase {
    t: Vec<u32>,
    w: Vec<u32>,
}

fn timed<R>(s: &mut S, ph: &mut Phase, f: impl FnOnce(&mut S) -> R) -> R {
    let w0 = s.work();
    let t0 = Instant::now();
    let r = f(s);
    let dt = t0.elapsed().as_nanos();
    ph.t.push(dt.min(u32::MAX as u128) as u32);
    ph.w.push((s.work() - w0).min(u32::MAX as u64) as u32);
    r
}

/// One run: phases churn-delete, churn-insert, drain-delete.
fn run(imp: &str, wl: &str, n: usize) -> [Phase; 3] {
    let mut seed: u64 = 0x9E3779B97F4A7C15 | 1;
    let mut rnd = move || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
    let cap = 2 * n + 2;
    let mut s = match imp {
        "bender" => S::B(Bender::new(1.4, cap)),
        "avl" => S::A(Avl::new(cap)),
        "native" => S::N(Native::new(4, cap)),
        _ => panic!("impl: native, avl or bender"),
    };
    let mut live = Live { fifo: wl == "fifo", q: VecDeque::with_capacity(n + 1) };
    assert!(wl == "fifo" || wl == "random", "workload: random or fifo");
    let mut ph: [Phase; 3] = Default::default();
    for p in ph.iter_mut() {
        p.t.reserve(n);
        p.w.reserve(n);
    }
    let first = s.insert_first();
    live.q.push_back(first);
    while live.q.len() < n {
        let x = live.pick_insert(&mut rnd).unwrap();
        let h = s.insert_after(x);
        live.q.push_back(h);
    }
    for _ in 0..n {
        let x = live.pick_delete(&mut rnd);
        timed(&mut s, &mut ph[0], |s| s.delete(x));
        let y = live.pick_insert(&mut rnd);
        let h = timed(&mut s, &mut ph[1], |s| match y { Some(y) => s.insert_after(y), None => s.insert_first() });
        live.q.push_back(h);
    }
    while !live.q.is_empty() {
        let x = live.pick_delete(&mut rnd);
        timed(&mut s, &mut ph[2], |s| s.delete(x));
    }
    ph
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let imp = a.get(1).expect("impl").clone();
    let wl = a.get(2).expect("workload").clone();
    let n: usize = a.get(3).map(|s| s.parse().unwrap()).unwrap_or(1_000_000);
    let reps: usize = a.get(4).map(|s| s.parse().unwrap()).unwrap_or(3);
    let mut best: Option<[Phase; 3]> = None;
    let mut means: Vec<[f64; 3]> = Vec::new();
    const PHASES: [&str; 3] = ["churn-delete", "churn-insert", "drain-delete"];
    let mut tails = lean_design::tails::sink(&lean_design::tails::header("impl,workload,phase,n"));
    for r in 0..reps {
        let ph = run(&imp, &wl, n);
        if let Some(f) = tails.as_mut() {
            for (i, name) in PHASES.iter().enumerate() {
                lean_design::tails::row(f, &format!("{imp},{wl},{name},{n}"), &r.to_string(), &ph[i].t);
            }
        }
        let mean = |p: &Phase| p.t.iter().map(|&t| t as f64).sum::<f64>() / p.t.len().max(1) as f64;
        means.push([mean(&ph[0]), mean(&ph[1]), mean(&ph[2])]);
        match best.as_mut() {
            None => best = Some(ph),
            Some(b) => {
                for (bp, p) in b.iter_mut().zip(ph.iter()) {
                    assert_eq!(bp.w, p.w, "the work differs between runs");
                    for (x, &t) in bp.t.iter_mut().zip(p.t.iter()) { *x = (*x).min(t); }
                }
            }
        }
    }
    let best = best.unwrap();
    if let Some(f) = tails.as_mut() {
        for (i, name) in PHASES.iter().enumerate() {
            lean_design::tails::row(f, &format!("{imp},{wl},{name},{n}"), "min", &best[i].t);
        }
    }
    for (i, name) in ["churn-delete", "churn-insert", "drain-delete"].iter().enumerate() {
        let (ts, ws) = (&best[i].t, &best[i].w);
        let k = ts.len();
        let mut rm: Vec<f64> = means.iter().map(|m| m[i]).collect();
        rm.sort_by(|x, y| x.partial_cmp(y).unwrap());
        let mean_t = rm[rm.len() / 2];
        let mean_w = ws.iter().map(|&w| w as f64).sum::<f64>() / k as f64;
        let max_w = *ws.iter().max().unwrap();
        let slowest = (0..k).max_by_key(|&j| ts[j]).unwrap();
        let mut sorted = ts.clone();
        sorted.sort_unstable();
        let pct = |p: f64| sorted[((k as f64 * p) as usize).min(k - 1)];
        println!("{imp},{wl},{name},{n},{k},{mean_t:.0},{},{},{},{mean_w:.1},{max_w},{}",
            pct(0.99), pct(0.9999), sorted[k - 1], ws[slowest]);
    }
}
