//! Copy of `rust/src/bin/cold.rs` with the implementations `native`, `lean` and `lean-touch` of
//! `lean_design::lean` (not verified; see `compare.rs`).
//!
//! Per-operation time with cold caches: before each measured operation, a 128 MB buffer is read
//! (stride 64 bytes, 4 KB pages), which evicts the structure from the data caches (L2 3 MB per
//! core, L3 36 MB on the Core Ultra 9 285K) and from the TLBs. Instruction cache and branch
//! predictors are not flushed.
//!
//!     cold (om|bender|avl|lean|lean-touch|native) (random|hammer|append|front) N [C=500]
//!
//! The workload (as in `compare`) is deterministic. A first, warm run records the work of every
//! insertion. Per decade of the number of elements, the measured insertions are the `C` with the
//! most work plus `C` evenly spaced ones; after each evenly spaced insertion, one order query on a
//! random pair is also measured, cold and then again at once (warm). Two more runs, each on a
//! fresh structure, measure the selected operations cold; an operation's time is its minimum over
//! the runs in which it took no page fault, or over both runs if it faulted in both (allocation is
//! deterministic, so an operation that maps new memory does so in every run). CSV rows:
//!
//!   impl,workload,kind,from,to,ops,faulted,mean_ns,max_ns,work_of_slowest,max_work,max_ns_all,work_of_slowest_all
//!
//! `mean_ns`, `max_ns` and `work_of_slowest` are over the operations without page faults, the
//! `_all` columns over all of them.
//!
//! With the environment variable `TAILS=PATH`, the same statistics of each cold run on its own are
//! appended to `PATH` (rows `impl,workload,kind,from,to,ops,run,faulted,mean_ns,max_ns,max_ns_all`,
//! `run` = 0, 1 or `min`); stdout is unchanged.
//!
//! with `kind` one of `insert-top` (the `C` with the most work), `insert-sample`, `query-cold`,
//! `query-warm`, and a first row `noop-cold` (from = to = 0): 1000 empty operations measured cold,
//! the floor that eviction adds to any operation (the timer's page, the stack and the TLB).

use lean_design::avl::Avl;
use lean_design::lean::{Lean, Native, Wide};
use om::baseline::Bender;
use om::Om;
use std::time::Instant;

enum S {
    Om(Om),
    B(Bender),
    A(Avl),
    L(Lean),
    N(Native<Wide>),
}

impl S {
    fn new(imp: &str, n: usize) -> S {
        match imp {
            "om" => S::Om(Om::new(4)),
            "bender" => S::B(Bender::new(1.4, n + 1)),
            "avl" => S::A(Avl::new(n + 1)),
            "lean" => S::L(Lean::new(n + 1, false)),
            "lean-touch" => S::L(Lean::new(n + 1, true)),
            "native" => S::N(Native::new(4, n + 1)),
            _ => panic!("impl: om, bender, avl, lean, lean-touch or native"),
        }
    }
    fn work(&self) -> u64 {
        match self { S::Om(o) => o.m.cost, S::B(b) => b.work, S::A(t) => t.work, S::L(l) => l.work, S::N(v) => v.work() }
    }
    fn insert_first(&mut self) -> u64 {
        match self { S::Om(o) => o.insert_first(), S::B(b) => b.insert_first() as u64, S::A(t) => t.insert_first() as u64, S::L(l) => l.insert_first() as u64, S::N(v) => v.insert_first() }
    }
    fn insert_after(&mut self, x: u64) -> u64 {
        match self { S::Om(o) => o.insert_after(x), S::B(b) => b.insert_after(x as u32) as u64, S::A(t) => t.insert_after(x as u32) as u64, S::L(l) => l.insert_after(x as u32) as u64, S::N(v) => v.insert_after(x) }
    }
    fn order(&mut self, x: u64, y: u64) -> bool {
        match self { S::Om(o) => o.order(x, y), S::B(b) => b.order(x as u32, y as u32), S::A(t) => t.order(x as u32, y as u32), S::L(l) => l.order(x as u32, y as u32), S::N(v) => v.order(x, y) }
    }
}

#[repr(C)]
struct Rusage {
    ru_utime: [i64; 2], ru_stime: [i64; 2], ru_maxrss: i64, ru_ixrss: i64, ru_idrss: i64,
    ru_isrss: i64, ru_minflt: i64, ru_majflt: i64, ru_nswap: i64, ru_inblock: i64,
    ru_oublock: i64, ru_msgsnd: i64, ru_msgrcv: i64, ru_nsignals: i64, ru_nvcsw: i64, ru_nivcsw: i64,
}
extern "C" { fn getrusage(who: i32, usage: *mut Rusage) -> i32; }

/// Page faults of this thread so far.
fn faults() -> i64 {
    let mut u: Rusage = unsafe { std::mem::zeroed() };
    unsafe { getrusage(1, &mut u) }; // RUSAGE_THREAD
    u.ru_minflt + u.ru_majflt
}

const EVICT: usize = 128 << 20;

fn evict(buf: &[u8]) {
    let mut s = 0u64;
    let mut i = 0;
    while i < buf.len() { s = s.wrapping_add(unsafe { std::ptr::read_volatile(&buf[i]) } as u64); i += 64; }
    std::hint::black_box(s);
}

/// A measured operation: its time in ns, plus `FAULT` if it took a page fault (so that the
/// minimum over runs prefers a run without one).
fn timed<T>(buf: &[u8], cold: bool, f: impl FnOnce() -> T) -> (u64, T) {
    if cold { evict(buf); }
    let f0 = faults();
    let t0 = Instant::now();
    let r = std::hint::black_box(f());
    let dt = t0.elapsed().as_nanos().min(u32::MAX as u128) as u64;
    (if faults() == f0 { dt } else { dt | FAULT }, r)
}

const FAULT: u64 = 1 << 32;

/// One run. `sel[k]`: 0 not measured, 1 measured insertion, 2 measured insertion followed by a
/// measured query. Returns the work of every insertion and, per measured operation (in order),
/// its time as given by `timed`: insertions in `ins`, queries in `qc` (cold) and `qw` (warm),
/// with the query work in `qwork`.
fn run(imp: &str, wl: &str, n: usize, sel: &[u8], buf: &[u8], ins: &mut Vec<u64>, qc: &mut Vec<u64>,
       qw: &mut Vec<u64>, qwork: &mut Vec<u32>) -> Vec<u32> {
    let mut qseed: u64 = 0xD1B54A32D192ED03 | 1;
    let mut qrnd = move || { qseed ^= qseed << 13; qseed ^= qseed >> 7; qseed ^= qseed << 17; qseed };
    let mut seed: u64 = 0x9E3779B97F4A7C15 | 1;
    let mut rnd = move || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
    let mut s = S::new(imp, n);
    let mut live: Vec<u64> = Vec::with_capacity(n);
    let first = s.insert_first();
    live.push(first);
    let mut works = Vec::with_capacity(n);
    ins.clear(); qc.clear(); qw.clear(); qwork.clear();
    while live.len() < n {
        let k = live.len() - 1;
        let x = match wl {
            "random" => Some(live[(rnd() % live.len() as u64) as usize]),
            "hammer" => Some(first),
            "append" => Some(*live.last().unwrap()),
            "front" => None,
            _ => panic!("workload"),
        };
        let w0 = s.work();
        let m = sel.get(k).copied().unwrap_or(0);
        let (dt, h) = timed(buf, m > 0, || match x { Some(x) => s.insert_after(x), None => s.insert_first() });
        works.push((s.work() - w0) as u32);
        if m > 0 { ins.push(dt); }
        live.push(h);
        if m == 2 {
            let (a, b) = (live[(qrnd() % live.len() as u64) as usize], live[(qrnd() % live.len() as u64) as usize]);
            let w0 = s.work();
            let (c, _) = timed(buf, true, || s.order(a, b));
            qwork.push((s.work() - w0) as u32);
            let (w, _) = timed(buf, false, || s.order(a, b));
            qc.push(c);
            qw.push(w);
        }
    }
    works
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let imp = a.get(1).expect("impl").clone();
    let wl = a.get(2).expect("workload").clone();
    let n: usize = a.get(3).map(|s| s.parse().unwrap()).unwrap_or(1_000_000);
    let c: usize = a.get(4).map(|s| s.parse().unwrap()).unwrap_or(500);
    let buf = vec![1u8; EVICT];
    let mut bounds = vec![1usize];
    while *bounds.last().unwrap() < n { bounds.push((bounds.last().unwrap() * 10).min(n)); }
    let (mut ins, mut qc, mut qw, mut qwork) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
    let noop: Vec<u64> = (0..1000).map(|_| timed(&buf, true, || ()).0).filter(|&t| t < FAULT).collect();
    println!("{imp},{wl},noop-cold,0,0,{},{},{:.0},{},0,0,,", noop.len(), 1000 - noop.len(),
        noop.iter().map(|&t| t as f64).sum::<f64>() / noop.len() as f64, noop.iter().max().unwrap());

    // warm run: the work of every insertion (operation k makes k + 2 elements)
    let work = run(&imp, &wl, n, &[], &buf, &mut ins, &mut qc, &mut qw, &mut qwork);
    let mut sel = vec![0u8; n - 1];
    let mut top = vec![false; n - 1];
    for w in bounds.windows(2) {
        let (lo, hi) = (w[0] - 1, w[1] - 1);
        if hi <= lo { continue; }
        let mut idx: Vec<usize> = (lo..hi).collect();
        idx.sort_by_key(|&k| std::cmp::Reverse(work[k]));
        for &k in idx.iter().take(c) { sel[k] = 1; top[k] = true; }
        let step = ((hi - lo) / c).max(1);
        for k in (lo..hi).step_by(step) { sel[k] = 2; }
    }

    // two cold runs: per measured operation the minimum, preferring runs without a page fault
    let (mut bi, mut bc, mut bw) = (Vec::new(), Vec::new(), Vec::new());
    let mut per_run: Vec<(Vec<u64>, Vec<u64>, Vec<u64>)> = Vec::new();
    for r in 0..2 {
        let w = run(&imp, &wl, n, &sel, &buf, &mut ins, &mut qc, &mut qw, &mut qwork);
        assert_eq!(w, work, "the work differs between runs");
        per_run.push((ins.clone(), qc.clone(), qw.clone()));
        if r == 0 { bi = ins.clone(); bc = qc.clone(); bw = qw.clone(); } else {
            for (b, &t) in bi.iter_mut().zip(&ins) { *b = (*b).min(t); }
            for (b, &t) in bc.iter_mut().zip(&qc) { *b = (*b).min(t); }
            for (b, &t) in bw.iter_mut().zip(&qw) { *b = (*b).min(t); }
        }
    }

    // per decade: (kind, time, work) of the measured operations, in order
    let measured: Vec<usize> = (0..n - 1).filter(|&k| sel[k] > 0).collect();
    let queried: Vec<usize> = (0..n - 1).filter(|&k| sel[k] == 2).collect();
    for w in bounds.windows(2) {
        let (lo, hi) = (w[0] - 1, w[1] - 1);
        let inside = |k: usize| k >= lo && k < hi;
        let mut groups: Vec<(&str, Vec<(u64, u32)>)> = vec![("insert-top", vec![]), ("insert-sample", vec![])];
        for (i, &k) in measured.iter().enumerate() {
            if !inside(k) { continue; }
            if top[k] { groups[0].1.push((bi[i], work[k])); }
            if sel[k] == 2 { groups[1].1.push((bi[i], work[k])); }
        }
        let (mut cold, mut warm) = (vec![], vec![]);
        for (i, &k) in queried.iter().enumerate() {
            if inside(k) { cold.push((bc[i], qwork[i])); warm.push((bw[i], qwork[i])); }
        }
        groups.push(("query-cold", cold));
        groups.push(("query-warm", warm));
        for (kind, ops) in groups {
            if ops.is_empty() { continue; }
            let ok: Vec<&(u64, u32)> = ops.iter().filter(|o| o.0 < FAULT).collect();
            let faulted = ops.len() - ok.len();
            let max_work = ops.iter().map(|o| o.1).max().unwrap();
            let all = ops.iter().max_by_key(|o| o.0 & (FAULT - 1)).unwrap();
            let (mean, max, wslow) = if ok.is_empty() { (String::new(), String::new(), String::new()) } else {
                let slowest = ok.iter().max_by_key(|o| o.0).unwrap();
                (format!("{:.0}", ok.iter().map(|o| o.0 as f64).sum::<f64>() / ok.len() as f64),
                 slowest.0.to_string(), slowest.1.to_string())
            };
            println!("{imp},{wl},{kind},{},{},{},{faulted},{mean},{max},{wslow},{max_work},{},{}",
                w[0], w[1], ops.len(), all.0 & (FAULT - 1), all.1);
        }
    }

    // with TAILS=PATH: the same statistics for each cold run on its own (run 0, 1) and for the
    // minima (run `min`), without the work columns
    if let Ok(path) = std::env::var("TAILS") {
        use std::io::Write;
        let mut f = std::fs::OpenOptions::new().create(true).append(true).open(&path).expect("TAILS file");
        if f.metadata().map(|m| m.len() == 0).unwrap_or(true) {
            writeln!(f, "impl,workload,kind,from,to,ops,run,faulted,mean_ns,max_ns,max_ns_all").unwrap();
        }
        let mut sets: Vec<(String, &Vec<u64>, &Vec<u64>, &Vec<u64>)> =
            per_run.iter().enumerate().map(|(r, x)| (r.to_string(), &x.0, &x.1, &x.2)).collect();
        sets.push(("min".into(), &bi, &bc, &bw));
        for (run, ri, rc, rw) in sets {
            for w in bounds.windows(2) {
                let (lo, hi) = (w[0] - 1, w[1] - 1);
                let inside = |k: usize| k >= lo && k < hi;
                let mut groups: Vec<(&str, Vec<u64>)> = vec![("insert-top", vec![]), ("insert-sample", vec![]),
                    ("query-cold", vec![]), ("query-warm", vec![])];
                for (i, &k) in measured.iter().enumerate() {
                    if !inside(k) { continue; }
                    if top[k] { groups[0].1.push(ri[i]); }
                    if sel[k] == 2 { groups[1].1.push(ri[i]); }
                }
                for (i, &k) in queried.iter().enumerate() {
                    if inside(k) { groups[2].1.push(rc[i]); groups[3].1.push(rw[i]); }
                }
                for (kind, ops) in groups {
                    if ops.is_empty() { continue; }
                    let ok: Vec<u64> = ops.iter().copied().filter(|&t| t < FAULT).collect();
                    let all = ops.iter().map(|&t| t & (FAULT - 1)).max().unwrap();
                    let (mean, max) = if ok.is_empty() { (String::new(), String::new()) } else {
                        (format!("{:.0}", ok.iter().map(|&t| t as f64).sum::<f64>() / ok.len() as f64),
                         ok.iter().max().unwrap().to_string())
                    };
                    writeln!(f, "{imp},{wl},{kind},{},{},{},{run},{},{mean},{max},{all}",
                        w[0], w[1], ops.len(), ops.len() - ok.len()).unwrap();
                }
            }
        }
    }
}
