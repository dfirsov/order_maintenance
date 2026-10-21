//! Where the native implementation's memory goes (`lean_design`, diagnostic, not verified).
//!
//!     membreak (random|churn) N [SAMPLES]
//!
//! Runs the workload of `mem` on `Native<Wide>` and, `SAMPLES` times per phase (default 400),
//! counts the resident pages of each part with `mincore`: the arrays of the current core and of
//! the core being built, the retired cores, the spare mapping and the handles. Prints the sample
//! with the most resident memory, per phase, next to the process's peak (VmHWM). Bytes are per
//! element (divided by the largest number of elements so far); `used` counts the records in use,
//! `resident` the mapped pages.

use lean_design::lean::{Core, Native, Wide};

fn status() -> (u64, u64) {
    let s = std::fs::read_to_string("/proc/self/status").unwrap();
    let get = |k: &str| -> u64 {
        let l = s.lines().find(|l| l.starts_with(k)).unwrap();
        l.split_whitespace().nth(1).unwrap().parse::<u64>().unwrap() * 1024
    };
    (get("VmRSS:"), get("VmHWM:"))
}

struct Sample {
    total: usize,
    parts: Vec<(String, usize, usize)>,
    at: String,
}

fn sample(v: &Native<Wide>, at: String) -> Sample {
    let parts = v.mem_parts();
    Sample { total: parts.iter().map(|p| p.2).sum(), parts, at }
}

fn print(phase: &str, s: &Sample, most: usize, base: u64) {
    let (_, hwm) = status();
    let pe = |b: usize| b as f64 / most as f64;
    println!("== {phase}: largest sample {:.1} B/element at {}; process peak so far {:.1} B/element",
        pe(s.total), s.at, pe(hwm.saturating_sub(base) as usize));
    // group the arrays of each core; print nonzero parts
    for (name, used, res) in &s.parts {
        if *res > 0 || *used > 0 {
            println!("  {name:<14} used {:>7.2}  resident {:>7.2}", pe(*used), pe(*res));
        }
    }
    for core in ["cur", "nxt"] {
        let r: usize = s.parts.iter().filter(|p| p.0.starts_with(core)).map(|p| p.2).sum();
        let u: usize = s.parts.iter().filter(|p| p.0.starts_with(core)).map(|p| p.1).sum();
        println!("  {core} total      used {:>7.2}  resident {:>7.2}", pe(u), pe(r));
    }
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let wl = a.get(1).expect("workload").clone();
    let n: usize = a.get(2).map(|s| s.parse().unwrap()).unwrap_or(10_000_000);
    let k: usize = a.get(3).map(|s| s.parse().unwrap()).unwrap_or(400);
    let mut seed: u64 = 0x9E3779B97F4A7C15 | 1;
    let mut rnd = move || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
    let mut live: Vec<u64> = vec![1; n + 1];
    live.clear();
    std::fs::write("/proc/self/clear_refs", "5").unwrap();
    let (base, _) = status();
    let mut v = Native::<Wide>::new(4, 2 * n + 2);
    println!("record sizes (element, group, chunk, top node): {:?} bytes; handle record 12",
        Core::<Wide>::record_sizes());
    let every = (n / k).max(1);
    let mut best = Sample { total: 0, parts: vec![], at: String::new() };
    let keep = |v: &Native<Wide>, at: String, best: &mut Sample| {
        let s = sample(v, at);
        if s.total > best.total { *best = s; }
    };
    live.push(v.insert_first());
    while live.len() < n {
        let x = live[(rnd() % live.len() as u64) as usize];
        live.push(v.insert_after(x));
        if live.len() % every == 0 {
            keep(&v, format!("{} elements (cap {}, building {:?})", live.len(), v.cur.p.n, v.nxt.as_ref().map(|c| c.p.n)), &mut best);
        }
    }
    print("insertions", &best, n, base);
    let s = sample(&v, "end".into());
    print("after insertions", &s, n, base);
    if wl != "churn" {
        return;
    }
    best = Sample { total: 0, parts: vec![], at: String::new() };
    for i in 0..n {
        let j = (rnd() % live.len() as u64) as usize;
        let x = live.swap_remove(j);
        v.delete(x);
        let y = live[(rnd() % live.len() as u64) as usize];
        live.push(v.insert_after(y));
        if i % every == 0 {
            keep(&v, format!("churn round {i} (cap {}, building {:?}, retired {})", v.cur.p.n, v.nxt.as_ref().map(|c| c.p.n), v.retired()), &mut best);
        }
    }
    print("churn", &best, n, base);
    best = Sample { total: 0, parts: vec![], at: String::new() };
    let mut i = 0;
    while let Some(x) = live.pop() {
        v.delete(x);
        i += 1;
        if i % every == 0 {
            keep(&v, format!("{} left (cap {}, building {:?}, retired {})", live.len(), v.cur.p.n, v.nxt.as_ref().map(|c| c.p.n), v.retired()), &mut best);
        }
    }
    print("drain", &best, n, base);
}
