//! A long history on a small list (`lean_design`, not verified; added for the paper revision of
//! 2026-10-27): the list keeps `N` elements while the number of operations grows large.
//!
//!     longrun (native|avl|bender) N OPS [WINDOWS=100]
//!
//! First `N` insertions after uniformly random live elements (not timed). Then `OPS` operations,
//! alternately a deletion of a uniformly random live element and an insertion after a uniformly
//! random live element, so the list keeps `N` elements, while every insertion takes a fresh handle
//! (no implementation reuses handles, so the handle maps grow with the number of insertions).
//!
//! One run, no minimum over runs: every time is a single measurement. The operations are split
//! into `WINDOWS` consecutive windows; after each window (outside the timed operations) one CSV row
//! is printed:
//!
//!   impl,n,window,ops_done,handles,del_mean_ns,del_p9999_ns,del_max_ns,ins_mean_ns,ins_p9999_ns,
//!   ins_max_ns,mean_ns,max_ns,rss_bytes,hwm_bytes,rebuilds,retired_cores,cores_res,retired_res,
//!   spare_res,handles_res,wall_s
//!
//! `rss_bytes` / `hwm_bytes` are `VmRSS` / `VmHWM` of `/proc/self/status` at the end of the window.
//! For `native` the last columns break its memory down with `mincore` (`Native::mem_parts`):
//! resident bytes of the cores in use (current and, during a rebuild, the next), of the retired
//! cores kept for reuse, of the spare mapping and of the handle records; `rebuilds` and
//! `retired_cores` are counters. For the baselines these columns are empty.

use lean_design::avl::Avl;
use lean_design::lean::{Native, Wide};
use om::baseline::Bender;
use std::time::Instant;

enum S {
    B(Bender),
    A(Avl),
    N(Native<Wide>),
}

impl S {
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

/// (VmRSS, VmHWM) in bytes.
fn status() -> (u64, u64) {
    let s = std::fs::read_to_string("/proc/self/status").unwrap();
    let get = |k: &str| s.lines().find(|l| l.starts_with(k)).and_then(|l| l.split_whitespace().nth(1))
        .map(|v| v.parse::<u64>().unwrap() * 1024).unwrap_or(0);
    (get("VmRSS:"), get("VmHWM:"))
}

fn stats(ts: &mut [u32]) -> (f64, u32, u32) {
    let k = ts.len();
    let mean = ts.iter().map(|&t| t as f64).sum::<f64>() / k as f64;
    ts.sort_unstable();
    (mean, ts[((k as f64 * 0.9999) as usize).min(k - 1)], ts[k - 1])
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let imp = a.get(1).expect("impl").clone();
    let n: usize = a.get(2).map(|s| s.parse().unwrap()).unwrap_or(1000);
    let ops: usize = a.get(3).map(|s| s.parse().unwrap()).unwrap_or(100_000_000);
    let windows: usize = a.get(4).map(|s| s.parse().unwrap()).unwrap_or(100);
    let rounds = ops / 2;
    let per = rounds / windows; // rounds per window
    assert!(per > 0);
    let cap = n + rounds + 2;
    let mut s = match imp.as_str() {
        "bender" => S::B(Bender::new(1.4, cap)),
        "avl" => S::A(Avl::new(cap)),
        "native" => S::N(Native::new(4, cap)),
        _ => panic!("impl: native, avl or bender"),
    };
    let mut seed: u64 = 0x9E3779B97F4A7C15 | 1;
    let mut rnd = move || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
    let mut live: Vec<u64> = Vec::with_capacity(n + 1);
    live.push(s.insert_first());
    let mut handles: u64 = 1;
    while live.len() < n {
        let x = live[(rnd() % live.len() as u64) as usize];
        live.push(s.insert_after(x));
        handles += 1;
    }
    println!("impl,n,window,ops_done,handles,del_mean_ns,del_p9999_ns,del_max_ns,ins_mean_ns,ins_p9999_ns,ins_max_ns,mean_ns,max_ns,rss_bytes,hwm_bytes,rebuilds,retired_cores,cores_res,retired_res,spare_res,handles_res,wall_s");
    let (mut dt, mut it) = (vec![0u32; per], vec![0u32; per]);
    let wall = Instant::now();
    for w in 0..windows {
        for j in 0..per {
            let i = (rnd() % live.len() as u64) as usize;
            let x = live.swap_remove(i);
            let t0 = Instant::now();
            s.delete(x);
            dt[j] = t0.elapsed().as_nanos().min(u32::MAX as u128) as u32;
            let y = live[(rnd() % live.len() as u64) as usize];
            let t0 = Instant::now();
            let h = s.insert_after(y);
            it[j] = t0.elapsed().as_nanos().min(u32::MAX as u128) as u32;
            live.push(h);
        }
        handles += per as u64;
        let (dm, dp, dx) = stats(&mut dt);
        let (im, ip, ix) = stats(&mut it);
        let (rss, hwm) = status();
        let extra = match &s {
            S::N(v) => {
                let parts = v.mem_parts();
                let sum = |f: &dyn Fn(&str) -> bool| parts.iter().filter(|p| f(&p.0)).map(|p| p.2).sum::<usize>();
                format!("{},{},{},{},{},{}", v.rebuilds, v.retired(),
                    sum(&|p| p.starts_with("cur.") || p.starts_with("nxt.")), sum(&|p| p.starts_with("retired")),
                    sum(&|p| p == "spare"), sum(&|p| p == "handles"))
            }
            _ => ",,,,,".to_string(),
        };
        println!("{imp},{n},{w},{},{handles},{dm:.0},{dp},{dx},{im:.0},{ip},{ix},{:.0},{},{rss},{hwm},{extra},{:.1}",
            2 * per * (w + 1), (dm + im) / 2.0, dx.max(ix), wall.elapsed().as_secs_f64());
    }
}
