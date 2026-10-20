//! The slowest operations of `Native<Wide>` under random insertion, with what happened in them
//! (diagnostic).
//!
//!     spikes N [TOP]
use lean_design::lean::{Native, Wide};
use std::time::Instant;
#[repr(C)]
struct Rusage { ru_utime: [i64; 2], ru_stime: [i64; 2], r: [i64; 14] }
extern "C" { fn getrusage(who: i32, usage: *mut Rusage) -> i32; }
/// (page faults, involuntary context switches) of this thread so far.
fn ru() -> (i64, i64) { let mut u: Rusage = unsafe { std::mem::zeroed() }; unsafe { getrusage(1, &mut u) }; (u.r[4] + 1000 * u.r[5], u.r[11]) }
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let n: usize = a[1].parse().unwrap();
    let top: usize = a.get(2).map(|s| s.parse().unwrap()).unwrap_or(15);
    let mut s: Native<Wide> = Native::new(4, n + 1);
    let mut seed: u64 = 0x9E3779B97F4A7C15 | 1;
    let mut rnd = move || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
    let first = s.insert_first();
    let mut live = vec![first];
    let mut ops: Vec<(u64, usize, String)> = Vec::new();
    while live.len() < n {
        let x = live[(rnd() % live.len() as u64) as usize];
        let (r0, g0, nx0, w0) = (s.rebuilds, s.retired(), s.nxt.is_some(), s.work());
        let r_0 = ru();
        let t0 = Instant::now();
        let h = s.insert_after(x);
        let dt = t0.elapsed().as_nanos() as u64;
        let r_1 = ru();
        let ev = format!("faults {} preempted {} work {} rebuild_start {} swap {} retired {}->{} cursor_set {}", r_1.0 - r_0.0, r_1.1 - r_0.1, s.work() - w0, s.rebuilds - r0,
            nx0 && s.nxt.is_none(), g0, s.retired(), s.cursor_set);
        ops.push((dt, live.len(), ev));
        live.push(h);
    }
    eprintln!("{}", std::fs::read_to_string("/proc/self/smaps_rollup").unwrap().lines().filter(|l| l.contains("Huge") || l.starts_with("Rss")).collect::<Vec<_>>().join(" / "));
    ops.sort_by(|a, b| b.0.cmp(&a.0));
    for (dt, k, ev) in ops.iter().take(top) { println!("{dt:>9} ns at {k:>8}: {ev}"); }
}
