//! Where the slowest operations (in time) come from: random insertions up to `n` elements; per
//! decade, the five slowest operations with their machine steps, the page faults during them,
//! and the rebuild phase (as in `maxop`).
//!
//!     spikes N [seed]

use om::Om;
use std::time::Instant;

fn faults() -> (i64, i64) {
    let mut u: libc_rusage = unsafe { std::mem::zeroed() };
    unsafe { getrusage(0, &mut u) };
    (u.ru_minflt, u.ru_majflt)
}

#[repr(C)]
struct libc_rusage {
    ru_utime: [i64; 2], ru_stime: [i64; 2], ru_maxrss: i64, ru_ixrss: i64, ru_idrss: i64,
    ru_isrss: i64, ru_minflt: i64, ru_majflt: i64, ru_nswap: i64, ru_inblock: i64,
    ru_oublock: i64, ru_msgsnd: i64, ru_msgrcv: i64, ru_nsignals: i64, ru_nvcsw: i64, ru_nivcsw: i64,
}
extern "C" { fn getrusage(who: i32, usage: *mut libc_rusage) -> i32; }

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let n: usize = a.get(1).map(|s| s.parse().unwrap()).unwrap_or(1_000_000);
    let mut seed: u64 = a.get(2).map(|s| s.parse().unwrap()).unwrap_or(1) * 0x9E3779B97F4A7C15 | 1;
    let mut rnd = move || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
    let mut om = Om::new(4);
    let mut live: Vec<u64> = Vec::with_capacity(n);
    live.push(om.insert_first());
    let mut from = 1usize;
    while live.len() < n {
        let to = (from * 10).min(n);
        let mut top: Vec<(u128, u64, i64, &'static str, usize)> = Vec::new();
        while live.len() < to {
            let nxt0 = om.m.peek(2001, 0).as_u64();
            let cap0 = om.capacity();
            let (f0, _) = faults();
            let c0 = om.m.cost;
            let x = live[(rnd() % live.len() as u64) as usize];
            let t0 = Instant::now();
            let h = om.insert_after(x);
            let dt = t0.elapsed().as_nanos();
            let (f1, _) = faults();
            live.push(h);
            let nxt1 = om.m.peek(2001, 0).as_u64();
            let what = match (nxt0, nxt1, om.capacity() != cap0) {
                (_, _, true) => "swap", (0, 1, _) => "start", (1, 1, _) => "copy", _ => "-",
            };
            top.push((dt, om.m.cost - c0, f1 - f0, what, live.len()));
            if top.len() > 64 { top.sort_unstable_by(|a, b| b.0.cmp(&a.0)); top.truncate(5); }
        }
        top.sort_unstable_by(|a, b| b.0.cmp(&a.0));
        for (t, s, f, w, k) in top.iter().take(5) {
            println!("{from}-{to}: {t} ns, {s} steps, {f} page faults, {w}, n={k}");
        }
        from = to;
    }
}
