//! The slowest deletions of `Native<Wide>` in the churn and drain phases of `deletes` (diagnostic).
//!
//!     dspikes N [TOP] [random|fifo]
use lean_design::lean::{Native, Wide};
use std::time::Instant;
#[repr(C)]
struct Rusage { ru_utime: [i64; 2], ru_stime: [i64; 2], r: [i64; 14] }
extern "C" { fn getrusage(who: i32, usage: *mut Rusage) -> i32; }
fn ru() -> i64 { let mut u: Rusage = unsafe { std::mem::zeroed() }; unsafe { getrusage(1, &mut u) }; u.r[4] + 1000 * u.r[5] }
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let n: usize = a[1].parse().unwrap();
    let top: usize = a.get(2).map(|s| s.parse().unwrap()).unwrap_or(15);
    let fifo = a.get(3).is_some_and(|w| w == "fifo");
    // minimum over three runs per operation, events of the last run
    let mut best: Vec<(u64, usize, String)> = Vec::new();
    for _ in 0..3 {
        let ops = run(n, fifo);
        if best.is_empty() { best = ops; } else { for (b, o) in best.iter_mut().zip(ops) { *b = (b.0.min(o.0), o.1, o.2); } }
    }
    best.sort_by(|a, b| b.0.cmp(&a.0));
    for (dt, k, ev) in best.iter().take(top) { println!("{dt:>9} ns at {k:>8}: {ev}"); }
}

fn run(n: usize, fifo: bool) -> Vec<(u64, usize, String)> {
    let mut s: Native<Wide> = Native::new(4, 2 * n + 2);
    let mut seed: u64 = 0x9E3779B97F4A7C15 | 1;
    let mut rnd = move || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
    let mut live = std::collections::VecDeque::from([s.insert_first()]);
    while live.len() < n { let x = if fifo { live[live.len() - 1] } else { live[(rnd() % live.len() as u64) as usize] }; live.push_back(s.insert_after(x)); }
    let mut ops: Vec<(u64, usize, String)> = Vec::new();
    for phase in 0..2 {
        let rounds = n;
        for k in 0..rounds {
            if live.is_empty() { break; }
            let x = if fifo { live.pop_front().unwrap() } else { let i = (rnd() % live.len() as u64) as usize; live.swap_remove_back(i).unwrap() };
            let sp0 = s.spare_state(); let (r0, nx0, w0, f0, m0, c0) = (s.rebuilds, s.nxt.is_some(), s.work(), ru(), s.spare_misses, s.cursor_set);
            let t0 = Instant::now();
            s.delete(x);
            let dt = t0.elapsed().as_nanos() as u64;
            let ev = format!("{} faults {} work {} start {} swap {} miss {} cursor_set {}->{} action {} live {} cap {} prof {:?} spare {:?} retired {}", if phase == 0 { "churn" } else { "drain" },
                ru() - f0, s.work() - w0, s.rebuilds - r0, nx0 && s.nxt.is_none(), s.spare_misses - m0, c0, s.cursor_set, s.last_action, s.live, s.cur.p.n, prof(&s), sp0, s.retired());
            if std::env::var("TRACE").is_ok() && phase == 1 && (s.spare_state() != sp0 && (sp0.is_none() || s.spare_state().is_none()) || s.rebuilds != r0 || (nx0 && s.nxt.is_none())) {
                eprintln!("{k}: {} -> {:?}", ev, s.spare_state());
            }
            ops.push((dt, k, ev));
            if phase == 0 {
                let y = if live.is_empty() { s.insert_first() } else if fifo { s.insert_after(live[live.len() - 1]) } else { let y = live[(rnd() % live.len() as u64) as usize]; s.insert_after(y) };
                live.push_back(y);
            }
        }
    }
    ops
}

#[cfg(feature = "prof")]
fn prof(s: &Native<Wide>) -> [u64; 4] { s.prof }
#[cfg(not(feature = "prof"))]
fn prof(_: &Native<Wide>) -> [u64; 4] { [0; 4] }
