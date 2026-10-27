//! Diagnostic (paper revision 2026-10-27): the latency of first touches of fresh anonymous pages,
//! with no order-maintenance structure at all.
//!
//!     pagetouch GB [REPS=3]
//!
//! Each run reserves `GB` GiB (`Vec::with_capacity`, mapped lazily by the system), then writes one
//! byte to each 4 KB page in order, timing every write (so every timed write takes one page
//! fault), and also times as many empty operations (two clock reads) in between. Per run, one
//! CSV row: run,pages,mean_ns,p99_ns,p9999_ns,max_ns,n_over_10us,n_over_100us,n_over_1ms,
//! empty_max_ns,empty_n_over_100us,minflt,majflt (page faults of the run, `getrusage`).

use std::time::Instant;

#[repr(C)]
struct Rusage {
    ru_utime: [i64; 2], ru_stime: [i64; 2], ru_maxrss: i64, ru_ixrss: i64, ru_idrss: i64,
    ru_isrss: i64, ru_minflt: i64, ru_majflt: i64, ru_nswap: i64, ru_inblock: i64,
    ru_oublock: i64, ru_msgsnd: i64, ru_msgrcv: i64, ru_nsignals: i64, ru_nvcsw: i64, ru_nivcsw: i64,
}
extern "C" { fn getrusage(who: i32, usage: *mut Rusage) -> i32; }

fn faults() -> (i64, i64) {
    let mut u: Rusage = unsafe { std::mem::zeroed() };
    unsafe { getrusage(1, &mut u) };
    (u.ru_minflt, u.ru_majflt)
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let gb: f64 = a.get(1).map(|s| s.parse().unwrap()).unwrap_or(1.0);
    let reps: usize = a.get(2).map(|s| s.parse().unwrap()).unwrap_or(3);
    let bytes = (gb * (1u64 << 30) as f64) as usize;
    let pages = bytes / 4096;
    println!("run,pages,mean_ns,p99_ns,p9999_ns,max_ns,n_over_10us,n_over_100us,n_over_1ms,empty_max_ns,empty_n_over_100us,minflt,majflt");
    let mut ts = vec![0u32; pages];
    let mut es = vec![0u32; pages];
    for r in 0..reps {
        let mut v: Vec<u8> = Vec::with_capacity(bytes);
        let p = v.as_mut_ptr();
        let f0 = faults();
        for i in 0..pages {
            let t0 = Instant::now();
            unsafe { std::ptr::write_volatile(p.add(i * 4096), 1) };
            ts[i] = t0.elapsed().as_nanos().min(u32::MAX as u128) as u32;
            let t0 = Instant::now();
            es[i] = t0.elapsed().as_nanos().min(u32::MAX as u128) as u32;
        }
        let f1 = faults();
        let mean = ts.iter().map(|&t| t as f64).sum::<f64>() / pages as f64;
        let mut s = ts.clone();
        s.sort_unstable();
        let pct = |q: f64| s[((pages as f64 * q) as usize).min(pages - 1)];
        let over = |t: u32| s.len() - s.partition_point(|&x| x <= t);
        let emax = *es.iter().max().unwrap();
        let eover = es.iter().filter(|&&x| x > 100_000).count();
        println!("{r},{pages},{mean:.0},{},{},{},{},{},{},{emax},{eover},{},{}", pct(0.99), pct(0.9999), s[pages - 1],
            over(10_000), over(100_000), over(1_000_000), f1.0 - f0.0, f1.1 - f0.1);
        drop(v);
    }
}
