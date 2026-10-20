//! Which insertions take page faults: random insertion into a `Lean` of capacity CAP, and per
//! faulting insertion after the first N/10, whether it is heavy (more than 20 steps of work) and
//! how many groups, chunks and top nodes it allocated.
//!
//!     faults N [CAP]

use lean_design::lean::Lean;

#[repr(C)]
struct Rusage { ru_utime: [i64; 2], ru_stime: [i64; 2], r: [i64; 14] }
extern "C" { fn getrusage(who: i32, usage: *mut Rusage) -> i32; }

/// Page faults of this thread so far (ru_minflt + ru_majflt).
fn faults() -> i64 { let mut u: Rusage = unsafe { std::mem::zeroed() }; unsafe { getrusage(1, &mut u) }; u.r[4] + u.r[5] }

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let n: usize = a[1].parse().unwrap();
    let cap: usize = a.get(2).map(|s| s.parse().unwrap()).unwrap_or(n + 1);
    let mut s = Lean::new(cap, false);
    let mut seed: u64 = 0x9E3779B97F4A7C15 | 1;
    let mut rnd = move || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
    let first = s.insert_first();
    let mut live = vec![first];
    let (mut fo, mut tot) = (0u64, 0i64);
    let mut by_kind = std::collections::BTreeMap::new();
    while live.len() < n {
        let x = live[(rnd() % live.len() as u64) as usize];
        let (z0, w0, f0) = (s.sizes(), s.work, faults());
        let h = s.insert_after(x);
        let (f, z1, w) = (faults() - f0, s.sizes(), s.work - w0);
        live.push(h);
        if f > 0 && live.len() > n / 10 {
            fo += 1;
            tot += f;
            let kind = format!("groups +{} chunks +{} nodes +{}", z1[1] - z0[1], z1[2] - z0[2], z1[3] - z0[3]);
            *by_kind.entry((if w > 20 { "heavy" } else { "light" }, kind)).or_insert(0u64) += 1;
        }
    }
    println!("insertions with page faults after N/10: {fo} ({tot} faults)");
    for (k, v) in by_kind { println!("{v:>8} {} {}", k.0, k.1); }
}
