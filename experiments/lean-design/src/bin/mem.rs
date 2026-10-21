//! Memory use (`lean_design`, not verified): resident memory of one structure, from
//! `/proc/self/status`, after each decade of insertions and after the deletion phases.
//!
//!     mem (native|core|avl|bender) (random|hammer|churn|fifo) N
//!
//! `random` and `hammer` insert as in `compare`. `churn` and `fifo` run the phases of `deletes`:
//! N insertions, N rounds of one deletion and one insertion, then deletions down to the empty
//! list (`core` only inserts). The harness's own list of live elements is written before the
//! structure is created and the peak is reset then, so the rows count the structure only. CSV:
//!
//!   impl,workload,point,elements,rss_bytes,peak_bytes,peak_per_element
//!
//! `peak_bytes` is the largest resident size since the structure was created; `peak_per_element`
//! divides it by the largest number of elements so far.

use lean_design::avl::Avl;
use lean_design::lean::{Core, Native, Params, Wide};
use om::baseline::Bender;

enum S {
    B(Bender),
    A(Avl),
    N(Native<Wide>),
    C(Core<Wide>),
}

impl S {
    fn insert_first(&mut self) -> u64 {
        match self { S::B(b) => b.insert_first() as u64, S::A(t) => t.insert_first() as u64, S::N(v) => v.insert_first(), S::C(c) => c.insert_first() as u64 }
    }
    fn insert_after(&mut self, x: u64) -> u64 {
        match self { S::B(b) => b.insert_after(x as u32) as u64, S::A(t) => t.insert_after(x as u32) as u64, S::N(v) => v.insert_after(x), S::C(c) => c.insert_after(x as u32) as u64 }
    }
    fn delete(&mut self, x: u64) {
        match self { S::B(b) => b.delete(x as u32), S::A(t) => t.delete(x as u32), S::N(v) => v.delete(x), S::C(_) => panic!("core: insertions only") }
    }
}

/// Deletes one live element from the ring (the oldest for `fifo`, else a random one, replaced by
/// the last) and returns where the next insertion goes (`None`: the list is empty).
fn del(s: &mut S, ring: &mut [u64], head: &mut usize, len: &mut usize, fifo: bool, rnd: &mut impl FnMut() -> u64) -> Option<u64> {
    let m = ring.len() - 1;
    let i = if fifo { 0 } else { (rnd() % *len as u64) as usize };
    let slot = (*head + i) & m;
    let x = ring[slot];
    if fifo {
        *head = (*head + 1) & m;
    } else {
        ring[slot] = ring[(*head + *len - 1) & m];
    }
    *len -= 1;
    s.delete(x);
    if *len == 0 {
        None
    } else if fifo {
        Some(ring[(*head + *len - 1) & m])
    } else {
        Some(ring[(*head + (rnd() % *len as u64) as usize) & m])
    }
}

/// (VmRSS, VmHWM) in bytes.
fn status() -> (u64, u64) {
    let s = std::fs::read_to_string("/proc/self/status").unwrap();
    let get = |k: &str| -> u64 {
        let l = s.lines().find(|l| l.starts_with(k)).unwrap();
        l.split_whitespace().nth(1).unwrap().parse::<u64>().unwrap() * 1024
    };
    (get("VmRSS:"), get("VmHWM:"))
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let imp = a.get(1).expect("impl").clone();
    let wl = a.get(2).expect("workload").clone();
    let n: usize = a.get(3).map(|s| s.parse().unwrap()).unwrap_or(1_000_000);
    let mut seed: u64 = 0x9E3779B97F4A7C15 | 1;
    let mut rnd = move || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
    // the live elements as a ring buffer of 2^k slots, all written before measuring
    let size = (n + 1).next_power_of_two();
    let mut ring = vec![1u64; size];
    let mut head = 0usize;
    std::fs::write("/proc/self/clear_refs", "5").unwrap();
    let (base, _) = status();
    let cap = 2 * n + 2;
    let mut s = match imp.as_str() {
        "bender" => S::B(Bender::new(1.4, cap)),
        "avl" => S::A(Avl::new(cap)),
        "native" => S::N(Native::new(4, cap)),
        "core" => S::C(Core::create(Params::verified(2 * n as u64 + 4), false, false)),
        _ => panic!("impl: native, core, avl or bender"),
    };
    let mut most = 1usize;
    let report = |point: &str, elems: usize, most: usize| {
        let (rss, hwm) = status();
        let (r, h) = (rss.saturating_sub(base), hwm.saturating_sub(base));
        println!("{imp},{wl},{point},{elems},{r},{h},{:.1}", h as f64 / most as f64);
    };
    let first = s.insert_first();
    ring[0] = first;
    let mut len = 1usize;
    let fifo = wl == "fifo";
    let mut next_decade = 10;
    while len < n {
        let x = match wl.as_str() {
            "hammer" => first,
            "fifo" => ring[(head + len - 1) & (size - 1)],
            "random" | "churn" => ring[(head + (rnd() % len as u64) as usize) & (size - 1)],
            _ => panic!("workload: random, hammer, churn or fifo"),
        };
        let h = s.insert_after(x);
        ring[(head + len) & (size - 1)] = h;
        len += 1;
        most = len;
        if len == next_decade || len == n {
            report("insert", len, most);
            next_decade *= 10;
        }
    }
    if wl != "churn" && wl != "fifo" {
        return;
    }
    for _ in 0..n {
        let y = del(&mut s, &mut ring, &mut head, &mut len, fifo, &mut rnd);
        let h = match y { Some(y) => s.insert_after(y), None => s.insert_first() };
        ring[(head + len) & (size - 1)] = h;
        len += 1;
    }
    report("churn", len, most);
    while len > 0 {
        del(&mut s, &mut ring, &mut head, &mut len, fifo, &mut rnd);
        if len == n / 10 || len == n / 100 {
            report("drain", len, most);
        }
    }
    report("drain", 0, most);
}
