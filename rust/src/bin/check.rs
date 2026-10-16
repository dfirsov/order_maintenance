//! Random operation sequences against a plain list implementation of the specification
//! (`lean/OM/Spec.lean`). Prints the steps per operation (maximum and mean), the peak bit
//! length, and the memory.
//!
//! Usage: `check [ops] [seed] [mode]`; mode `grow` (mostly insertions), `mix`, or `churn`
//! (insertions and deletions balanced, so the structure grows and shrinks).

use om::Om;
use std::time::Instant;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let ops: usize = args.get(1).map(|s| s.parse().unwrap()).unwrap_or(100_000);
    let seed: u64 = args.get(2).map(|s| s.parse().unwrap()).unwrap_or(1);
    let mode = args.get(3).cloned().unwrap_or_else(|| "mix".into());
    let mut rng = Rng(seed.wrapping_mul(0x9E3779B97F4A7C15) | 1);

    let mut om = Om::new(4);
    let init_cost = om.m.cost;
    // the specification: the list of live handles, in order
    let mut list: Vec<u64> = Vec::new();
    let mut fresh: u64 = 0;
    let (mut maxc, mut sumc, mut maxop) = (0u64, 0u64, String::new());
    let mut maxn = 0usize;
    let t0 = Instant::now();
    for k in 0..ops {
        let r = rng.below(100);
        let (p_ins, p_del) = match mode.as_str() {
            "grow" => (70, 10),
            "churn" => (45, 45),
            _ => (45, 25),
        };
        let before = om.m.cost;
        let what;
        if list.is_empty() || r < p_ins {
            if list.is_empty() || rng.below(10) == 0 {
                let h = om.insert_first();
                assert_eq!(h, fresh, "op {k}: handle");
                list.insert(0, h);
                what = "insertFirst";
            } else {
                let i = rng.below(list.len());
                let h = om.insert_after(list[i]);
                assert_eq!(h, fresh, "op {k}: handle");
                list.insert(i + 1, h);
                what = "insertAfter";
            }
            fresh += 1;
        } else if r < p_ins + p_del {
            let i = rng.below(list.len());
            om.delete(list[i]);
            list.remove(i);
            what = "delete";
        } else {
            let i = rng.below(list.len());
            let j = rng.below(list.len());
            let b = om.order(list[i], list[j]);
            assert_eq!(b, i < j, "op {k}: order({}, {})", list[i], list[j]);
            what = "order";
        }
        let c = om.m.cost - before;
        sumc += c;
        if c > maxc {
            maxc = c;
            maxop = format!("{what} at op {k}, n = {}", list.len());
        }
        maxn = maxn.max(list.len());
    }
    let dt = t0.elapsed();
    println!("mode {mode}, {ops} operations, seed {seed}: all answers agree with the specification");
    println!("  live elements at the end {}, at most {maxn}", list.len());
    println!("  initialization steps {init_cost}");
    println!("  steps per operation: max {maxc} ({maxop}), mean {:.0}", sumc as f64 / ops as f64);
    println!("  bound opB 4 = 1133561742; max / bound = {:.2e}", maxc as f64 / 1133561742.0);
    println!("  peak value: {} bits", om.m.peak);
    println!("  allocated cells {} (capacities), {} in blocks in use", om.m.cells(), om.m.resident());
    println!("  time {:.2?} ({:.2} us per operation)", dt, dt.as_secs_f64() * 1e6 / ops as f64);
}
