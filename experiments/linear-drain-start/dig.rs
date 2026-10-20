//! Experiment: `check`'s random operations, printing a digest of the memory every `every`
//! operations and at the end. Usage: dig ops seed mode every
use om::Om;
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 }
    fn below(&mut self, n: usize) -> usize { (self.next() % n as u64) as usize }
}
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let ops: usize = a[1].parse().unwrap();
    let seed: u64 = a[2].parse().unwrap();
    let mode = a[3].clone();
    let every: usize = a[4].parse().unwrap();
    let mut rng = Rng(seed.wrapping_mul(0x9E3779B97F4A7C15) | 1);
    let mut om = Om::new(4);
    let mut list: Vec<u64> = Vec::new();
    let (mut maxc, mut sumc) = (0u64, 0u64);
    for k in 0..ops {
        let r = rng.below(100);
        let (p_ins, p_del, hot) = match mode.as_str() { "grow" => (70, 10, false), "churn" => (45, 45, false), "hot" => (70, 10, true), _ => (45, 25, false) };
        let before = om.m.cost;
        if list.is_empty() || r < p_ins {
            if list.is_empty() || rng.below(10) == 0 { let h = om.insert_first(); list.insert(0, h); }
            else { let i = if hot { 0 } else { rng.below(list.len()) }; let h = om.insert_after(list[i]); list.insert(i + 1, h); }
        } else if r < p_ins + p_del {
            let i = rng.below(list.len()); om.delete(list[i]); list.remove(i);
        } else {
            let i = rng.below(list.len()); let j = rng.below(list.len());
            assert_eq!(om.order(list[i], list[j]), i < j, "op {k}");
        }
        let c = om.m.cost - before; sumc += c; maxc = maxc.max(c);
        if (k + 1) % every == 0 { println!("{} {:016x}", k + 1, om.m.digest()); }
    }
    println!("end {:016x}", om.m.digest());
    eprintln!("{mode} seed {seed}: max steps {maxc}, mean {:.0}", sumc as f64 / ops as f64);
}
