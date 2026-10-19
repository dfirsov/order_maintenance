//! Built only in the profiling copy made by `scripts/profile/instrument.sh`.
// Per decade: the slowest operation (steps) and its pieces; the largest single job step and
// drain start; the most job steps, drain starts and core insertions in one operation.
use om::gen::{CNT, MAXC, G_JOBSTEP, G_STARTDRAIN, G_INSERTAFTER};
use om::Om;
fn sum(g: &[usize], a: &[u64; 256]) -> u64 { g.iter().map(|&i| a[i]).sum() }
fn mx(g: &[usize], a: &[u64; 256]) -> u64 { g.iter().map(|&i| a[i]).max().unwrap_or(0) }
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let wl = a[1].clone();
    let n: usize = a[2].parse().unwrap();
    let mut seed: u64 = 0x9E3779B97F4A7C15 | 1;
    let mut rnd = move || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
    let mut om = Om::new(4);
    let first = om.insert_first();
    let mut live: Vec<u64> = Vec::with_capacity(n);
    live.push(first);
    println!("workload,from,to,max_op_steps,op_jobsteps,op_drains,op_inserts,max_jobstep_steps,max_drain_steps,max_jobsteps_per_op,max_drains_per_op,max_inserts_per_op");
    let mut from = 1usize;
    while live.len() < n {
        let to = (from * 10).min(n);
        let (mut best, mut bj, mut bd, mut bi) = (0u64, 0u64, 0u64, 0u64);
        let (mut mjs, mut mds, mut mj, mut md, mut mi) = (0u64, 0u64, 0u64, 0u64, 0u64);
        while live.len() < to {
            unsafe { CNT = [0; 256]; MAXC = [0; 256]; }
            let c0 = om.m.cost;
            let h = match wl.as_str() {
                "random" => { let x = live[(rnd() % live.len() as u64) as usize]; om.insert_after(x) }
                "hammer" => om.insert_after(first),
                _ => panic!(),
            };
            live.push(h);
            let s = om.m.cost - c0;
            let (cnt, maxc) = unsafe { (CNT, MAXC) };
            let (j, d, i) = (sum(G_JOBSTEP, &cnt), sum(G_STARTDRAIN, &cnt), sum(G_INSERTAFTER, &cnt));
            if s > best { best = s; bj = j; bd = d; bi = i; }
            mjs = mjs.max(mx(G_JOBSTEP, &maxc));
            mds = mds.max(mx(G_STARTDRAIN, &maxc));
            mj = mj.max(j); md = md.max(d); mi = mi.max(i);
        }
        println!("{wl},{from},{to},{best},{bj},{bd},{bi},{mjs},{mds},{mj},{md},{mi}");
        from = to;
    }
}
