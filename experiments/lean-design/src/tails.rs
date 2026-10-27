//! Per-run tail statistics for the timing harnesses (`compare`, `deletes`, `cold`), added for the
//! paper revision of 2026-10-27.
//!
//! The harnesses report statistics of per-operation minima over the runs: the time of the k-th
//! operation is its minimum over the runs, and the slowest is the maximum of these minima, a figure
//! that no single run shows. With the environment variable `TAILS=PATH`, they also append, to the
//! CSV file `PATH`, the statistics of each run on its own (rows with `run` = 0, 1, ...) and, for
//! comparison, those of the per-operation minima (`run` = `min`), with p99.9 added, the numbers of
//! operations slower than 10, 50 and 100 µs, and the second and third largest times. The main
//! output (stdout) is unchanged.

use std::fs::OpenOptions;
use std::io::Write;

/// mean, p99, p99.9, p99.99, max of `ts` (the same percentile index as the harnesses:
/// `sorted[floor(k p)]`, capped at `k - 1`).
pub fn stats(ts: &[u32]) -> Option<(f64, u32, u32, u32, u32)> {
    stats_sorted(ts).map(|(st, _)| st)
}

/// `stats`, and the sorted times.
fn stats_sorted(ts: &[u32]) -> Option<((f64, u32, u32, u32, u32), Vec<u32>)> {
    let k = ts.len();
    if k == 0 {
        return None;
    }
    let mean = ts.iter().map(|&t| t as f64).sum::<f64>() / k as f64;
    let mut s = ts.to_vec();
    s.sort_unstable();
    let pct = |p: f64| s[((k as f64 * p) as usize).min(k - 1)];
    let st = (mean, pct(0.99), pct(0.999), pct(0.9999), s[k - 1]);
    Some((st, s))
}

/// The file named by `TAILS`, if set; a header is written when the file is new or empty.
pub fn sink(header: &str) -> Option<std::fs::File> {
    let path = std::env::var("TAILS").ok()?;
    let mut f = OpenOptions::new().create(true).append(true).open(&path).expect("TAILS file");
    if f.metadata().map(|m| m.len() == 0).unwrap_or(true) {
        writeln!(f, "{header}").unwrap();
    }
    Some(f)
}

/// Thresholds (ns) for the counts of slow operations.
const OVER: [u32; 3] = [10_000, 50_000, 100_000];

/// One row: `prefix` (the key columns, without a trailing comma), the run, the statistics, the
/// numbers of operations slower than 10, 50 and 100 µs, and the second and third largest times.
pub fn row(f: &mut std::fs::File, prefix: &str, run: &str, ts: &[u32]) {
    if let Some(((mean, p99, p999, p9999, max), s)) = stats_sorted(ts) {
        let k = s.len();
        let over: Vec<String> = OVER.iter().map(|&t| (k - s.partition_point(|&x| x <= t)).to_string()).collect();
        let nth = |i: usize| if k > i { s[k - 1 - i].to_string() } else { String::new() };
        writeln!(f, "{prefix},{},{run},{mean:.0},{p99},{p999},{p9999},{max},{},{},{}", k, over.join(","), nth(1), nth(2)).unwrap();
    }
}

/// The header matching `row`, after the key columns `keys`.
pub fn header(keys: &str) -> String {
    format!("{keys},ops,run,mean_ns,p99_ns,p999_ns,p9999_ns,max_ns,n_over_10us,n_over_50us,n_over_100us,max2_ns,max3_ns")
}
