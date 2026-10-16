//! Replay prototype traces (`prototype/trace.py`) through the generated code.
//!
//!     replay TRACE.jsonl...
//!
//! Checks every answer the specification determines: the handle of every insertion and the
//! answer of every order query. (The prototype's internal checkpoints, keys and digests, depend
//! on its parameters, which differ from the proof parameters of the machine program.) Reports
//! the steps per update and per query (maximum and mean), the peak bit length and the time.

use om::Om;
use std::io::{BufRead, BufReader};
use std::time::Instant;

/// The first fields of a record `["k", a, b, c, ...]`: the kind and up to three scalars.
fn fields(line: &str) -> (String, Vec<String>) {
    let inner = line.trim().trim_start_matches('[');
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut cur = String::new();
    for ch in inner.chars() {
        match ch {
            '[' | '{' => { depth += 1; cur.push(ch); }
            ']' | '}' => { if depth == 0 { break; } depth -= 1; cur.push(ch); }
            ',' if depth == 0 => { out.push(cur.trim().to_string()); cur.clear(); if out.len() == 4 { break; } }
            _ => cur.push(ch),
        }
    }
    if !cur.trim().is_empty() && out.len() < 4 { out.push(cur.trim().to_string()); }
    let kind = out.first().cloned().unwrap_or_default().trim_matches('"').to_string();
    (kind, out.into_iter().skip(1).collect())
}

fn kb_of(header: &str) -> u64 {
    let i = header.find("\"K_B\":").expect("K_B in the header") + 6;
    header[i..].trim_start().chars().take_while(|c| c.is_ascii_digit()).collect::<String>().parse().unwrap()
}

fn main() {
    let mut failed = false;
    for path in std::env::args().skip(1) {
        let f = BufReader::new(std::fs::File::open(&path).expect("trace"));
        let mut lines = f.lines();
        let header = lines.next().unwrap().unwrap();
        // The answers do not depend on K_B; the theorems need K_B >= 4.
        let kb = kb_of(&header).max(4);
        let mut om = Om::new(kb);
        let (mut n, mut live, mut maxn) = (0usize, 0i64, 0i64);
        let (mut maxu, mut sumu, mut nu, mut maxq, mut sumq, mut nq) = (0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
        let t0 = Instant::now();
        let mut err = None;
        for (k, line) in lines.enumerate() {
            let line = line.unwrap();
            let (kind, v) = fields(&line);
            let before = om.m.cost;
            match kind.as_str() {
                "i" => {
                    let x: i64 = v[0].parse().unwrap();
                    let h: u64 = v[1].parse().unwrap();
                    let got = if x < 0 { om.insert_first() } else { om.insert_after(x as u64) };
                    if got != h { err = Some(format!("record {k}: insertion returned handle {got}, prototype {h}")); break; }
                    live += 1;
                }
                "d" => {
                    let x: u64 = v[0].parse().unwrap();
                    om.delete(x);
                    live -= 1;
                }
                "o" => {
                    let x: u64 = v[0].parse().unwrap();
                    let y: u64 = v[1].parse().unwrap();
                    let want = v[2] == "true";
                    let got = om.order(x, y);
                    if got != want { err = Some(format!("record {k}: order({x}, {y}) = {got}, prototype {want}")); break; }
                }
                _ => continue,
            }
            let c = om.m.cost - before;
            if kind == "o" { maxq = maxq.max(c); sumq += c; nq += 1; } else { maxu = maxu.max(c); sumu += c; nu += 1; }
            maxn = maxn.max(live);
            n += 1;
        }
        let dt = t0.elapsed();
        let name = std::path::Path::new(&path).file_stem().unwrap().to_string_lossy().to_string();
        match err {
            Some(e) => { failed = true; println!("{name}: MISMATCH {e}"); }
            None => println!(
                "{name:14} ops {n:7} live<= {maxn:7}  update max {maxu:7} mean {:6.0}  query max {maxq:4} mean {:4.0}  peak {:5} bits  {:6.2} us/op",
                sumu as f64 / nu.max(1) as f64, sumq as f64 / nq.max(1) as f64, om.m.peak,
                dt.as_secs_f64() * 1e6 / n.max(1) as f64),
        }
    }
    if failed { std::process::exit(1); }
}
