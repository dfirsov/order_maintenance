//! Replays traces written by `prototype/trace.py --preset verified` on `Native<Wide>` (the
//! verified program's parameters and label widths) and checks every handle, inserted key, order
//! answer, counter and state digest, as `lake exe replay` does for the Lean model.
//!
//!     trace TRACE.jsonl...

use lean_design::lean::{Dg, GLab, Native, Params, Wide};
use num_bigint::BigUint;

#[derive(Debug, Clone)]
enum J {
    Null,
    Bool(bool),
    Num(String),
    Str(String),
    Arr(Vec<J>),
    Obj(Vec<(String, J)>),
}

struct P<'a> { s: &'a [u8], i: usize }

impl<'a> P<'a> {
    fn ws(&mut self) { while self.i < self.s.len() && (self.s[self.i] as char).is_whitespace() { self.i += 1; } }
    fn val(&mut self) -> J {
        self.ws();
        match self.s[self.i] {
            b'[' => {
                self.i += 1;
                let mut v = vec![];
                self.ws();
                if self.s[self.i] == b']' { self.i += 1; return J::Arr(v); }
                loop {
                    v.push(self.val());
                    self.ws();
                    let c = self.s[self.i];
                    self.i += 1;
                    if c == b']' { return J::Arr(v); }
                }
            }
            b'{' => {
                self.i += 1;
                let mut v = vec![];
                self.ws();
                if self.s[self.i] == b'}' { self.i += 1; return J::Obj(v); }
                loop {
                    let k = match self.val() { J::Str(s) => s, _ => panic!("key") };
                    self.ws();
                    self.i += 1; // ':'
                    let x = self.val();
                    v.push((k, x));
                    self.ws();
                    let c = self.s[self.i];
                    self.i += 1;
                    if c == b'}' { return J::Obj(v); }
                }
            }
            b'"' => {
                self.i += 1;
                let st = self.i;
                while self.s[self.i] != b'"' { self.i += 1; }
                self.i += 1;
                J::Str(String::from_utf8_lossy(&self.s[st..self.i - 1]).into())
            }
            b't' => { self.i += 4; J::Bool(true) }
            b'f' => { self.i += 5; J::Bool(false) }
            b'n' => { self.i += 4; J::Null }
            _ => {
                let st = self.i;
                while self.i < self.s.len() && (self.s[self.i] == b'-' || self.s[self.i].is_ascii_digit()) { self.i += 1; }
                J::Num(String::from_utf8_lossy(&self.s[st..self.i]).into())
            }
        }
    }
}

fn parse(s: &str) -> J { P { s: s.as_bytes(), i: 0 }.val() }

impl J {
    fn at(&self, i: usize) -> &J { match self { J::Arr(v) => &v[i], _ => panic!("not an array") } }
    fn num(&self) -> &str { match self { J::Num(s) => s, _ => panic!("not a number: {self:?}") } }
    fn i64(&self) -> i64 { self.num().parse().unwrap() }
    fn get(&self, k: &str) -> &J { match self { J::Obj(v) => &v.iter().find(|(a, _)| a == k).unwrap().1, _ => panic!("not an object") } }
}

fn big(words: &[u64]) -> String {
    let mut b = BigUint::from(0u32);
    for &w in words.iter().rev() { b = (b << 64u32) + BigUint::from(w); }
    b.to_string()
}

/// The header's parameters must be `Params::verified` (what `Native` uses).
fn check_params(j: &J) {
    let n: u64 = j.get("N").i64() as u64;
    let p = Params::verified(n);
    let dg = match p.d_g { Dg::Pow2(k) => (BigUint::from(1u32) << k).to_string(), Dg::Val(v) => v.to_string() };
    let want = [("L", p.l.to_string()), ("G", p.g.to_string()), ("T", p.t.to_string()), ("theta", p.theta.to_string()),
        ("B_e", p.b_e.to_string()), ("B_g", p.b_g.to_string()), ("D_e", p.d_e.to_string()), ("D_g", dg),
        ("K_G", p.k_g.to_string()), ("K_C", p.k_c.to_string()), ("K_R", p.k_r.to_string()), ("a", p.a.to_string()),
        ("s", p.s.to_string()), ("beta", p.beta.to_string()), ("H", p.h.to_string())];
    for (k, v) in want {
        assert_eq!(j.get(k).num(), v, "parameter {k} of the core of capacity {n}");
    }
}

fn counters(om: &Native<Wide>) -> [i64; 3] {
    [0, if om.nxt.is_some() { 0 } else { -1 }, om.rebuilds as i64]
}

fn check_digests(om: &Native<Wide>, j: &J, at: usize) {
    if let J::Null = j { return; }
    let (d1, d2) = om.digests();
    assert_eq!(d1.to_string(), j.at(0).num(), "digest of cur at record {at}");
    assert_eq!(d2, j.at(1).i64(), "digest of nxt at record {at}");
}

fn replay(path: &str) -> usize {
    let text = std::fs::read_to_string(path).unwrap();
    let mut lines = text.lines().filter(|l| !l.is_empty());
    let hdr = parse(lines.next().unwrap());
    match hdr.get("params") { J::Arr(v) => v.iter().for_each(check_params), _ => panic!() }
    let kb = hdr.get("K_B").i64() as u32;
    let n_ops = hdr.get("n").i64() as usize;
    let mut om: Native<Wide> = Native::new(kb, n_ops + 1);
    let mut k = 0;
    for (i, line) in lines.enumerate() {
        let r = parse(line);
        let tag = match r.at(0) { J::Str(s) => s.clone(), _ => panic!() };
        match tag.as_str() {
            "i" => {
                let x = r.at(1).i64();
                let h = if x < 0 { om.insert_first() } else { om.insert_after(x as u64) };
                assert_eq!(h as i64, r.at(2).i64(), "handle at record {}", i + 1);
                let (t, g, e) = om.key(h);
                let key = r.at(3);
                assert_eq!(big(&t.iter().rev().copied().collect::<Vec<_>>()), key.at(0).num(), "tag at record {}", i + 1);
                assert_eq!(big(&g.words()), key.at(1).num(), "group label at record {}", i + 1);
                assert_eq!(e.to_string(), key.at(2).num(), "element label at record {}", i + 1);
                let c = r.at(4);
                assert_eq!(counters(&om), [c.at(0).i64(), c.at(1).i64(), c.at(2).i64()], "counters at record {}", i + 1);
                check_digests(&om, r.at(5), i + 1);
            }
            "d" => {
                om.delete(r.at(1).i64() as u64);
                let c = r.at(2);
                assert_eq!(counters(&om), [c.at(0).i64(), c.at(1).i64(), c.at(2).i64()], "counters at record {}", i + 1);
                check_digests(&om, r.at(3), i + 1);
            }
            "o" => {
                let want = matches!(r.at(3), J::Bool(true));
                assert_eq!(om.order(r.at(1).i64() as u64, r.at(2).i64() as u64), want, "answer at record {}", i + 1);
            }
            "f" => check_digests(&om, r.at(1), i + 1),
            t => panic!("unknown record {t}"),
        }
        k = i + 1;
    }
    k
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    for a in &args {
        let t0 = std::time::Instant::now();
        let n = replay(a);
        println!("OK   {a}: {n} records ({} ms)", t0.elapsed().as_millis());
    }
    println!("{}/{} traces replayed exactly", args.len(), args.len());
}
