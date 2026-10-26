//! A baseline for comparison, NOT verified: the amortized O(1) algorithm of Bender, Cole, Demaine,
//! Farach-Colton and Zito (ESA 2002, Sec. 3 with one level of indirection).
//!
//! * Elements are kept in groups of at most `GMAX` consecutive elements, with 62-bit labels inside
//!   their group. A full group splits in two, which inserts one group into the top list.
//! * Groups carry 62-bit tags, maintained by tag-range relabeling: when a new group finds no free
//!   tag, the smallest enclosing aligned tag range of size 2^i whose density (with the new group)
//!   is at most T^-i is relabeled evenly. Amortized O(log n) tag writes per group insertion, so
//!   amortized O(1) per element insertion; a single insertion can rewrite many tags.
//! * `order(x, y)` compares (tag, label) pairs.
//!
//! `work` counts the tags and labels written and the groups scanned, a machine-independent proxy
//! for the time of an operation.

const NIL: u32 = u32::MAX;
/// Labels and tags lie in [0, 2^UBITS).
const UBITS: u32 = 62;
const U: u64 = 1 << UBITS;
/// The largest group.
pub const GMAX: u32 = 64;

pub struct Bender {
    e_prev: Vec<u32>,
    e_next: Vec<u32>,
    e_grp: Vec<u32>,
    e_lab: Vec<u64>,
    g_prev: Vec<u32>,
    g_next: Vec<u32>,
    g_tag: Vec<u64>,
    g_first: Vec<u32>,
    g_last: Vec<u32>,
    g_size: Vec<u32>,
    /// thr[i]: the most groups a tag range of size 2^i may hold after a relabeling (2^i·T^-i).
    thr: Vec<u64>,
    pub work: u64,
}

impl Bender {
    /// A structure for up to `cap` insertions; element 0 is a sentinel that precedes every element.
    pub fn new(t: f64, cap: usize) -> Bender {
        let gcap = cap / (GMAX as usize / 2) + 2;
        let mut b = Bender {
            e_prev: Vec::with_capacity(cap + 1),
            e_next: Vec::with_capacity(cap + 1),
            e_grp: Vec::with_capacity(cap + 1),
            e_lab: Vec::with_capacity(cap + 1),
            g_prev: Vec::with_capacity(gcap),
            g_next: Vec::with_capacity(gcap),
            g_tag: Vec::with_capacity(gcap),
            g_first: Vec::with_capacity(gcap),
            g_last: Vec::with_capacity(gcap),
            g_size: Vec::with_capacity(gcap),
            thr: (0..=UBITS).map(|i| ((2f64).powi(i as i32) * t.powi(-(i as i32))).floor() as u64).collect(),
            work: 0,
        };
        b.new_group(NIL, NIL, U / 2);
        b.e_prev.push(NIL);
        b.e_next.push(NIL);
        b.e_grp.push(0);
        b.e_lab.push(U / 2);
        b.g_first[0] = 0;
        b.g_last[0] = 0;
        b.g_size[0] = 1;
        b
    }

    fn new_group(&mut self, prev: u32, next: u32, tag: u64) -> u32 {
        let g = self.g_tag.len() as u32;
        self.g_prev.push(prev);
        self.g_next.push(next);
        self.g_tag.push(tag);
        self.g_first.push(NIL);
        self.g_last.push(NIL);
        self.g_size.push(0);
        if prev != NIL { self.g_next[prev as usize] = g; }
        if next != NIL { self.g_prev[next as usize] = g; }
        g
    }

    /// Insert a new group right after group `g` and give it a tag, relabeling if needed.
    fn group_after(&mut self, g: u32) -> u32 {
        let nx = self.g_next[g as usize];
        let lo = self.g_tag[g as usize];
        let hi = if nx == NIL { U } else { self.g_tag[nx as usize] };
        let h = self.new_group(g, nx, 0);
        self.work += 1;
        if hi - lo >= 2 {
            self.g_tag[h as usize] = lo + (hi - lo) / 2;
            return h;
        }
        // The smallest enclosing range of lo that is not overflowing with h. The range's groups
        // are the run from `l` to `r` (h is in it, right after g).
        let (mut l, mut r) = (g, h);
        let mut count: u64 = 2;
        for i in 1..=UBITS {
            let base = (lo >> i) << i;
            let end = base + (1u64 << i);
            loop {
                let p = self.g_prev[l as usize];
                if p == NIL || self.g_tag[p as usize] < base { break; }
                l = p; count += 1; self.work += 1;
            }
            loop {
                let q = self.g_next[r as usize];
                if q == NIL || self.g_tag[q as usize] >= end { break; }
                r = q; count += 1; self.work += 1;
            }
            if count <= self.thr[i as usize] {
                let step = (1u64 << i) / count;
                let mut x = l;
                let mut k = 0;
                loop {
                    self.g_tag[x as usize] = base + k * step;
                    self.work += 1;
                    if x == r { break; }
                    x = self.g_next[x as usize];
                    k += 1;
                }
                return h;
            }
        }
        panic!("baseline: the root tag range overflows");
    }

    /// Give the elements of group `g` evenly spaced labels.
    fn relabel_group(&mut self, g: u32) {
        let n = self.g_size[g as usize] as u64;
        let step = U / (n + 1);
        let mut x = self.g_first[g as usize];
        let mut k = 1;
        while x != NIL && self.e_grp[x as usize] == g {
            self.e_lab[x as usize] = k * step;
            self.work += 1;
            k += 1;
            if x == self.g_last[g as usize] { break; }
            x = self.e_next[x as usize];
        }
    }

    /// Split a full group: its second half moves to a new group after it.
    fn split(&mut self, g: u32) {
        let h = self.group_after(g);
        let n = self.g_size[g as usize];
        let mut x = self.g_first[g as usize];
        for _ in 0..n / 2 { x = self.e_next[x as usize]; }
        self.g_first[h as usize] = x;
        self.g_last[h as usize] = self.g_last[g as usize];
        self.g_last[g as usize] = self.e_prev[x as usize];
        self.g_size[h as usize] = n - n / 2;
        self.g_size[g as usize] = n / 2;
        let last = self.g_last[h as usize];
        loop {
            self.e_grp[x as usize] = h;
            self.work += 1;
            if x == last { break; }
            x = self.e_next[x as usize];
        }
        self.relabel_group(g);
        self.relabel_group(h);
    }

    /// Insert a new element right after element `x`; returns its handle.
    pub fn insert_after(&mut self, x: u32) -> u32 {
        if self.g_size[self.e_grp[x as usize] as usize] >= GMAX {
            self.split(self.e_grp[x as usize]);
        }
        let g = self.e_grp[x as usize];
        let y = self.e_lab.len() as u32;
        let nx = self.e_next[x as usize];
        self.e_prev.push(x);
        self.e_next.push(nx);
        self.e_grp.push(g);
        self.e_next[x as usize] = y;
        if nx != NIL { self.e_prev[nx as usize] = y; }
        if self.g_last[g as usize] == x { self.g_last[g as usize] = y; }
        self.g_size[g as usize] += 1;
        let lo = self.e_lab[x as usize];
        let hi = if self.g_last[g as usize] == y { U } else { self.e_lab[nx as usize] };
        self.e_lab.push(lo + (hi - lo) / 2);
        self.work += 1;
        if hi - lo < 2 { self.relabel_group(g); }
        y
    }

    /// Insert a new first element.
    pub fn insert_first(&mut self) -> u32 {
        self.insert_after(0)
    }

    /// Delete element `x` (not the sentinel).
    pub fn delete(&mut self, x: u32) {
        let g = self.e_grp[x as usize];
        let (p, n) = (self.e_prev[x as usize], self.e_next[x as usize]);
        if p != NIL { self.e_next[p as usize] = n; }
        if n != NIL { self.e_prev[n as usize] = p; }
        self.g_size[g as usize] -= 1;
        self.work += 1;
        if self.g_size[g as usize] == 0 {
            let (gp, gn) = (self.g_prev[g as usize], self.g_next[g as usize]);
            if gp != NIL { self.g_next[gp as usize] = gn; }
            if gn != NIL { self.g_prev[gn as usize] = gp; }
        } else {
            if self.g_first[g as usize] == x { self.g_first[g as usize] = n; }
            if self.g_last[g as usize] == x { self.g_last[g as usize] = p; }
        }
    }

    /// Whether element `x` precedes element `y`.
    pub fn order(&mut self, x: u32, y: u32) -> bool {
        let (gx, gy) = (self.e_grp[x as usize] as usize, self.e_grp[y as usize] as usize);
        (self.g_tag[gx], self.e_lab[x as usize]) < (self.g_tag[gy], self.e_lab[y as usize])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Random insertions, deletions and order queries against a plain list.
    #[test]
    fn against_a_list() {
        for (seed, hot) in [(1u64, false), (2, true), (3, false), (4, true)] {
            let mut s = seed.wrapping_mul(0x9E3779B97F4A7C15) | 1;
            let mut rnd = move || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s };
            let mut b = Bender::new(1.4, 200_000);
            let mut list: Vec<u32> = Vec::new();
            for _ in 0..200_000 {
                let r = rnd() % 10;
                if list.is_empty() || r < 6 {
                    let i = if list.is_empty() || rnd() % 4 == 0 { 0 } else if hot { 1.min(list.len()) } else { (rnd() as usize % list.len()) + 1 };
                    let y = if i == 0 { b.insert_first() } else { b.insert_after(list[i - 1]) };
                    list.insert(i, y);
                } else if r < 8 {
                    let i = rnd() as usize % list.len();
                    b.delete(list.remove(i));
                } else {
                    let (i, j) = (rnd() as usize % list.len(), rnd() as usize % list.len());
                    assert_eq!(b.order(list[i], list[j]), i < j);
                }
            }
            for w in list.windows(2) { assert!(b.order(w[0], w[1])); }
        }
    }
}
