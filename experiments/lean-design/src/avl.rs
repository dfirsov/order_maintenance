//! Copy of `rust/src/avl.rs` with `new_touched`, which maps the arrays before use (as
//! `Lean::new(cap, true)` does). A second baseline for comparison, NOT verified: the textbook O(log n) solution, a balanced
//! (AVL) binary tree whose in-order sequence is the list, with parent pointers.
//!
//! * `insert_after(x)` links the new node as the in-order successor of `x` and rebalances on the
//!   way up: O(log n) worst case.
//! * `order(x, y)` finds the lowest common ancestor by walking both nodes up (after lifting the
//!   deeper one to the same depth) and compares the sides they come from: O(log n) worst case.
//! * `delete(x)` unlinks the node and rebalances on the way up: O(log n) worst case.
//!
//! `work` counts the nodes visited, a machine-independent proxy for the time of an operation.

const NIL: u32 = u32::MAX;

pub struct Avl {
    left: Vec<u32>,
    right: Vec<u32>,
    parent: Vec<u32>,
    height: Vec<u8>,
    root: u32,
    pub work: u64,
}

impl Avl {
    /// A tree for up to `cap` elements whose arrays are mapped (written once) before use.
    pub fn new_touched(cap: usize) -> Avl {
        let mut t = Avl::new(cap);
        t.left = { let mut v = vec![1u32; cap]; v.clear(); v };
        t.right = { let mut v = vec![1u32; cap]; v.clear(); v };
        t.parent = { let mut v = vec![1u32; cap]; v.clear(); v };
        t.height = { let mut v = vec![1u8; cap]; v.clear(); v };
        t
    }

    /// A tree for up to `cap` elements.
    pub fn new(cap: usize) -> Avl {
        Avl {
            left: Vec::with_capacity(cap),
            right: Vec::with_capacity(cap),
            parent: Vec::with_capacity(cap),
            height: Vec::with_capacity(cap),
            root: NIL,
            work: 0,
        }
    }

    fn h(&self, v: u32) -> i32 {
        if v == NIL { 0 } else { self.height[v as usize] as i32 }
    }

    fn fix_height(&mut self, v: u32) {
        let hv = 1 + self.h(self.left[v as usize]).max(self.h(self.right[v as usize]));
        self.height[v as usize] = hv as u8;
    }

    /// Replace `old` by `new` as a child of `p` (or as the root).
    fn relink(&mut self, p: u32, old: u32, new: u32) {
        if p == NIL {
            self.root = new;
        } else if self.left[p as usize] == old {
            self.left[p as usize] = new;
        } else {
            self.right[p as usize] = new;
        }
        if new != NIL { self.parent[new as usize] = p; }
    }

    /// Rotate `v`'s right child up; returns the new subtree root.
    fn rotate_left(&mut self, v: u32) -> u32 {
        let r = self.right[v as usize];
        let rl = self.left[r as usize];
        let p = self.parent[v as usize];
        self.right[v as usize] = rl;
        if rl != NIL { self.parent[rl as usize] = v; }
        self.left[r as usize] = v;
        self.parent[v as usize] = r;
        self.relink(p, v, r);
        self.fix_height(v);
        self.fix_height(r);
        r
    }

    /// Rotate `v`'s left child up; returns the new subtree root.
    fn rotate_right(&mut self, v: u32) -> u32 {
        let l = self.left[v as usize];
        let lr = self.right[l as usize];
        let p = self.parent[v as usize];
        self.left[v as usize] = lr;
        if lr != NIL { self.parent[lr as usize] = v; }
        self.right[l as usize] = v;
        self.parent[v as usize] = l;
        self.relink(p, v, l);
        self.fix_height(v);
        self.fix_height(l);
        l
    }

    /// Restore the AVL property from `v` up, after an insertion below `v`.
    fn retrace(&mut self, mut v: u32) {
        while v != NIL {
            self.work += 1;
            let old = self.height[v as usize];
            let bal = self.h(self.left[v as usize]) - self.h(self.right[v as usize]);
            if bal > 1 {
                let l = self.left[v as usize];
                if self.h(self.left[l as usize]) < self.h(self.right[l as usize]) { self.rotate_left(l); }
                self.rotate_right(v);
                return; // after an insertion, one (double) rotation restores the old height
            } else if bal < -1 {
                let r = self.right[v as usize];
                if self.h(self.right[r as usize]) < self.h(self.left[r as usize]) { self.rotate_right(r); }
                self.rotate_left(v);
                return;
            }
            self.fix_height(v);
            if self.height[v as usize] == old { return; }
            v = self.parent[v as usize];
        }
    }

    fn new_node(&mut self, p: u32) -> u32 {
        let y = self.height.len() as u32;
        self.left.push(NIL);
        self.right.push(NIL);
        self.parent.push(p);
        self.height.push(1);
        y
    }

    /// Insert a new element right after element `x`; returns its handle.
    pub fn insert_after(&mut self, x: u32) -> u32 {
        let r = self.right[x as usize];
        let y;
        if r == NIL {
            y = self.new_node(x);
            self.right[x as usize] = y;
        } else {
            let mut v = r;
            while self.left[v as usize] != NIL { v = self.left[v as usize]; self.work += 1; }
            y = self.new_node(v);
            self.left[v as usize] = y;
        }
        self.retrace(self.parent[y as usize]);
        y
    }

    /// Insert a new first element.
    pub fn insert_first(&mut self) -> u32 {
        if self.root == NIL {
            let y = self.new_node(NIL);
            self.root = y;
            return y;
        }
        let mut v = self.root;
        while self.left[v as usize] != NIL { v = self.left[v as usize]; self.work += 1; }
        let y = self.new_node(v);
        self.left[v as usize] = y;
        self.retrace(v);
        y
    }

    /// Restore the AVL property from `v` up, after a deletion below `v`: unlike after an
    /// insertion, a rotation can lower the subtree's height, so the walk continues above it.
    fn retrace_delete(&mut self, mut v: u32) {
        while v != NIL {
            self.work += 1;
            let old = self.height[v as usize];
            let bal = self.h(self.left[v as usize]) - self.h(self.right[v as usize]);
            let top = if bal > 1 {
                let l = self.left[v as usize];
                if self.h(self.left[l as usize]) < self.h(self.right[l as usize]) { self.rotate_left(l); }
                self.rotate_right(v)
            } else if bal < -1 {
                let r = self.right[v as usize];
                if self.h(self.right[r as usize]) < self.h(self.left[r as usize]) { self.rotate_right(r); }
                self.rotate_left(v)
            } else {
                self.fix_height(v);
                v
            };
            if self.height[top as usize] == old { return; }
            v = self.parent[top as usize];
        }
    }

    /// Delete element `x`: unlink its node (if it has two children, its in-order successor takes
    /// its place) and rebalance on the way up: O(log n) worst case. Handles are not reused.
    pub fn delete(&mut self, x: u32) {
        let (l, r, p) = (self.left[x as usize], self.right[x as usize], self.parent[x as usize]);
        let start;
        if l == NIL || r == NIL {
            self.relink(p, x, if l == NIL { r } else { l });
            start = p;
        } else {
            let mut y = r;
            while self.left[y as usize] != NIL { y = self.left[y as usize]; self.work += 1; }
            if y == r {
                start = y;
            } else {
                start = self.parent[y as usize];
                self.relink(start, y, self.right[y as usize]);
                self.right[y as usize] = r;
                self.parent[r as usize] = y;
            }
            self.left[y as usize] = l;
            self.parent[l as usize] = y;
            self.height[y as usize] = self.height[x as usize];
            self.relink(p, x, y);
        }
        self.retrace_delete(start);
    }

    fn depth(&mut self, mut v: u32) -> u32 {
        let mut d = 0;
        while self.parent[v as usize] != NIL { v = self.parent[v as usize]; d += 1; }
        self.work += d as u64;
        d
    }

    /// Whether element `x` precedes element `y`.
    pub fn order(&mut self, x: u32, y: u32) -> bool {
        if x == y { return false; }
        let (mut a, mut b) = (x, y);
        let (mut da, mut db) = (self.depth(a), self.depth(b));
        // lift the deeper node; if it meets the other, the other is its ancestor
        while da > db {
            let p = self.parent[a as usize];
            if p == b { return self.right[b as usize] != a; }
            a = p; da -= 1; self.work += 1;
        }
        while db > da {
            let p = self.parent[b as usize];
            if p == a { return self.left[a as usize] != b; }
            b = p; db -= 1; self.work += 1;
        }
        // a and b are distinct nodes at the same depth: climb to the children of the LCA
        while self.parent[a as usize] != self.parent[b as usize] {
            a = self.parent[a as usize];
            b = self.parent[b as usize];
            self.work += 2;
        }
        self.left[self.parent[a as usize] as usize] == a
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Random insertions and order queries against a plain list; the tree stays balanced.
    #[test]
    fn against_a_list() {
        for (seed, hot) in [(1u64, false), (2, true), (3, false)] {
            let mut s = seed * 0x9E3779B97F4A7C15 | 1;
            let mut rnd = move || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s };
            let mut t = Avl::new(100_000);
            let mut list: Vec<u32> = Vec::new();
            for _ in 0..100_000 {
                if list.is_empty() || rnd() % 3 != 0 {
                    let i = if list.is_empty() || rnd() % 5 == 0 { 0 } else if hot { 1 } else { (rnd() as usize % list.len()) + 1 };
                    let y = if i == 0 { t.insert_first() } else { t.insert_after(list[i - 1]) };
                    list.insert(i, y);
                } else {
                    let (i, j) = (rnd() as usize % list.len(), rnd() as usize % list.len());
                    assert_eq!(t.order(list[i], list[j]), i < j);
                }
            }
            for w in list.windows(2) { assert!(t.order(w[0], w[1]) && !t.order(w[1], w[0])); }
            // AVL height bound: h < 1.45 log2(n + 2)
            let n = list.len() as f64;
            assert!((t.h(t.root) as f64) < 1.45 * (n + 2.0).log2());
        }
    }

    /// Checks heights, balance and parent links of the subtree at `v`; returns its height.
    fn check(t: &Avl, v: u32) -> i32 {
        if v == NIL { return 0; }
        for c in [t.left[v as usize], t.right[v as usize]] {
            if c != NIL { assert_eq!(t.parent[c as usize], v); }
        }
        let (hl, hr) = (check(t, t.left[v as usize]), check(t, t.right[v as usize]));
        assert!((hl - hr).abs() <= 1, "unbalanced");
        assert_eq!(t.h(v), 1 + hl.max(hr), "height");
        1 + hl.max(hr)
    }

    /// Insertions, deletions (also down to the empty list) and queries against a plain list.
    #[test]
    fn with_deletions() {
        for (seed, hot) in [(4u64, false), (5, true), (6, false)] {
            let mut s = seed * 0x9E3779B97F4A7C15 | 1;
            let mut rnd = move || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s };
            let mut t = Avl::new(200_000);
            let mut list: Vec<u32> = Vec::new();
            for step in 0..200_000 {
                let grow = (step / 20_000) % 2 == 0;
                let k = rnd() % 10;
                if list.is_empty() || (grow && k < 6) || (!grow && k < 3) {
                    let i = if list.is_empty() || rnd() % 5 == 0 { 0 } else if hot { 1.min(list.len()) } else { (rnd() as usize % list.len()) + 1 };
                    let y = if i == 0 { t.insert_first() } else { t.insert_after(list[i - 1]) };
                    list.insert(i, y);
                } else if k < 8 {
                    let i = if hot { 0 } else { rnd() as usize % list.len() };
                    t.delete(list.remove(i));
                    if list.is_empty() { assert_eq!(t.root, NIL); }
                } else {
                    let (i, j) = (rnd() as usize % list.len(), rnd() as usize % list.len());
                    assert_eq!(t.order(list[i], list[j]), i < j);
                }
                if step % 10_000 == 0 { check(&t, t.root); }
            }
            check(&t, t.root);
            for w in list.windows(2) { assert!(t.order(w[0], w[1]) && !t.order(w[1], w[0])); }
            while let Some(x) = list.pop() { t.delete(x); }
            assert_eq!(t.root, NIL);
        }
    }
}
