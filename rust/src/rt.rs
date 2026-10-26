//! The runtime of the generated code: words, arrays and operators, with the semantics of the
//! machine (`lean/OM/Machine/Exec.lean`).
//!
//! * A word is a natural number of arbitrary size (`W`): a `u64`, or a shared `BigUint` above it
//!   (reference-counted, so that copying a word never allocates).
//! * An array has a capacity; an access at an index beyond it is a machine error (a panic),
//!   and so is a subtraction below 0. The proofs show that neither happens.
//! * `alloc` gives an array a capacity with every cell reading 0, in constant time, as the model
//!   assumes: a large block table is mapped from zeroed memory that the system maps lazily, and the cells
//!   live in blocks of `BLOCK` cells, each allocated when first written (an unwritten block reads
//!   0), so memory follows the cells actually used, not the capacities. Blocks come from the
//!   runtime's own pool, and the replaced array's blocks return to it a few per operation
//!   (`M::collect`), so that no single operation pays for allocating or freeing a core. A cell
//!   holding a value of 2^63 or more refers to the array's arena of large values (`Arr`).
//! * `m.cost` counts the machine's steps; `m.peak` is the bit length of the largest value
//!   computed so far (`State.peak`).

use num_bigint::BigUint;
use num_traits::{ToPrimitive, Zero};
use std::borrow::Cow;
use std::cmp::Ordering;
use std::collections::LinkedList;
use std::rc::Rc;

use crate::gen::{ARRS, NARR};

/// A machine word: a natural number. Invariant: `B` only above `u64::MAX`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum W {
    S(u64),
    B(Rc<BigUint>),
}

impl Default for W {
    fn default() -> W {
        W::S(0)
    }
}

fn norm(b: BigUint) -> W {
    match b.to_u64() {
        Some(v) => W::S(v),
        None => W::B(Rc::new(b)),
    }
}

impl W {
    pub fn big(s: &str) -> W {
        norm(s.parse::<BigUint>().expect("numeral"))
    }
    /// Nonzero (the machine's truth value).
    pub fn nz(&self) -> bool {
        !matches!(self, W::S(0))
    }
    /// The value as a `u64` (a loop bound or an index).
    pub fn as_u64(&self) -> u64 {
        match self {
            W::S(v) => *v,
            W::B(_) => panic!("machine: a value above 2^64 used as a loop bound"),
        }
    }
    /// The value as a `BigUint`, borrowed when it is one.
    fn as_big(&self) -> Cow<'_, BigUint> {
        match self {
            W::S(v) => Cow::Owned(BigUint::from(*v)),
            W::B(b) => Cow::Borrowed(&**b),
        }
    }
    #[allow(dead_code)]
    fn to_big(&self) -> BigUint {
        match self {
            W::S(v) => BigUint::from(*v),
            W::B(b) => (**b).clone(),
        }
    }
    /// The bit length.
    pub fn bits(&self) -> u64 {
        match self {
            W::S(v) => 64 - v.leading_zeros() as u64,
            W::B(b) => b.bits(),
        }
    }
}

impl PartialOrd for W {
    fn partial_cmp(&self, o: &W) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}
impl Ord for W {
    fn cmp(&self, o: &W) -> Ordering {
        match (self, o) {
            (W::S(a), W::S(b)) => a.cmp(b),
            (W::S(_), W::B(_)) => Ordering::Less,
            (W::B(_), W::S(_)) => Ordering::Greater,
            (W::B(a), W::B(b)) => a.cmp(b),
        }
    }
}

/// A failed algorithmic guard (`fail`); it propagates to the nearest `catch`.
#[derive(Debug)]
pub struct Fail;
pub type R<T> = Result<T, Fail>;

#[derive(Clone, Copy)]
pub enum Op {
    Add, Sub, Mul, Div, Mod, Shl, Shr, Lt, Le, Eq, And, Or,
}
#[derive(Clone, Copy)]
pub enum Uop {
    Not, Msb,
}

const TAG: u64 = 1 << 63;

/// Cells per block (32 KB).
pub const BLOCK: usize = 4096;
/// Blocks per slab: blocks are carved from slabs of 2 MB, mapped directly by the system.
const SLAB: usize = 64;
/// Large values per segment of an array's list of large values.
const SEG: usize = 256;

type Block = [u64; BLOCK];

/// The runtime's own memory for blocks, so that no operation calls `malloc` or `free` for
/// them: free blocks form an intrusive list (the link in cell 0); otherwise the next block of the
/// current slab is used, and a new slab is mapped when it is used up. Slabs come from zeroed
/// memory that the system maps lazily, so a block's pages are touched only when it is used.
struct Pool {
    free: *mut Block,
    slab: *mut Block,
    left: usize,
    /// Every slab mapped, for `Drop`. Adding a slab must not copy older entries.
    slabs: LinkedList<*mut Block>,
}

fn slab_layout() -> std::alloc::Layout {
    std::alloc::Layout::from_size_align(SLAB * BLOCK * 8, 16).unwrap()
}

impl Pool {
    fn take(&mut self) -> *mut Block {
        if !self.free.is_null() {
            let b = self.free;
            unsafe {
                self.free = (*b)[0] as *mut Block;
                (*b).fill(0);
            }
            return b;
        }
        if self.left == 0 {
            self.slab = unsafe { std::alloc::alloc_zeroed(slab_layout()) } as *mut Block;
            assert!(!self.slab.is_null(), "out of memory");
            self.slabs.push_back(self.slab);
            self.left = SLAB;
        }
        self.left -= 1;
        unsafe { self.slab.add(SLAB - 1 - self.left) }
    }
    fn give(&mut self, b: *mut Block) {
        unsafe { (*b)[0] = self.free as u64 };
        self.free = b;
    }
}

enum BigSlot {
    Value(Rc<BigUint>),
    /// Index of the next vacant slot, or `NO_BIG`.
    Free(usize),
}

const NO_BIG: usize = usize::MAX;

/// An array. Its block table is mapped directly from zeroed memory, which the system maps
/// lazily, so creating an array of any capacity takes constant time; a block is taken from the
/// pool when first written. Values of 2^63 and more are kept, shared, in the array's segmented
/// list of large values (`SEG` per segment, so adding one never copies the others): a cell then
/// holds `TAG | index`, and loading it copies a reference, not the number. Vacant large-value
/// slots form an intrusive free list, so clearing a cell releases its reference immediately.
struct Arr {
    cap: usize,
    table: *mut *mut Block,
    nblocks: usize,
    touched: Vec<*mut Block>,
    bigs: Vec<Vec<BigSlot>>,
    free_big: usize,
}

/// Tables of at least this many bytes (one page) are mapped directly from the system
/// (`map_table`): smaller ones are zeroed on the heap, which for up to ~95 tables of 64 KB took up
/// to 0.6 ms in a rebuild start.
const MAP_MIN: usize = 4096;

fn table_bytes(n: usize) -> usize {
    n.max(1) * std::mem::size_of::<*mut Block>()
}

#[cfg(unix)]
extern "C" {
    fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut u8;
    fn munmap(addr: *mut u8, len: usize) -> i32;
}

/// A zeroed block table for `n` blocks, in constant time: a large one is mapped directly
/// (`mmap`), so its pages are zeroed lazily by the system; a small one comes from the heap.
fn map_table(n: usize) -> *mut *mut Block {
    let len = table_bytes(n);
    #[cfg(all(unix, target_os = "linux"))]
    if len >= MAP_MIN {
        const PROT_RW: i32 = 1 | 2;
        const MAP_PRIVATE_ANON: i32 = 0x02 | 0x20;
        let p = unsafe { mmap(std::ptr::null_mut(), len, PROT_RW, MAP_PRIVATE_ANON, -1, 0) };
        assert!(p as isize != -1, "out of memory");
        return p as *mut *mut Block;
    }
    let layout = std::alloc::Layout::array::<*mut Block>(n.max(1)).expect("block table");
    let p = unsafe { std::alloc::alloc_zeroed(layout) } as *mut *mut Block;
    assert!(!p.is_null(), "out of memory");
    p
}

fn unmap_table(t: *mut *mut Block, n: usize) {
    let len = table_bytes(n);
    #[cfg(all(unix, target_os = "linux"))]
    if len >= MAP_MIN {
        unsafe { munmap(t as *mut u8, len) };
        return;
    }
    let layout = std::alloc::Layout::array::<*mut Block>(n.max(1)).expect("block table");
    unsafe { std::alloc::dealloc(t as *mut u8, layout) };
}

impl Arr {
    fn new(cap: usize) -> Arr {
        let nblocks = cap.div_ceil(BLOCK);
        let table = map_table(nblocks);
        Arr { cap, table, nblocks, touched: Vec::new(), bigs: Vec::new(), free_big: NO_BIG }
    }
    #[inline]
    fn get(&self, i: usize) -> u64 {
        assert!(i < self.cap, "machine error: access at {i} beyond the capacity {}", self.cap);
        let b = unsafe { *self.table.add(i / BLOCK) };
        if b.is_null() { 0 } else { unsafe { (*b)[i % BLOCK] } }
    }
    #[inline]
    fn set(&mut self, i: usize, c: u64, pool: &mut Pool) {
        assert!(i < self.cap, "machine error: access at {i} beyond the capacity {}", self.cap);
        let slot = unsafe { self.table.add(i / BLOCK) };
        let mut b = unsafe { *slot };
        if b.is_null() {
            b = pool.take();
            unsafe { *slot = b };
            if self.touched.capacity() == 0 {
                // the full capacity at once (large reservations are mapped lazily), so that the
                // list never grows by copying
                self.touched.reserve_exact(self.nblocks);
            }
            self.touched.push(b);
        }
        unsafe { (*b)[i % BLOCK] = c };
    }
    /// The large value at index `k`, as a word. Values in [2^63, 2^64) are stored here too, but
    /// a word holds them as `W::S` (`W::B` only above `u64::MAX`).
    fn big_get(&self, k: u64) -> W {
        let k = k as usize;
        let BigSlot::Value(b) = &self.bigs[k / SEG][k % SEG] else {
            panic!("machine: access to a vacant large-value slot");
        };
        match b.to_u64() {
            Some(v) => W::S(v),
            None => W::B(b.clone()),
        }
    }
    /// Release a large value and link its vacant slot into the free list, without allocation.
    fn big_free(&mut self, k: u64) {
        let k = k as usize;
        self.bigs[k / SEG][k % SEG] = BigSlot::Free(self.free_big);
        self.free_big = k;
    }
    /// Store a large value: replace `old`, reuse a vacant slot, or append a new slot.
    /// Reusing vacancies bounds the number of slots by the array's capacity.
    /// Returns its index.
    fn big_put(&mut self, old: Option<u64>, v: Rc<BigUint>) -> u64 {
        if let Some(k) = old {
            let k = k as usize;
            self.bigs[k / SEG][k % SEG] = BigSlot::Value(v);
            return k as u64;
        }
        if self.free_big != NO_BIG {
            let k = self.free_big;
            let BigSlot::Free(next) = self.bigs[k / SEG][k % SEG] else {
                panic!("machine: occupied large-value slot on the free list");
            };
            self.free_big = next;
            self.bigs[k / SEG][k % SEG] = BigSlot::Value(v);
            return k as u64;
        }
        if self.bigs.last().map_or(true, |seg| seg.len() == SEG) {
            if self.bigs.capacity() == 0 {
                // as for `touched`: enough segments for every cell, reserved once
                self.bigs.reserve_exact(self.cap / SEG + 1);
            }
            self.bigs.push(Vec::with_capacity(SEG));
        }
        let k = (self.bigs.len() - 1) * SEG + self.bigs.last().unwrap().len();
        self.bigs.last_mut().unwrap().push(BigSlot::Value(v));
        k as u64
    }
}

/// Memory of replaced arrays, returned to the pool a little at a time (`M::collect`), so that no
/// operation pays for a whole core. Linked lists avoid copying pending entries during retirement.
#[derive(Default)]
struct Garbage {
    blocks: LinkedList<Vec<*mut Block>>,
    tables: LinkedList<(*mut *mut Block, usize)>,
    /// Retired arrays' lists of large values, each handed over whole (constant time).
    bigs: LinkedList<Vec<Vec<BigSlot>>>,
}

/// glibc's `free` and `malloc` occasionally do work proportional to the heap (trimming it,
/// consolidating free chunks), which shows up as millisecond pauses in single operations. Turn
/// trimming off and fix the threshold above which memory is mapped directly, so that slabs never
/// come from the heap.
#[cfg(all(target_os = "linux", target_env = "gnu"))]
fn tune_malloc() {
    extern "C" { fn mallopt(param: i32, value: i32) -> i32; }
    const M_TRIM_THRESHOLD: i32 = -1;
    const M_MMAP_THRESHOLD: i32 = -3;
    unsafe {
        mallopt(M_TRIM_THRESHOLD, i32::MAX);
        mallopt(M_MMAP_THRESHOLD, 1 << 20);
    }
}
#[cfg(not(all(target_os = "linux", target_env = "gnu")))]
fn tune_malloc() {}

/// The machine's memory, step counter and peak.
pub struct M {
    arrs: Vec<Arr>,
    pool: Pool,
    garbage: Garbage,
    pub cost: u64,
    pub peak: u64,
}

impl M {
    pub fn new() -> M {
        tune_malloc();
        M {
            arrs: (0..NARR).map(|_| Arr::new(0)).collect(),
            pool: Pool { free: std::ptr::null_mut(), slab: std::ptr::null_mut(), left: 0, slabs: LinkedList::new() },
            garbage: Garbage::default(),
            cost: 0,
            peak: 0,
        }
    }
    /// Retire array `a`'s memory and give it a new, empty one of capacity `n` (constant time).
    fn replace(&mut self, a: usize, n: usize) {
        let old = std::mem::replace(&mut self.arrs[a], Arr::new(n));
        if !old.touched.is_empty() { self.garbage.blocks.push_back(old.touched); }
        if !old.bigs.is_empty() { self.garbage.bigs.push_back(old.bigs); }
        self.garbage.tables.push_back((old.table, old.nblocks));
    }
    /// Perform at most `k` cleanup actions: return a block, drop a fixed-size large-value
    /// segment, remove an empty list, or unmap a table. Called once per update by `Om`;
    /// it is outside the machine and does not count as steps.
    pub fn collect(&mut self, mut k: usize) {
        while k > 0 {
            k -= 1;
            if let Some(v) = self.garbage.blocks.back_mut() {
                match v.pop() {
                    Some(b) => { self.pool.give(b); }
                    None => { self.garbage.blocks.pop_back(); }
                }
            } else if let Some(v) = self.garbage.bigs.back_mut() {
                match v.pop() {
                    Some(seg) => { drop(seg); }
                    None => { self.garbage.bigs.pop_back(); }
                }
            } else if let Some((t, n)) = self.garbage.tables.pop_back() {
                unmap_table(t, n);
            } else {
                break;
            }
        }
    }
    /// Read cell `i` of machine array `arr` (for monitoring; not used by the program).
    pub fn peek(&self, arr: u64, i: usize) -> W {
        let a = ARRS.iter().position(|&x| x == arr).expect("array used by the program");
        let c = self.arrs[a].get(i);
        if c & TAG == 0 { W::S(c) } else { self.arrs[a].big_get(c & !TAG) }
    }
    /// The capacity of machine array `arr` (for monitoring).
    pub fn cap(&self, arr: u64) -> usize {
        let a = ARRS.iter().position(|&x| x == arr).expect("array used by the program");
        self.arrs[a].cap
    }
    /// The total capacity of all arrays (the machine's allocated cells).
    pub fn cells(&self) -> usize {
        self.arrs.iter().map(|a| a.cap).sum()
    }
    /// The cells in blocks actually allocated (memory in use, without the tables of large values).
    pub fn resident(&self) -> usize {
        self.arrs.iter().map(|a| a.touched.len() * BLOCK).sum()
    }
}

/// Teardown (not part of any operation): unmap every table and slab. Every block lies in a slab.
impl Drop for M {
    fn drop(&mut self) {
        for a in &self.arrs {
            unmap_table(a.table, a.nblocks);
        }
        for &(t, n) in &self.garbage.tables {
            unmap_table(t, n);
        }
        for &s in &self.pool.slabs {
            unsafe { std::alloc::dealloc(s as *mut u8, slab_layout()) };
        }
    }
}

impl Default for M {
    fn default() -> M {
        M::new()
    }
}

/// Record a computed value in the peak.
#[inline]
pub fn pk(v: W, m: &mut M) -> W {
    let b = v.bits();
    if b > m.peak {
        m.peak = b;
    }
    v
}

fn index(i: &W, a: usize, m: &M) -> usize {
    match i {
        W::S(v) if (*v as usize) < m.arrs[a].cap => *v as usize,
        _ => panic!("machine error: access at {:?} beyond the capacity {} of array {}", i, m.arrs[a].cap, ARRS[a]),
    }
}

pub fn load(a: usize, i: W, m: &mut M) -> W {
    let ix = index(&i, a, m);
    let c = m.arrs[a].get(ix);
    let v = if c & TAG == 0 { W::S(c) } else { m.arrs[a].big_get(c & !TAG) };
    pk(v, m)
}

pub fn store(a: usize, i: W, v: W, m: &mut M) {
    let ix = index(&i, a, m);
    let arr = &mut m.arrs[a];
    let old = arr.get(ix);
    let c = match v {
        W::S(x) if x < TAG => {
            if old & TAG != 0 { arr.big_free(old & !TAG); }
            x
        }
        v => {
            let prev = if old & TAG != 0 { Some(old & !TAG) } else { None };
            let rc = match v { W::B(b) => b, W::S(x) => Rc::new(BigUint::from(x)) };
            TAG | arr.big_put(prev, rc)
        }
    };
    arr.set(ix, c, &mut m.pool);
}

pub fn alloc(a: usize, k: W, m: &mut M) {
    let n = k.as_u64() as usize;
    m.replace(a, n);
}

fn shl(a: &W, b: &W) -> W {
    if !a.nz() {
        return W::S(0);
    }
    let s = match b {
        W::S(s) => *s,
        W::B(_) => panic!("machine: shift by more than 2^64"),
    };
    if let W::S(x) = a {
        if s < 64 && (x.leading_zeros() as u64) >= s {
            return W::S(x << s);
        }
    }
    norm(&*a.as_big() << (s as usize))
}

fn shr(a: &W, b: &W) -> W {
    let s = match b {
        W::S(s) => *s,
        W::B(_) => return W::S(0),
    };
    match a {
        W::S(x) => W::S(if s >= 64 { 0 } else { x >> s }),
        W::B(x) => {
            if s >= x.bits() { W::S(0) } else { norm(&**x >> (s as usize)) }
        }
    }
}

fn b2w(b: bool) -> W {
    W::S(b as u64)
}

pub fn bin(op: Op, a: W, b: W, m: &mut M) -> W {
    let v = match op {
        Op::Add => match (&a, &b) {
            (W::S(x), W::S(y)) => match x.checked_add(*y) { Some(z) => W::S(z), None => norm(&*a.as_big() + &*b.as_big()) },
            _ => norm(&*a.as_big() + &*b.as_big()),
        },
        Op::Sub => {
            if a < b {
                panic!("machine error: subtraction below 0");
            }
            match (&a, &b) {
                (W::S(x), W::S(y)) => W::S(x - y),
                _ => norm(&*a.as_big() - &*b.as_big()),
            }
        }
        Op::Mul => match (&a, &b) {
            (W::S(x), W::S(y)) => match x.checked_mul(*y) { Some(z) => W::S(z), None => norm(&*a.as_big() * &*b.as_big()) },
            _ => norm(&*a.as_big() * &*b.as_big()),
        },
        Op::Div => {
            if !b.nz() { W::S(0) } else {
                match (&a, &b) {
                    (W::S(x), W::S(y)) => W::S(x / y),
                    _ => norm(&*a.as_big() / &*b.as_big()),
                }
            }
        }
        Op::Mod => {
            if !b.nz() { a.clone() } else {
                match (&a, &b) {
                    (W::S(x), W::S(y)) => W::S(x % y),
                    _ => norm(&*a.as_big() % &*b.as_big()),
                }
            }
        }
        Op::Shl => shl(&a, &b),
        Op::Shr => shr(&a, &b),
        Op::Lt => b2w(a < b),
        Op::Le => b2w(a <= b),
        Op::Eq => b2w(a == b),
        Op::And => b2w(a.nz() && b.nz()),
        Op::Or => b2w(a.nz() || b.nz()),
    };
    pk(v, m)
}

pub fn un(op: Uop, a: W, m: &mut M) -> W {
    let v = match op {
        Uop::Not => b2w(!a.nz()),
        Uop::Msb => W::S(if a.nz() { a.bits() - 1 } else { 0 }),
    };
    pk(v, m)
}

#[allow(dead_code)]
fn _unused() -> BigUint {
    BigUint::zero()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::panic::{catch_unwind, AssertUnwindSafe};

    #[test]
    fn peek_checks_capacity_even_in_release() {
        let mut m = M::new();
        for cap in [0, 1, BLOCK + 1] {
            alloc(0, W::S(cap as u64), &mut m);
            for i in [cap, usize::MAX] {
                assert!(catch_unwind(AssertUnwindSafe(|| m.peek(ARRS[0], i))).is_err());
            }
            if cap > 0 {
                assert_eq!(m.peek(ARRS[0], cap - 1), W::S(0));
                store(0, W::S((cap - 1) as u64), W::S(42), &mut m);
                let counters = (m.cost, m.peak);
                assert_eq!(m.peek(ARRS[0], cap - 1), W::S(42));
                assert_eq!((m.cost, m.peak), counters);
            }
        }
    }

    #[test]
    fn clearing_large_values_releases_and_reuses_slots() {
        let mut m = M::new();
        alloc(0, W::S(1), &mut m);
        let W::B(b) = W::big("18446744073709551616") else { panic!() };
        for _ in 0..1024 {
            store(0, W::S(0), W::B(b.clone()), &mut m);
            assert_eq!(load(0, W::S(0), &mut m), W::B(b.clone()));
            assert_eq!(Rc::strong_count(&b), 2);
            store(0, W::S(0), W::S(0), &mut m);
            assert_eq!(load(0, W::S(0), &mut m), W::S(0));
            assert_eq!(Rc::strong_count(&b), 1);
        }
        assert_eq!(m.arrs[0].bigs.len(), 1);
        assert_eq!(m.arrs[0].bigs[0].len(), 1);
    }

    #[test]
    fn large_slots_recycle_across_segments_without_aliasing() {
        let mut m = M::new();
        let n = 2 * SEG + 3;
        alloc(0, W::S(n as u64), &mut m);
        let W::B(b) = W::big("18446744073709551616") else { panic!() };
        for i in 0..n {
            store(0, W::S(i as u64), W::B(b.clone()), &mut m);
        }
        assert_eq!(Rc::strong_count(&b), n + 1);
        for i in (0..n).step_by(2) {
            store(0, W::S(i as u64), W::S(7), &mut m);
        }
        assert_eq!(Rc::strong_count(&b), n / 2 + 1);
        // Replace occupied slots and reuse vacant ones with distinct values, including
        // values stored in the arena that still fit in W::S.
        for i in (0..n).rev() {
            store(0, W::S(i as u64), W::S(TAG + i as u64), &mut m);
        }
        assert_eq!(Rc::strong_count(&b), 1);
        assert_eq!(m.arrs[0].bigs.iter().map(Vec::len).sum::<usize>(), n);
        for i in 0..n {
            assert_eq!(load(0, W::S(i as u64), &mut m), W::S(TAG + i as u64));
        }
    }

    #[test]
    fn retired_large_values_are_collected_and_new_array_is_zeroed() {
        let mut m = M::new();
        let n = SEG + 1;
        alloc(0, W::S(n as u64), &mut m);
        let W::B(b) = W::big("18446744073709551616") else { panic!() };
        for i in 0..n {
            store(0, W::S(i as u64), W::B(b.clone()), &mut m);
        }
        store(0, W::S(0), W::S(0), &mut m);
        alloc(0, W::S(n as u64), &mut m);
        assert_eq!(Rc::strong_count(&b), n);
        m.collect(usize::MAX);
        assert_eq!(Rc::strong_count(&b), 1);
        assert!(m.garbage.blocks.is_empty());
        assert!(m.garbage.bigs.is_empty());
        assert!(m.garbage.tables.is_empty());
        for i in 0..n {
            assert_eq!(load(0, W::S(i as u64), &mut m), W::S(0));
        }
        store(0, W::S(0), W::B(b.clone()), &mut m);
        assert_eq!(load(0, W::S(0), &mut m), W::B(b.clone()));
        drop(m);
        assert_eq!(Rc::strong_count(&b), 1);
    }

    #[test]
    fn pool_grows_and_reuses_zeroed_blocks_across_slabs() {
        let mut m = M::new();
        let mut blocks = Vec::new();
        for i in 0..(2 * SLAB + 1) {
            let b = m.pool.take();
            unsafe {
                assert!((*b).iter().all(|&x| x == 0));
                (*b)[BLOCK - 1] = i as u64 + 1;
            }
            blocks.push(b);
        }
        assert_eq!(m.pool.slabs.len(), 3);
        for (i, &b) in blocks.iter().enumerate() {
            assert_eq!(unsafe { (*b)[BLOCK - 1] }, i as u64 + 1);
            m.pool.give(b);
        }
        for &b in blocks.iter().rev() {
            assert_eq!(m.pool.take(), b);
            assert!(unsafe { (*b).iter().all(|&x| x == 0) });
        }
        assert_eq!(m.pool.slabs.len(), 3);
    }

    #[test]
    fn collection_charges_empty_lists_to_its_budget() {
        let mut m = M::new();
        for _ in 0..3 {
            m.garbage.blocks.push_back(Vec::new());
            m.garbage.bigs.push_back(Vec::new());
        }
        m.collect(0);
        assert_eq!(m.garbage.blocks.len(), 3);
        m.collect(1);
        assert_eq!(m.garbage.blocks.len(), 2);
        assert_eq!(m.garbage.bigs.len(), 3);
        m.collect(3);
        assert!(m.garbage.blocks.is_empty());
        assert_eq!(m.garbage.bigs.len(), 2);
    }
}
