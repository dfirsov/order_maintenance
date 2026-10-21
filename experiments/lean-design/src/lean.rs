//! Experiment (not verified): the algorithm of `docs/PROOF.md` §2 written directly in Rust.
//!
//! [`Native`] follows the verified machine program (`lean/OM/Impl`) decision for decision: the
//! same core (elements → groups → chunks, reservation process, top structure with ghost drains),
//! the same wrapper (deletion by tombstones, growth by incremental global rebuilding, handles with
//! one slot per core parity), and the same parameters (`Params::verified` = `proofParams N`). With
//! group labels of type [`Wide`] it uses the label widths of the proof; `check_trace` compares it
//! with the prototype's traces, which the Lean model replays exactly.
//!
//! [`Core`] alone, with `Params::profile`, is the fixed-capacity variant measured first
//! (`Lean::new`): one core sized at construction, no rebuilding, insertion only, K_R = 1.
//!
//! What differs from the verified program is the representation, not the decisions: records
//! instead of an array per field, fixed-width words (128-bit element labels, group labels of
//! `GL::BITS` bits, tags of `H` 64-bit fields), top tables as inline arrays, memory mapped lazily
//! and released incrementally. A failed guard panics (the verified program's FALLBACK never runs).

pub const NIL: u32 = u32::MAX;
const QUIET: u8 = 0;
const OVERFLOW: u8 = 1;
const SPLITTING: u8 = 2;
const DEAD: u8 = 3;
const LEFT: u8 = 0;
const RIGHT: u8 = 1;

/// Largest top height; a tag is `H` fields (labels of at most 64 bits), most significant first.
pub const H_MAX: usize = 20;
/// Capacity of a table, of a live-children list, of a "tables containing" list.
const TMAX: usize = 64;
const KMAX: usize = 48;
const IMAX: usize = 4;
/// The digest modulus of `prototype/trace.py`.
pub const MODP: u64 = (1 << 61) - 1;

type Tag = [u64; H_MAX];

#[cold]
#[inline(never)]
fn fail(why: &str) -> ! {
    panic!("guard failed: {why}")
}

// ---------------------------------------------------------------------------------- memory

extern "C" {
    fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut u8;
    fn munmap(addr: *mut u8, len: usize) -> i32;
    fn madvise(addr: *mut u8, len: usize, advice: i32) -> i32;
}
const MADV_DONTNEED: i32 = 4;
const PAGE: usize = 4096;

/// An array of records at full capacity in anonymous memory (the system supplies zero pages
/// when first touched); a core maps all its arrays with one `mmap` (`Region`). `prefault` maps at
/// most one page per call while fewer than `reserve` bytes beyond the records in use are mapped;
/// an operation calls it before its work, so page faults fall on ordinary operations instead of
/// the heavy ones that grow the rarely growing arenas (top nodes, chunks).
struct Arena<T: Copy> {
    ptr: *mut T,
    len: usize,
    cap: usize,
    bytes: usize,
    mapped: usize,
}

impl<T: Copy> Arena<T> {
    /// Bytes of an array of `cap` records (whole pages).
    fn size(cap: usize) -> usize {
        (cap.max(1) * std::mem::size_of::<T>()).div_ceil(PAGE) * PAGE
    }
    /// An array of `cap` records in the `slot` bytes mapped at `ptr` (at least its size), whose
    /// first `pre` bytes are already mapped; `all` makes all records in use (zero records).
    fn at(ptr: *mut u8, cap: usize, slot: usize, pre: usize, all: bool, touch: bool) -> Self {
        let cap = cap.max(1);
        let bytes = slot;
        assert!(Self::size(cap) <= bytes);
        let mut a = Arena { ptr: ptr as *mut T, len: if all { cap } else { 0 }, cap, bytes, mapped: pre.min(bytes) };
        if touch {
            while a.mapped < bytes {
                unsafe { ptr.add(a.mapped).write_volatile(0) };
                a.mapped += PAGE;
            }
        }
        a
    }
    fn new(cap: usize, touch: bool) -> Self {
        Self::at(Region::map(Self::size(cap)).ptr, cap, Self::size(cap), 0, false, touch)
    }
    #[inline]
    fn push(&mut self, v: T) -> u32 {
        assert!(self.len < self.cap, "arena full");
        unsafe { self.ptr.add(self.len).write(v) };
        self.len += 1;
        (self.len - 1) as u32
    }
    #[inline]
    fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }
        self.len -= 1;
        Some(unsafe { *self.ptr.add(self.len) })
    }
    /// Map one more page if fewer than `reserve` bytes beyond the records in use are mapped;
    /// true if it did.
    #[inline]
    fn prefault(&mut self, reserve: usize) -> bool {
        let used = self.len * std::mem::size_of::<T>();
        // pages holding records are mapped already; never write below the records in use
        self.mapped = self.mapped.max(used.div_ceil(PAGE) * PAGE);
        let want = (used + reserve).min(self.bytes);
        if self.mapped < want {
            unsafe { (self.ptr as *mut u8).add(self.mapped).write_volatile(0) };
            self.mapped += PAGE;
            return true;
        }
        false
    }
}

impl<T: Copy> std::ops::Index<u32> for Arena<T> {
    type Output = T;
    #[inline]
    fn index(&self, i: u32) -> &T {
        assert!((i as usize) < self.len);
        unsafe { &*self.ptr.add(i as usize) }
    }
}

impl<T: Copy> std::ops::IndexMut<u32> for Arena<T> {
    #[inline]
    fn index_mut(&mut self, i: u32) -> &mut T {
        assert!((i as usize) < self.len);
        unsafe { &mut *self.ptr.add(i as usize) }
    }
}

impl<T: Copy> Drop for Arena<T> {
    fn drop(&mut self) {
        unsafe { munmap(self.ptr as *mut u8, self.bytes) };
    }
}

/// One anonymous mapping (each array carved from it unmaps its own part).
struct Region {
    ptr: *mut u8,
}

/// A mapping prepared for a future core, one mapping per array (`ptrs`, null until mapped:
/// mapping all at once costs several µs in one operation): the arrays' sizes (`slots`), the bytes
/// mapped ahead at the start of each (`done`, up to `PRE` for the record arrays), and, for the
/// mappings of a retired core, the queue arrays still to clear (`clear..8`).
pub struct Spare {
    ptrs: [*mut u8; 8],
    slots: [usize; 8],
    done: [usize; 8],
    clear: usize,
}

/// Bytes mapped ahead at the start of each record array of a spare.
const PRE: usize = 16 * PAGE;

impl Spare {
    fn new(slots: [usize; 8]) -> Spare {
        Spare { ptrs: [std::ptr::null_mut(); 8], slots, done: [0; 8], clear: 8 }
    }
    fn unmap(self) {
        for i in 0..8 {
            if !self.ptrs[i].is_null() {
                unsafe { munmap(self.ptrs[i], self.slots[i]) };
            }
        }
    }
    /// Map one array, or clear one queue array (`MADV_DONTNEED`: it reads as zero again), or map
    /// one page ahead in a record array; true if it did.
    fn touch_one(&mut self) -> bool {
        if let Some(i) = self.ptrs.iter().position(|p| p.is_null()) {
            self.ptrs[i] = Region::map(self.slots[i]).ptr;
            return true;
        }
        if self.clear < 8 {
            let i = self.clear;
            unsafe { madvise(self.ptrs[i], self.slots[i], MADV_DONTNEED) };
            self.clear += 1;
            return true;
        }
        for i in 0..5 {
            if self.done[i] < PRE.min(self.slots[i]) {
                unsafe { self.ptrs[i].add(self.done[i]).write_volatile(0) };
                self.done[i] += PAGE;
                return true;
            }
        }
        false
    }
    /// Map and clear what is left (normally nothing: the spare is prepared while the previous
    /// rebuild runs, Ω(N) operations before it is needed).
    fn finish(&mut self) {
        while self.ptrs.iter().any(|p| p.is_null()) || self.clear < 8 {
            self.touch_one();
        }
    }
}

impl Region {
    fn map(bytes: usize) -> Region {
        // PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE
        let ptr = unsafe { mmap(std::ptr::null_mut(), bytes.max(PAGE), 3, 0x22 | 0x4000, -1, 0) };
        assert!(ptr as isize != -1 && !ptr.is_null(), "mmap failed");
        Region { ptr }
    }
}

// ---------------------------------------------------------------------------------- labels

/// Group labels: unsigned integers of `BITS` bits with the guarded primitives of `docs/PROOF.md`
/// §2.2.
pub trait GLab: Copy + Ord + std::fmt::Debug {
    const BITS: u32;
    fn zero() -> Self;
    fn pow2(k: u32) -> Self;
    fn from_u128(v: u128) -> Self;
    /// `self + d`, if it is below `2^b` and `d > 0`.
    fn add_below(self, d: Self, b: u32) -> Option<Self>;
    /// `self - d`, if `self ≥ d` and `d > 0`.
    fn sub_pos(self, d: Self) -> Option<Self>;
    /// `⌊(a + b)/2⌋`, if `a + 1 < b`.
    fn mid(a: Self, b: Self) -> Option<Self>;
    /// The value modulo `MODP`.
    fn modp(self) -> u64;
    /// Little-endian 64-bit words of the value.
    fn words(self) -> Vec<u64>;
}

impl GLab for u128 {
    const BITS: u32 = 128;
    fn zero() -> Self { 0 }
    fn pow2(k: u32) -> Self { 1u128 << k }
    fn from_u128(v: u128) -> Self { v }
    #[inline]
    fn add_below(self, d: Self, b: u32) -> Option<Self> {
        let v = self.checked_add(d)?;
        if d == 0 || (b < 128 && v >> b != 0) { None } else { Some(v) }
    }
    #[inline]
    fn sub_pos(self, d: Self) -> Option<Self> {
        if d == 0 || self < d { None } else { Some(self - d) }
    }
    #[inline]
    fn mid(a: Self, b: Self) -> Option<Self> {
        if a >= b || b - a < 2 { None } else { Some(a + (b - a) / 2) }
    }
    fn modp(self) -> u64 { (self % MODP as u128) as u64 }
    fn words(self) -> Vec<u64> { vec![self as u64, (self >> 64) as u64] }
}

/// A 1024-bit unsigned integer (16 little-endian words), for the proof's group-label widths.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Wide(pub [u64; 16]);

impl Ord for Wide {
    #[inline]
    fn cmp(&self, o: &Self) -> std::cmp::Ordering {
        for i in (0..16).rev() {
            if self.0[i] != o.0[i] {
                return self.0[i].cmp(&o.0[i]);
            }
        }
        std::cmp::Ordering::Equal
    }
}
impl PartialOrd for Wide {
    fn partial_cmp(&self, o: &Self) -> Option<std::cmp::Ordering> { Some(self.cmp(o)) }
}

impl Wide {
    fn add(self, d: Self) -> (Self, bool) {
        let mut r = [0u64; 16];
        let mut c = false;
        for i in 0..16 {
            let (s1, c1) = self.0[i].overflowing_add(d.0[i]);
            let (s2, c2) = s1.overflowing_add(c as u64);
            r[i] = s2;
            c = c1 || c2;
        }
        (Wide(r), c)
    }
    fn sub(self, d: Self) -> Self {
        let mut r = [0u64; 16];
        let mut b = false;
        for i in 0..16 {
            let (s1, b1) = self.0[i].overflowing_sub(d.0[i]);
            let (s2, b2) = s1.overflowing_sub(b as u64);
            r[i] = s2;
            b = b1 || b2;
        }
        Wide(r)
    }
    fn is_zero(&self) -> bool { self.0.iter().all(|&w| w == 0) }
    fn below(&self, b: u32) -> bool {
        if b >= 1024 {
            return true;
        }
        let (w, s) = ((b / 64) as usize, b % 64);
        if self.0[w] >> s != 0 {
            return false;
        }
        self.0[w + 1..].iter().all(|&x| x == 0)
    }
}

impl GLab for Wide {
    const BITS: u32 = 1024;
    fn zero() -> Self { Wide([0; 16]) }
    fn pow2(k: u32) -> Self {
        let mut r = [0u64; 16];
        r[(k / 64) as usize] = 1u64 << (k % 64);
        Wide(r)
    }
    fn from_u128(v: u128) -> Self {
        let mut r = [0u64; 16];
        r[0] = v as u64;
        r[1] = (v >> 64) as u64;
        Wide(r)
    }
    #[inline]
    fn add_below(self, d: Self, b: u32) -> Option<Self> {
        let (v, c) = self.add(d);
        if c || d.is_zero() || !v.below(b) { None } else { Some(v) }
    }
    #[inline]
    fn sub_pos(self, d: Self) -> Option<Self> {
        if d.is_zero() || self < d { None } else { Some(self.sub(d)) }
    }
    #[inline]
    fn mid(a: Self, b: Self) -> Option<Self> {
        if a >= b {
            return None;
        }
        let mut diff = b.sub(a);
        if diff < Wide::from_u128(2) {
            return None;
        }
        for i in 0..16 {
            diff.0[i] = (diff.0[i] >> 1) | if i + 1 < 16 { diff.0[i + 1] << 63 } else { 0 };
        }
        Some(a.add(diff).0)
    }
    fn modp(self) -> u64 {
        let mut r: u128 = 0;
        for i in (0..16).rev() {
            r = (r * 8 + self.0[i] as u128 % MODP as u128) % MODP as u128; // 2^64 ≡ 8 (mod 2^61 - 1)
        }
        r as u64
    }
    fn words(self) -> Vec<u64> { self.0.to_vec() }
}

// ---------------------------------------------------------------------------------- parameters

#[derive(Clone, Debug)]
pub enum Dg {
    Pow2(u32),
    Val(u128),
}

#[derive(Clone, Debug)]
pub struct Params {
    pub n: u64,
    pub l: u32,
    pub g: u32,
    pub t: u32,
    pub theta: u32,
    pub b_e: u32,
    pub b_g: u32,
    pub d_e: u128,
    pub d_g: Dg,
    pub k_g: u32,
    pub k_c: u32,
    pub k_r: u32,
    pub a: u32,
    pub s: u32,
    pub beta: u32,
    pub h: usize,
}

fn log2(x: u64) -> u32 { 63 - x.leading_zeros() }

impl Params {
    /// `proofParams N` (`lean/OM/Impl/Params.lean`), the parameters of the verified program.
    pub fn verified(n: u64) -> Params {
        let l = (log2(n.max(1)) + 1).max(8);
        let (g, t) = (2 * l, 3 * l * l);
        let (kg, gm) = (g / 3 + 1, (g - 2) / 2);
        let ug = g + kg + kg.saturating_sub(gm);
        let ut = t / gm + 1;
        let kc = ut / 3 + 1;
        let mu = ut + kc;
        let csb = (t + 2 * kc) / gm;
        let rsb = 3 * mu + 1;
        let hc = 2 * (csb + rsb);
        let pc = 3 * mu + rsb + csb;
        let b_e = ug + log2((g + kg) as u64) + 2;
        assert!(b_e <= 127, "element labels wider than 127 bits");
        Params {
            n, l, g, t, theta: 2 * l * l,
            b_e, b_g: hc + log2(pc as u64) + 2,
            d_e: 1u128 << ug, d_g: Dg::Pow2(hc),
            k_g: 4, k_c: 4, k_r: 8, a: 8, s: 11, beta: 64, h: (l / 3 + 1) as usize,
        }
    }

    /// The profile K_R = 1 of `../worst-case` (a = 5, s = 16, T = 12L², θ = 2T/3, β = 32,
    /// 128-bit labels), top height large enough for `n_max` elements (at least L/2 + 1).
    pub fn profile(l: u32, n_max: u64) -> Params {
        let g = 2 * l;
        let t = 12 * l * l;
        let theta = 2 * t / 3;
        let gpc = (3 * t / g).max(1);
        let a = 5u32;
        let m_max = 6 * n_max / theta as u64 + 16;
        let mut h = 2usize;
        while (a as u64).pow(h as u32 - 1) < m_max {
            h += 1;
        }
        let h = h.max(l as usize / 2 + 1);
        Params {
            n: n_max, l, g, t, theta, b_e: 128, b_g: 128,
            d_e: (1u128 << 127) / (8 * g as u128 + 8), d_g: Dg::Val((1u128 << 127) / (8 * gpc as u128 + 8)),
            k_g: 4, k_c: 4, k_r: 1, a, s: 16, beta: 32, h,
        }
    }

    /// The profile with L = ⌈log₂ cap⌉ (at least 8).
    pub fn for_capacity(cap: u64) -> Params {
        let l = (64 - cap.max(2).saturating_sub(1).leading_zeros()).max(8);
        Params::profile(l, cap)
    }

    /// Capacities of the record arrays (`capsOf (proofParams N)`, with `s + 1` per node).
    fn caps(&self) -> [usize; 4] {
        let (g, t, l) = (self.g as u64, self.t as u64, self.l as u64);
        let (kg, gm) = (g / 3 + 1, (g - 2) / 2);
        let kc = (t / gm + 1) / 3 + 1;
        let cm = (t + kc + (g + kg) + 1) / 2;
        let cb = 2 + 2 * (self.n / (self.theta as u64 + 1 - cm));
        let h = self.h as u64;
        let nb = (h + 2) + ((h + 1) + (h * (self.s as u64 + 1) + 1)) * cb;
        let _ = l;
        [self.n as usize + 2, 2 * self.n as usize + 4, cb as usize + 2, (nb + cb) as usize + 2]
    }
}

// ---------------------------------------------------------------------------------- records

#[derive(Clone, Copy)]
struct Elem {
    lab: [u64; 2],
    next: u32,
    prev: u32,
    grp: u32,
    h: u32,
    live: bool,
}

impl Elem {
    #[inline]
    fn lab(&self) -> u128 { self.lab[0] as u128 | (self.lab[1] as u128) << 64 }
}
#[inline]
fn lab2(v: u128) -> [u64; 2] { [v as u64, (v >> 64) as u64] }

#[derive(Clone, Copy)]
struct Group<GL: GLab> {
    lab: GL,
    next: u32,
    prev: u32,
    first: u32,
    last: u32,
    chk: u32,
    size: u32,
    src: u32,
    l: u32,
    r: u32,
    st: u8,
    alive: bool,
}

#[derive(Clone, Copy)]
struct Chunk {
    tag: Tag,
    next: u32,
    prev: u32,
    first: u32,
    last: u32,
    size: u32,
    src: u32,
    l: u32,
    r: u32,
    st: u8,
    pq_b: u32,
    pq_next: u32,
    pq_prev: u32,
    // top structure: stored path p[1..H], tables containing the chunk, live parent
    lpar: u32,
    ncin: u8,
    cin: [u32; IMAX],
    path: [u32; H_MAX + 1],
}

#[derive(Clone, Copy)]
struct Node {
    height: u8,
    draining: bool,
    alive: bool,
    ntab: u8,
    nkids: u8,
    nin: u8,
    live_parent: u32,
    weight: u32,
    first: u32,
    last: u32,
    t1: u32,
    t2: u32,
    overflow_of: u32,
    tab_e: [u32; TMAX],
    tab_l: [u64; TMAX],
    side: [u8; TMAX],
    kids: [u32; KMAX],
    ins: [u32; IMAX],
}

/// The reservation job (`top_wbbt._job`) as a state machine: one call of `step` per yield.
#[derive(Clone, Copy)]
enum Job {
    Idle,
    Copy { x: u32, y: u32, z: u32, j: u8 },
    Walk { v: u32 },
    After { v: u32, up: u32 },
    Sweep { up: u32, src: u32, i: u32 },
    End { up: u32 },
}

// ---------------------------------------------------------------------------------- the core

/// An insert-only core of fixed capacity (`prototype/core.py` with `top_wbbt.py` and `pq.py`).
pub struct Core<GL: GLab> {
    pub p: Params,
    e: Arena<Elem>,
    g: Arena<Group<GL>>,
    c: Arena<Chunk>,
    n: Arena<Node>,
    free_g: Arena<u32>,
    // bucket queue of the quiet chunks above θ, LIFO within a bucket; arrays hold value + 1
    pq_head: Arena<u32>,
    pq_nbn: Arena<u32>,
    pq_nbp: Arena<u32>,
    pq_hi: u32,
    pq_lo: u32,
    pq_scan: u64,
    job: Job,
    wh: [u64; H_MAX + 2],
    center_e: u128,
    center_g: GL,
    dg: GL,
    pub head: u32,
    tail: u32,
    first_group: u32,
    first_chunk: u32,
    pub count: u64,
    ready: bool,
    prep_h: usize,
    prep_below: u32,
    /// Primitive steps (insertions, moves, job steps, table entries copied or shifted).
    pub work: u64,
    pub drains: u64,
    pub max_table: usize,
}

#[inline]
fn enc(v: u32) -> u32 { v.wrapping_add(1) }
#[inline]
fn dec(v: u32) -> u32 { v.wrapping_sub(1) }

/// The fixed-capacity variant: `Lean::new(cap, touch)`.
pub type Lean = Core<u128>;

impl Core<u128> {
    /// A core for up to `cap` elements with the profile parameters; `touch` maps all its memory.
    pub fn new(cap: usize, touch: bool) -> Self {
        Self::with_params(cap, Params::for_capacity(cap as u64 + 1), touch)
    }
    pub fn with_params(cap: usize, mut p: Params, touch: bool) -> Self {
        p.n = cap as u64;
        Core::create(p, false, touch)
    }
}

impl<GL: GLab> Core<GL> {
    /// A core with parameters `p` (capacity `p.n`). With `lazy`, the top structure is built by
    /// `prepare_step`, one node per call.
    pub fn create(p: Params, lazy: bool, touch: bool) -> Self {
        Self::create_in(p, lazy, touch, None)
    }

    /// The capacities of the arrays of a core with parameters `p`, and their sizes in bytes.
    fn slots(p: &Params) -> ([usize; 8], [usize; 8]) {
        let [ke, kg, kc, kn] = p.caps();
        let blen = 4 * p.t as usize + 16;
        let caps = [ke, kg, kc, kn, kg, blen, blen, blen];
        let u = |c| Arena::<u32>::size(c);
        (caps, [Arena::<Elem>::size(ke), Arena::<Group<GL>>::size(kg), Arena::<Chunk>::size(kc), Arena::<Node>::size(kn),
            u(kg), u(blen), u(blen), u(blen)])
    }

    /// A spare mapping large enough for a core with parameters `p`.
    pub fn spare_for(p: &Params) -> Spare {
        Spare::new(Self::slots(p).1)
    }

    /// This (retired) core's mapping, as a spare for a later core: the records left in it are
    /// overwritten before being read, except the queue arrays, which the spare clears first.
    fn into_spare(self) -> Spare {
        let slots = [self.e.bytes, self.g.bytes, self.c.bytes, self.n.bytes, self.free_g.bytes,
            self.pq_head.bytes, self.pq_nbn.bytes, self.pq_nbp.bytes];
        let ptrs = [self.e.ptr as *mut u8, self.g.ptr as *mut u8, self.c.ptr as *mut u8, self.n.ptr as *mut u8,
            self.free_g.ptr as *mut u8, self.pq_head.ptr as *mut u8, self.pq_nbn.ptr as *mut u8, self.pq_nbp.ptr as *mut u8];
        let sp = Spare { ptrs, slots, done: [0; 8], clear: 5 };
        std::mem::forget(self);
        sp
    }

    /// Bytes of this core's mapping.
    fn region_bytes(&self) -> usize {
        self.e.bytes + self.g.bytes + self.c.bytes + self.n.bytes + self.free_g.bytes
            + self.pq_head.bytes + self.pq_nbn.bytes + self.pq_nbp.bytes
    }

    /// Whether a core with parameters `p` fits in this core's mapping.
    fn region_fits(&self, p: &Params) -> bool {
        let have = [self.e.bytes, self.g.bytes, self.c.bytes, self.n.bytes, self.free_g.bytes,
            self.pq_head.bytes, self.pq_nbn.bytes, self.pq_nbp.bytes];
        Self::slots(p).1.iter().zip(have.iter()).all(|(a, b)| a <= b)
    }

    /// Whether a core with parameters `p` fits in spare `sp`.
    fn fits(p: &Params, sp: &Spare) -> bool {
        Self::slots(p).1.iter().zip(sp.slots.iter()).all(|(a, b)| a <= b)
    }

    /// As `create`, in the mapping `spare` if given (it must fit).
    fn create_in(p: Params, lazy: bool, touch: bool, spare: Option<Spare>) -> Self {
        assert!(p.h <= H_MAX && p.beta <= 64 && p.b_g <= GL::BITS && p.b_e <= 128);
        let (caps, sizes) = Self::slots(&p);
        let mut wh = [u64::MAX; H_MAX + 2];
        for h in 0..=p.h {
            wh[h] = 2u64.saturating_mul((p.a as u64).saturating_pow(h as u32));
        }
        let dg = match p.d_g {
            Dg::Pow2(k) => GL::pow2(k),
            Dg::Val(v) => GL::from_u128(v),
        };
        let (ptrs, slots, done) = match spare {
            Some(mut sp) => {
                sp.finish();
                (sp.ptrs, sp.slots, sp.done)
            }
            None => {
                // one mapping for all arrays
                let r = Region::map(sizes.iter().sum());
                let mut ptrs = [r.ptr; 8];
                for i in 1..8 {
                    ptrs[i] = unsafe { ptrs[i - 1].add(sizes[i - 1]) };
                }
                (ptrs, sizes, [0; 8])
            }
        };
        let a = |i: usize, all: bool, t: bool| (ptrs[i], caps[i], slots[i], done[i], all, t);
        macro_rules! arr { ($i:expr, $all:expr, $t:expr) => {{ let (p, c, sl, pr, al, t) = a($i, $all, $t); Arena::at(p, c, sl, pr, al, t) }} }
        let mut s = Core {
            e: arr!(0, false, touch),
            g: arr!(1, false, touch),
            c: arr!(2, false, touch),
            n: arr!(3, false, touch),
            free_g: arr!(4, false, touch),
            pq_head: arr!(5, true, false),
            pq_nbn: arr!(6, true, false),
            pq_nbp: arr!(7, true, false),
            pq_hi: NIL,
            pq_lo: NIL,
            pq_scan: 0,
            job: Job::Idle,
            wh,
            center_e: 1u128 << (p.b_e - 1),
            center_g: GL::pow2(p.b_g - 1),
            dg,
            head: NIL,
            tail: NIL,
            first_group: NIL,
            first_chunk: NIL,
            count: 0,
            ready: false,
            prep_h: 0,
            prep_below: NIL,
            work: 0,
            drains: 0,
            max_table: 0,
            p,
        };
        let c = s.new_chunk();
        let g = s.new_group(c);
        s.g[g].lab = s.center_g;
        s.c[c].first = g;
        s.c[c].last = g;
        let e = s.e.push(Elem { lab: lab2(s.center_e), next: NIL, prev: NIL, grp: g, h: NIL, live: false });
        s.g[g].first = e;
        s.g[g].last = e;
        s.g[g].size = 1;
        s.c[c].size = 1;
        s.head = e;
        s.tail = e;
        s.first_group = g;
        s.first_chunk = c;
        s.count = 1;
        s.prep_below = c;
        if !lazy {
            while !s.prepare_step() {}
        }
        s
    }

    pub fn len(&self) -> usize {
        self.e.len
    }

    /// Records in use: elements, groups (including free ones), chunks, top nodes; free groups.
    pub fn sizes(&self) -> [usize; 5] {
        [self.e.len, self.g.len, self.c.len, self.n.len, self.free_g.len]
    }

    /// Map at most one page, in the first array short of its reserve; true if it did.
    #[inline]
    pub fn prefault(&mut self) -> bool {
        self.e.prefault(8 * PAGE)
            || self.g.prefault(8 * PAGE)
            || self.c.prefault(8 * PAGE)
            || self.n.prefault(16 * PAGE)
            || self.free_g.prefault(2 * PAGE)
    }

    // ------------------------------------------------------------------ interface
    pub fn insert_first(&mut self) -> u32 {
        self.prefault();
        self.insert_after_h(self.head, NIL)
    }

    pub fn insert_after(&mut self, x: u32) -> u32 {
        self.prefault();
        self.insert_after_h(x, NIL)
    }

    /// Insert after element `x` an element carrying handle `h`.
    pub fn insert_after_h(&mut self, x: u32, h: u32) -> u32 {
        let y = self.insert_elem(x, h);
        self.background(y);
        y
    }

    pub fn mark_dead(&mut self, x: u32) {
        self.e[x].live = false;
    }

    #[inline]
    pub fn order(&self, x: u32, y: u32) -> bool {
        let (ex, ey) = (&self.e[x], &self.e[y]);
        if ex.grp == ey.grp {
            return ex.lab() < ey.lab();
        }
        let (gx, gy) = (&self.g[ex.grp], &self.g[ey.grp]);
        if gx.chk == gy.chk {
            return gx.lab < gy.lab;
        }
        self.c[gx.chk].tag < self.c[gy.chk].tag
    }

    /// One step of the deferred initialization; true once the core is ready (`init_steps`).
    pub fn prepare_step(&mut self) -> bool {
        if self.ready {
            return true;
        }
        let c = self.first_chunk;
        let center = 1u64 << (self.p.beta - 1);
        if self.prep_h < self.p.h {
            let h = self.prep_h + 1;
            let below = self.prep_below;
            let v = self.new_node(h);
            {
                let vm = &mut self.n[v];
                vm.kids[0] = below;
                vm.nkids = 1;
                vm.tab_e[0] = below;
                vm.tab_l[0] = center;
                vm.ntab = 1;
                vm.weight = 1;
                vm.first = c;
                vm.last = c;
            }
            if h == 1 {
                self.c[c].cin[0] = v;
                self.c[c].ncin = 1;
                self.c[c].lpar = v;
            } else {
                self.n[below].ins[0] = v;
                self.n[below].nin = 1;
                self.n[below].live_parent = v;
            }
            self.c[c].path[h] = v;
            self.prep_below = v;
            self.prep_h = h;
            return false;
        }
        let mut tag = [0u64; H_MAX];
        for h in 1..=self.p.h {
            self.tag_set(&mut tag, h, center);
        }
        self.c[c].tag = tag;
        self.ready = true;
        true
    }

    /// The key of element `x`: (tag fields, most significant first; group label; element label).
    pub fn key(&self, x: u32) -> (Vec<u64>, GL, u128) {
        let ex = &self.e[x];
        let gr = &self.g[ex.grp];
        let t = &self.c[gr.chk].tag;
        let h = self.p.h;
        (t[H_MAX - h..].to_vec(), gr.lab, ex.lab())
    }

    /// `prototype/trace.py`'s digest: the keys of all elements in list order, hashed.
    pub fn digest(&self) -> u64 {
        let m = MODP as u128;
        let b = (1u128 << self.p.beta.min(63)) % m * if self.p.beta == 64 { 2 } else { 1 } % m;
        let mut hsh: u128 = 0;
        let mut e = self.head;
        while e != NIL {
            let (t, gl, el) = self.key(e);
            let mut tv: u128 = 0;
            for f in t {
                tv = (tv * b + f as u128 % m) % m;
            }
            for v in [tv, gl.modp() as u128, el % m] {
                hsh = (hsh * 1000003 + v) % m;
            }
            e = self.e[e].next;
        }
        hsh as u64
    }

    pub fn elem_next(&self, x: u32) -> u32 { self.e[x].next }
    pub fn elem_live(&self, x: u32) -> bool { self.e[x].live }
    pub fn elem_handle(&self, x: u32) -> u32 { self.e[x].h }
    pub fn tail(&self) -> u32 { self.tail }

    // ------------------------------------------------------------------ allocation
    fn new_group(&mut self, c: u32) -> u32 {
        let r = Group { lab: GL::zero(), next: NIL, prev: NIL, first: NIL, last: NIL, chk: c, size: 0, src: NIL, l: NIL, r: NIL, st: QUIET, alive: true };
        if let Some(i) = self.free_g.pop() {
            self.g[i] = r;
            i
        } else {
            self.g.push(r)
        }
    }

    fn new_chunk(&mut self) -> u32 {
        self.c.push(Chunk {
            tag: [0; H_MAX], next: NIL, prev: NIL, first: NIL, last: NIL, size: 0, src: NIL, l: NIL, r: NIL,
            st: QUIET, pq_b: 0, pq_next: NIL, pq_prev: NIL,
            lpar: NIL, ncin: 0, cin: [NIL; IMAX], path: [NIL; H_MAX + 1],
        })
    }

    fn new_node(&mut self, h: usize) -> u32 {
        self.n.push(Node {
            height: h as u8, draining: false, alive: true, ntab: 0, nkids: 0, nin: 0,
            live_parent: NIL, weight: 0, first: NIL, last: NIL, t1: NIL, t2: NIL, overflow_of: NIL,
            tab_e: [NIL; TMAX], tab_l: [0; TMAX], side: [0; TMAX], kids: [NIL; KMAX], ins: [NIL; IMAX],
        })
    }

    // ------------------------------------------------------------------ elements
    fn insert_elem(&mut self, x: u32, h: u32) -> u32 {
        let ex = self.e[x];
        let gi = ex.grp;
        let gr = self.g[gi];
        let lab = if x == gr.last {
            match ex.lab().checked_add(self.p.d_e) {
                Some(v) if self.p.d_e > 0 && (self.p.b_e >= 128 || v >> self.p.b_e == 0) => v,
                _ => fail("elem: no room after last"),
            }
        } else {
            u128::mid(ex.lab(), self.e[ex.next].lab()).unwrap_or_else(|| fail("elem: no room between"))
        };
        self.work += 1;
        let y = self.e.push(Elem { lab: lab2(lab), next: ex.next, prev: x, grp: gi, h, live: true });
        if ex.next != NIL {
            self.e[ex.next].prev = y;
        }
        self.e[x].next = y;
        if self.tail == x {
            self.tail = y;
        }
        if gr.last == x {
            self.g[gi].last = y;
        }
        self.g[gi].size += 1;
        self.count += 1;
        self.chunk_size(gr.chk, 1);
        y
    }

    fn background(&mut self, y: u32) {
        let g = self.e[y].grp;
        if self.g[g].st == QUIET && self.g[g].size >= self.p.g {
            self.start_group_split(g);
        }
        let g = self.e[y].grp;
        self.drive_group(g);
        let c = self.g[self.e[y].grp].chk;
        self.drive_chunk(c);
        self.reservation(self.p.k_r);
    }

    fn chunk_size(&mut self, c: u32, d: i32) {
        let old = self.c[c].size;
        let new = (old as i64 + d as i64) as u32;
        self.c[c].size = new;
        if self.c[c].st == QUIET {
            self.pq_adjust(c, old, new);
        }
    }

    // ------------------------------------------------------------------ group splits
    fn start_group_split(&mut self, g: u32) {
        let gr = self.g[g];
        if !gr.alive {
            fail("group: split of a dead group");
        }
        let c = gr.chk;
        let cr = self.c[c];
        let lab_l = if g == cr.first {
            gr.lab.sub_pos(self.dg).unwrap_or_else(|| fail("group: no room before first"))
        } else {
            GL::mid(self.g[gr.prev].lab, gr.lab).unwrap_or_else(|| fail("group: no room left"))
        };
        let lab_r = if g == cr.last {
            gr.lab.add_below(self.dg, self.p.b_g).unwrap_or_else(|| fail("group: no room after last"))
        } else {
            GL::mid(gr.lab, self.g[gr.next].lab).unwrap_or_else(|| fail("group: no room right"))
        };
        self.work += 1;
        let gl = self.new_group(c);
        let grr = self.new_group(c);
        {
            let l = &mut self.g[gl];
            l.lab = lab_l;
            l.st = OVERFLOW;
            l.src = g;
            l.prev = gr.prev;
            l.next = g;
        }
        if gr.prev != NIL {
            self.g[gr.prev].next = gl;
        } else {
            self.first_group = gl;
        }
        {
            let r = &mut self.g[grr];
            r.lab = lab_r;
            r.st = OVERFLOW;
            r.src = g;
            r.prev = g;
            r.next = gr.next;
        }
        if gr.next != NIL {
            self.g[gr.next].prev = grr;
        }
        let gm = &mut self.g[g];
        gm.prev = gl;
        gm.next = grr;
        gm.st = SPLITTING;
        gm.l = gl;
        gm.r = grr;
        if cr.first == g {
            self.c[c].first = gl;
        }
        if cr.last == g {
            self.c[c].last = grr;
        }
    }

    fn drive_group(&mut self, g: u32) {
        let s = match self.g[g].st {
            SPLITTING => g,
            OVERFLOW => self.g[g].src,
            _ => return,
        };
        for _ in 0..self.p.k_g {
            if !self.group_split_step(s) {
                return;
            }
        }
    }

    fn group_split_step(&mut self, g: u32) -> bool {
        let gr = self.g[g];
        if !gr.alive {
            fail("group split: dead group");
        }
        if gr.first == NIL {
            self.remove_group(g);
            return false;
        }
        let (gl, grr) = (gr.l, gr.r);
        let (lsz, rsz) = (self.g[gl].size, self.g[grr].size);
        let (e, lab, dst);
        if lsz <= rsz {
            let l = self.g[gl];
            if l.next != g {
                fail("group split: left sibling not adjacent");
            }
            e = gr.first;
            lab = if l.first == NIL {
                self.center_e
            } else {
                match self.e[l.last].lab().checked_add(self.p.d_e) {
                    Some(v) if self.p.b_e >= 128 || v >> self.p.b_e == 0 => v,
                    _ => fail("elem: push-back room"),
                }
            };
            self.work += 1;
            let nf = if gr.first == gr.last { NIL } else { self.e[e].next };
            let gm = &mut self.g[g];
            gm.first = nf;
            if nf == NIL {
                gm.last = NIL;
            }
            let lm = &mut self.g[gl];
            if lm.first == NIL {
                lm.first = e;
            }
            lm.last = e;
            dst = gl;
        } else {
            let r = self.g[grr];
            if r.prev != g {
                fail("group split: right sibling not adjacent");
            }
            e = gr.last;
            lab = if r.first == NIL {
                self.center_e
            } else {
                let b = self.e[r.first].lab();
                if b < self.p.d_e {
                    fail("elem: push-front room");
                }
                b - self.p.d_e
            };
            self.work += 1;
            let nl = if gr.first == gr.last { NIL } else { self.e[e].prev };
            let gm = &mut self.g[g];
            gm.last = nl;
            if nl == NIL {
                gm.first = NIL;
            }
            let rm = &mut self.g[grr];
            if rm.first == NIL {
                rm.last = e;
            }
            rm.first = e;
            dst = grr;
        }
        let em = &mut self.e[e];
        em.grp = dst;
        em.lab = lab2(lab);
        self.g[g].size -= 1;
        self.g[dst].size += 1;
        if self.g[dst].chk != gr.chk {
            fail("group split: move across chunks");
        }
        true
    }

    fn remove_group(&mut self, g: u32) {
        self.work += 1;
        let gr = self.g[g];
        let c = gr.chk;
        if gr.prev != NIL {
            self.g[gr.prev].next = gr.next;
        } else {
            self.first_group = gr.next;
        }
        if gr.next != NIL {
            self.g[gr.next].prev = gr.prev;
        }
        let cr = self.c[c];
        if cr.first == g && cr.last == g {
            self.c[c].first = NIL;
            self.c[c].last = NIL;
        } else if cr.first == g {
            self.c[c].first = gr.next;
        } else if cr.last == g {
            self.c[c].last = gr.prev;
        }
        let mut quiet = [NIL; 2];
        for (k, s) in [gr.l, gr.r].into_iter().enumerate() {
            let sm = &mut self.g[s];
            if sm.st == OVERFLOW && sm.src == g {
                sm.st = QUIET;
                sm.src = NIL;
                quiet[k] = s;
            }
        }
        let gm = &mut self.g[g];
        gm.alive = false;
        gm.next = NIL;
        gm.prev = NIL;
        self.free_g.push(g);
        for s in quiet {
            if s != NIL && self.g[s].size >= self.p.g {
                self.start_group_split(s);
            }
        }
    }

    // ------------------------------------------------------------------ chunk splits
    fn drive_chunk(&mut self, c: u32) {
        let s = match self.c[c].st {
            SPLITTING => c,
            OVERFLOW => self.c[c].src,
            _ => return,
        };
        for _ in 0..self.p.k_c {
            if !self.chunk_split_step(s) {
                return;
            }
        }
    }

    /// The groups one chunk-split move takes from the left or right end of chunk x: a whole
    /// family of a splitting group, or one group.
    fn unit(&self, x: u32, left: bool) -> ([u32; 3], usize) {
        let xr = self.c[x];
        let g0 = if left { xr.first } else { xr.last };
        let g0r = self.g[g0];
        if g0r.st == OVERFLOW {
            let s = self.g[g0r.src];
            let u = if left && s.l == g0 {
                [g0, g0r.src, s.r]
            } else if !left && s.r == g0 {
                [s.l, g0r.src, g0]
            } else {
                return ([g0, NIL, NIL], 1);
            };
            for a in u {
                if self.g[a].chk != x {
                    fail("chunk split: family not contiguous in chunk");
                }
            }
            if self.g[u[0]].next != u[1] || self.g[u[1]].next != u[2] {
                fail("chunk split: family not contiguous in chunk");
            }
            return (u, 3);
        }
        ([g0, NIL, NIL], 1)
    }

    fn chunk_split_step(&mut self, x: u32) -> bool {
        let xr = self.c[x];
        if xr.first == NIL {
            self.remove_chunk(x);
            return false;
        }
        let (y, z) = (xr.l, xr.r);
        let (yr, zr) = (self.c[y], self.c[z]);
        let left = yr.size <= zr.size;
        let (unit, k) = self.unit(x, left);
        let mut labs = [GL::zero(); 3];
        if left {
            if yr.next != x {
                fail("chunk split: left sibling not adjacent");
            }
            let mut prev = if yr.first == NIL { None } else { Some(self.g[yr.last].lab) };
            for lab in labs.iter_mut().take(k) {
                let v = match prev {
                    None => self.center_g,
                    Some(p) => p.add_below(self.dg, self.p.b_g).unwrap_or_else(|| fail("group: push-back room")),
                };
                *lab = v;
                prev = Some(v);
            }
        } else {
            if zr.prev != x {
                fail("chunk split: right sibling not adjacent");
            }
            let mut nxt = if zr.first == NIL { None } else { Some(self.g[zr.first].lab) };
            for i in (0..k).rev() {
                let v = match nxt {
                    None => self.center_g,
                    Some(p) => p.sub_pos(self.dg).unwrap_or_else(|| fail("group: push-front room")),
                };
                labs[i] = v;
                nxt = Some(v);
            }
        }
        self.work += k as u64;
        let (first, last) = (unit[0], unit[k - 1]);
        let dst;
        if left {
            if xr.last == last {
                self.c[x].first = NIL;
                self.c[x].last = NIL;
            } else {
                self.c[x].first = self.g[last].next;
            }
            if yr.first == NIL {
                self.c[y].first = first;
            }
            self.c[y].last = last;
            dst = y;
        } else {
            if xr.first == first {
                self.c[x].first = NIL;
                self.c[x].last = NIL;
            } else {
                self.c[x].last = self.g[first].prev;
            }
            if zr.first == NIL {
                self.c[z].last = last;
            }
            self.c[z].first = first;
            dst = z;
        }
        let mut s = 0;
        for i in 0..k {
            let gm = &mut self.g[unit[i]];
            gm.chk = dst;
            gm.lab = labs[i];
            s += gm.size;
        }
        self.c[x].size -= s;
        self.c[dst].size += s;
        true
    }

    fn remove_chunk(&mut self, x: u32) {
        self.work += 1;
        self.c[x].st = DEAD;
        let xr = self.c[x];
        for s in [xr.l, xr.r] {
            let sr = self.c[s];
            if sr.st == OVERFLOW && sr.src == x {
                self.c[s].st = QUIET;
                self.c[s].src = NIL;
                let sz = self.c[s].size;
                if sz > self.p.theta {
                    self.pq_insert_scan(s, sz);
                }
            }
        }
    }

    // ------------------------------------------------------------------ reservation
    fn reservation(&mut self, k: u32) {
        for _ in 0..k {
            if let Job::Idle = self.job {
                if self.pq_hi == NIL {
                    return;
                }
                let x = self.pq_pop_max();
                let y = self.new_chunk();
                let z = self.new_chunk();
                let xp = self.c[x].prev;
                let xn = self.c[x].next;
                self.c[y].prev = xp;
                self.c[y].next = x;
                if xp != NIL {
                    self.c[xp].next = y;
                } else {
                    self.first_chunk = y;
                }
                self.c[x].prev = y;
                self.c[z].prev = x;
                self.c[z].next = xn;
                if xn != NIL {
                    self.c[xn].prev = z;
                }
                self.c[x].next = z;
                self.insert_around(x, y, z);
                let xm = &mut self.c[x];
                xm.st = SPLITTING;
                xm.l = y;
                xm.r = z;
                for w in [y, z] {
                    self.c[w].st = OVERFLOW;
                    self.c[w].src = x;
                }
            } else {
                self.step();
            }
        }
    }

    // ------------------------------------------------------------------ priority queue
    fn pq_link_after(&mut self, s: u32, p: u32) {
        let n;
        if p == NIL {
            n = self.pq_lo;
            self.pq_lo = s;
        } else {
            n = dec(self.pq_nbn[p]);
            self.pq_nbn[p] = enc(s);
        }
        self.pq_nbp[s] = enc(p);
        self.pq_nbn[s] = enc(n);
        if n != NIL {
            self.pq_nbp[n] = enc(s);
        } else {
            self.pq_hi = s;
        }
    }

    fn pq_add(&mut self, c: u32, s: u32, p: u32) {
        let h = dec(self.pq_head[s]);
        {
            let cm = &mut self.c[c];
            cm.pq_b = s;
            cm.pq_prev = NIL;
            cm.pq_next = h;
        }
        self.pq_head[s] = enc(c);
        if h != NIL {
            self.c[h].pq_prev = c;
        } else {
            self.pq_link_after(s, p);
        }
    }

    fn pq_del(&mut self, c: u32) {
        let cr = self.c[c];
        let s = cr.pq_b;
        if cr.pq_prev != NIL {
            self.c[cr.pq_prev].pq_next = cr.pq_next;
        } else {
            self.pq_head[s] = enc(cr.pq_next);
        }
        if cr.pq_next != NIL {
            self.c[cr.pq_next].pq_prev = cr.pq_prev;
        }
        if dec(self.pq_head[s]) == NIL {
            let (p, n) = (dec(self.pq_nbp[s]), dec(self.pq_nbn[s]));
            if p != NIL {
                self.pq_nbn[p] = enc(n);
            } else {
                self.pq_lo = n;
            }
            if n != NIL {
                self.pq_nbp[n] = enc(p);
            } else {
                self.pq_hi = p;
            }
        }
    }

    fn pq_insert_scan(&mut self, c: u32, s: u32) {
        assert!((s as usize) < self.pq_head.cap, "chunk too large for the queue");
        let th = self.p.theta;
        let mut p = s - 1;
        while p > th && dec(self.pq_head[p]) == NIL {
            p -= 1;
            self.pq_scan += 1;
        }
        self.pq_add(c, s, if p > th { p } else { NIL });
    }

    fn pq_adjust(&mut self, c: u32, old: u32, new: u32) {
        let th = self.p.theta;
        if old <= th && th < new {
            self.pq_insert_scan(c, new);
        } else if new <= th && th < old {
            self.pq_del(c);
        } else if old > th && new > th {
            assert!((new as usize) < self.pq_head.cap, "chunk too large for the queue");
            if new == old + 1 {
                let multi = self.c[c].pq_prev != NIL || self.c[c].pq_next != NIL;
                let p = if multi { old } else { dec(self.pq_nbp[old]) };
                self.pq_del(c);
                self.pq_add(c, new, p);
            } else if new + 1 == old {
                let p = dec(self.pq_nbp[old]);
                self.pq_del(c);
                self.pq_add(c, new, p);
            } else {
                self.pq_del(c);
                self.pq_insert_scan(c, new);
            }
        }
    }

    fn pq_pop_max(&mut self) -> u32 {
        let c = dec(self.pq_head[self.pq_hi]);
        self.pq_del(c);
        c
    }

    // ------------------------------------------------------------------ top structure
    #[inline]
    fn tag_set(&self, t: &mut Tag, j: usize, v: u64) {
        t[H_MAX - j] = v;
    }

    #[inline]
    fn find(&self, t: u32, e: u32) -> Option<usize> {
        let tn = &self.n[t];
        tn.tab_e[..tn.ntab as usize].iter().position(|&x| x == e)
    }

    #[inline]
    fn lab_in(&self, t: u32, e: u32) -> u64 {
        match self.find(t, e) {
            Some(i) => self.n[t].tab_l[i],
            None => fail("top: missing table entry"),
        }
    }

    fn guard_tag(&self, c: u32, t: &Tag) {
        let cr = &self.c[c];
        if cr.prev != NIL && !(self.c[cr.prev].tag < *t) {
            fail("top: tag not above predecessor");
        }
        if cr.next != NIL && !(*t < self.c[cr.next].tag) {
            fail("top: tag not below successor");
        }
    }

    fn room_next_to(&self, t: u32, e: u32, before: bool) -> u64 {
        let i = self.find(t, e).unwrap_or_else(|| fail("top: missing table entry"));
        let tn = &self.n[t];
        let (lo, hi): (i128, i128) = if before {
            (if i > 0 { tn.tab_l[i - 1] as i128 } else { -1 }, tn.tab_l[i] as i128)
        } else {
            (tn.tab_l[i] as i128, if i + 1 < tn.ntab as usize { tn.tab_l[i + 1] as i128 } else { 1i128 << self.p.beta })
        };
        if lo + 1 >= hi {
            fail("top: table full");
        }
        ((lo + hi) / 2) as u64
    }

    fn table_insert(&mut self, t: u32, e: u32, new: u32, before: bool, lab: u64) {
        let i = self.find(t, e).unwrap_or_else(|| fail("top: missing table entry"));
        let tn = &mut self.n[t];
        let nt = tn.ntab as usize;
        assert!(nt < TMAX, "table overflow");
        let pos = if before { i } else { i + 1 };
        let se = tn.side[i];
        tn.tab_e.copy_within(pos..nt, pos + 1);
        tn.tab_l.copy_within(pos..nt, pos + 1);
        tn.side.copy_within(pos..nt, pos + 1);
        tn.tab_e[pos] = new;
        tn.tab_l[pos] = lab;
        tn.side[pos] = if tn.draining { se } else { 0 };
        tn.ntab += 1;
        self.work += (nt - pos) as u64 + 1;
        self.max_table = self.max_table.max(nt + 1);
    }

    fn table_remove(&mut self, t: u32, e: u32) {
        if let Some(i) = self.find(t, e) {
            let tn = &mut self.n[t];
            let nt = tn.ntab as usize;
            tn.tab_e.copy_within(i + 1..nt, i);
            tn.tab_l.copy_within(i + 1..nt, i);
            tn.side.copy_within(i + 1..nt, i);
            tn.ntab -= 1;
            self.work += (nt - i) as u64;
        }
    }

    /// Add table `t` to the "tables containing" list of entry `e` at height `h` (0 = chunk).
    fn in_push(&mut self, e: u32, h: usize, t: u32) {
        if h == 0 {
            let cm = &mut self.c[e];
            assert!((cm.ncin as usize) < IMAX);
            cm.cin[cm.ncin as usize] = t;
            cm.ncin += 1;
        } else {
            let nm = &mut self.n[e];
            assert!((nm.nin as usize) < IMAX);
            nm.ins[nm.nin as usize] = t;
            nm.nin += 1;
        }
    }

    fn in_remove(&mut self, e: u32, h: usize, t: u32) {
        let (arr, len) = if h == 0 {
            let cm = &mut self.c[e];
            (&mut cm.cin, &mut cm.ncin)
        } else {
            let nm = &mut self.n[e];
            (&mut nm.ins, &mut nm.nin)
        };
        let l = *len as usize;
        if let Some(i) = arr[..l].iter().position(|&x| x == t) {
            arr.copy_within(i + 1..l, i);
            *len -= 1;
        }
    }

    fn insert_around(&mut self, x: u32, y: u32, z: u32) {
        let xr = self.c[x];
        let tabs = xr.cin;
        let nt = xr.ncin as usize;
        let mut ly = [0u64; IMAX];
        let mut lz = [0u64; IMAX];
        let mut f1 = None;
        for q in 0..nt {
            ly[q] = self.room_next_to(tabs[q], x, true);
            lz[q] = self.room_next_to(tabs[q], x, false);
            if tabs[q] == xr.path[1] {
                f1 = Some(q);
            }
        }
        let q1 = f1.unwrap_or_else(|| fail("top: path not in tables"));
        let mut ty = xr.tag;
        self.tag_set(&mut ty, 1, ly[q1]);
        let mut tz = xr.tag;
        self.tag_set(&mut tz, 1, lz[q1]);
        self.guard_tag(y, &ty);
        self.guard_tag(z, &tz);
        for q in 0..nt {
            self.table_insert(tabs[q], x, y, true, ly[q]);
            self.table_insert(tabs[q], x, z, false, lz[q]);
        }
        for c in [y, z] {
            let cm = &mut self.c[c];
            cm.cin = tabs;
            cm.ncin = nt as u8;
            cm.lpar = xr.lpar;
        }
        let lp = xr.lpar;
        let ln = &mut self.n[lp];
        let k = ln.nkids as usize;
        assert!(k + 2 <= KMAX, "children overflow");
        let i = ln.kids[..k].iter().position(|&c| c == x).unwrap_or_else(|| fail("top: chunk not a child"));
        ln.kids.copy_within(i + 1..k, i + 3);
        ln.kids[i] = y;
        ln.kids[i + 1] = x;
        ln.kids[i + 2] = z;
        ln.nkids += 2;
        self.c[y].tag = ty;
        self.c[z].tag = tz;
        self.work += 1;
        self.job = Job::Copy { x, y, z, j: 1 };
    }

    /// One step of the job; false once it has finished.
    fn step(&mut self) -> bool {
        self.work += 1;
        loop {
            match self.job {
                Job::Idle => return false,
                Job::Copy { x, y, z, j } => {
                    let jj = j as usize;
                    let v = self.c[x].path[jj];
                    self.c[y].path[jj] = v;
                    self.c[z].path[jj] = v;
                    let vm = &mut self.n[v];
                    if vm.first == x {
                        vm.first = y;
                    }
                    if vm.last == x {
                        vm.last = z;
                    }
                    self.job = if jj == self.p.h { Job::Walk { v: self.c[y].lpar } } else { Job::Copy { x, y, z, j: j + 1 } };
                    return true;
                }
                Job::Walk { v } => {
                    if v == NIL {
                        self.job = Job::Idle;
                        return false;
                    }
                    let vm = &mut self.n[v];
                    let up = vm.live_parent;
                    vm.weight += 2;
                    if up != NIL && !vm.draining && vm.overflow_of == NIL && vm.weight as u64 > self.wh[vm.height as usize] {
                        self.start_drain(v);
                        self.job = Job::After { v, up };
                        return true;
                    }
                    self.job = Job::After { v, up };
                }
                Job::After { v, up } => {
                    let src = self.n[v].overflow_of;
                    self.job = if src != NIL { Job::Sweep { up, src, i: 0 } } else { Job::End { up } };
                }
                Job::Sweep { up, src, i } => {
                    if i < self.p.s && self.drain_step(src) {
                        self.job = Job::Sweep { up, src, i: i + 1 };
                        return true;
                    }
                    self.job = Job::End { up };
                }
                Job::End { up } => {
                    self.job = Job::Walk { v: up };
                    return true;
                }
            }
        }
    }

    fn same_drain(&self, a: u32, b: u32) -> bool {
        let (an, bn) = (&self.n[a], &self.n[b]);
        an.overflow_of != NIL && an.overflow_of == bn.overflow_of
    }

    fn start_drain(&mut self, v: u32) {
        let vn = self.n[v];
        let h = vn.height as usize;
        let nk = vn.nkids as usize;
        if nk < 2 {
            return;
        }
        let kids = &vn.kids[..nk];
        let wt = |s: &Self, e: u32| if h == 1 { 1u64 } else { s.n[e].weight as u64 };
        let total: u64 = kids.iter().map(|&e| wt(self, e)).sum();
        let (mut acc, mut k) = (0u64, 0usize);
        while k < nk - 1 && acc + wt(self, kids[k]) <= total / 2 {
            acc += wt(self, kids[k]);
            k += 1;
        }
        k = k.max(1);
        if h > 1 {
            while k > 0 && k < nk && self.same_drain(kids[k - 1], kids[k]) {
                k += 1;
            }
            if k >= nk {
                k = nk - 1;
                while k > 0 && self.same_drain(kids[k - 1], kids[k]) {
                    k -= 1;
                }
            }
            if k == 0 {
                return;
            }
        }
        let boundary = kids[k];
        let nt = vn.ntab as usize;
        let mut side = [LEFT; TMAX];
        let mut s_ = LEFT;
        for i in 0..nt {
            if vn.tab_e[i] == boundary {
                s_ = RIGHT;
            }
            side[i] = s_;
        }
        // entries that still matter: live children and ghosts with chunks
        let mut keep = [true; TMAX];
        if h > 1 {
            for i in 0..nt {
                let en = &self.n[vn.tab_e[i]];
                keep[i] = en.live_parent == v || en.first != NIL;
            }
            for i in 0..nt {
                let en = self.n[vn.tab_e[i]];
                if keep[i] && en.draining {
                    let j = vn.tab_e[..nt].iter().position(|&x| x == en.t1).unwrap_or_else(|| fail("top: target missing"));
                    side[i] = side[j];
                }
            }
        }
        let nin = vn.nin as usize;
        let mut l1 = [0u64; IMAX];
        let mut l2 = [0u64; IMAX];
        for q in 0..nin {
            l1[q] = self.room_next_to(vn.ins[q], v, true);
            l2[q] = self.room_next_to(vn.ins[q], v, false);
        }
        // -- mutate
        self.drains += 1;
        let v1 = self.new_node(h);
        let v2 = self.new_node(h);
        for q in 0..nin {
            self.table_insert(vn.ins[q], v, v1, true, l1[q]);
            self.table_insert(vn.ins[q], v, v2, false, l2[q]);
        }
        for (w, sd) in [(v1, LEFT), (v2, RIGHT)] {
            let np = (0..nt).filter(|&i| keep[i] && side[i] == sd).count();
            let gap = (1u128 << self.p.beta) / (np as u128 + 1);
            let mut j = 0;
            for i in 0..nt {
                if keep[i] && side[i] == sd {
                    let e = vn.tab_e[i];
                    let wm = &mut self.n[w];
                    wm.tab_e[j] = e;
                    wm.tab_l[j] = ((j as u128 + 1) * gap) as u64;
                    j += 1;
                    self.in_push(e, h - 1, w);
                }
            }
            let wm = &mut self.n[w];
            wm.ntab = j as u8;
            wm.ins = vn.ins;
            wm.nin = vn.nin;
            self.work += j as u64;
            self.max_table = self.max_table.max(j);
        }
        let mut wsum = [0u64; 2];
        for (i, &e) in kids.iter().enumerate() {
            let (w, sidx) = if i < k { (v1, 0) } else { (v2, 1) };
            wsum[sidx] += wt(self, e);
            if h == 1 {
                self.c[e].lpar = w;
            } else {
                self.n[e].live_parent = w;
            }
            let wm = &mut self.n[w];
            wm.kids[wm.nkids as usize] = e;
            wm.nkids += 1;
        }
        for (w, ws) in [(v1, wsum[0]), (v2, wsum[1])] {
            let wm = &mut self.n[w];
            wm.weight = ws as u32;
            wm.live_parent = vn.live_parent;
            wm.overflow_of = v;
        }
        let par = vn.live_parent;
        let pn = &mut self.n[par];
        let pk = pn.nkids as usize;
        assert!(pk < KMAX, "children overflow");
        let i = pn.kids[..pk].iter().position(|&c| c == v).unwrap_or_else(|| fail("top: node not a child"));
        pn.kids.copy_within(i + 1..pk, i + 2);
        pn.kids[i] = v1;
        pn.kids[i + 1] = v2;
        pn.nkids += 1;
        let vm = &mut self.n[v];
        vm.draining = true;
        vm.t1 = v1;
        vm.t2 = v2;
        vm.side = side;
        vm.live_parent = NIL;
        vm.nkids = 0;
        self.work += nt as u64;
    }

    fn drain_step(&mut self, v: u32) -> bool {
        let vn = &self.n[v];
        if !vn.alive {
            return false;
        }
        let h = vn.height as usize;
        if vn.first == NIL {
            self.finish_drain(v);
            return false;
        }
        let side_of = |s: &Self, below: u32| -> u8 {
            match s.find(v, below) {
                Some(i) => s.n[v].side[i],
                None => fail("top: missing table entry"),
            }
        };
        let mut y = vn.first;
        let mut below = if h == 1 { y } else { self.c[y].path[h - 1] };
        let (t, left) = if side_of(self, below) == LEFT {
            (vn.t1, true)
        } else {
            y = vn.last;
            below = if h == 1 { y } else { self.c[y].path[h - 1] };
            if side_of(self, below) != RIGHT {
                fail("top: drain sides out of order");
            }
            (vn.t2, false)
        };
        let par = self.c[y].path[h + 1];
        let mut tag = self.c[y].tag;
        let (lp, lt) = (self.lab_in(par, t), self.lab_in(t, below));
        self.tag_set(&mut tag, h + 1, lp);
        self.tag_set(&mut tag, h, lt);
        self.guard_tag(y, &tag);
        // -- mutate
        self.work += 1;
        let cm = &mut self.c[y];
        cm.tag = tag;
        cm.path[h] = t;
        let (yn, yp) = (cm.next, cm.prev);
        let vm = &mut self.n[v];
        if vm.first == vm.last {
            vm.first = NIL;
            vm.last = NIL;
        } else if left {
            vm.first = yn;
        } else {
            vm.last = yp;
        }
        let tm = &mut self.n[t];
        if left {
            if tm.first == NIL {
                tm.first = y;
            }
            tm.last = y;
        } else {
            if tm.last == NIL {
                tm.last = y;
            }
            tm.first = y;
        }
        true
    }

    fn finish_drain(&mut self, v: u32) {
        let vn = self.n[v];
        let h = vn.height as usize;
        for i in 0..vn.ntab as usize {
            self.in_remove(vn.tab_e[i], h - 1, v);
        }
        for q in 0..vn.nin as usize {
            self.table_remove(vn.ins[q], v);
        }
        for t in [vn.t1, vn.t2] {
            if self.n[t].overflow_of == v {
                self.n[t].overflow_of = NIL;
            }
        }
        let vm = &mut self.n[v];
        vm.alive = false;
        vm.nin = 0;
        self.work += vn.ntab as u64;
    }

    // ------------------------------------------------------------------ checking
    /// The tag computed from a chunk's stored path, if the path is complete.
    fn tag_of(&self, c: u32) -> Option<Tag> {
        let cr = &self.c[c];
        let mut t = [0u64; H_MAX];
        let mut below = c;
        for j in 1..=self.p.h {
            let v = cr.path[j];
            if v == NIL {
                return None;
            }
            self.tag_set(&mut t, j, self.lab_in(v, below));
            below = v;
        }
        Some(t)
    }

    /// Full check (O(n)): the element list is `reference` (element indices in list order,
    /// sentinel first), keys strictly increase along it, groups tile elements and chunks tile
    /// groups, and every completed path gives the chunk's tag. Panics on a violation.
    pub fn check(&self, reference: &[u32]) {
        let mut e = self.head;
        let mut i = 0;
        let mut prev = NIL;
        while e != NIL {
            assert_eq!(reference.get(i).copied(), Some(e), "element list differs at {i}");
            if prev != NIL {
                assert!(self.order(prev, e), "keys not increasing at {i}");
                assert!(!self.order(e, prev), "order not strict at {i}");
            }
            prev = e;
            e = self.e[e].next;
            i += 1;
        }
        assert_eq!(i, reference.len(), "list length");
        self.check_structure();
    }

    /// The structural part of `check` (nesting, tags, queue).
    pub fn check_structure(&self) {
        let mut g = self.first_group;
        let mut e = self.head;
        while g != NIL {
            let gr = &self.g[g];
            assert!(gr.alive);
            let mut sz = 0;
            if gr.first != NIL {
                assert_eq!(gr.first, e, "group range not contiguous");
                loop {
                    assert_eq!(self.e[e].grp, g);
                    sz += 1;
                    if e == gr.last {
                        break;
                    }
                    e = self.e[e].next;
                }
                e = self.e[e].next;
            }
            assert_eq!(sz, gr.size, "group size");
            g = gr.next;
        }
        assert_eq!(e, NIL, "groups do not cover the list");
        let mut c = self.first_chunk;
        let mut g = self.first_group;
        let mut prev_tag: Option<Tag> = None;
        while c != NIL {
            let cr = &self.c[c];
            let mut sz = 0;
            if cr.first != NIL {
                assert_eq!(cr.first, g, "chunk range not contiguous");
                loop {
                    assert_eq!(self.g[g].chk, c);
                    sz += self.g[g].size;
                    if g == cr.last {
                        break;
                    }
                    g = self.g[g].next;
                }
                g = self.g[g].next;
            }
            assert_eq!(sz, cr.size, "chunk size");
            if let Some(p) = prev_tag {
                assert!(p < cr.tag, "chunk tags not increasing");
            }
            prev_tag = Some(cr.tag);
            if self.ready {
                if let Some(t) = self.tag_of(c) {
                    assert_eq!(t, cr.tag, "tag differs from the stored path");
                }
            }
            c = cr.next;
        }
        assert_eq!(g, NIL, "chunks do not cover the groups");
        assert_eq!(self.pq_scan, 0, "slow path of the queue taken");
    }
}

// ---------------------------------------------------------------------------------- the wrapper

/// A handle's record: its element in the core of each parity, and the epoch in which it was
/// copied into (or mirrored to) the next core.
#[derive(Clone, Copy)]
struct Hrec {
    slot: [u32; 2],
    stamp: u32,
}

const N_MIN: u64 = 64;

/// The full structure (`prototype/wrapper.py`, the verified program's `insertWS`, `deleteWS`,
/// `orderWS`): handles are the insertion counter.
pub struct Native<GL: GLab> {
    kb: u32,
    pub cur: Core<GL>,
    pub nxt: Option<Core<GL>>,
    cursor: u32,
    pub cursor_set: bool,
    pub live: u64,
    next_handle: u64,
    pub rebuilds: u64,
    epoch: u32,
    hs: Arena<Hrec>,
    /// Retired cores, kept for reuse as the mapping of a later core (their memory is not given
    /// back to the system: doing so costs up to tens of µs in single operations).
    retired: Vec<Core<GL>>,
    mk: fn(u64) -> Params,
    retired_work: u64,
    spare: Option<Spare>,
    rr: usize,
    /// Rebuilds whose core did not fit the spare mapping (mapped in the operation itself).
    pub spare_misses: u64,
    /// The memory action of the last operation (diagnostic): 0 `cur`, 1 `nxt`, 2 handles, 3 spare
    /// (4 if a new spare was taken), 9 none.
    pub last_action: u8,
    /// Nanoseconds of the last operation's parts (feature `prof`, diagnostic): upkeep, the spare's
    /// remaining preparation at a rebuild start, the creation of the next core, the rest.
    #[cfg(feature = "prof")]
    pub prof: [u64; 4],
}

impl<GL: GLab> Native<GL> {
    /// The structure with `K_B = kb`, for up to `max_handles` insertions in all.
    pub fn new(kb: u32, max_handles: usize) -> Self {
        Self::with_params(kb, max_handles, Params::verified)
    }

    pub fn with_params(kb: u32, max_handles: usize, mk: fn(u64) -> Params) -> Self {
        assert!(kb >= 2);
        Native {
            kb,
            cur: Core::create(mk(N_MIN), false, false),
            nxt: None,
            cursor: NIL,
            cursor_set: false,
            live: 0,
            next_handle: 0,
            rebuilds: 0,
            epoch: 0,
            hs: Arena::new(max_handles + 1, false),
            retired: Vec::new(),
            mk,
            retired_work: 0,
            spare: None,
            rr: 0,
            spare_misses: 0,
            last_action: 9,
            #[cfg(feature = "prof")]
            prof: [0; 4],
        }
    }

    #[inline]
    fn cs(&self) -> usize { (self.epoch & 1) as usize }
    #[inline]
    fn ns(&self) -> usize { ((self.epoch + 1) & 1) as usize }

    /// Per-operation upkeep, at most one memory action (round robin among those with something
    /// to do): map a page ahead in `cur`, in `nxt` or in the handles; prepare the spare mapping for
    /// the next core to be created (take a retired core's mapping that fits, or map a new one;
    /// then map a page ahead in one of its arrays or clear one of its queue arrays).
    #[inline]
    fn upkeep(&mut self) {
        for i in 0..4 {
            let a = (self.rr + i) % 4;
            let did = match a {
                0 => self.cur.prefault(),
                1 => self.nxt.as_mut().is_some_and(|n| n.prefault()),
                2 => self.hs.prefault(2 * PAGE),
                _ => match self.spare.as_mut() {
                    Some(sp) => sp.touch_one(),
                    None => {
                        // the next core's capacity is at most 4N (Lemma W); while a rebuild runs,
                        // the mapping is prepared for the core after it, whose rebuild can start
                        // right at the swap (when deletions empty the new core while it is built)
                        let base = self.nxt.as_ref().map_or(self.cur.p.n, |n| n.p.n);
                        let p = (self.mk)(4 * base);
                        let fit = (0..self.retired.len()).filter(|&i| self.retired[i].region_fits(&p))
                            .min_by_key(|&i| self.retired[i].region_bytes());
                        self.spare = Some(match fit {
                            Some(i) => self.retired.swap_remove(i).into_spare(),
                            None => Core::<GL>::spare_for(&p),
                        });
                        true
                    }
                },
            };
            if did {
                self.rr = a + 1;
                self.last_action = a as u8;
                return;
            }
        }
        self.last_action = 9;
    }

    pub fn insert_first(&mut self) -> u64 {
        self.insert(None)
    }

    pub fn insert_after(&mut self, x: u64) -> u64 {
        self.insert(Some(x))
    }

    fn insert(&mut self, hx: Option<u64>) -> u64 {
        self.upkeep();
        let hy = self.next_handle;
        self.next_handle += 1;
        let r = self.hs.push(Hrec { slot: [NIL; 2], stamp: 0 });
        debug_assert_eq!(r as u64, hy);
        let (cs, ns) = (self.cs(), self.ns());
        let xi = match hx { None => self.cur.head, Some(x) => self.hs[x as u32].slot[cs] };
        let yi = self.cur.insert_after_h(xi, hy as u32);
        self.hs[hy as u32].slot[cs] = yi;
        if self.cursor_set && self.nxt.is_some() {
            let copied = match hx { None => true, Some(x) => self.hs[x as u32].stamp == self.epoch + 1 };
            if copied {
                let n = self.nxt.as_mut().unwrap();
                let xn = match hx { None => n.head, Some(x) => self.hs[x as u32].slot[ns] };
                let yn = n.insert_after_h(xn, hy as u32);
                let hr = &mut self.hs[hy as u32];
                hr.slot[ns] = yn;
                hr.stamp = self.epoch + 1;
            }
        }
        self.live += 1;
        self.rebuild_step();
        hy
    }

    pub fn delete(&mut self, x: u64) {
        #[cfg(feature = "prof")]
        let t0 = std::time::Instant::now();
        self.upkeep();
        #[cfg(feature = "prof")]
        { self.prof = [t0.elapsed().as_nanos() as u64, 0, 0, 0]; }
        let (cs, ns) = (self.cs(), self.ns());
        let hr = self.hs[x as u32];
        self.cur.mark_dead(hr.slot[cs]);
        if let Some(n) = self.nxt.as_mut() {
            if hr.stamp == self.epoch + 1 {
                n.mark_dead(hr.slot[ns]);
                self.hs[x as u32].stamp = 0;
            }
        }
        self.live -= 1;
        self.rebuild_step();
    }

    #[inline]
    pub fn order(&self, x: u64, y: u64) -> bool {
        let cs = self.cs();
        self.cur.order(self.hs[x as u32].slot[cs], self.hs[y as u32].slot[cs])
    }

    /// The key of handle `h` in `cur`.
    pub fn key(&self, h: u64) -> (Vec<u64>, GL, u128) {
        self.cur.key(self.hs[h as u32].slot[self.cs()])
    }

    pub fn work(&self) -> u64 {
        self.retired_work + self.cur.work + self.nxt.as_ref().map_or(0, |n| n.work)
    }

    /// The spare mapping's state (diagnostic): arrays not yet mapped, queue arrays not yet
    /// cleared, pages not yet mapped ahead.
    pub fn spare_state(&self) -> Option<(usize, usize, usize)> {
        self.spare.as_ref().map(|sp| {
            let todo = (0..5).map(|i| PRE.min(sp.slots[i]).saturating_sub(sp.done[i]) / PAGE).sum();
            (sp.ptrs.iter().filter(|p| p.is_null()).count(), 8 - sp.clear, todo)
        })
    }

    /// Retired cores kept for reuse.
    pub fn retired(&self) -> usize {
        self.retired.len()
    }

    fn next_capacity(&self) -> u64 {
        let prep = self.cur.p.l as u64 + 2;
        let mirrored = (self.cur.count + prep) / (self.kb as u64 - 1) + 1;
        4 * (self.live + mirrored).max(16)
    }

    fn rebuild_step(&mut self) {
        if self.nxt.is_none() {
            let n = self.cur.p.n;
            if self.cur.count >= n / 2 || (n > N_MIN && self.live < n / 8) {
                let p = (self.mk)(self.next_capacity());
                #[cfg(feature = "prof")]
                let t1 = std::time::Instant::now();
                let sp = match self.spare.take() {
                    Some(mut sp) if Core::<GL>::fits(&p, &sp) => {
                        sp.finish();
                        Some(sp)
                    }
                    other => {
                        if let Some(o) = other {
                            o.unmap();
                        }
                        self.spare_misses += 1;
                        None
                    }
                };
                #[cfg(feature = "prof")]
                let t2 = std::time::Instant::now();
                self.nxt = Some(Core::create_in(p, true, false, sp));
                #[cfg(feature = "prof")]
                { self.prof[1] = (t2 - t1).as_nanos() as u64; self.prof[2] = t2.elapsed().as_nanos() as u64; }
                self.cursor_set = false;
                self.rebuilds += 1;
            }
            return;
        }
        let mut budget = self.kb;
        let ns = self.ns();
        while budget > 0 {
            if !self.cursor_set {
                if self.nxt.as_mut().unwrap().prepare_step() {
                    self.cursor = self.cur.elem_next(self.cur.head);
                    self.cursor_set = true;
                } else {
                    budget -= 1;
                }
                continue;
            }
            if self.cursor != NIL {
                let e = self.cursor;
                if self.cur.elem_live(e) {
                    let h = self.cur.elem_handle(e);
                    let n = self.nxt.as_mut().unwrap();
                    let t = n.tail();
                    let yn = n.insert_after_h(t, h);
                    let hr = &mut self.hs[h];
                    assert_ne!(hr.stamp, self.epoch + 1, "cursor met an already-copied element");
                    hr.slot[ns] = yn;
                    hr.stamp = self.epoch + 1;
                }
                self.cursor = self.cur.elem_next(e);
                budget -= 1;
            }
            if self.cursor == NIL {
                let n = self.nxt.take().unwrap();
                let old = std::mem::replace(&mut self.cur, n);
                self.retired_work += old.work;
                // the retired core's mapping becomes the spare for the next core if it is large
                // enough (no system call, no page fault); otherwise it is kept for later reuse
                let next = (self.mk)(4 * self.cur.p.n);
                if self.spare.is_none() && old.region_fits(&next) {
                    self.spare = Some(old.into_spare());
                } else {
                    self.retired.push(old);
                }
                self.epoch += 1;
                return;
            }
        }
    }

    /// Digests of `cur` and of `nxt` (-1 if there is none or it is not yet being filled).
    pub fn digests(&self) -> (u64, i64) {
        let d2 = match &self.nxt {
            Some(n) if self.cursor_set => n.digest() as i64,
            _ => -1,
        };
        (self.cur.digest(), d2)
    }
}

impl<GL: GLab> Drop for Native<GL> {
    fn drop(&mut self) {
        if let Some(sp) = self.spare.take() {
            sp.unmap();
        }
    }
}
