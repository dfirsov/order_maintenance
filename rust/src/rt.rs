//! The runtime of the generated code: words, arrays and operators, with the semantics of the
//! machine (`lean/OM/Machine/Exec.lean`).
//!
//! * A word is a natural number of arbitrary size (`W`): a `u64`, or a `BigUint` above it.
//! * An array has a capacity; an access at an index beyond it is a machine error (a panic),
//!   and so is a subtraction below 0. The proofs show that neither happens.
//! * `alloc` gives an array a capacity with every cell reading 0. The cells live in blocks of
//!   `BLOCK` cells, each allocated when first written (an unwritten block reads 0), so memory
//!   follows the cells actually used, not the capacities. A cell holding a value of 2^63 or more
//!   refers to the array's table of large values.
//! * `m.cost` counts the machine's steps; `m.peak` is the bit length of the largest value
//!   computed so far (`State.peak`).

use num_bigint::BigUint;
use num_traits::{ToPrimitive, Zero};
use std::cmp::Ordering;

use crate::gen::{ARRS, NARR};

/// A machine word: a natural number. Invariant: `B` only above `u64::MAX`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum W {
    S(u64),
    B(Box<BigUint>),
}

impl Default for W {
    fn default() -> W {
        W::S(0)
    }
}

fn norm(b: BigUint) -> W {
    match b.to_u64() {
        Some(v) => W::S(v),
        None => W::B(Box::new(b)),
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

struct Arr {
    cap: usize,
    blocks: Vec<Option<Box<[u64; BLOCK]>>>,
    big: Vec<BigUint>,
}

impl Arr {
    fn new(cap: usize) -> Arr {
        Arr { cap, blocks: (0..cap.div_ceil(BLOCK)).map(|_| None).collect(), big: Vec::new() }
    }
    #[inline]
    fn get(&self, i: usize) -> u64 {
        match &self.blocks[i / BLOCK] {
            Some(b) => b[i % BLOCK],
            None => 0,
        }
    }
    #[inline]
    fn set(&mut self, i: usize, c: u64) {
        let b = self.blocks[i / BLOCK].get_or_insert_with(|| Box::new([0u64; BLOCK]));
        b[i % BLOCK] = c;
    }
}

/// The machine's memory, step counter and peak.
pub struct M {
    arrs: Vec<Arr>,
    pub cost: u64,
    pub peak: u64,
}

impl M {
    pub fn new() -> M {
        M {
            arrs: (0..NARR).map(|_| Arr::new(0)).collect(),
            cost: 0,
            peak: 0,
        }
    }
    /// Read cell `i` of machine array `arr` (for monitoring; not used by the program).
    pub fn peek(&self, arr: u64, i: usize) -> W {
        let a = ARRS.iter().position(|&x| x == arr).expect("array used by the program");
        let c = self.arrs[a].get(i);
        if c & TAG == 0 { W::S(c) } else { norm(self.arrs[a].big[(c & !TAG) as usize].clone()) }
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
        self.arrs.iter().map(|a| a.blocks.iter().filter(|b| b.is_some()).count() * BLOCK).sum()
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
    let v = if c & TAG == 0 { W::S(c) } else { norm(m.arrs[a].big[(c & !TAG) as usize].clone()) };
    pk(v, m)
}

pub fn store(a: usize, i: W, v: W, m: &mut M) {
    let ix = index(&i, a, m);
    let arr = &mut m.arrs[a];
    let old = arr.get(ix);
    let c = match v {
        W::S(x) if x < TAG => x,
        v => {
            let b = v.to_big();
            if old & TAG != 0 {
                arr.big[(old & !TAG) as usize] = b;
                old
            } else {
                arr.big.push(b);
                TAG | (arr.big.len() - 1) as u64
            }
        }
    };
    arr.set(ix, c);
}

pub fn alloc(a: usize, k: W, m: &mut M) {
    let n = k.as_u64() as usize;
    m.arrs[a] = Arr::new(n);
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
    norm(a.to_big() << (s as usize))
}

fn shr(a: &W, b: &W) -> W {
    let s = match b {
        W::S(s) => *s,
        W::B(_) => return W::S(0),
    };
    match a {
        W::S(x) => W::S(if s >= 64 { 0 } else { x >> s }),
        W::B(x) => {
            if s >= x.bits() { W::S(0) } else { norm((**x).clone() >> (s as usize)) }
        }
    }
}

fn b2w(b: bool) -> W {
    W::S(b as u64)
}

pub fn bin(op: Op, a: W, b: W, m: &mut M) -> W {
    let v = match op {
        Op::Add => match (&a, &b) {
            (W::S(x), W::S(y)) => match x.checked_add(*y) { Some(z) => W::S(z), None => norm(a.to_big() + b.to_big()) },
            _ => norm(a.to_big() + b.to_big()),
        },
        Op::Sub => {
            if a < b {
                panic!("machine error: subtraction below 0");
            }
            match (&a, &b) {
                (W::S(x), W::S(y)) => W::S(x - y),
                _ => norm(a.to_big() - b.to_big()),
            }
        }
        Op::Mul => match (&a, &b) {
            (W::S(x), W::S(y)) => match x.checked_mul(*y) { Some(z) => W::S(z), None => norm(a.to_big() * b.to_big()) },
            _ => norm(a.to_big() * b.to_big()),
        },
        Op::Div => {
            if !b.nz() { W::S(0) } else {
                match (&a, &b) {
                    (W::S(x), W::S(y)) => W::S(x / y),
                    _ => norm(a.to_big() / b.to_big()),
                }
            }
        }
        Op::Mod => {
            if !b.nz() { a.clone() } else {
                match (&a, &b) {
                    (W::S(x), W::S(y)) => W::S(x % y),
                    _ => norm(a.to_big() % b.to_big()),
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
