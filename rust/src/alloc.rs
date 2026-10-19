//! The global allocator: constant-time `alloc` and `free` for small objects, so that no single
//! operation pays for the C allocator's occasional reorganizations (consolidating free chunks,
//! sorting its unsorted list, trimming the heap), which showed up as pauses of several
//! milliseconds when a retired core's large values were freed.
//!
//! Objects of up to `SMALL_MAX` bytes (alignment at most 16) are served from per-size-class free
//! lists (a freed object holds the link to the next one); a list that is empty takes the next
//! bytes of the current chunk (shared by all classes), and a used-up chunk is replaced by a new
//! one of `CHUNK` bytes from the system allocator (the rest of the old one is left unused).
//! Memory of freed objects is reused, never returned. Larger objects go to the system allocator
//! directly (`calloc` for zeroed ones, so that large zeroed memory is still mapped lazily).
//!
//! The program is single-threaded; a spin flag makes the allocator safe anyway.

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::UnsafeCell;
use std::sync::atomic::{AtomicBool, Ordering};

/// Largest object served by the size classes.
const SMALL_MAX: usize = 4096;
/// Size classes: multiples of 16 bytes.
const CLASSES: usize = SMALL_MAX / 16;
/// Bytes per chunk taken from the system.
const CHUNK: usize = 1 << 16;

struct State {
    free: [*mut u8; CLASSES],
    /// The current chunk, shared by all classes, so that objects allocated one after the other
    /// (a shared number and its digits) lie next to each other, as with the C allocator.
    next: *mut u8,
    left: usize,
}

pub struct Alloc {
    lock: AtomicBool,
    st: UnsafeCell<State>,
}

unsafe impl Sync for Alloc {}

impl Alloc {
    pub const fn new() -> Alloc {
        Alloc {
            lock: AtomicBool::new(false),
            st: UnsafeCell::new(State {
                free: [std::ptr::null_mut(); CLASSES],
                next: std::ptr::null_mut(),
                left: 0,
            }),
        }
    }
    #[inline]
    fn class(l: &Layout) -> Option<usize> {
        if l.size() <= SMALL_MAX && l.align() <= 16 { Some((l.size().max(1) + 15) / 16 - 1) } else { None }
    }
    #[inline]
    fn lock(&self) {
        while self.lock.compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed).is_err() {
            std::hint::spin_loop();
        }
    }
    #[inline]
    fn unlock(&self) {
        self.lock.store(false, Ordering::Release);
    }
}

unsafe impl GlobalAlloc for Alloc {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        let Some(c) = Self::class(&l) else { return System.alloc(l) };
        self.lock();
        let st = &mut *self.st.get();
        let p = if !st.free[c].is_null() {
            let p = st.free[c];
            st.free[c] = *(p as *mut *mut u8);
            p
        } else {
            let size = (c + 1) * 16;
            if st.left < size {
                let chunk = System.alloc(Layout::from_size_align_unchecked(CHUNK, 16));
                if chunk.is_null() { self.unlock(); return chunk; }
                st.next = chunk;
                st.left = CHUNK;
            }
            let p = st.next;
            st.next = p.add(size);
            st.left -= size;
            p
        };
        self.unlock();
        p
    }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        if Self::class(&l).is_none() { return System.alloc_zeroed(l); }
        let p = self.alloc(l);
        if !p.is_null() { std::ptr::write_bytes(p, 0, l.size()); }
        p
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        let Some(c) = Self::class(&l) else { return System.dealloc(p, l) };
        self.lock();
        let st = &mut *self.st.get();
        *(p as *mut *mut u8) = st.free[c];
        st.free[c] = p;
        self.unlock();
    }
}
