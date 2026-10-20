impl M {
    /// Experiment: a hash of the contents of all arrays (large values by their digits).
    pub fn digest(&self) -> u64 {
        let mut h: u64 = 0xcbf29ce484222325;
        let mut mix = |x: u64| { h ^= x; h = h.wrapping_mul(0x100000001b3); };
        for (ai, a) in self.arrs.iter().enumerate() {
            for b in 0..a.nblocks {
                let p = unsafe { *a.table.add(b) };
                if p.is_null() { continue; }
                for k in 0..BLOCK {
                    let c = unsafe { (*p)[k] };
                    if c == 0 { continue; }
                    mix(ai as u64); mix((b * BLOCK + k) as u64);
                    if c & TAG == 0 { mix(c) } else { for d in a.big_get(c & !TAG).as_big().to_u64_digits() { mix(d) } }
                }
            }
        }
        h
    }
}
