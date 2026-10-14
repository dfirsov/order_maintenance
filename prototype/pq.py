"""Bucket priority queue over quiet chunks with size > theta (docs/SPEC.md §5.5).

Buckets are indexed by chunk size. Non-empty buckets form a sorted doubly
linked list, so pop_max and +-1 size changes cost O(1). Entering at a size
above theta+1 needs a downward scan for the predecessor bucket; that slow path
is counted in stats.pq_scan and should never happen.

Within a bucket, chunks are kept in insertion order and pop_max takes the most
recently added one (LIFO), so runs are deterministic and the Lean model
(lean/OM/Model) can replay them exactly.
"""
from __future__ import annotations


class BucketPQ:
    def __init__(self, core) -> None:
        self.core = core
        self.theta = core.P.theta
        self.bucket: dict[int, dict[int, None]] = {}   # ordered sets
        self.nb_next: dict[int, int | None] = {}
        self.nb_prev: dict[int, int | None] = {}
        self.hi: int | None = None          # largest non-empty bucket
        self.lo: int | None = None          # smallest non-empty bucket
        self.where: dict[int, int] = {}     # chunk -> its bucket

    def empty(self) -> bool:
        return self.hi is None

    # ---------------------------------------------------------- internals
    def _link_after(self, s: int, p: int | None) -> None:
        """Make empty bucket s non-empty, right after non-empty bucket p (None = new min)."""
        if p is None:
            n = self.lo
            self.lo = s
        else:
            n = self.nb_next[p]
            self.nb_next[p] = s
        self.nb_prev[s] = p
        self.nb_next[s] = n
        if n is not None:
            self.nb_prev[n] = s
        else:
            self.hi = s

    def _add(self, c: int, s: int, p: int | None) -> None:
        b = self.bucket.get(s)
        if b:
            b[c] = None
        else:
            self.bucket[s] = {c: None}
            self._link_after(s, p)
        self.where[c] = s

    def _del(self, c: int) -> None:
        s = self.where.pop(c)
        b = self.bucket[s]
        del b[c]
        if not b:
            del self.bucket[s]
            p, n = self.nb_prev.pop(s), self.nb_next.pop(s)
            if p is not None:
                self.nb_next[p] = n
            else:
                self.lo = n
            if n is not None:
                self.nb_prev[n] = p
            else:
                self.hi = p

    def _insert_scan(self, c: int, s: int) -> None:
        """Insert c at bucket s, scanning downward for the predecessor bucket."""
        p = s - 1
        while p > self.theta and p not in self.bucket:
            p -= 1
            self.core.stats.pq_scan += 1
        self._add(c, s, p if p > self.theta else None)

    # ---------------------------------------------------------- interface
    def adjust(self, c: int, old: int, new: int) -> None:
        """Size of quiet chunk c changed from old to new."""
        self.core.stats.steps += 1
        th = self.theta
        if old <= th < new:
            self._insert_scan(c, new)       # O(1) when new == th+1
        elif new <= th < old:
            self._del(c)
        elif old > th and new > th:
            if new == old + 1:
                b = self.bucket[old]
                p = old if len(b) > 1 else self.nb_prev[old]
                self._del(c)
                self._add(c, new, p)
            elif new == old - 1:
                p = self.nb_prev[old]
                self._del(c)
                self._add(c, new, p)
            else:
                self._del(c)
                self._insert_scan(c, new)

    def enter_if_above(self, c: int) -> None:
        s = self.core.C[c].size
        if s > self.theta:
            self._insert_scan(c, s)

    def pop_max(self) -> int:
        s = self.hi
        c = next(reversed(self.bucket[s]))
        self._del(c)
        return c

    def check(self, want: set[int]) -> None:
        assert set(self.where) == want, "PQ membership"
        for c, s in self.where.items():
            assert self.core.C[c].size == s, "PQ bucket != size"
        # linked list of non-empty buckets is sorted and complete
        seq = []
        s = self.lo
        prev = None
        while s is not None:
            assert self.nb_prev[s] == prev
            seq.append(s)
            prev, s = s, self.nb_next[s]
        assert prev == self.hi
        assert seq == sorted(self.bucket), "bucket list"
