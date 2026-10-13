"""Milestone-1 top structure (docs/SPEC.md §5.6): correct but not O(1).

Chunk tags are chosen by averaging neighbour tags in [0, 2^B_t). When there is
no room, every chunk is relabelled evenly; that O(m) work is counted in
`top_steps`, separately from the core's O(1) steps.

`job_length` simulates the duration of a real top insertion (Θ(log m) steps),
so the reservation process and the zeroing-game dynamics behave as they would
with the target structure.
"""
from __future__ import annotations

NIL = -1


class SimpleTop:
    def __init__(self, core) -> None:
        self.core = core
        self.top_steps = 0
        self.relabels = 0

    def init_first(self, c: int) -> None:
        self.core.C[c].tag = 1 << (self.core.P.B_t - 1)

    def _room(self, c: int) -> tuple[int, int]:
        C = self.core.C
        lo = C[C[c].prev].tag if C[c].prev != NIL else -1
        hi = C[C[c].next].tag if C[c].next != NIL else 1 << self.core.P.B_t
        return lo, hi

    def insert_around(self, x: int, y: int, z: int) -> list[int]:
        """y and z are already linked before and after x in the chunk list.

        Returns the job: a countdown of simulated top-structure steps."""
        C = self.core.C
        self.top_steps += 1
        lo, _ = self._room(y)
        _, hi = self._room(z)
        tx = C[x].tag
        if lo + 1 < tx and tx + 1 < hi:
            C[y].tag = (lo + tx) // 2
            C[z].tag = (tx + hi) // 2
        else:
            self.relabel_all()
        return [self.core.P.J]

    def step(self, job: list[int]) -> bool:
        """One unit of background work; False when the job is finished."""
        self.top_steps += 1
        job[0] -= 1
        return job[0] > 0

    def relabel_all(self) -> None:
        core = self.core
        chunks = []
        c = core.first_chunk
        while c != NIL:
            chunks.append(c)
            c = core.C[c].next
        gap = (1 << core.P.B_t) // (len(chunks) + 1)
        assert gap >= 2, "top tag space exhausted"
        for i, c in enumerate(chunks):
            core.C[c].tag = (i + 1) * gap
        self.top_steps += len(chunks)
        self.relabels += 1
