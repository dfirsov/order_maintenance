"""Stress the WBBT top structure in isolation, with up to millions of chunks.

    python3 top_stress.py [m] [workload ...]

A fake core supplies only the chunk list. Each insertion places two chunks
around an adversarially chosen x (as the reservation process does) and runs
its job to completion before the next one (reservations are serialized).
Reports: fallbacks (target 0), max job length vs log m (target O(log m)),
smallest label gap in bits (headroom before tables run out), max table size,
max simultaneous ghosts.
"""
from __future__ import annotations

import math
import random
import sys
import time
from dataclasses import dataclass

from guards import GuardFailure
from top_wbbt import WBBTTop

NIL = -1


@dataclass(slots=True)
class FakeChunk:
    prev: int = NIL
    next: int = NIL
    tag: int = 0


@dataclass
class FakeP:
    N: int
    theta: int = 1          # makes m_max = 6N + 16: N counts chunks here


class FakeCore:
    def __init__(self, m_max: int, **kw) -> None:
        self.P = FakeP(N=m_max)
        self.C: list[FakeChunk] = [FakeChunk()]
        self.first_chunk = 0
        self.top = WBBTTop(self, **kw)
        self.top.init_first(0)
        self.fallbacks = 0

    def insert_around(self, x: int) -> tuple[int, int]:
        C = self.C
        y, z = len(C), len(C) + 1
        C.append(FakeChunk())
        C.append(FakeChunk())
        X = C[x]
        C[y].prev, C[y].next = X.prev, x
        if X.prev != NIL:
            C[X.prev].next = y
        else:
            self.first_chunk = y
        X.prev = y
        C[z].prev, C[z].next = x, X.next
        if X.next != NIL:
            C[X.next].prev = z
        X.next = z
        try:
            self.top.run_job(self.top.insert_around(x, y, z))
        except GuardFailure:
            self.fallbacks += 1
            self.top.relabel_all()
        return y, z

    def check(self) -> None:
        c = self.first_chunk
        prev_tag = -1
        n = 0
        while c != NIL:
            assert self.C[c].tag > prev_tag, "tags unsorted"
            prev_tag = self.C[c].tag
            c = self.C[c].next
            n += 1
        assert n == len(self.C)
        self.top.check(quiescent=True)


def pick_random(rng, core, i, st):
    return rng.randrange(len(core.C))


def pick_hammer(rng, core, i, st):
    return 0                      # always around the very first chunk


def pick_newest(rng, core, i, st):
    return len(core.C) - 1        # around the chunk created last (moves right)


def pick_oldest_left(rng, core, i, st):
    return max(0, len(core.C) - 2)  # the y of the previous insertion (moves left)


def pick_hotspots(rng, core, i, st):
    # a few hot spots, switching periodically: forces drains at many levels
    if i % 5000 == 0:
        st["spots"] = [rng.randrange(len(core.C)) for _ in range(4)]
    return st["spots"][i % 4]


WORKLOADS = {"random": pick_random, "hammer": pick_hammer, "newest": pick_newest,
             "leftward": pick_oldest_left, "hotspots": pick_hotspots}


def run(name: str, m: int, check_every: int = 0, seed: int = 1, **kw) -> dict:
    rng = random.Random(seed)
    core = FakeCore(m_max=m, **kw)
    pick = WORKLOADS[name]
    st: dict = {}
    t0 = time.time()
    for i in range((m - 1) // 2):
        core.insert_around(pick(rng, core, i, st))
        if check_every and i % check_every == 0:
            core.check()
    core.check()
    top = core.top
    return {
        "workload": name, "m": len(core.C), "H": top.H,
        "fallbacks": core.fallbacks,
        "max_job": top.max_job,
        "job/log2m": round(top.max_job / math.log2(len(core.C)), 1),
        "drains": top.drains,
        "max_ghosts": top.max_ghosts,
        "max_table": top.max_table,
        "min_gap_bits": top.min_gap.bit_length(),
        "beta": top.beta,
        "secs": round(time.time() - t0, 1),
    }


def main() -> None:
    m = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
    for name in sys.argv[2:] or list(WORKLOADS):
        r = run(name, m)
        print("  ".join(f"{k}={v}" for k, v in r.items()))


if __name__ == "__main__":
    main()
