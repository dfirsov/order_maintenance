"""Adversary for the wrapper's rebuild sizing rule (docs/PROOF.md §6.1).

    python3 rebuild_attack.py [log2_n ...]        (default: 14 16 18 20)

1. Grow to a large core, fill it to count N/2 - 1 with live just above N/8.
2. One more insert triggers a rebuild (count >= N/2).
3. Delete every live element while the copy runs; the installed copy is empty.
4. The next rebuild sizes its core for live = 0 (capacity 64), and its copy has to
   crawl over the tombstones while every insertFirst is mirrored into it.

With the sizing rule N' = 4*max(live, 16) the small core is overloaded by orders of
magnitude, its top tree's root table grows without bound, and at n = 2^20 it runs
out of labels ("top: table full"): fallbacks and ~4000 steps per op.
"""
from __future__ import annotations

import sys
import time

from core import Params
from wrapper import OrderMaintenance


def run(n0: int, ops_after: int) -> dict:
    om = OrderMaintenance(params=lambda N: Params.for_capacity(N, top="wbbt"))
    live: list[int] = []
    while not (om.nxt is None and om.cur.P.N >= n0):
        live.append(om.insert_first())
    N = om.cur.P.N
    while om.cur.count < N // 2 - 1:
        live.append(om.insert_first())
    while om.live > N // 8 + 2:
        om.delete(live.pop(0))
    assert om.nxt is None
    live.append(om.insert_first())              # count reaches N/2: rebuild starts
    assert om.nxt is not None
    while om.nxt is not None and live:
        om.delete(live.pop())
    while om.nxt is not None:
        h = om.insert_first()
        om.delete(h)
    worst, t0 = 0, time.time()
    fb0 = sum(c.stats.fallbacks for c in om.cores())
    for _ in range(ops_after):
        s0 = om.total_steps()
        om.insert_first()
        worst = max(worst, om.total_steps() - s0)
    cores = om.cores()
    over = max(cores, key=lambda c: c.count / c.P.N)
    return {"N": N, "fallbacks": sum(c.stats.fallbacks for c in cores) - fb0,
            "max_steps/op": worst, "worst_core_N": over.P.N, "worst_core_count": over.count,
            "worst_core_max_table": over.top.max_table,
            "reasons": over.stats.fallback_reasons, "secs": round(time.time() - t0, 1)}


def main() -> None:
    logs = [int(a) for a in sys.argv[1:]] or [14, 16, 18, 20]
    for k in logs:
        print(run(2 ** k, 2 ** k // 4), flush=True)


if __name__ == "__main__":
    main()
