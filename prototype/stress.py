"""Adversarial stress runs with instrumentation (no reference model).

    python3 stress.py [n] [workload ...]

For each workload reports: fallbacks (target 0), max core steps in a single
operation (target: flat in n), max group / chunk size relative to G / T,
slow PQ scans (target 0), top-structure work, rebuilds.
"""
from __future__ import annotations

import random
import sys
import time

from wrapper import OrderMaintenance


def wl_random(rng, om, live, i):
    if live and rng.random() < 0.1:
        j = rng.randrange(len(live))
        live[j], live[-1] = live[-1], live[j]
        om.delete(live.pop())
        return
    live.append(om.insert_after(rng.choice(live)) if live else om.insert_first())


def wl_insert_random(rng, om, live, i):
    live.append(om.insert_after(rng.choice(live)) if live else om.insert_first())


def wl_front(rng, om, live, i):
    live.append(om.insert_first())


def wl_append(rng, om, live, i):
    live.append(om.insert_after(live[-1]) if live else om.insert_first())


def wl_hammer(rng, om, live, i):
    # new element always right after the first one: one gap absorbs everything
    live.append(om.insert_after(live[0]) if live else om.insert_first())


def make_spread(k):
    """Round-robin over k anchors spread through the list.

    Grows all chunks at the same rate, so many reach the PQ threshold together:
    the scenario the zeroing game is about.
    """
    anchors: list[int] = []

    def wl(rng, om, live, i):
        if len(live) < 4 * k:
            live.append(om.insert_after(rng.choice(live)) if live else om.insert_first())
            if len(live) == 4 * k:
                anchors.extend(live[j] for j in range(0, len(live), 4))
            return
        live.append(om.insert_after(anchors[i % k]))
    return wl


def make_churn():
    """Insert/delete in one region: exercises rebuilds driven by deletions."""
    def wl(rng, om, live, i):
        if len(live) > 200 and rng.random() < 0.5:
            om.delete(live.pop())
        else:
            live.append(om.insert_after(live[-1]) if live else om.insert_first())
    return wl


def make_harmonic(frac: float = 1.0):
    """Zeroing-game adversary (Dietz–Sleator Thm 5); peeks into the structure.

    Picks one anchor element in each of a fraction `frac` of the current chunks,
    then inserts round-robin after the anchors whose chunk is still quiet. All
    picked chunks reach the PQ threshold together; the reservation process
    serves one per J/K_R operations; inserts concentrate on the survivors, so
    the last one served gains ~ (J/K_R) * H_s elements above theta.
    """
    from core import QUIET
    state = {"core": None, "anchors": []}

    def pick(om, live):
        core = om.cur
        chunk_of = {}
        for h in live:
            e = om.cur_idx[h]
            c = core.Gs[core.E[e].grp].chk
            if core.C[c].st == QUIET and c not in chunk_of:
                chunk_of[c] = h
        items = list(chunk_of.items())
        items = items[: max(1, int(len(items) * frac))]
        state["core"] = core
        state["anchors"] = [(c, h) for c, h in items]

    def wl(rng, om, live, i):
        if len(live) < 2000:
            live.append(om.insert_after(rng.choice(live)) if live else om.insert_first())
            return
        core = om.cur
        if state["core"] is not core or not state["anchors"]:
            pick(om, live)
        anchors = state["anchors"]
        # drop anchors whose chunk is no longer quiet (served) or moved
        while anchors:
            j = i % len(anchors)
            c, h = anchors[j]
            e = om.cur_idx[h]
            if core.C[c].alive and core.C[c].st == QUIET and core.Gs[core.E[e].grp].chk == c:
                live.append(om.insert_after(h))
                return
            anchors[j] = anchors[-1]
            anchors.pop()
        live.append(om.insert_after(rng.choice(live)))
    return wl


WORKLOADS = {
    "harmonic": make_harmonic,
    "harmonic_half": lambda: make_harmonic(0.5),
    "random": lambda: wl_random,
    "insert_random": lambda: wl_insert_random,
    "front": lambda: wl_front,
    "append": lambda: wl_append,
    "hammer": lambda: wl_hammer,
    "spread64": lambda: make_spread(64),
    "spread1k": lambda: make_spread(1024),
    "churn": make_churn,
}


def run(name: str, n: int, seed: int = 1, check_every: int = 0, params=None) -> dict:
    rng = random.Random(seed)
    om = OrderMaintenance(params=params) if params else OrderMaintenance()
    wl = WORKLOADS[name]()
    live: list[int] = []
    max_steps = 0
    t0 = time.time()
    for i in range(n):
        before = om.total_steps()
        wl(rng, om, live, i)
        max_steps = max(max_steps, om.total_steps() - before)
        if check_every and i % check_every == 0:
            om.check()
    om.check()
    cores = om.cores()
    st = [c.stats for c in cores]
    P = om.cur.P
    return {
        "workload": name,
        "n": n,
        "live": om.live,
        "fallbacks": sum(s.fallbacks for s in st),
        "max_steps/op": max_steps,
        "max_group/G": max(s.max_group / c.P.G for s, c in zip(st, cores)),
        "max_chunk/T": max(s.max_chunk / c.P.T for s, c in zip(st, cores)),
        "pq_scan": sum(s.pq_scan for s in st),
        "big_core_chunk/T": round(max((s.max_chunk / c.P.T for s, c in zip(st, cores) if c.P.N >= n), default=0), 3),
        "max_pq": max(s.max_pq for s in st),
        "reservations": sum(s.reservations for s in st),
        "top_relabels": sum(c.top.relabels for c in cores),
        "drains": sum(getattr(c.top, "drains", 0) for c in cores),
        "max_table": max(getattr(c.top, "max_table", 0) for c in cores),
        "lab_bits": max(getattr(c.top, "max_lab", 0) for c in cores).bit_length(),
        "rebuilds": om.rebuilds,
        "max_fill": round(om.max_fill, 3),
        "L": P.L,
        "secs": round(time.time() - t0, 1),
        "reasons": {k: v for s in st for k, v in s.fallback_reasons.items()},
    }


def main() -> None:
    import os
    from core import Params
    top = os.environ.get("TOP", "simple")
    params = lambda N: Params.for_capacity(N, top=top)
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    names = sys.argv[2:] or list(WORKLOADS)
    for name in names:
        r = run(name, n, params=params)
        reasons = r.pop("reasons")
        print("  ".join(f"{k}={v:.2f}" if isinstance(v, float) else f"{k}={v}"
                        for k, v in r.items()))
        if reasons:
            print("    fallback reasons:", reasons)


if __name__ == "__main__":
    main()
