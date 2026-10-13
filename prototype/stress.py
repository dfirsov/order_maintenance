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
        if (state["core"] is not core or not state["anchors"]
                or state.get("fb") != core.stats.fallbacks):   # a fallback renumbers chunks
            pick(om, live)
            state["fb"] = core.stats.fallbacks
        anchors = state["anchors"]
        # drop anchors whose chunk is no longer quiet (served) or moved
        while anchors:
            j = i % len(anchors)
            c, h = anchors[j]
            e = om.cur_idx.get(h)           # anchors may have been deleted
            if (e is not None and core.C[c].alive and core.C[c].st == QUIET
                    and core.Gs[core.E[e].grp].chk == c):
                live.append(om.insert_after(h))
                return
            anchors[j] = anchors[-1]
            anchors.pop()
        live.append(om.insert_after(rng.choice(live)))
    return wl


def make_starve(k: int = 20):
    """Priority-policy adversary; peeks into the structure.

    Round-robin over one anchor per chunk until at least k chunks wait in the
    PQ, then hammer the *smallest* waiting chunk until it is served, and repeat.
    Serving the fullest chunk first (the correct policy) makes the victim the
    maximum quickly; a wrong policy lets it wait behind the others and grow.
    """
    from core import QUIET
    st = {"core": None, "anchors": [], "victim": None}

    def pick(om, live):
        core = om.cur
        chunk_of = {}
        for h in live:
            c = core.Gs[core.E[om.cur_idx[h]].grp].chk
            if core.C[c].st == QUIET and c not in chunk_of:
                chunk_of[c] = h
        st["core"], st["anchors"], st["victim"] = core, list(chunk_of.items()), None

    def ok(core, om, c, h):
        e = om.cur_idx.get(h)
        return e is not None and core.C[c].st == QUIET and core.Gs[core.E[e].grp].chk == c

    def wl(rng, om, live, i):
        if len(live) < 2000:
            live.append(om.insert_after(rng.choice(live)) if live else om.insert_first())
            return
        core = om.cur
        if st["core"] is not core or not st["anchors"] or st.get("fb") != core.stats.fallbacks:
            pick(om, live)
            st["fb"] = core.stats.fallbacks
        v = st["victim"]
        if v is not None and ok(core, om, *v):
            live.append(om.insert_after(v[1]))
            return
        st["victim"] = None
        waiting = core.pq.where
        if len(waiting) >= k:
            cand = [(core.C[c].size, c, h) for c, h in st["anchors"]
                    if c in waiting and ok(core, om, c, h)]
            if cand:
                _, c, h = min(cand)
                st["victim"] = (c, h)
                live.append(om.insert_after(h))
                return
        anchors = st["anchors"]
        while anchors:
            j = i % len(anchors)
            c, h = anchors[j]
            if ok(core, om, c, h):
                live.append(om.insert_after(h))
                return
            anchors[j] = anchors[-1]
            anchors.pop()
        live.append(om.insert_after(rng.choice(live)))
    return wl


def make_boundary(level: str):
    """Insert right after the last element of a random group or chunk: always
    the push-back label path (labAfter) instead of averaging."""
    def wl(rng, om, live, i):
        if len(live) < 50:
            live.append(om.insert_after(rng.choice(live)) if live else om.insert_first())
            return
        core = om.cur
        e = om.cur_idx[rng.choice(live)]
        g = core.E[e].grp
        if level == "chunk":
            c = core.Gs[g].chk
            g = core.C[c].last
            while g != -1 and core.Gs[g].last == -1:      # skip empty trailing groups
                g = core.Gs[g].prev
            if g == -1:
                g = core.E[e].grp
        x = core.Gs[g].last
        h = core.E[x].h
        if h < 0 or not core.E[x].live:
            h = rng.choice(live)
        live.append(om.insert_after(h))
    return wl


def make_narrow_gap(samples: int = 16):
    """Sample elements, insert after the one with the narrowest label gap to its
    group successor: pushes label consumption at the element level."""
    def wl(rng, om, live, i):
        if len(live) < 50:
            live.append(om.insert_after(rng.choice(live)) if live else om.insert_first())
            return
        core = om.cur
        best, bh = None, None
        for _ in range(samples):
            h = rng.choice(live)
            e = om.cur_idx[h]
            g = core.Gs[core.E[e].grp]
            if g.last == e:
                continue
            gap = core.E[core.E[e].next].lab - core.E[e].lab
            if best is None or gap < best:
                best, bh = gap, h
        live.append(om.insert_after(bh if bh is not None else rng.choice(live)))
    return wl


def make_zigzag():
    """Alternate between the front and the back of the list."""
    def wl(rng, om, live, i):
        if not live or i % 2 == 0:
            live.append(om.insert_first())
        else:
            live.append(om.insert_after(st["last"]))
        st["last"] = live[-1] if i % 2 else st.get("last", live[-1])
    st: dict = {}
    def wl2(rng, om, live, i):
        if not live:
            h = om.insert_first()
            live.append(h)
            st["tail"] = h
        elif i % 2 == 0:
            live.append(om.insert_first())
        else:
            h = om.insert_after(st["tail"])
            st["tail"] = h
            live.append(h)
    return wl2


def make_delete_burst(grow: int = 4000):
    """Grow, delete 90% to force a shrinking rebuild, and while the copy runs
    hammer both the copied prefix and the uncopied suffix; repeat."""
    st = {"phase": "grow"}

    def wl(rng, om, live, i):
        if st["phase"] == "grow":
            live.append(om.insert_after(rng.choice(live)) if live else om.insert_first())
            if len(live) >= grow:
                st["phase"] = "delete"
            return
        if st["phase"] == "delete":
            if len(live) > grow // 10:
                j = rng.randrange(len(live))
                live[j], live[-1] = live[-1], live[j]
                om.delete(live.pop())
                return
            st["phase"] = "attack"
            st["t"] = 0
        st["t"] += 1
        # front of the list is copied first, the back last
        if st["t"] % 2:
            live.append(om.insert_first())
        else:
            live.append(om.insert_after(live[-1]))
        if st["t"] > 2 * grow:
            st["phase"] = "grow"
    return wl


MIX_ACTIONS = ["uniform", "hotspot", "sequential", "front", "group_end", "chunk_end",
               "narrow_gap", "starve", "delete", "delete_run", "rr_chunks"]


def make_mix(genome: dict):
    """Parameterized adversary for automated search.

    genome = {"w": {action: weight}, "k": #hot spots, "period": ops between
    hot-spot reshuffles}. Each operation draws an action by weight.
    """
    from core import QUIET
    acts = [a for a in MIX_ACTIONS if genome["w"].get(a, 0) > 0]
    weights = [genome["w"][a] for a in acts]
    st: dict = {"spots": [], "tail": None, "run": 0}
    boundary_g, boundary_c = make_boundary("group"), make_boundary("chunk")
    narrow = make_narrow_gap(8)
    harm = make_harmonic(genome.get("frac", 1.0))    # round-robin over one anchor per chunk

    def ins(om, live, h):
        y = om.insert_after(h)
        live.append(y)
        st["tail"] = y

    def wl(rng, om, live, i):
        if len(live) < 200:
            live.append(om.insert_after(rng.choice(live)) if live else om.insert_first())
            st["tail"] = live[-1]
            return
        if i % genome["period"] == 0 or not st["spots"]:
            st["spots"] = [rng.choice(live) for _ in range(genome["k"])]
        if st["run"] > 0:                      # in the middle of a deletion run
            st["run"] -= 1
            j = rng.randrange(len(live))
            live[j], live[-1] = live[-1], live[j]
            h = live.pop()
            om.delete(h)
            if h in st["spots"]:
                st["spots"] = []
            if h == st["tail"]:
                st["tail"] = None
            return
        a = rng.choices(acts, weights)[0]
        if a == "uniform":
            ins(om, live, rng.choice(live))
        elif a == "hotspot":
            h = rng.choice(st["spots"]) if st["spots"] else rng.choice(live)
            ins(om, live, h if h in om.cur_idx else rng.choice(live))
        elif a == "sequential":
            h = st["tail"]
            ins(om, live, h if h is not None and h in om.cur_idx else rng.choice(live))
        elif a == "front":
            y = om.insert_first()
            live.append(y)
        elif a == "group_end":
            boundary_g(rng, om, live, i)
        elif a == "chunk_end":
            boundary_c(rng, om, live, i)
        elif a == "narrow_gap":
            narrow(rng, om, live, i)
        elif a == "starve":
            core = om.cur
            waiting = core.pq.where
            target = None
            if waiting:
                c = min(waiting, key=lambda c: core.C[c].size)
                g = core.C[c].first
                while g != -1 and core.Gs[g].first == -1 and g != core.C[c].last:
                    g = core.Gs[g].next
                if g != -1 and core.Gs[g].first != -1:
                    e = core.Gs[g].first
                    if core.E[e].live and core.E[e].h >= 0:
                        target = core.E[e].h
            ins(om, live, target if target is not None else rng.choice(live))
        elif a == "delete":
            j = rng.randrange(len(live))
            live[j], live[-1] = live[-1], live[j]
            h = live.pop()
            om.delete(h)
            if h in st["spots"]:
                st["spots"] = []
            if h == st["tail"]:
                st["tail"] = None
        elif a == "delete_run":
            st["run"] = len(live) // 2
        elif a == "rr_chunks":
            harm(rng, om, live, i)
    return wl


WORKLOADS = {
    "starve": make_starve,
    "group_end": lambda: make_boundary("group"),
    "chunk_end": lambda: make_boundary("chunk"),
    "narrow_gap": make_narrow_gap,
    "zigzag": make_zigzag,
    "delete_burst": make_delete_burst,
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


def run(name: str, n: int, seed: int = 1, check_every: int = 0, params=None,
        K_B: int = 4, wl=None) -> dict:
    """Run workload `name` (or the workload function `wl`) for n operations."""
    rng = random.Random(seed)
    om = OrderMaintenance(params=params, K_B=K_B) if params else OrderMaintenance(K_B=K_B)
    wl = wl or WORKLOADS[name]()
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
        # label bits consumed by averaging, relative to each core's own width
        "e_bits_used": max(c.P.B_e - min(c.stats.min_gap_e.bit_length() - 1, c.P.B_e) for c in cores),
        "B_e_last": om.cur.P.B_e,
        "g_bits_used": max(c.P.B_g - min(c.stats.min_gap_g.bit_length() - 1, c.P.B_g) for c in cores),
        "B_g_last": om.cur.P.B_g,
        "e_push_used": round(max(max(c.stats.max_lab_e - (1 << (c.P.B_e - 1)),
                                     (1 << (c.P.B_e - 1)) - min(c.stats.min_lab_e, 1 << (c.P.B_e - 1)))
                                 / (1 << (c.P.B_e - 1)) for c in cores), 4),
        "g_push_used": round(max(max(c.stats.max_lab_g - (1 << (c.P.B_g - 1)),
                                     (1 << (c.P.B_g - 1)) - min(c.stats.min_lab_g, 1 << (c.P.B_g - 1)))
                                 / (1 << (c.P.B_g - 1)) for c in cores), 4),
        "top_bits_used": max((c.top.beta - min(c.top.min_gap.bit_length() - 1, c.top.beta)
                              for c in cores if hasattr(c.top, "min_gap")), default=-1),
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
