"""Traces of the prototype core for the differential test of viz/om.js (check.js).

    python3 gen_traces.py OUT_DIR

Each trace runs one insert-only Core (no wrapper, no rebuild) on a workload and
records, after every operation: the new element's key, the number of fallbacks,
the total step count (core steps plus top-structure steps), the number of
reservations and drains, and (often enough) a digest of all keys in list order.
"""
from __future__ import annotations

import json
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "prototype"))

from core import Params, Core  # noqa: E402

MOD = (1 << 61) - 1


def digest(core) -> int:
    h = 0
    for e in core.elements():
        for v in core.key(e):
            h = (h * 1000003 + v) % MOD
    return h


def params(N, o):
    P = Params.for_capacity(N, c_G=o.get("c_G", 2), c_T=o.get("c_T", 1),
                            K_G=o.get("K_G", 4), K_C=o.get("K_C", 4), K_R=o.get("K_R", 2),
                            top="wbbt", L_min=o.get("L_min", 4))
    P.top_a = o.get("a", 8)
    P.top_s = o.get("s", 8)
    P.top_beta = o.get("beta")
    return P


def ops_for(workload, n_ops, seed):
    """Operations as ["i", x] (insert after element x; 0 is the head) or ["d", x].
    Element indices are assigned in insertion order, 1, 2, 3, ..."""
    rnd = random.Random(seed)
    live, tail, ops, nxt = [], 0, [], 1
    spot = None
    for _ in range(n_ops):
        if workload == "churn" and live and rnd.random() < 0.3:
            x = live.pop(rnd.randrange(len(live)))
            ops.append(["d", x])
            continue
        if workload in ("random", "churn"):
            x = rnd.choice([0] + live)
        elif workload == "front":
            x = 0
        elif workload == "append":
            x = tail
        elif workload == "spot":       # always after the same element
            spot = spot or (live[0] if live else 0)
            x = spot
        elif workload == "newest":     # after the element inserted last
            x = nxt - 1
        else:
            raise ValueError(workload)
        ops.append(["i", x])
        if x == tail:
            tail = nxt
        live.append(nxt)
        nxt += 1
    return ops


CONFIGS = [
    # name, N, overrides, workloads, ops (as a multiple of N)
    ("default-64", 64, {}, ["random", "front", "append", "spot", "newest", "churn"], 1.0),
    ("default-256", 256, {}, ["random", "front", "spot", "newest", "churn"], 1.0),
    ("default-1024", 1024, {}, ["random", "front", "spot", "newest"], 0.6),
    ("default-4096", 4096, {}, ["random", "front"], 0.5),
    ("over-capacity", 64, {}, ["random", "front", "spot"], 3.0),
    ("K_G=1", 128, {"K_G": 1}, ["random", "front", "spot"], 1.0),
    ("K_C=1", 128, {"K_C": 1}, ["random", "front", "spot"], 1.0),
    ("K_R=1", 512, {"K_R": 1}, ["random", "front", "newest"], 1.0),
    ("beta=6", 256, {"beta": 6}, ["random", "front", "newest"], 1.0),
    ("s=2", 1024, {"s": 2}, ["random", "front", "newest"], 0.6),
    ("a=2", 256, {"a": 2}, ["random", "front", "newest"], 1.0),
    ("a=3", 256, {"a": 3}, ["random", "newest"], 1.0),
    ("deep", 8192, {}, ["front", "newest"], 1.0),
    ("over-capacity-10x", 32, {}, ["random", "front", "spot"], 10.0),
    ("beta=8", 1024, {"beta": 8}, ["random", "front", "newest"], 1.0),
    ("a=2,s=1", 512, {"a": 2, "s": 1}, ["random", "front", "newest"], 1.0),
    ("c_T=3", 256, {"c_T": 3, "K_R": 4, "L_min": 8, "s": 11, "beta": 48}, ["random", "front"], 1.0),
]


def run(N, o, ops):
    core = Core(params(N, o))
    recs = []
    for i, op in enumerate(ops):
        y = None
        if op[0] == "i":
            y = core.insert_after(op[1], len(core.E))
        else:
            core.mark_dead(op[1])
        n = len(core.E)
        take = n <= 1500 or i % 25 == 0 or i == len(ops) - 1
        recs.append([
            [str(v) for v in core.key(y)] if y is not None else None,
            core.stats.fallbacks,
            core.stats.steps + core.top.top_steps,
            core.stats.reservations,
            core.top.drains,
            str(digest(core)) if take else None,
        ])
    return recs


def main() -> None:
    out = sys.argv[1]
    os.makedirs(out, exist_ok=True)
    for name, N, o, workloads, mult in CONFIGS:
        for w in workloads:
            for seed in (1, 2):
                if w in ("front", "append", "newest") and seed == 2:
                    continue        # deterministic workloads: one seed is enough
                ops = ops_for(w, int(N * mult), seed)
                recs = run(N, o, ops)
                fn = os.path.join(out, f"{name}.{w}.{seed}.json")
                with open(fn, "w") as f:
                    json.dump({"N": N, "params": o, "ops": ops, "recs": recs}, f)
                fb = recs[-1][1]
                print(f"{fn}: {len(ops)} ops, {fb} fallbacks, {recs[-1][3]} reservations, "
                      f"{recs[-1][4]} drains")


if __name__ == "__main__":
    main()
