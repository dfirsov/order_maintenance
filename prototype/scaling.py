"""Scaling experiment: headroom metrics vs n for every workload (no tracing).

    python3 scaling.py [-j jobs] [--max N]

Writes results/scaling.json and prints one row per (workload, n). Everything
that bounds the O(1) claim should stay flat as n grows: max steps per op,
chunk and group fullness, PQ length, label bits consumed at every level,
top-level table sizes, rebuild fill.
"""
from __future__ import annotations

import concurrent.futures as cf
import json
import os
import sys

NS = [1_000, 10_000, 100_000, 1_000_000, 3_000_000]
TOP_MS = [10_000, 100_000, 1_000_000, 3_000_000]
KEYS = ["fallbacks", "max_steps/op", "max_chunk/T", "max_group/G", "max_pq", "pq_scan",
        "max_table", "e_bits_used", "B_e_last", "g_bits_used", "B_g_last", "top_bits_used",
        "e_push_used", "g_push_used", "max_fill", "rebuilds", "L", "secs"]


def one_full(args):
    name, n = args
    import stress
    from core import Params
    r = stress.run(name, n, params=lambda N: Params.for_capacity(N, top="wbbt"))
    r.pop("reasons", None)
    return {"kind": "full", **r}


def one_top(args):
    name, m = args
    import top_stress
    return {"kind": "top", **top_stress.run(name, m)}


def main() -> None:
    import stress
    import top_stress
    jobs = int(sys.argv[sys.argv.index("-j") + 1]) if "-j" in sys.argv else 8
    nmax = int(sys.argv[sys.argv.index("--max") + 1]) if "--max" in sys.argv else NS[-1]
    full = [(w, n) for n in NS if n <= nmax for w in stress.WORKLOADS]
    top = [(w, m) for m in TOP_MS if m <= nmax for w in top_stress.WORKLOADS]
    out = []
    with cf.ProcessPoolExecutor(jobs) as ex:
        futs = [ex.submit(one_full, a) for a in full] + [ex.submit(one_top, a) for a in top]
        for f in cf.as_completed(futs):
            r = f.result()
            out.append(r)
            if r["kind"] == "full":
                print(f"full {r['workload']:14s} n={r['n']:>8}  " +
                      "  ".join(f"{k}={r.get(k)}" for k in KEYS if k in r), flush=True)
            else:
                print(f"top  {r['workload']:14s} m={r['m']:>8}  " +
                      "  ".join(f"{k}={v}" for k, v in r.items() if k not in ("kind", "workload", "m")),
                      flush=True)
    os.makedirs("results", exist_ok=True)
    with open("results/scaling.json", "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
