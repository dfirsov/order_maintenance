"""Parameter sensitivity: vary one tuning constant at a time around the defaults.

    python3 sweep.py [n] [-j jobs]

For each setting and each tough workload reports fallbacks and the headroom
ratios. Shows which constants have slack and where the failure frontier is.
"""
from __future__ import annotations

import concurrent.futures as cf
import json
import sys

from core import Params

DEFAULT = dict(K_R=2, top_s=8, top_a=8, c_T=1, K_G=4, K_C=4, K_B=4, c_G=2)
GRID = {
    "K_R": [1, 2, 3, 4],
    "top_s": [3, 4, 5, 6, 8, 12],
    "top_a": [5, 6, 8, 12, 16],
    "c_T": [1, 2],
    "K_G": [1, 2, 3, 4],
    "K_C": [1, 2, 4],
    "K_B": [2, 3, 4, 8],
    "c_G": [1, 2, 3],
}
WORKLOADS = ["hammer", "harmonic", "starve", "random", "delete_burst", "zigzag"]
SHOW = ["fallbacks", "max_steps/op", "max_chunk/T", "max_group/G", "max_fill",
        "e_bits_used", "g_bits_used", "top_bits_used", "pq_scan", "max_table"]


def one(args):
    setting, wl, n = args
    import stress
    cfg = {**DEFAULT, **setting}

    def params(N):
        P = Params.for_capacity(N, top="wbbt", K_R=cfg["K_R"], K_G=cfg["K_G"],
                                K_C=cfg["K_C"], c_T=cfg["c_T"], c_G=cfg["c_G"])
        P.top_a, P.top_s = cfg["top_a"], cfg["top_s"]
        return P
    r = stress.run(wl, n, params=params, K_B=cfg["K_B"])
    return setting, wl, {k: r[k] for k in SHOW}


def main() -> None:
    n = int(sys.argv[1]) if len(sys.argv) > 1 and sys.argv[1].isdigit() else 100000
    jobs = int(sys.argv[sys.argv.index("-j") + 1]) if "-j" in sys.argv else 8
    only = sys.argv[sys.argv.index("--only") + 1].split(",") if "--only" in sys.argv else list(GRID)
    tasks = [({p: v}, wl, n) for p, vs in GRID.items() if p in only for v in vs for wl in WORKLOADS]
    rows = []
    with cf.ProcessPoolExecutor(jobs) as ex:
        for setting, wl, r in ex.map(one, tasks):
            rows.append({"setting": setting, "workload": wl, **r})
            (p, v), = setting.items()
            flag = "" if r["fallbacks"] == 0 and r["max_chunk/T"] < 1 and r["max_fill"] <= 0.75 else "  <-- margin exceeded"
            print(f"{p}={v:<3} {'(default)' if DEFAULT[p] == v else '         '} {wl:13s} " +
                  "  ".join(f"{k}={r[k]:.2f}" if isinstance(r[k], float) else f"{k}={r[k]}" for k in SHOW) + flag,
                  flush=True)
    with open(f"results/sweep_{'_'.join(only)}.json", "w") as f:
        json.dump(rows, f, indent=1)


if __name__ == "__main__":
    main()
