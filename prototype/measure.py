"""Per-operation cost measured as executed Python lines (sys.monitoring, Python 3.12+).

Every LINE event in the algorithm's own files counts as one unit; workload and
adversary code is excluded. Unlike the hand-placed step counters, this catches
any loop the counters miss. It does not see work hidden inside C calls; those
are bounded separately:
  * list.index / insert on top-level tables: length ≤ max_table (reported);
  * big-int tag arithmetic: tag width in bits (reported) vs. word size log2 N;
  * list.append: amortized O(1) (an allocation-model assumption, see report).

    python3 measure.py [n] [workload ...]          (TOP defaults to wbbt)

For each workload prints: max lines per op overall and per decade window of n
(flat = O(1) evidence), percentiles, and the functions that make up the worst op.
"""
from __future__ import annotations

import os
import random
import sys
import time
from array import array

ALGO_FILES = {"core.py", "pq.py", "top_wbbt.py", "top_simple.py", "wrapper.py", "guards.py"}
HERE = os.path.dirname(os.path.abspath(__file__))
ALGO_PATHS = {os.path.join(HERE, f) for f in ALGO_FILES}

mon = sys.monitoring
TOOL = mon.PROFILER_ID


class LineCounter:
    def __init__(self) -> None:
        self.count = 0
        self.by_fn: dict = {}
        self.breakdown = False

    def _cb(self, code, line):
        if code.co_filename not in ALGO_PATHS:
            return mon.DISABLE
        self.count += 1
        if self.breakdown:
            k = code.co_qualname
            self.by_fn[k] = self.by_fn.get(k, 0) + 1

    def __enter__(self):
        mon.use_tool_id(TOOL, "om-lines")
        mon.register_callback(TOOL, mon.events.LINE, self._cb)
        mon.set_events(TOOL, mon.events.LINE)
        return self

    def __exit__(self, *exc):
        mon.set_events(TOOL, 0)
        mon.register_callback(TOOL, mon.events.LINE, None)
        mon.free_tool_id(TOOL)


def percentile(sorted_vals, q):
    if not sorted_vals:
        return 0
    return sorted_vals[min(len(sorted_vals) - 1, int(q * len(sorted_vals)))]


def measure(name: str, n: int, *, top: str = "wbbt", seed: int = 1, params=None) -> dict:
    from core import Params
    from stress import WORKLOADS
    from wrapper import OrderMaintenance
    params = params or (lambda N: Params.for_capacity(N, top=top))
    rng = random.Random(seed)
    om = OrderMaintenance(params=params)
    wl = WORKLOADS[name]()
    live: list[int] = []
    costs = array("I")
    windows: dict[int, int] = {}          # decade -> max cost in [10^d, 10^(d+1))
    worst, worst_i, worst_fns = -1, -1, {}
    fn_max: dict[int, dict[str, int]] = {}  # decade -> function -> max lines in one op
    t0 = time.time()
    with LineCounter() as lc:
        for i in range(n):
            lc.count = 0
            lc.by_fn = {}
            lc.breakdown = True
            wl(rng, om, live, i)
            c = lc.count
            costs.append(c)
            d = len(str(i + 1)) - 1
            windows[d] = max(windows.get(d, 0), c)
            if c > worst:
                worst, worst_i, worst_fns = c, i, dict(lc.by_fn)
            fm = fn_max.setdefault(d, {})
            for k, v in lc.by_fn.items():
                if v > fm.get(k, 0):
                    fm[k] = v
    s = sorted(costs)
    cores = om.cores()
    return {
        "workload": name, "n": n, "top": top,
        "max": worst, "at_op": worst_i,
        "p50": percentile(s, 0.5), "p99": percentile(s, 0.99),
        "p99.9": percentile(s, 0.999), "p99.99": percentile(s, 0.9999),
        "mean": round(sum(costs) / max(1, len(costs)), 1),
        "max_by_decade": {f"1e{d}": windows[d] for d in sorted(windows)},
        "fallbacks": sum(c.stats.fallbacks for c in cores),
        "max_table": max(getattr(c.top, "max_table", 0) for c in cores),
        "max_children": max(getattr(c.top, "max_children", 0) for c in cores),
        "max_in_tables": max(getattr(c.top, "max_in_tables", 0) for c in cores),
        "max_tag_bits": max(max((x.tag for x in c.C), default=0).bit_length() for c in cores),
        "log2N": max(c.P.L for c in cores),
        "worst_op_top_fns": sorted(worst_fns.items(), key=lambda kv: -kv[1])[:8],
        "fn_max_by_decade": fn_max,
        "secs": round(time.time() - t0, 1),
    }


def _one(args):
    name, n, top = args
    return measure(name, n, top=top)


def main() -> None:
    import concurrent.futures as cf
    from stress import WORKLOADS
    top = os.environ.get("TOP", "wbbt")
    args = [a for a in sys.argv[1:] if not a.startswith("-")]
    jobs = int(sys.argv[sys.argv.index("-j") + 1]) if "-j" in sys.argv else 1
    if "-j" in sys.argv:
        args = [a for a in args if a != str(jobs)]
    n = int(args[0]) if args else 100000
    names = args[1:] or list(WORKLOADS)
    with cf.ProcessPoolExecutor(jobs) as ex:
        results = list(ex.map(_one, [(w, n, top) for w in names]))
    for r in results:
        fns = r.pop("worst_op_top_fns")
        fmd = r.pop("fn_max_by_decade")
        print(r, flush=True)
        print("    worst op:", fns, flush=True)
        # per-function max lines in a single op, by decade (each should plateau)
        names = sorted({k for d in fmd.values() for k in d},
                       key=lambda k: -max(d.get(k, 0) for d in fmd.values()))[:10]
        for k in names:
            print(f"    {k:45s}", " ".join(f"{fmd[d].get(k, 0):5d}" for d in sorted(fmd)), flush=True)


if __name__ == "__main__":
    main()
