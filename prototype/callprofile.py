"""Per-invocation cost profile: turns "max lines per op" into an explicit bound.

For every function of the algorithm records
  * the maximum *exclusive* executed lines in one invocation (a generator's
    resume..yield segment counts as one invocation), and
  * the maximum number of invocations within one operation.
Then  bound = Σ_f  max_calls_per_op(f) × max_lines_per_call(f)  is an upper
bound on the cost of any single operation that does not depend on how rarely
the worst cases coincide. Both columns should be flat in n (the first bounded
by table sizes, the second by the code's fixed loop counts K_*, s, ...).

    python3 callprofile.py [n] [workload ...]
"""
from __future__ import annotations

import random
import sys
import time

from measure import ALGO_PATHS

mon = sys.monitoring
TOOL = mon.PROFILER_ID
E = mon.events


class CallProfiler:
    def __init__(self) -> None:
        self.stack: list[list] = []          # [code, lines]
        self.max_lines: dict = {}
        self.calls_op: dict = {}
        self.max_calls: dict = {}
        self.op_lines = 0

    def _push(self, code, offset):
        if code.co_filename not in ALGO_PATHS:
            return mon.DISABLE
        self.stack.append([code, 0])

    def _pop(self, code, offset, retval=None):
        if code.co_filename not in ALGO_PATHS:
            return mon.DISABLE
        if not self.stack or self.stack[-1][0] is not code:
            return                           # frames entered before profiling began
        c, n = self.stack.pop()
        k = c.co_qualname
        if n > self.max_lines.get(k, 0):
            self.max_lines[k] = n
        self.calls_op[k] = self.calls_op.get(k, 0) + 1

    def _unwind(self, code, offset, exc):
        return self._pop(code, offset)

    def _line(self, code, line):
        if code.co_filename not in ALGO_PATHS:
            return mon.DISABLE
        self.op_lines += 1
        if self.stack and self.stack[-1][0] is code:
            self.stack[-1][1] += 1

    def end_op(self):
        for k, v in self.calls_op.items():
            if v > self.max_calls.get(k, 0):
                self.max_calls[k] = v
        self.calls_op = {}
        n, self.op_lines = self.op_lines, 0
        return n

    def __enter__(self):
        mon.use_tool_id(TOOL, "om-calls")
        mon.register_callback(TOOL, E.PY_START, self._push)
        mon.register_callback(TOOL, E.PY_RESUME, self._push)
        mon.register_callback(TOOL, E.PY_RETURN, self._pop)
        mon.register_callback(TOOL, E.PY_YIELD, self._pop)
        mon.register_callback(TOOL, E.PY_UNWIND, self._unwind)
        mon.register_callback(TOOL, E.LINE, self._line)
        mon.set_events(TOOL, E.PY_START | E.PY_RESUME | E.PY_RETURN | E.PY_YIELD | E.LINE)
        return self

    def __exit__(self, *exc):
        mon.set_events(TOOL, 0)
        for ev in (E.PY_START, E.PY_RESUME, E.PY_RETURN, E.PY_YIELD, E.PY_UNWIND, E.LINE):
            mon.register_callback(TOOL, ev, None)
        mon.free_tool_id(TOOL)


def profile(name: str, n: int, seed: int = 1) -> dict:
    from core import Params
    from stress import WORKLOADS
    from wrapper import OrderMaintenance
    rng = random.Random(seed)
    om = OrderMaintenance(params=lambda N: Params.for_capacity(N, top="wbbt"))
    wl = WORKLOADS[name]()
    live: list[int] = []
    max_op = 0
    t0 = time.time()
    with CallProfiler() as cp:
        for i in range(n):
            wl(rng, om, live, i)
            max_op = max(max_op, cp.end_op())
    rows = sorted(cp.max_lines, key=lambda k: -cp.max_lines[k] * cp.max_calls.get(k, 0))
    bound = sum(cp.max_lines[k] * cp.max_calls.get(k, 0) for k in rows)
    return {"workload": name, "n": n, "max_op": max_op, "bound": bound,
            "rows": [(k, cp.max_lines[k], cp.max_calls.get(k, 0)) for k in rows],
            "secs": round(time.time() - t0, 1)}


def main() -> None:
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
    for name in sys.argv[2:] or ["hammer", "chunk_end", "harmonic"]:
        r = profile(name, n)
        print(f"{name}: n={n} observed max lines/op={r['max_op']}  structural bound={r['bound']}  ({r['secs']}s)")
        for k, l, c in r["rows"][:14]:
            print(f"    {k:45s} max lines/call {l:4d}  x  max calls/op {c:3d}  = {l * c}")


if __name__ == "__main__":
    main()
