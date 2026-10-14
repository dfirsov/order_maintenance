"""Line coverage of the algorithm files under the test suites (sys.monitoring).

    python3 linecov.py [fuzz_trials]

Runs the differential tests, a sample of fuzz trials, the stress workloads
(both presets, small n) and the lemma checker's workloads, then lists every
line of the algorithm files that never executed. An unexecuted line is either
a path the proof sketch claims unreachable (expected) or an untested corner
case (to be covered). Instrumentation-only and checker code is ignored.
"""
from __future__ import annotations

import dis
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ALGO = ["core.py", "pq.py", "top_wbbt.py", "wrapper.py", "top_simple.py"]
PATHS = {os.path.join(HERE, f): f for f in ALGO}
mon = sys.monitoring
TOOL = mon.COVERAGE_ID
hit: dict[str, set[int]] = {f: set() for f in ALGO}


def _line(code, line):
    f = PATHS.get(code.co_filename)
    if f is None:
        return mon.DISABLE
    hit[f].add(line)
    return mon.DISABLE              # each (code, line) only needs to be seen once


def executable_lines(path: str) -> set[int]:
    src = open(path).read()
    code = compile(src, path, "exec")
    lines: set[int] = set()

    def walk(co):
        for _, _, ln in co.co_lines():
            if ln is not None:
                lines.add(ln)
        for c in co.co_consts:
            if hasattr(c, "co_lines"):
                walk(c)
    walk(code)
    return lines


def main() -> None:
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    mon.use_tool_id(TOOL, "linecov")
    mon.register_callback(TOOL, mon.events.LINE, _line)
    mon.set_events(TOOL, mon.events.LINE)
    try:
        import unittest
        import test_om
        unittest.main(module=test_om, argv=["x"], exit=False, verbosity=0)
        import fuzz
        for seed in range(trials):
            fuzz.trial(500_000 + seed)
        fuzz.LONG = True
        for seed in range(trials // 30):
            fuzz.trial(600_000 + seed)
        fuzz.LONG = False
        import stress
        from core import Params
        for P in (lambda N: Params.for_capacity(N, top="wbbt"), Params.proof,
                  lambda N: Params.for_capacity(N, top="simple")):
            for w in stress.WORKLOADS:
                stress.run(w, 6000, params=P, check_every=1500)
        import top_stress
        for w in top_stress.WORKLOADS:
            top_stress.run(w, 5000, check_every=1000)
    finally:
        mon.set_events(TOOL, 0)
        mon.free_tool_id(TOOL)
    total_miss = 0
    for f in ALGO:
        path = os.path.join(HERE, f)
        src = open(path).read().splitlines()
        exe = executable_lines(path)
        miss = sorted(exe - hit[f])
        # ignore checker code and lines that are pure declarations
        miss = [ln for ln in miss if not src[ln - 1].strip().startswith(("assert", "def ", "class ", "@", "\"\"\"", "#"))]
        total_miss += len(miss)
        print(f"\n{f}: {len(exe) - len(miss)}/{len(exe)} executable lines covered")
        for ln in miss:
            print(f"  {ln:4d}  {src[ln - 1].rstrip()}")
    print(f"\n{total_miss} uncovered lines")


if __name__ == "__main__":
    main()
