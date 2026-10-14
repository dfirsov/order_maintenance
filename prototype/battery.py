"""Quick but broad pass/fail battery, used by mutate.py (exit 0 = all good).

Correctness: differential tests against the list model with invariant checks
(core INV-S and top W1-W4), both top structures, including tiny-label runs that
force fallbacks. Timing/cost: stress runs must have zero fallbacks, no slow PQ
scans, and stay within headroom bounds.
"""
from __future__ import annotations

import sys

import stress
import test_om
import top_stress
from core import Params


def main() -> int:
    # correctness, both tops
    for top in ("simple", "wbbt"):
        test_om.TOP = top
        for seed in range(6):
            test_om.run_diff(seed, 500, check_every=1)
        test_om.run_diff(50, 3000, p_ins=0.85, p_del=0.02, check_every=7)
        test_om.run_diff(51, 3000, p_ins=0.45, p_del=0.45, check_every=7)
        test_om.run_diff(52, 3000, p_ins=0.9, p_del=0.0, p_first=0.0, check_every=7,
                         pick=lambda rng, live: live[0])
        test_om.run_diff(53, 1500, p_ins=0.8, p_del=0.05, check_every=7,
                         params=test_om.tiny_labels)
    test_om.TOP = "simple"
    # random-parameter fuzzing (rare paths: cross-chunk moves, fallbacks, ...)
    import fuzz
    for seed in range(40):
        _, err, desc = fuzz.trial(10_000 + seed)
        if err:
            print(f"fuzz seed {10_000 + seed} {desc}: {err.strip().splitlines()[-1]}")
            return 1
    # timing and headroom, full system with the real top
    params = lambda N: Params.for_capacity(N, top="wbbt")
    for wl in ("hammer", "harmonic", "starve", "churn", "random"):
        r = stress.run(wl, 20000, params=params, check_every=2000)
        bad = []
        if r["fallbacks"]:
            bad.append(f"fallbacks={r['fallbacks']}")
        if r["pq_scan"]:
            bad.append(f"pq_scan={r['pq_scan']}")
        if r["max_chunk/T"] > 0.95:
            bad.append(f"max_chunk/T={r['max_chunk/T']:.2f}")
        if r["max_group/G"] > 1.5:
            bad.append(f"max_group/G={r['max_group/G']:.2f}")
        if r["max_fill"] > 0.75:
            bad.append(f"max_fill={r['max_fill']}")
        if bad:
            print(f"stress {wl}: " + ", ".join(bad))
            return 1
    # corner cases from the proof sketch (docs/PROOF.md), full invariant checks
    for wl in ("rebuild_cycle", "family_edge", "fifo", "yoyo", "cursor_chase", "flicker"):
        r = stress.run(wl, 20000, params=params, check_every=1000)
        if r["fallbacks"] or r["pq_scan"]:
            print(f"stress {wl}: fallbacks={r['fallbacks']} pq_scan={r['pq_scan']}")
            return 1
    # every quantitative lemma bound, proof preset (lemmas.py)
    import lemmas
    for wl in ("rebuild_cycle", "harmonic", "starve", "family_edge", "hammer"):
        r = lemmas.run((wl, 20000, "proof", 3))
        bad = [c for c, v in r["claims"].items() if v[0] > 1 and v[3]]
        if bad:
            print(f"lemmas {wl}: violated {bad}")
            return 1
    # top structure alone
    for wl in ("hotspots", "newest", "random"):
        r = top_stress.run(wl, 20000, check_every=2500)
        if r["fallbacks"]:
            print(f"top_stress {wl}: fallbacks={r['fallbacks']}")
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
