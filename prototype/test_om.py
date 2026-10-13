"""Differential tests: OrderMaintenance vs the list model (python3 -m unittest)."""
from __future__ import annotations

import random
import unittest

from spec import SpecOM
from core import Params
from wrapper import OrderMaintenance


TOP = "simple"     # overridden by the WBBT subclass below


def tiny_labels(N: int) -> Params:
    """Label widths far too small: guards fail constantly, forcing fallbacks."""
    P = Params.for_capacity(N, top=TOP)
    P.B_e, P.B_g = 7, 6
    P.D_e, P.D_g = 4, 4
    return P


def run_diff(seed: int, ops: int, *, p_ins=0.6, p_first=0.05, p_del=0.15,
             check_every=1, pick=None, params=None) -> OrderMaintenance:
    """Random operations on both structures; compare every answer.

    `pick(rng, live)` chooses the anchor for insert_after (default: uniform).
    Handles coincide because both structures allocate them sequentially.
    """
    rng = random.Random(seed)
    if params is None:
        params = lambda N: Params.for_capacity(N, top=TOP)
    om, sp = OrderMaintenance(params=params), SpecOM()
    live: list[int] = []
    for i in range(ops):
        r = rng.random()
        if not live or r < p_first:
            a, b = om.insert_first(), sp.insert_first()
            assert a == b
            live.append(a)
        elif r < p_first + p_ins:
            x = pick(rng, live) if pick else rng.choice(live)
            a, b = om.insert_after(x), sp.insert_after(x)
            assert a == b
            live.append(a)
        elif r < p_first + p_ins + p_del:
            j = rng.randrange(len(live))
            live[j], live[-1] = live[-1], live[j]
            x = live.pop()
            om.delete(x)
            sp.delete(x)
        else:
            x, y = rng.choice(live), rng.choice(live)
            assert om.order(x, y) == sp.order(x, y), f"order mismatch at op {i}"
        if check_every and i % check_every == 0:
            assert om.check() == sp.items, f"lists differ at op {i}"
    assert om.check() == sp.items
    return om


class DiffTests(unittest.TestCase):
    def test_small_random_every_op(self):
        for seed in range(20):
            run_diff(seed, 600, check_every=1)

    def test_insert_heavy(self):
        for seed in range(5):
            run_diff(100 + seed, 4000, p_ins=0.85, p_del=0.02, check_every=97)

    def test_delete_heavy(self):
        for seed in range(5):
            run_diff(200 + seed, 4000, p_ins=0.45, p_del=0.45, check_every=97)

    def test_hammer_one_gap(self):
        # always insert right after the oldest live element
        run_diff(7, 4000, p_ins=0.9, p_del=0.0, p_first=0.0, check_every=53,
                 pick=lambda rng, live: live[0])

    def test_sequential(self):
        # always insert after the most recent element (append-like in the middle)
        run_diff(8, 4000, p_ins=0.9, p_del=0.0, p_first=0.0, check_every=53,
                 pick=lambda rng, live: live[-1])

    def test_fallback_path(self):
        # tiny labels: guards fail all the time, the fallback rebuild must keep
        # the structure correct
        for seed in range(5):
            om = run_diff(300 + seed, 2000, p_ins=0.8, p_del=0.05, check_every=7,
                          params=tiny_labels)
            self.assertGreater(sum(c.stats.fallbacks for c in om.cores()), 0)
        run_diff(310, 2000, p_ins=0.9, p_del=0.0, p_first=0.0, check_every=7,
                 pick=lambda rng, live: live[0], params=tiny_labels)

    def test_slow_reservation(self):
        # long top jobs: chunks overfill; still correct
        slow = lambda N: Params.for_capacity(N, K_R=1, c_J=4, top=TOP)
        for seed in range(3):
            run_diff(400 + seed, 4000, p_ins=0.85, p_del=0.05, check_every=31, params=slow)

    def test_front(self):
        run_diff(9, 3000, p_ins=0.0, p_first=0.9, p_del=0.0, check_every=53)


class DiffTestsWBBT(DiffTests):
    """Same tests with the weight-balanced B-tree top structure."""

    def setUp(self):
        global TOP
        TOP = "wbbt"

    def tearDown(self):
        global TOP
        TOP = "simple"


if __name__ == "__main__":
    unittest.main()
