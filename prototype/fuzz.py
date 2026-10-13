"""Correctness fuzzing with random, deliberately small and skewed parameters.

Each trial draws parameters near the feasible minimum (tiny groups, chunks and
label widths, slow or fast background work, small WBBT branching, little sweep
funding) and a random workload, then runs it against the list model with the
full invariant check (core INV-S, top W1-W4) after every operation.

Fallbacks are allowed here: safety must hold for *any* parameters. Timing and
headroom are measured elsewhere.

    python3 fuzz.py [trials] [-j jobs] [--start S]
"""
from __future__ import annotations

import concurrent.futures as cf
import math
import random
import sys
import traceback

from core import Params


def random_params(rng: random.Random, top: str):
    """A factory N -> Params with fuzzed fields (same fuzz for every epoch)."""
    G = rng.randint(2, 10)
    T = rng.randint(max(3, G), 8 * G)
    K_G, K_C, K_R = rng.randint(1, 5), rng.randint(1, 5), rng.randint(1, 4)
    J = rng.randint(1, 12)
    slack_e, slack_g = rng.randint(0, 6), rng.randint(0, 6)
    a = rng.randint(5, 10)
    s = rng.randint(1, 10)
    beta_slack = rng.randint(0, 12)

    def make(N: int) -> Params:
        P = Params.for_capacity(N, top=top)
        P.G, P.T = G, T
        P.theta = (2 * T) // 3
        P.K_G, P.K_C, P.K_R, P.J = K_G, K_C, K_R, J
        gpc = max(1, (3 * T) // G)
        P.B_e = math.ceil(math.log2(8 * G + 8)) + 2 + slack_e
        P.B_g = math.ceil(math.log2(8 * gpc + 8)) + 2 + slack_g
        P.D_e = (1 << (P.B_e - 1)) // (8 * G + 8)
        P.D_g = (1 << (P.B_g - 1)) // (8 * gpc + 8)
        P.top_a, P.top_s = a, s
        P.top_beta = math.ceil(math.log2(8 * a)) + 2 + beta_slack
        return P
    desc = dict(G=G, T=T, K_G=K_G, K_C=K_C, K_R=K_R, J=J, se=slack_e, sg=slack_g,
                a=a, s=s, bs=beta_slack)
    return make, desc


def trial(seed: int) -> tuple[int, str | None, dict]:
    import test_om
    rng = random.Random(seed)
    top = rng.choice(["simple", "wbbt", "wbbt"])
    make, desc = random_params(rng, top)
    desc["top"] = top
    ops = rng.randint(200, 1500)
    p_first = rng.choice([0.0, 0.02, 0.2])
    p_del = rng.choice([0.0, 0.05, 0.2, 0.45])
    p_ins = rng.uniform(0.3, 0.95 - p_del) if p_del < 0.6 else 0.3
    mode = rng.choice(["uniform", "hammer", "sequential", "mixed"])
    picks = {
        "uniform": None,
        "hammer": lambda r, live: live[0],
        "sequential": lambda r, live: live[-1],
        "mixed": lambda r, live: live[0] if r.random() < 0.3 else
                 (live[-1] if r.random() < 0.5 else r.choice(live)),
    }
    desc.update(ops=ops, p_first=p_first, p_del=p_del, p_ins=round(p_ins, 2), mode=mode)
    try:
        om = test_om.run_diff(seed, ops, p_ins=p_ins, p_first=p_first, p_del=p_del,
                              check_every=1, pick=picks[mode], params=make)
        desc["fallbacks"] = sum(c.stats.fallbacks for c in om.cores())
        return seed, None, desc
    except Exception:
        return seed, traceback.format_exc(limit=4), desc


def main() -> None:
    args = sys.argv[1:]
    trials = int(args[0]) if args and args[0].isdigit() else 500
    jobs = int(args[args.index("-j") + 1]) if "-j" in args else 8
    start = int(args[args.index("--start") + 1]) if "--start" in args else 0
    fails = 0
    fb_trials = 0
    with cf.ProcessPoolExecutor(jobs) as ex:
        for seed, err, desc in ex.map(trial, range(start, start + trials), chunksize=4):
            if err:
                fails += 1
                print(f"FAIL seed={seed} {desc}\n{err}", flush=True)
            elif desc.get("fallbacks"):
                fb_trials += 1
    print(f"{trials} trials, {fails} failures, {fb_trials} trials exercised fallbacks")


if __name__ == "__main__":
    main()
