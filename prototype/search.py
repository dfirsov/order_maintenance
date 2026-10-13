"""Automated adversary search over the mixed-strategy family stress.make_mix.

    python3 search.py [trials] [-j jobs] [--n N] [--final N]

Score = the worst normalized headroom ratio (1.0 = a budget is exhausted);
any fallback scores 10. Random sampling, then hill climbing around the best
genomes; the best few are re-run at a larger n.
"""
from __future__ import annotations

import concurrent.futures as cf
import json
import random
import sys

import stress
from core import Params

PARAMS = lambda N: Params.for_capacity(N, top="wbbt")


def score(r: dict) -> float:
    if r["fallbacks"]:
        return 10.0 + r["fallbacks"]
    return max(
        r["max_chunk/T"],                       # chunk capacity
        r["max_group/G"] / 2,                   # groups (labels sized for ~2G)
        r["e_bits_used"] / r["B_e_last"],       # element label room
        r["g_bits_used"] / r["B_g_last"],       # group label room
        r["top_bits_used"] / 40,                # top label room (beta)
        r["max_fill"] / 1.0,                    # rebuild must finish before capacity
        r["max_steps/op"] / 200,                # per-op work vs a generous budget
        r["e_push_used"], r["g_push_used"],
    )


def random_genome(rng):
    w = {a: (rng.random() ** 2 if rng.random() < 0.6 else 0.0) for a in stress.MIX_ACTIONS}
    w["delete_run"] = w["delete_run"] * 0.01
    if sum(v for a, v in w.items() if a not in ("delete", "delete_run")) == 0:
        w["hotspot"] = 1.0
    return {"w": w, "k": rng.choice([1, 2, 3, 5, 8, 32, 256]),
            "period": rng.choice([100, 1000, 5000, 20000, 10**9]),
            "frac": rng.choice([0.1, 0.25, 0.5, 1.0])}


def mutate(g, rng):
    g = json.loads(json.dumps(g))
    for a in rng.sample(stress.MIX_ACTIONS, 3):
        g["w"][a] = max(0.0, g["w"][a] + rng.gauss(0, 0.3))
    if rng.random() < 0.3:
        g["k"] = max(1, int(g["k"] * rng.choice([0.5, 2])))
    if rng.random() < 0.3:
        g["period"] = rng.choice([100, 1000, 5000, 20000, 10**9])
    if rng.random() < 0.3:
        g["frac"] = rng.choice([0.1, 0.25, 0.5, 1.0])
    return g


def evaluate(args):
    g, n, seed = args
    r = stress.run("mix", n, seed=seed, params=PARAMS, wl=stress.make_mix(g))
    r.pop("reasons", None)
    return score(r), g, r


def main() -> None:
    args = sys.argv[1:]
    trials = int(args[0]) if args and args[0].isdigit() else 120
    jobs = int(args[args.index("-j") + 1]) if "-j" in args else 8
    n = int(args[args.index("--n") + 1]) if "--n" in args else 20000
    nfinal = int(args[args.index("--final") + 1]) if "--final" in args else 200000
    rng = random.Random(2026)
    pop = []
    with cf.ProcessPoolExecutor(jobs) as ex:
        first = [(random_genome(rng), n, i) for i in range(trials // 2)]
        pop += list(ex.map(evaluate, first))
        for rnd in range(4):
            pop.sort(key=lambda t: -t[0])
            parents = [g for _, g, _ in pop[:6]]
            kids = [(mutate(rng.choice(parents), rng), n, 1000 * (rnd + 1) + i)
                    for i in range(trials // 8)]
            pop += list(ex.map(evaluate, kids))
            print(f"round {rnd}: best score so far {max(p[0] for p in pop):.3f}", flush=True)
        pop.sort(key=lambda t: -t[0])
        print("top genomes at n =", n)
        for s_, g, r in pop[:5]:
            print(f"  score={s_:.3f}", {k: r[k] for k in ("fallbacks", "max_chunk/T", "max_group/G",
                  "e_bits_used", "g_bits_used", "top_bits_used", "max_fill", "max_steps/op")})
            print("    genome:", {a: round(v, 2) for a, v in g["w"].items() if v > 0}, "k", g["k"], "period", g["period"])
        final = list(ex.map(evaluate, [(g, nfinal, 7) for _, g, _ in pop[:3]]))
    print("best genomes re-run at n =", nfinal)
    for s_, g, r in final:
        print(f"  score={s_:.3f}", {k: r[k] for k in ("fallbacks", "max_chunk/T", "max_group/G",
              "e_bits_used", "g_bits_used", "top_bits_used", "max_fill", "max_steps/op")})
    with open("results/search.json", "w") as f:
        json.dump([{"score": s_, "genome": g, "result": r} for s_, g, r in pop[:20]], f, indent=1, default=str)


if __name__ == "__main__":
    main()
