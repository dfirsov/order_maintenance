"""Lemma checker: measure every quantitative claim of docs/PROOF.md §4.

    python3 lemmas.py [n] [-j jobs] [--preset default|proof|both] [workload ...]

Runs each workload (stress.WORKLOADS) under the chosen parameter presets and,
for every core that existed during the run, compares the instrumented maxima
with the bound the proof sketch claims for that core's parameters. A claim is
reported as a ratio measured / bound (<= 1 means the claim held) and as a
VIOLATION if it exceeds 1 *and* the lemma's hypotheses hold for the preset
(e.g. Lemma T3 assumes q = 1/2 + 2/a + 2/(s-2) < 1, which the default s = 8
does not satisfy; there the ratio is reported but not judged).

Correctness invariants (INV-S, W1-W4, invariant F) are checked along the way
by Core.check(), every n/20 operations and at the end.
"""
from __future__ import annotations

import concurrent.futures as cf
import math
import random
import sys
import time

HARMONIC = lambda k: sum(1.0 / i for i in range(1, k + 1))


def claims_for(core) -> list[tuple[str, float, float, bool]]:
    """[(claim, measured, bound, hypotheses_hold)] for one core."""
    P, st, top = core.P, core.stats, core.top
    G, T = P.G, P.T
    out = []
    k_G = -(-G // (P.K_G - 1)) + 1 if P.K_G >= 2 else None
    # Group level (Lemmas G1-G4); hypotheses: K_G >= 2
    if k_G is not None and st.g1_excess > -(1 << 29):
        out.append(("G1 family insertions - k_G(s0)", st.g1_excess, 0, True))
    out.append(("G1 sibling imbalance", st.g1_imbalance, 1.5, k_G is not None))
    out.append(("G2 freshly quiet group size < G", st.g1_fresh, G - 1, k_G is not None))
    out.append(("G2 max group size", st.max_group, G + 1, k_G is not None))
    if k_G is not None:
        U_G = max(2 * k_G + -(-(G + 3) // 2), G - 1 + k_G)
        A_G = max((G + k_G + 3) // 2 + -(-(G + 3) // 2) + k_G, G + k_G)
        out.append(("G3 lifetime insertions per group", st.g_ins, U_G, True))
        out.append(("G3 lifetime arrivals per group", st.g_arr, A_G, True))
        if st.min_gap_e < (1 << 4000):
            halvings = math.floor(math.log2(P.D_e)) - (st.min_gap_e.bit_length() - 1)
            out.append(("G4 nested halvings of an element gap", halvings, U_G, True))
            out.append(("G4 element label budget (halvings)", halvings,
                        math.floor(math.log2(P.D_e)) - 1, True))
    # Chunk level (C1-C3, F); hypotheses: K_C >= 2 (and G1's)
    hc = P.K_C >= 2 and k_G is not None and G >= 5
    if st.c1_excess > -(1 << 29):
        out.append(("C1 family insertions - k_C(s0)", st.c1_excess, 0, hc))
    if st.c1_size_excess > -1e8:
        out.append(("C1 fresh chunk size - bound", st.c1_size_excess, 0, hc))
    out.append(("C2 freshly quiet chunk size <= theta", st.c1_fresh, P.theta, hc))
    out.append(("C2 PQ slow-path scans", st.pq_scan, 0, True))
    out.append(("F element moves across chunks", st.cross_moves, 0, True))
    if st.min_gap_g < (1 << 4000):
        halvings = math.floor(math.log2(P.D_g)) - (st.min_gap_g.bit_length() - 1)
        # C3: 2 + (chunk lifetime insertions + k_G) / ceil((G-3)/2), lifetime = quiet max + 2 k_C
        if hc:
            units = max(T, st.max_quiet) // -(-(G - 3) // 2) + 1
            k_C = -(-units // (P.K_C - 1)) + 1
            I_C = max(T, st.max_quiet) + 2 * k_C
            out.append(("C3 nested halvings of a group gap", halvings,
                        2 + I_C // -(-(G - 3) // 2), hc))
    out.append(("no fallbacks", st.fallbacks, 0, True))
    # Reservation (Lemma R) and the top structure (T3-T5)
    if P.top == "wbbt":
        a, s, H, beta = top.a, top.s, top.H, top.beta
        m = sum(1 for C in core.C if C.alive)
        J = (s + 3) * H
        R = -(-J // P.K_R) + 1            # Lemma R: a job may start mid-insertion
        T_hard = P.theta + R * (HARMONIC(max(m - 1, 1)) + 1)
        over = max(0, st.max_quiet - P.theta)
        out.append(("R zeroing pops a largest quiet chunk (count of other pops)", st.pop_not_max, 0, True))
        out.append(("R overshoot above theta <= R(H_m+1) (provable J)", over, T_hard - P.theta, True))
        if st.max_job:
            R_meas = -(-st.max_job // P.K_R) + 1
            out.append(("R overshoot above theta <= R(H_m+1) (measured J)", over,
                        R_meas * (HARMONIC(max(m - 1, 1)) + 1), True))
            out.append(("R insertions per round <= ceil(J/K_R)+1", st.max_round, R_meas, True))
        out.append(("R quiet chunk size <= T (I5 target)", st.max_quiet, T, True))
        q = 0.5 + 2 / a + (2 / (s - 2) if s > 2 else 9)
        hyp3 = q < 1
        out.append(("T3 drain start weight / W_h", top.max_start_ratio, 1 + 2 / (2 * a), hyp3))
        out.append(("T3 blocked target weight / W_h (claim: q + O(1/W))", top.max_target_ratio,
                    1.0, hyp3))
        out.append(("T3 funding jobs / ((W_h+2)/(s-2)+1)", top.max_funded_ratio, 1.0, hyp3))
        out.append(("T4 live children <= 4a+1", top.max_children, 4 * a + 1, hyp3))
        out.append(("T4 table entries <= 6a+2", top.max_table, 6 * a + 2, hyp3))
        out.append(("T4 tables per entry <= 2", top.max_in_tables, 2, True))
        if st.max_job:
            out.append(("T4 job length <= (s+3)H", st.max_job, J, True))
        import top_bounds
        try:
            hyp_exact = top_bounds.summary(a, s, H)["ok"] if s >= 3 else False
        except (ValueError, AssertionError):
            hyp_exact = False
        for claim, h, meas, bound in top_bounds.check_top(top):
            if claim.startswith("T4.4"):
                continue           # cores step jobs themselves: st.max_job below
            if bound < 0:          # lower bounds are recorded negated
                out.append((f"{claim} [exact; lam/min]", -bound, -meas, hyp_exact))
            else:
                out.append((f"{claim} [exact]", meas, bound, hyp_exact))
        if top.min_gap < (1 << (beta + 1)):
            used = beta - (top.min_gap.bit_length() - 1)
            out.append(("T5 table label bits used <= 4qa+3+log2(6a+3)", used,
                        4 * q * a + 3 + math.log2(6 * a + 3), hyp3))
            out.append(("T5 table label bits used <= beta", used, beta, True))
    return out


def run(args):
    name, n, preset, seed = args
    import stress
    from core import Params
    from wrapper import OrderMaintenance
    params = Params.proof if preset == "proof" else (lambda N: Params.for_capacity(N, top="wbbt"))
    rng = random.Random(seed)
    om = OrderMaintenance(params=params)
    wl = stress.WORKLOADS[name]()
    live: list[int] = []
    check_every = max(1, n // 20)
    max_steps = 0
    t0 = time.time()
    for i in range(n):
        before = om.total_steps()
        wl(rng, om, live, i)
        max_steps = max(max_steps, om.total_steps() - before)
        if i % check_every == 0:
            om.check()
    om.check()
    worst: dict[str, tuple] = {}
    for core in om.cores():
        for claim, meas, bound, hyp in claims_for(core):
            ratio = (meas / bound) if bound > 0 else (0.0 if meas <= 0 else math.inf)
            if claim not in worst or ratio > worst[claim][0]:
                worst[claim] = (ratio, meas, bound, hyp, core.P.N)
    # wrapper (Lemma W)
    K_B = om.K_B
    ex = lambda v: 0.0 if v <= 0 else math.inf
    worst["W1 cur.count - (N/2 + floor((N/2+L+2)/(K_B-1)) + 1)"] = (
        ex(om.max_fill_excess), om.max_fill_excess, 0, K_B >= 4, None)
    worst["W2 nxt.count - (N'/4 + 1) at install"] = (
        ex(om.max_install_excess), om.max_install_excess, 0, K_B >= 4, None)
    worst["W max fill cur.count/N (info)"] = (om.max_fill, om.max_fill, None, False, None)
    return {"workload": name, "n": n, "preset": preset, "seed": seed, "max_steps/op": max_steps,
            "secs": round(time.time() - t0, 1), "claims": worst}


def main() -> None:
    import stress
    args = sys.argv[1:]
    jobs = int(args[args.index("-j") + 1]) if "-j" in args else 8
    preset = args[args.index("--preset") + 1] if "--preset" in args else "both"
    rest = [a for a in args if not a.startswith("-") and a not in (str(jobs), preset)]
    n = int(rest[0]) if rest and rest[0].isdigit() else 100000
    names = [a for a in rest if not a.isdigit()] or list(stress.WORKLOADS)
    presets = ["default", "proof"] if preset == "both" else [preset]
    seeds = int(args[args.index("--seeds") + 1]) if "--seeds" in args else 1
    rest = [a for a in rest if a != str(seeds)]
    names = [a for a in rest if not a.isdigit()] or list(stress.WORKLOADS)
    tasks = [(w, n, p, sd) for sd in range(1, seeds + 1) for p in presets for w in names]
    summary: dict[tuple, tuple] = {}
    violations = []
    with cf.ProcessPoolExecutor(jobs) as ex:
        for r in ex.map(run, tasks):
            bad = [c for c, v in r["claims"].items() if v[0] > 1 and v[3]]
            print(f"{r['preset']:8s} {r['workload']:14s} n={r['n']} seed={r['seed']} steps/op<={r['max_steps/op']} "
                  f"{r['secs']}s  " + ("OK" if not bad else "VIOLATED: " + "; ".join(bad)), flush=True)
            for c, v in r["claims"].items():
                key = (r["preset"], c)
                if key not in summary or v[0] > summary[key][0]:
                    summary[key] = v + (r["workload"],)
                if v[0] > 1 and v[3]:
                    violations.append((r["preset"], r["workload"], c, v))
    print("\nWorst ratio measured/bound per claim (<= 1: claim held; * = hypotheses not met, not judged)")
    for p in presets:
        print(f"\n  preset {p}")
        for (pp, c), v in sorted(summary.items()):
            if pp != p:
                continue
            ratio, meas, bound, hyp, N, wl = v
            r = "inf" if ratio == math.inf else f"{ratio:6.3f}"
            b = "" if bound is None else f" / {bound:.4g}"
            print(f"    {r}{'' if hyp else '*'}  {c:52s} {meas:.4g}{b}   ({wl}, N={N})")
    print(f"\n{len(violations)} violations")
    for v in violations:
        print("  ", v)


if __name__ == "__main__":
    main()
