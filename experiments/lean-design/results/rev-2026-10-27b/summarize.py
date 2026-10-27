"""Tables of the revision runs 2026-10-27b (python3 results/rev-2026-10-27b/summarize.py).

compare.rs no longer times the choice of the insertion argument. This prints, against replicate 2
of results/rev-2026-10-27 (rep2/):
  1. the work check: every main CSV here has the same work columns (mean_work, max_work) as its
     rep2 counterpart, row by row (work_of_slowest depends on which operation was slowest, so it
     is not compared);
  2. the cells of the paper's Table 2 (tab:eval-summary) and tab:native, in its format: mean /
     run p99.99 (median of the 3 runs) / slowest repeatable time (largest per-operation minimum),
     in µs, rep2 -> new;
  3. the native/AVL ratios of mean, run p99.99 and slowest for random and clustered insertion at
     both sizes;
  4. the seed spread of random insertion at 10^7 (decade 10^6-10^7): default seed, SEED=1, SEED=2;
  5. the cost of the old in-interval work alone (selcost_*.csv).
The full tables (all columns, slow-operation counts) come from the old script:
  python3 results/rev-2026-10-27/summarize.py results/rev-2026-10-27b
"""
import csv
import importlib.util
import os
import statistics

HERE = os.path.dirname(os.path.abspath(__file__))
REP2 = os.path.join(HERE, "..", "rev-2026-10-27", "rep2")
REP1 = os.path.join(HERE, "..", "rev-2026-10-27")
_spec = importlib.util.spec_from_file_location("s27", os.path.join(REP1, "summarize.py"))
s27 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(s27)
load, pick, cell_runs = s27.load, s27.pick, s27.cell_runs
IMPLS = s27.IMPLS


def work_check():
    """Main CSVs: impl,workload,from|phase,to|n,ops,...,mean_work (9),max_work (10)."""
    bad, n = [], 0
    for name in sorted(os.listdir(HERE)):
        if not name.endswith(".csv") or name.startswith(("tails_", "selcost")):
            continue
        old = os.path.join(REP2, name)
        if not os.path.exists(old):
            bad.append(f"{name}: no rep2 file")
            continue
        key = lambda p: [tuple(r[:5] + r[9:11]) for r in csv.reader(open(p))]
        a, b = key(os.path.join(HERE, name)), key(old)
        n += 1
        if a != b:
            bad.append(f"{name}: work columns differ")
    print(f"Work check: {n} main CSVs compared with rep2 (ops, mean_work, max_work of every row): "
          + ("all identical." if not bad else "DIFFERENCES: " + "; ".join(bad)) + "\n")


def f_mean(us):
    return f"{us:.3f}" if us < 0.1 else f"{us:.2f}"


def f_tail(us):
    return f"{us:.2f}" if us < 1 else f"{us:.1f}" if us < 100 else f"{us:,.0f}"


def paper_cell(c):
    return f"{f_mean(c['mean'] / 1000)} / {f_tail(c['p9999_ns'][0] / 1000)} / {f_tail(c['min_max'] / 1000)}"


SPECS = [
    ("random insertion", "tails_{i}_random_1e8.csv", dict(workload="random", **{"from": 10000000})),
    ("clustered insertion", "tails_{i}_hammer_1e8.csv", dict(workload="hammer", **{"from": 10000000})),
    ("random churn: deletion", "tails_del_{i}_random_10000000.csv", dict(phase="churn-delete")),
    ("random churn: insertion", "tails_del_{i}_random_10000000.csv", dict(phase="churn-insert")),
    ("queue churn: deletion", "tails_del_{i}_fifo_10000000.csv", dict(phase="churn-delete")),
    ("queue churn: insertion", "tails_del_{i}_fifo_10000000.csv", dict(phase="churn-insert")),
    ("teardown: deletion", "tails_del_{i}_random_10000000.csv", dict(phase="drain-delete")),
    ("order query, warm", "tails_q_{i}_random.csv", dict(workload="query-random", **{"from": 1000000})),
]


def cell(d, path, kw):
    return cell_runs(pick(load(os.path.join(d, path)), **kw))


def paper_tables():
    print("Paper cells, µs: mean / run p99.99 (median of 3 runs) / slowest (largest per-op minimum); "
          "rep2 → new. Table 2 uses the rows random insertion, clustered insertion and cold query.\n")
    print("| row | native | AVL | amortized |")
    print("|---|---|---|---|")
    for name, path, kw in SPECS:
        cells = []
        for imp, _ in IMPLS:
            p = path.format(i=imp)
            o, n = cell(REP2, p, kw), cell(HERE, p, kw)
            cells.append(f"{paper_cell(o)} → **{paper_cell(n)}**" if o and n else "–")
        print(f"| {name} | " + " | ".join(cells) + " |")
    cells = []
    for imp, _ in IMPLS:
        rs = pick(load(os.path.join(REP1, f"tails_cold_{imp}_random.csv")), kind="query-cold", **{"from": 10000000})
        d = {r["run"]: r for r in rs}
        cells.append(f"{f_mean(float(d['min']['mean_ns']) / 1000)} / – / {f_tail(float(d['min']['max_ns_all']) / 1000)} (unchanged)")
    print("| order query, cold (rep 1, cold.rs unchanged) | " + " | ".join(cells) + " |")
    print()


def ratios():
    print("Native / AVL ratios (rep2 → new):\n")
    print("| workload | mean | run p99.99 | slowest |")
    print("|---|---|---|---|")
    lo_hi = {k: [] for k in ("old", "new")}
    for suffix, frm, label in (("_1e8", 10000000, "10^7–10^8"), ("", 1000000, "10^6–10^7")):
        for w, wname in (("random", "random"), ("hammer", "clustered")):
            out = []
            for which, d in (("old", REP2), ("new", HERE)):
                c = {imp: cell(d, f"tails_{imp}_{w}{suffix}.csv", dict(workload=w, **{"from": frm})) for imp in ("native", "avl")}
                r = (c["native"]["mean"] / c["avl"]["mean"], c["native"]["p9999_ns"][0] / c["avl"]["p9999_ns"][0],
                     c["native"]["min_max"] / c["avl"]["min_max"])
                lo_hi[which].append(r)
                out.append(r)
            print(f"| {wname} insertion, {label} | " + " | ".join(f"{out[0][i]:.2f} → **{out[1][i]:.2f}**" for i in range(3)) + " |")
    for which in ("old", "new"):
        rs = lo_hi[which]
        print(f"\n{which}: mean {min(r[0] for r in rs):.2f}–{max(r[0] for r in rs):.2f}, "
              f"p99.99 {min(r[1] for r in rs):.2f}–{max(r[1] for r in rs):.2f}, "
              f"slowest {min(r[2] for r in rs):.2f}–{max(r[2] for r in rs):.2f}", end="")
    print("\n")


def seeds():
    print("Seed spread, random insertion, 10^7 elements, decade 10^6–10^7, µs: mean / run p99.99 / slowest\n")
    print("| impl | default seed | SEED=1 | SEED=2 | spread (max/min − 1): mean, p99.99, slowest |")
    print("|---|---|---|---|---|")
    kw = dict(workload="random", **{"from": 1000000})
    allc = {}
    for imp, iname in IMPLS:
        cs = [cell(HERE, f"tails_{imp}_random.csv", kw)] + [cell(os.path.join(HERE, "seeds"), f"tails_{imp}_random_seed{k}.csv", kw) for k in (1, 2)]
        if any(c is None for c in cs):
            print(f"| {iname} | – | – | – | – |")
            continue
        sp = lambda f: max(f(c) for c in cs) / min(f(c) for c in cs) - 1
        spread = f"{100 * sp(lambda c: c['mean']):.1f}%, {100 * sp(lambda c: c['p9999_ns'][0]):.1f}%, {100 * sp(lambda c: c['min_max']):.1f}%"
        print(f"| {iname} | " + " | ".join(paper_cell(c) for c in cs) + f" | {spread} |")
        allc[imp] = cs
    print("\nNative / AVL per seed (mean, run p99.99, slowest): " + "; ".join(
        f"{lab} {n['mean'] / a['mean']:.2f}, {n['p9999_ns'][0] / a['p9999_ns'][0]:.2f}, {n['min_max'] / a['min_max']:.2f}"
        for lab, n, a in zip(("default", "SEED=1", "SEED=2"), allc["native"], allc["avl"])))
    print()


def selcost():
    print("Cost of the old in-interval work alone (selcost.rs, no structure), ns per step; "
          "mean (median of 3 runs) / run p99.99 (median) / slowest per-step minimum\n")
    print("| decade | empty interval | rng | rng + read live[i] | old body (string match + read) | old − empty, mean |")
    print("|---|---|---|---|---|---|")
    for sfx, label in (("1e7", "10^6–10^7"), ("1e8", "10^7–10^8")):
        rows = load(os.path.join(HERE, f"selcost_{sfx}.csv"))
        if not rows:
            continue
        def st(body):
            rs = [r for r in rows if r["body"] == body]
            runs = [r for r in rs if r["run"] != "min"]
            mn = [r for r in rs if r["run"] == "min"][0]
            return (statistics.median(float(r["mean_ns"]) for r in runs),
                    statistics.median(float(r["p9999_ns"]) for r in runs), float(mn["max_ns"]))
        s = {b: st(b) for b in ("empty", "rng", "select", "old")}
        f = lambda t: f"{t[0]:.1f} / {t[1]:.0f} / {t[2]:.0f}"
        print(f"| {label} | {f(s['empty'])} | {f(s['rng'])} | {f(s['select'])} | {f(s['old'])} | {s['old'][0] - s['empty'][0]:.1f} |")
    print()


if __name__ == "__main__":
    work_check()
    selcost()
    paper_tables()
    ratios()
    seeds()
