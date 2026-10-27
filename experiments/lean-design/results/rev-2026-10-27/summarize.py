"""Tables of the revision runs of 2026-10-27 (python3 results/rev-2026-10-27/summarize.py).

For each implementation and workload of Table 2 / tab:native of the paper:
  mean            median over the 3 runs of each run's mean (the old `mean_ns`)
  slowest (min)   maximum of the per-operation minima over the runs (the old `max_ns`)
  run max         each run's own maximum: median over the runs [largest run]
  run p99.9       each run's own p99.9: median [largest]
  run p99.99      each run's own p99.99: median [largest]
from tails_*.csv (src/tails.rs). Cold queries: 2 cold runs of 500 sampled queries per decade
(cold.rs); per run the mean and the maximum (percentiles of 500 samples are not meaningful).
Also the long-history runs (longrun_*.csv)."""
import csv
import os
import statistics
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
OLD = os.path.join(HERE, "..")
# optional argument: the directory of a replicate (e.g. rep2), with the long-history files read
# from HERE in any case
DIR = os.path.abspath(sys.argv[1]) if len(sys.argv) > 1 else HERE
IMPLS = [("native", "native"), ("avl", "AVL"), ("bender", "amortized")]


def us(ns):
    v = float(ns)
    if v >= 1e6:
        return f"{v / 1e6:.2f} ms"
    return f"{v:.0f} ns" if v < 1000 else f"{v / 1000:.1f} µs"


def load(path):
    if not os.path.exists(path):
        return []
    with open(path) as f:
        return list(csv.DictReader(f))


def pick(rows, **kw):
    return [r for r in rows if all(r[k] == str(v) for k, v in kw.items())]


def med_max(vals):
    return statistics.median(vals), max(vals)


def cell_runs(rows):
    """rows: the per-run rows (run 0..2) and the `min` row of one configuration and decade."""
    runs = [r for r in rows if r["run"] != "min"]
    mn = [r for r in rows if r["run"] == "min"]
    if not runs or not mn:
        return None
    mn = mn[0]
    out = {
        "mean": statistics.median(float(r["mean_ns"]) for r in runs),
        "min_max": float(mn["max_ns"]),
        "min_p9999": float(mn["p9999_ns"]),
        "min_p999": float(mn["p999_ns"]),
        "runs": len(runs),
    }
    for k in ("max_ns", "p999_ns", "p9999_ns"):
        out[k] = med_max([float(r[k]) for r in runs])
    if "n_over_100us" in runs[0]:
        out["over"] = (statistics.median(int(r["n_over_10us"]) for r in runs),
                       statistics.median(int(r["n_over_100us"]) for r in runs))
    return out


def fmt_line(name, impl, c, old=None):
    if c is None:
        return f"| {name} | {impl} | – | – | – | – | – |"
    m = lambda t: f"{us(t[0])} [{us(t[1])}]"
    o = "" if old is None else f" ({us(old)})"
    ov = f" {c['over'][0]:.0f} / {c['over'][1]:.0f} |" if "over" in c else ""
    return (f"| {name} | {impl} | {us(c['mean'])} | {us(c['min_max'])}{o} | {m(c['max_ns'])} | "
            f"{m(c['p999_ns'])} | {m(c['p9999_ns'])} |" + ov)


def old_max(path, key_col, key, from_col=None):
    """The old `max_ns` (column 9) of the published CSV, for the reproduction check."""
    if not os.path.exists(path):
        return None
    with open(path) as f:
        for r in csv.reader(f):
            if r[key_col] == key:
                return float(r[8])
    return None


def main():
    hdr = ("| workload | impl | mean | slowest, per-op min (old method; published) | run max: median [largest] "
           "| run p99.9: median [largest] | run p99.99: median [largest] |"
           + (" ops > 10 µs / > 100 µs per run (median) |" if os.path.exists(os.path.join(DIR, "times.log")) and DIR != HERE else "")
           + "\n|---|---|---|---|---|---|---|" + ("---|" if DIR != HERE else ""))
    print("## Insertions\n")
    print(hdr)
    for suffix, frm, label in (("_1e8", 10000000, "10^7–10^8"), ("", 1000000, "10^6–10^7")):
        for w, wname in (("random", "random insertion"), ("hammer", "clustered insertion")):
            for imp, iname in IMPLS:
                rows = pick(load(os.path.join(DIR, f"tails_{imp}_{w}{suffix}.csv")), workload=w, **{"from": frm})
                old = None
                p = os.path.join(OLD, f"{imp}_{w}{suffix}.csv")
                if os.path.exists(p):
                    with open(p) as f:
                        for r in csv.reader(f):
                            if r[1] == w and int(r[2]) == frm:
                                old = float(r[8])
                print(fmt_line(f"{wname}, {label}", iname, cell_runs(rows), old))
    print("\n## Deletions (10^7)\n")
    print(hdr)
    for w in ("random", "fifo"):
        for ph in ("churn-delete", "churn-insert", "drain-delete"):
            for imp, iname in IMPLS:
                rows = pick(load(os.path.join(DIR, f"tails_del_{imp}_{w}_10000000.csv")), workload=w, phase=ph)
                old = None
                p = os.path.join(OLD, "deletes", f"{imp}_{w}_10000000.csv")
                if os.path.exists(p):
                    with open(p) as f:
                        for r in csv.reader(f):
                            if r[2] == ph:
                                old = float(r[8])
                print(fmt_line(f"{w} {ph}", iname, cell_runs(rows), old))
    print("\n## Warm order queries (one per insertion, 10^6–10^7)\n")
    print(hdr)
    for w in ("random", "hammer"):
        for imp, iname in IMPLS:
            rows = pick(load(os.path.join(DIR, f"tails_q_{imp}_{w}.csv")), workload=f"query-{w}", **{"from": 1000000})
            old = None
            p = os.path.join(OLD, f"q_{imp}_{w}.csv")
            if os.path.exists(p):
                with open(p) as f:
                    for r in csv.reader(f):
                        if r[1] == f"query-{w}" and int(r[2]) == 1000000:
                            old = float(r[8])
            print(fmt_line(f"query after {w}", iname, cell_runs(rows), old))
    if not os.path.exists(os.path.join(DIR, "tails_cold_native_random.csv")):
        return
    print("\n## Cold caches (10^7–10^8; 500 sampled operations per kind; 2 cold runs)\n")
    print("| workload | impl | kind | mean (min over runs) | slowest, min over runs, no fault (all) | run 0: mean / max (all) | run 1: mean / max (all) |")
    print("|---|---|---|---|---|---|---|")
    for w in ("random", "hammer"):
        for imp, iname in IMPLS:
            rows = load(os.path.join(DIR, f"tails_cold_{imp}_{w}.csv"))
            for kind in ("query-cold", "insert-top"):
                rs = pick(rows, kind=kind, **{"from": 10000000})
                if not rs:
                    continue
                d = {r["run"]: r for r in rs}
                f = lambda r: f"{us(r['mean_ns'])} / {us(r['max_ns']) if r['max_ns'] else '–'} ({us(r['max_ns_all'])})"
                mn = d["min"]
                print(f"| {w} | {iname} | {kind} | {us(mn['mean_ns'])} | {us(mn['max_ns']) if mn['max_ns'] else '–'} ({us(mn['max_ns_all'])}) | {f(d['0'])} | {f(d['1'])} |")
    print("\n## Long history, n = 10^3\n")
    for imp, iname in IMPLS:
        rows = load(os.path.join(HERE, f"longrun_{imp}.csv"))
        if not rows:
            continue
        print(f"\n{iname}: {rows[-1]['ops_done']} operations, {rows[-1]['wall_s']} s\n")
        print("| window | ops done | handles | delete mean / p99.99 / max | insert mean / p99.99 / max | RSS MB | "
              + ("rebuilds | retired cores | cores MB | retired MB | spare MB | handles MB |" if imp == "native" else ""))
        print("|---" * (12 if imp == "native" else 6) + "|")
        idx = sorted(set([0, 1, 4, 9, 24, 49, 74, len(rows) - 1]))
        for i in idx:
            if i >= len(rows):
                continue
            r = rows[i]
            line = (f"| {r['window']} | {int(r['ops_done']):,} | {int(r['handles']):,} | {us(r['del_mean_ns'])} / {us(r['del_p9999_ns'])} / {us(r['del_max_ns'])} | "
                    f"{us(r['ins_mean_ns'])} / {us(r['ins_p9999_ns'])} / {us(r['ins_max_ns'])} | {int(r['rss_bytes']) / 2**20:.1f} |")
            if imp == "native":
                mb = lambda k: f"{int(r[k]) / 2**20:.2f}"
                line += f" {r['rebuilds']} | {r['retired_cores']} | {mb('cores_res')} | {mb('retired_res')} | {mb('spare_res')} | {mb('handles_res')} |"
            print(line)
        means = [float(r["mean_ns"]) for r in rows]
        maxes = [float(r["max_ns"]) for r in rows]
        print(f"\nover all windows: window mean {us(min(means))}–{us(max(means))}; window max {us(min(maxes))}–{us(max(maxes))}, "
              f"median of the window maxima {us(statistics.median(maxes))}")


def compact(cold_dir):
    """The rows of tab:native, one cell per implementation: mean / slowest (per-op min) /
    run max / run p99.9 / run p99.99 (medians over the runs), in µs. Cold queries (from
    `cold_dir`): mean / slowest (min over 2 runs) / run max (median over the 2 runs, i.e. their mean)."""
    u = lambda ns: (f"{float(ns) / 1000:.2f}" if float(ns) < 10000 else
                    f"{float(ns) / 1000:.1f}" if float(ns) < 100000 else f"{float(ns) / 1000:,.0f}")
    specs = [
        ("random insertion", lambda i: (f"tails_{i}_random_1e8.csv", dict(workload="random", **{"from": 10000000}))),
        ("clustered insertion", lambda i: (f"tails_{i}_hammer_1e8.csv", dict(workload="hammer", **{"from": 10000000}))),
        ("random churn: deletion", lambda i: (f"tails_del_{i}_random_10000000.csv", dict(phase="churn-delete"))),
        ("random churn: insertion", lambda i: (f"tails_del_{i}_random_10000000.csv", dict(phase="churn-insert"))),
        ("queue churn: deletion", lambda i: (f"tails_del_{i}_fifo_10000000.csv", dict(phase="churn-delete"))),
        ("queue churn: insertion", lambda i: (f"tails_del_{i}_fifo_10000000.csv", dict(phase="churn-insert"))),
        ("teardown: deletion", lambda i: (f"tails_del_{i}_random_10000000.csv", dict(phase="drain-delete"))),
        ("order query, warm", lambda i: (f"tails_q_{i}_random.csv", dict(workload="query-random", **{"from": 1000000}))),
    ]
    print("| µs: mean / slowest (per-op min) / run max / run p99.9 / run p99.99 | native | AVL | amortized |")
    print("|---|---|---|---|")
    for name, f in specs:
        cells = []
        for imp, _ in IMPLS:
            path, kw = f(imp)
            c = cell_runs(pick(load(os.path.join(DIR, path)), **kw))
            cells.append("–" if c is None else " / ".join(u(x) for x in (c["mean"], c["min_max"], c["max_ns"][0], c["p999_ns"][0], c["p9999_ns"][0])))
        print(f"| {name} | " + " | ".join(cells) + " |")
    cells = []
    for imp, _ in IMPLS:
        rs = pick(load(os.path.join(cold_dir, f"tails_cold_{imp}_random.csv")), kind="query-cold", **{"from": 10000000})
        d = {r["run"]: r for r in rs}
        if not d:
            cells.append("–")
            continue
        runmax = statistics.median(float(d[k]["max_ns_all"]) for k in ("0", "1"))
        cells.append(f"{u(d['min']['mean_ns'])} / {u(d['min']['max_ns_all'])} / {u(runmax)} / – / –")
    print("| order query, cold (500 per run) | " + " | ".join(cells) + " |")


if __name__ == "__main__":
    if os.environ.get("COMPACT"):
        compact(HERE)
    else:
        main()
