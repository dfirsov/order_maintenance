"""Collect the CSV files of results/compare/run.sh into summary.csv and plot compare.pdf / .png.

Each file already combines three runs per operation (see `compare`). Where two files cover the
same decade (a run to 10^7 and one to 5*10^7), the smaller slowest operation is kept: the
workloads are deterministic, so an algorithmic spike shows in both.

    python3 summarize.py
"""
import csv
import glob
import os
import statistics
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
COLS = ["impl", "workload", "from", "to", "ops", "mean_ns", "p99_ns", "p9999_ns", "max_ns",
        "mean_work", "max_work", "work_of_slowest"]

# the native implementation of the verified algorithm (experiments/lean-design, not verified)
NATIVE = os.path.join(HERE, "..", "..", "..", "experiments", "lean-design", "results")

runs = defaultdict(list)
for path in sorted(glob.glob(os.path.join(HERE, "*.csv")) + glob.glob(os.path.join(NATIVE, "native_*.csv"))):
    if os.path.basename(path) == "summary.csv":
        continue
    with open(path) as f:
        for row in csv.reader(f):
            r = dict(zip(COLS, row))
            runs[(r["impl"], r["workload"], int(r["to"]))].append(r)

rows = []
for (imp, wl, to), rs in sorted(runs.items()):
    works = {r["max_work"] for r in rs}
    assert len(works) == 1, (imp, wl, to, works)
    rows.append({
        "impl": imp, "workload": wl, "elements": to,
        "mean_ns": statistics.median(float(r["mean_ns"]) for r in rs),
        "p9999_ns": min(int(r["p9999_ns"]) for r in rs),
        "max_ns": min(int(r["max_ns"]) for r in rs),
        "max_work": int(rs[0]["max_work"]),
    })

with open(os.path.join(HERE, "summary.csv"), "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=list(rows[0]))
    w.writeheader()
    w.writerows(rows)

# ---- plot ----
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.ticker

SERIES = {  # categorical slots 1-3 of the reference palette, with distinct markers; the native
    # implementation shares the verified program's hue (same algorithm), dashed with open markers
    "om": ("worst-case O(1): verified program", "#2a78d6", "o"),
    "native": ("worst-case O(1): same algorithm, native (not verified)", "#2a78d6", "o"),
    "bender": ("amortized O(1) (Bender et al.)", "#eb6834", "s"),
    "avl": ("balanced tree, O(log n)", "#1baf7a", "^"),
}
INK, MUTED, GRID = "#0b0b0b", "#52514e", "#e4e3df"
plt.rcParams.update({"font.size": 8, "axes.edgecolor": MUTED, "axes.labelcolor": INK,
                     "xtick.color": MUTED, "ytick.color": MUTED, "font.family": "serif"})

fig, axes = plt.subplots(1, 2, figsize=(6.3, 3.0))
MIN_N = 1000
def style(imp, color, marker):
    if imp == "native":
        return dict(color=color, marker=marker, markersize=4, linewidth=1.5, linestyle="--",
                    markerfacecolor="white")
    return dict(color=color, marker=marker, markersize=4, linewidth=1.5)


for imp, (label, color, marker) in SERIES.items():
    by_n = defaultdict(list)
    for r in rows:
        if r["impl"] == imp and r["elements"] >= MIN_N and not r["workload"].startswith("query"):
            by_n[r["elements"]].append(r)
    ns = sorted(by_n)
    worst = [max(r["max_ns"] for r in by_n[n]) / 1e6 for n in ns]
    means = [[r["mean_ns"] / 1e3 for r in by_n[n]] for n in ns]
    rnd = [next((r["mean_ns"] / 1e3 for r in by_n[n] if r["workload"] == "random"), float("nan")) for n in ns]
    axes[0].plot(ns, worst, label=label, **style(imp, color, marker))
    axes[1].fill_between(ns, [min(m) for m in means], [max(m) for m in means], color=color,
                         alpha=0.10 if imp == "native" else 0.18, linewidth=0)
    axes[1].plot(ns, rnd, label=label, **style(imp, color, marker))

axes[0].set_ylabel("slowest operation (ms)")
axes[1].set_ylabel("mean time per operation (µs)")
for ax, title in zip(axes, ["(a) slowest single operation", "(b) mean time (line: random insertion)"]):
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlabel("elements")
    ax.set_title(title, fontsize=8, color=INK, loc="left")
    ax.grid(True, which="major", color=GRID, linewidth=0.6)
    ax.set_axisbelow(True)
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)
h, l = axes[0].get_legend_handles_labels()
fig.legend(h, l, frameon=False, loc="lower center", ncol=2, labelcolor=INK)
fig.tight_layout(rect=(0, 0.13, 1, 1))
for ext in ("pdf", "png"):
    fig.savefig(os.path.join(HERE, f"compare.{ext}"), dpi=200)
print(f"{len(rows)} rows -> summary.csv, compare.pdf, compare.png")

# ---- queries: (a) one random order query after every random insertion (queries/*.csv; native:
# the experiment's q_native_random.csv), (b) cold caches (rust/results/cold; native: the
# experiment's cold/), random workload, mean per decade ----
COLD = os.path.join(HERE, "..", "cold")
q = defaultdict(dict)
for path in sorted(glob.glob(os.path.join(HERE, "queries", "*.csv")) + [os.path.join(NATIVE, "q_native_random.csv")]):
    with open(path) as f:
        for row in csv.reader(f):
            r = dict(zip(COLS, row))
            if r["workload"] == "query-random" and int(r["to"]) >= MIN_N:
                q[r["impl"]][int(r["to"])] = r
CCOLS = ["impl", "workload", "kind", "from", "to", "ops", "faulted", "mean_ns", "max_ns"]
cold = defaultdict(dict)
for path in [os.path.join(COLD, f"{i}_random.csv") for i in ("om", "avl", "bender")] + [os.path.join(NATIVE, "cold", "native_random.csv")]:
    with open(path) as f:
        for row in csv.reader(f):
            r = dict(zip(CCOLS, row))
            if r["kind"] == "query-cold" and int(r["to"]) >= MIN_N:
                cold[r["impl"]][int(r["to"])] = r
with open(os.path.join(HERE, "queries", "summary.csv"), "w", newline="") as f:
    w = csv.writer(f)
    w.writerow(["impl", "elements", "mean_ns", "p99_ns", "max_ns", "mean_work", "max_work", "cold_mean_ns", "cold_max_ns"])
    for imp in SERIES:
        for n in sorted(set(q[imp]) | set(cold[imp])):
            r, c = q[imp].get(n, {}), cold[imp].get(n, {})
            w.writerow([imp, n, r.get("mean_ns"), r.get("p99_ns"), r.get("max_ns"), r.get("mean_work"),
                        r.get("max_work"), c.get("mean_ns"), c.get("max_ns")])
fig, axes = plt.subplots(1, 2, figsize=(6.3, 3.0))
for imp, (label, color, marker) in SERIES.items():
    for ax, d in ((axes[0], q[imp]), (axes[1], cold[imp])):
        ns = sorted(d)
        ax.plot(ns, [float(d[n]["mean_ns"]) for n in ns], label=label, **style(imp, color, marker))
axes[0].set_ylabel("mean time per query (ns)")
axes[1].set_ylabel("mean time per query (ns)")
for ax, title in zip(axes, ["(a) warm: one query after every insertion", "(b) cold: caches evicted before each query"]):
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlabel("elements")
    ax.set_title(title, fontsize=8, color=INK, loc="left")
    ax.grid(True, which="major", color=GRID, linewidth=0.6)
    ax.set_axisbelow(True)
    for sp in ("top", "right"):
        ax.spines[sp].set_visible(False)
    ax.yaxis.set_major_locator(matplotlib.ticker.LogLocator(subs=(1, 2, 5)))
    ax.yaxis.set_major_formatter(matplotlib.ticker.FuncFormatter(lambda v, _: f"{v:g}"))
    ax.yaxis.set_minor_formatter(matplotlib.ticker.NullFormatter())
h, l = axes[0].get_legend_handles_labels()
fig.legend(h, l, frameon=False, loc="lower center", ncol=2, labelcolor=INK)
fig.tight_layout(rect=(0, 0.13, 1, 1))
for ext in ("pdf", "png"):
    fig.savefig(os.path.join(HERE, f"queries.{ext}"), dpi=200)
print("queries/summary.csv, queries.pdf, queries.png")
