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

runs = defaultdict(list)
for path in sorted(glob.glob(os.path.join(HERE, "*.csv"))):
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

SERIES = {  # categorical slots 1 and 2 of the reference palette, with distinct markers
    "om": ("verified worst-case O(1)", "#2a78d6", "o"),
    "bender": ("amortized baseline", "#eb6834", "s"),
}
INK, MUTED, GRID = "#0b0b0b", "#52514e", "#e4e3df"
plt.rcParams.update({"font.size": 8, "axes.edgecolor": MUTED, "axes.labelcolor": INK,
                     "xtick.color": MUTED, "ytick.color": MUTED, "font.family": "serif"})

fig, axes = plt.subplots(1, 2, figsize=(6.3, 2.5))
MIN_N = 1000
for imp, (label, color, marker) in SERIES.items():
    by_n = defaultdict(list)
    for r in rows:
        if r["impl"] == imp and r["elements"] >= MIN_N:
            by_n[r["elements"]].append(r)
    ns = sorted(by_n)
    worst = [max(r["max_ns"] for r in by_n[n]) / 1e6 for n in ns]
    means = [[r["mean_ns"] / 1e3 for r in by_n[n]] for n in ns]
    rnd = [next(r["mean_ns"] / 1e3 for r in by_n[n] if r["workload"] == "random") for n in ns]
    axes[0].plot(ns, worst, color=color, marker=marker, markersize=4, linewidth=1.5, label=label)
    axes[1].fill_between(ns, [min(m) for m in means], [max(m) for m in means], color=color, alpha=0.18, linewidth=0)
    axes[1].plot(ns, rnd, color=color, marker=marker, markersize=4, linewidth=1.5, label=label)

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
axes[0].legend(frameon=False, loc="upper left", labelcolor=INK)
fig.tight_layout()
for ext in ("pdf", "png"):
    fig.savefig(os.path.join(HERE, f"compare.{ext}"), dpi=200)
print(f"{len(rows)} rows -> summary.csv, compare.pdf, compare.png")
