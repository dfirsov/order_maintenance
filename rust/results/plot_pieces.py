"""Plot pieces.pdf / pieces.png from pieces_random.csv and pieces_hammer.csv (scripts/profile):
per decade, the slowest operation and the largest single top-job step, in machine steps.

    python3 plot_pieces.py
"""
import csv
import os

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
METRICS = [  # categorical slots 1 and 2 of the reference palette
    ("max_op_steps", "slowest operation", "#2a78d6", "o"),
    ("max_jobstep_steps", "largest single job step", "#eb6834", "s"),
]
WORKLOADS = [("random", "-"), ("hammer", "--")]
INK, MUTED, GRID = "#0b0b0b", "#52514e", "#e4e3df"
plt.rcParams.update({"font.size": 8, "axes.edgecolor": MUTED, "axes.labelcolor": INK,
                     "xtick.color": MUTED, "ytick.color": MUTED, "font.family": "serif"})

fig, ax = plt.subplots(figsize=(4.2, 2.4))
for wl, style in WORKLOADS:
    with open(os.path.join(HERE, f"pieces_{wl}.csv")) as f:
        rows = [r for r in csv.DictReader(f) if int(r["to"]) >= 10000]
    ns = [int(r["to"]) for r in rows]
    for key, label, color, marker in METRICS:
        ax.plot(ns, [int(r[key]) / 1000 for r in rows], linestyle=style, color=color, marker=marker,
                markersize=4, linewidth=1.5, label=f"{label} ({wl})")
ax.set_xscale("log")
ax.set_ylim(0, None)
ax.set_xlabel("elements")
ax.set_ylabel("machine steps (thousands)")
ax.grid(True, which="major", color=GRID, linewidth=0.6)
ax.set_axisbelow(True)
for s in ("top", "right"):
    ax.spines[s].set_visible(False)
ax.legend(frameon=False, loc="upper left", labelcolor=INK, fontsize=7)
fig.tight_layout()
for ext in ("pdf", "png"):
    fig.savefig(os.path.join(HERE, f"pieces.{ext}"), dpi=200)
print("pieces.pdf, pieces.png")
