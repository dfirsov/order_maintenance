"""Plot results/growth.csv (from `growth 4000000 50000 1`) into results/growth.png."""
import csv
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

rows = list(csv.DictReader(open("results/growth.csv")))
live = [int(r["live"]) for r in rows]
ns = [float(r["ns_per_op"]) for r in rows]
steps = [float(r["mean_steps"]) for r in rows]
mx = [int(r["max_steps"]) for r in rows]
nsps = [a / b for a, b in zip(ns, steps)]
peak = [int(r["peak_bits"]) for r in rows]
cap = [int(r["N"]) for r in rows]

fig, ax = plt.subplots(4, 1, figsize=(9, 12), sharex=True)
ax[0].plot(live, ns, ".-", ms=3)
ax[0].set_ylabel("ns per operation\n(mean over 50k)")
ax[0].set_title("Generated Rust code, random insertions (K_B = 4)")
ax[1].plot(live, nsps, ".-", ms=3, color="tab:red")
ax[1].set_ylabel("ns per machine step")
ax[2].plot(live, steps, ".-", ms=3, label="mean")
ax[2].plot(live, mx, ".-", ms=3, label="max in window")
ax[2].set_yscale("log")
ax[2].axhline(1133561742, color="k", ls="--", lw=0.8, label="proved bound opB 4")
ax[2].set_ylabel("machine steps\nper operation")
ax[2].legend(loc="center right", fontsize=8)
ax[3].step(live, peak, where="post", label="peak value (bits)")
ax3 = ax[3].twinx()
ax3.step(live, cap, where="post", color="tab:green", label="capacity N")
ax3.set_yscale("log")
ax3.set_ylabel("capacity N", color="tab:green")
ax[3].set_ylabel("peak value (bits)")
ax[3].set_xlabel("live elements")
ax[3].set_xscale("log")
fig.tight_layout()
fig.savefig("results/growth.png", dpi=110)
print("wrote results/growth.png")
