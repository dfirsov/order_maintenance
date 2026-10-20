"""Markdown tables of results/ for README.md (python3 results/summarize.py).

Per configuration and workload: mean / p99.99 / slowest per-operation time of the insertions in
the last decade (10^6..10^7 from run.sh, 10^7..10^8 from run_1e8.sh), queries (run_queries.sh),
and cold-cache insertions and queries (cold/run.sh, with the baselines' rows from
rust/results/cold)."""
import csv
import os

HERE = os.path.dirname(os.path.abspath(__file__))
COLD_BASE = os.path.join(HERE, "..", "..", "..", "rust", "results", "cold")

NAMES = {
    "native": "native (the verified algorithm)",
    "avl": "AVL tree",
    "avl-touch": "AVL tree, arrays mapped before the run",
    "bender": "amortized (Bender et al.)",
    "core": "ablation: one core, no rebuilding",
    "native-k1": "ablation: native, profile K_R = 1",
    "native-k1-128": "ablation: native, K_R = 1, 128-bit group labels",
    "lean": "ablation: one core, K_R = 1, 128-bit labels",
}


def us(ns):
    v = int(ns)
    return f"{v} ns" if v < 1000 else f"{v / 1000:.1f} µs"


def row(path, frm):
    if not os.path.exists(path):
        return None
    with open(path) as f:
        for r in csv.reader(f):
            if int(r[2]) == frm and not r[1].startswith("query"):
                return r
    return None


def qrow(path, frm):
    if not os.path.exists(path):
        return None
    with open(path) as f:
        for r in csv.reader(f):
            if int(r[2]) == frm and r[1].startswith("query"):
                return r
    return None


def fmt(r):
    return "–" if r is None else f"{us(r[5])} / {us(r[7])} / {us(r[8])}"


def table(suffix, frm, impls, wls):
    out = ["| configuration | " + " | ".join(wls) + " |", "|---" * (len(wls) + 1) + "|"]
    for i in impls:
        cells = [fmt(row(os.path.join(HERE, f"{i}_{w}{suffix}.csv"), frm)) for w in wls]
        if all(c == "–" for c in cells):
            continue
        out.append(f"| {NAMES[i]} | " + " | ".join(cells) + " |")
    return "\n".join(out)


def cold(impl, wl, base):
    path = os.path.join(base, f"{impl}_{wl}.csv")
    if not os.path.exists(path):
        return {}
    res = {}
    with open(path) as f:
        for r in csv.reader(f):
            if r[2] in ("insert-top", "insert-sample", "query-cold"):
                res[(r[2], int(r[3]))] = r
    return res


def cold_table():
    out = ["| configuration, workload | slowest insertion 10^6 / 10^7 / 10^8 (no fault; with faults) | cold query mean / slowest at 10^7..10^8 |",
           "|---|---|---|"]
    for impl, base in (("native", os.path.join(HERE, "cold")), ("avl", COLD_BASE), ("bender", COLD_BASE)):
        for wl in ("random", "hammer"):
            c = cold(impl, wl, base)
            if not c:
                continue
            ins = []
            for frm in (100000, 1000000, 10000000):
                rs = [c.get((k, frm)) for k in ("insert-top", "insert-sample")]
                rs = [r for r in rs if r]
                if not rs:
                    ins.append("–")
                    continue
                mx = max(int(r[8]) for r in rs if r[8])
                mxall = max(int(r[11]) for r in rs)
                ins.append(f"{us(mx)} ({us(mxall)})")
            q = c.get(("query-cold", 10000000))
            qs = "–" if q is None else f"{us(q[7])} / {us(q[8])}"
            out.append(f"| {NAMES[impl]}, {wl} | " + " / ".join(ins) + f" | {qs} |")
    return "\n".join(out)


def main():
    wl4 = ["random", "hammer", "append", "front"]
    print("Insertions, 10^6..10^7 elements, mean / p99.99 / slowest:\n")
    print(table("", 1000000, list(NAMES), wl4))
    print("\nInsertions, 10^7..10^8 elements, mean / p99.99 / slowest:\n")
    print(table("_1e8", 10000000, list(NAMES), ["random", "hammer"]))
    print("\nWarm order queries after each insertion, 10^6..10^7 elements, mean / p99.99 / slowest:\n")
    out = ["| configuration | random | hammer |", "|---|---|---|"]
    for i in ("native", "avl", "bender"):
        cells = [fmt(qrow(os.path.join(HERE, f"q_{i}_{w}.csv"), 1000000)) for w in ("random", "hammer")]
        out.append(f"| {NAMES[i]} | " + " | ".join(cells) + " |")
    print("\n".join(out))
    print("\nCold caches (128 MB evicted before each measured operation):\n")
    print(cold_table())


if __name__ == "__main__":
    main()
