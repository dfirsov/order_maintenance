"""Print a compact table from results/scaling.txt (works on partial output)."""
import re
import sys

rows = []
for line in open(sys.argv[1] if len(sys.argv) > 1 else "results/scaling.txt"):
    line = re.sub(r"=\s+", "=", line)
    kind, wl = line.split()[:2]
    rows.append((kind, wl, dict(re.findall(r"(\S+?)=(\S+)", line))))
bad = [r for r in rows if r[2].get("fallbacks", "0") != "0" or r[2].get("pq_scan", "0") != "0"]
print(f"{len(rows)} rows; rows with fallbacks or slow PQ scans: {len(bad)}")
key = lambda r: (r[0], r[1], int(r[2].get("n") or r[2].get("m")))
for kind, w, kv in sorted(rows, key=key):
    if kind == "full":
        print(f"{w:13s} n={kv['n']:>8} steps/op={kv['max_steps/op']:>4} chunk/T={float(kv['max_chunk/T']):.2f} "
              f"group/G={float(kv['max_group/G']):.2f} pq={kv['max_pq']:>3} e_bits={kv['e_bits_used']}/{kv['B_e_last']} "
              f"g_bits={kv['g_bits_used']}/{kv['B_g_last']} top_bits={kv['top_bits_used']}/40 fill={kv['max_fill']} "
              f"table={kv['max_table']}")
    else:
        print(f"TOP {w:9s} m={kv['m']:>8} job={kv['max_job']} fallbacks={kv['fallbacks']} table={kv['max_table']} "
              f"gap_bits_left={kv['min_gap_bits']}/40 ghosts={kv['max_ghosts']}")
