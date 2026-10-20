#!/bin/sh
# Reproduces results/traces/*.txt: trace equivalence of `Native<Wide>` with the verified algorithm.
# The prototype writes traces with the verified program's parameters (`trace.py --preset verified`,
# = `proofParams N`); the Lean model (`lake exe replay`) and the native version (`trace`) replay
# them, checking every handle, inserted key, order answer, counter and state digest.
# TRACES (default: a temporary directory) receives the traces, about 7 GB.
set -e
cd "$(dirname "$0")/../.."
ROOT=$(cd ../.. && pwd)
T=${TRACES:-$(mktemp -d)}
WL="starve group_end chunk_end narrow_gap zigzag delete_burst harmonic harmonic_half random insert_random
front append hammer spread64 spread1k churn rebuild_cycle yoyo fifo cursor_chase shrink_only flicker family_edge"
for w in $WL; do echo "$w 200000 2e5"; done > "$T/jobs"
# (harmonic rescans all elements whenever its anchors run out: hours at 2e6)
for w in random hammer churn delete_burst yoyo; do echo "$w 2000000 2e6"; done >> "$T/jobs"
(cd "$ROOT/prototype" && while read -r w n tag; do echo "python3 trace.py $T/${w}_$tag.jsonl $w $n --preset verified"; done < "$T/jobs" | xargs -P 8 -I{} sh -c '{}')
./target/release/trace "$T"/*.jsonl > results/traces/native.txt
(cd "$ROOT/lean" && ./.lake/build/bin/replay "$T"/*.jsonl) > results/traces/lean.txt
tail -1 results/traces/native.txt results/traces/lean.txt
