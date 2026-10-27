#!/bin/sh
# Paper revision 2026-10-27: long history on a small list (src/bin/longrun.rs): N = 10^3 live
# elements, 10^8 and 10^9 operations (alternately a random deletion and a random insertion), 100
# windows, one configuration at a time on performance core 2.
set -e
cd "$(dirname "$0")/../.."
O=results/rev-2026-10-27
for ops in 100000000 1000000000; do
  sfx=$([ $ops = 100000000 ] && echo "" || echo "_1e9")
  for imp in native avl bender; do
    /usr/bin/time -f "longrun_${imp}$sfx.csv: %e s, max RSS %M KB" -a -o $O/times.log \
      taskset -c 2 ./target/release/longrun $imp 1000 $ops 100 > $O/longrun_${imp}$sfx.csv
  done
done
