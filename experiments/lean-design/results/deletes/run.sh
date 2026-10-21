#!/bin/sh
# Reproduces results/deletes/*.csv: deletion timings (bin deletes) at 10^6 and 10^7 elements,
# minimum over 3 in-process runs, on performance cores (2, 3, 5), three runs at a time.
set -e
cd "$(dirname "$0")/../.."
B=./target/release/deletes
for n in ${NS:-1000000 10000000}; do
  for w in random fifo; do
    set -- 2 3 5
    for imp in native avl bender; do
      taskset -c $1 $B $imp $w $n 3 > results/deletes/${imp}_${w}_$n.csv &
      shift
    done
    wait
  done
done
