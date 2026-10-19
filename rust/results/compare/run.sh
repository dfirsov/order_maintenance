#!/bin/sh
# Reproduces results/compare/*.csv. Every configuration runs three times in one process
# (`compare ... 3`, per-operation minima), on performance cores only (cores 0-7 of the Core Ultra
# 9 285K; cores 8-23 are efficiency cores), four configurations at a time. Our structure is run to
# 10^7 elements on all workloads and to 5*10^7 (about 10 GB) on two, one at a time; the baseline
# to 10^8. summarize.py makes summary.csv and the plot.
set -e
cd "$(dirname "$0")/../.."
B=./target/release/compare
OUT=results/compare
CORES="2 3 5 6"
for imp in om bender; do
  n=10000000; [ $imp = bender ] && n=100000000
  set -- $CORES
  for w in random hammer append front; do
    taskset -c $1 $B $imp $w $n 3 > $OUT/${imp}_$w.csv &
    shift
  done
  wait
done
for w in hammer random; do
  taskset -c 3 $B om $w 50000000 3 > $OUT/om_${w}_5e7.csv
done
