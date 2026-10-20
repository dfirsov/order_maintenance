#!/bin/sh
# Reproduces results/q_*.csv: as run.sh, with one timed order query on a random pair after every
# insertion (rows "query-WORKLOAD"), 10^7 elements, random and hammer insertion.
set -e
cd "$(dirname "$0")/.."
B=./target/release/compare
for w in random hammer; do
  taskset -c 2 $B native $w 10000000 3 1 > results/q_native_$w.csv &
  taskset -c 3 $B avl $w 10000000 3 1 > results/q_avl_$w.csv &
  taskset -c 5 $B bender $w 10000000 3 1 > results/q_bender_$w.csv &
  wait
done
