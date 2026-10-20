#!/bin/sh
# Reproduces results/*_1e8.csv: as run.sh, at 10^8 elements, random and hammer insertion, two runs
# at a time.
set -e
cd "$(dirname "$0")/.."
B=./target/release/compare
for imp in ${IMPS:-native avl avl-touch bender core}; do
  taskset -c 2 $B $imp random 100000000 3 > results/${imp}_random_1e8.csv &
  taskset -c 3 $B $imp hammer 100000000 3 > results/${imp}_hammer_1e8.csv &
  wait
done
