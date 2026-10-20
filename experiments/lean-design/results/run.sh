#!/bin/sh
# Reproduces results/*.csv at 10^7 elements: per-operation times (minimum over 3 in-process runs)
# on performance cores only (2, 3, 5, 6 of the Core Ultra 9 285K), four runs at a time, as in
# rust/results/compare. `native` is the verified algorithm written natively; `core`, `lean`,
# `native-k1`, `native-k1-128` are the ablation configurations (see README.md).
set -e
cd "$(dirname "$0")/.."
B=./target/release/compare
N=${N:-10000000}
for imp in ${IMPS:-native avl avl-touch bender core lean native-k1 native-k1-128}; do
  set -- 2 3 5 6
  for w in random hammer append front; do
    taskset -c $1 $B $imp $w $N 3 > results/${imp}_$w.csv &
    shift
  done
  wait
done
