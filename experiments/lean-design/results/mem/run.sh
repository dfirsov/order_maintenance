#!/bin/sh
# Reproduces results/mem/*.csv: resident memory of one structure (bin mem), one run at a time.
set -e
cd "$(dirname "$0")/../.."
B=./target/release/mem
for imp in native core avl bender; do
  for w in random hammer; do
    taskset -c 2 $B $imp $w ${N:-100000000} > results/mem/${imp}_$w.csv
  done
done
for imp in native avl bender; do
  for w in churn fifo; do
    taskset -c 2 $B $imp $w ${ND:-10000000} > results/mem/${imp}_$w.csv
  done
done
