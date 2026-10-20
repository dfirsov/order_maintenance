#!/bin/sh
# Reproduces results/cold/*.csv: as rust/results/cold/run.sh (one configuration at a time, core 2),
# for `native`, to 10^8 elements. The baselines' rows to compare with are rust/results/cold/*.csv
# (same harness, same machine, same day).
set -e
cd "$(dirname "$0")/../.."
B=./target/release/cold
for w in random hammer; do
  taskset -c 2 $B native $w 100000000 500 > results/cold/native_$w.csv
done
