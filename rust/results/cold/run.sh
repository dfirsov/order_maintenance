#!/bin/sh
# Reproduces results/cold/*.csv: per-operation time with cold caches (src/bin/cold.rs), one
# configuration at a time on performance core 2 (cache sweeps of concurrent runs would disturb
# each other). Each implementation's own worst workload first. Our structure to 10^7 elements,
# the baselines to 10^8.
set -e
cd "$(dirname "$0")/../.."
B=./target/release/cold
OUT=results/cold
for cfg in "avl random 100000000" "bender hammer 100000000" "om random 10000000" "om hammer 10000000" \
           "avl front 100000000" "bender random 100000000" "om append 10000000" "om front 10000000" \
           "avl hammer 100000000" "bender front 100000000"; do
  set -- $cfg
  taskset -c 2 $B $1 $2 $3 500 > $OUT/$1_$2.csv
done
