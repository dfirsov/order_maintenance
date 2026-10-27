#!/bin/sh
# Paper revision 2026-10-27: re-runs the configurations behind Table 2 and tab:native of the paper
# with per-run tail statistics (TAILS=..., src/tails.rs). The commands and arguments are those of
# results/run.sh (10^7), run_1e8.sh (10^8), run_queries.sh, deletes/run.sh and cold/run.sh, but
# ONE CONFIGURATION AT A TIME on performance core 2 (the earlier scripts ran two to four
# configurations at once on cores 2, 3, 5, 6, except cold/run.sh, which also ran one at a time).
# Each main CSV (stdout) has the old columns; tails_*.csv have the per-run rows. Wall time and peak
# RSS of each configuration go to times.log. O= sets the output directory, PARTS= a subset of
# "ins ins8 q del cold" (replicate 2: O=results/rev-2026-10-27/rep2 PARTS="ins ins8 q del").
set -e
cd "$(dirname "$0")/../.."
O=${O:-results/rev-2026-10-27}
mkdir -p $O
P=" ${PARTS:-ins ins8 q del cold} "
has() { case "$P" in *" $1 "*) return 0;; *) return 1;; esac; }
B=./target/release
run() { # out-name tails-name command...
  out=$1; t=$2; shift 2
  rm -f $O/$t
  /usr/bin/time -f "$out: %e s, max RSS %M KB" -a -o $O/times.log env TAILS=$O/$t taskset -c 2 "$@" > $O/$out
}
has ins && for imp in ${IMPS:-native avl bender}; do
  for w in random hammer; do
    run ${imp}_$w.csv tails_${imp}_$w.csv $B/compare $imp $w 10000000 3
  done
done
has ins8 && for imp in ${IMPS:-native avl bender}; do
  for w in random hammer; do
    run ${imp}_${w}_1e8.csv tails_${imp}_${w}_1e8.csv $B/compare $imp $w 100000000 3
  done
done
has q && for imp in ${IMPS:-native avl bender}; do
  for w in random hammer; do
    run q_${imp}_$w.csv tails_q_${imp}_$w.csv $B/compare $imp $w 10000000 3 1
  done
done
has del && for imp in ${IMPS:-native avl bender}; do
  for w in random fifo; do
    run del_${imp}_${w}_10000000.csv tails_del_${imp}_${w}_10000000.csv $B/deletes $imp $w 10000000 3
  done
done
has cold && for imp in ${IMPS:-native avl bender}; do
  for w in random hammer; do
    run cold_${imp}_$w.csv tails_cold_${imp}_$w.csv $B/cold $imp $w 100000000 500
  done
done
true
