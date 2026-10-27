#!/bin/sh
# Paper revision 2026-10-27b: compare.rs no longer times the choice of the element to insert after
# (the random draw and the read of the vector of live handles at a random index were inside the
# timed interval). This re-runs the configurations of results/rev-2026-10-27/run.sh, replicate-2
# settings (PARTS="ins ins8 q del"), with the same commands, one configuration at a time on
# performance core 2. deletes.rs is unchanged (its arguments were already chosen outside the timed
# interval); "del" is re-run as a same-session control. cold.rs is unchanged and not re-run.
# Extra parts:
#   sel   src/bin/selcost.rs: the cost of the old in-interval work alone, per decade 10^6-10^7 and
#         10^7-10^8 (no data structure)
#   seed  random insertion at 10^7 with SEED=1 and SEED=2 (compare's new optional seed), into seeds/
set -e
cd "$(dirname "$0")/../.."
O=${O:-results/rev-2026-10-27b}
mkdir -p $O
P=" ${PARTS:-sel ins ins8 q del seed} "
has() { case "$P" in *" $1 "*) return 0;; *) return 1;; esac; }
B=./target/release
run() { # out-name tails-name command...
  out=$1; t=$2; shift 2
  rm -f $O/$t
  /usr/bin/time -f "$out: %e s, max RSS %M KB" -a -o $O/times.log env TAILS=$O/$t taskset -c 2 "$@" > $O/$out
}
has sel && for d in "1000000 10000000 1e7" "10000000 100000000 1e8"; do
  set -- $d
  /usr/bin/time -f "selcost_$3.csv: %e s, max RSS %M KB" -a -o $O/times.log taskset -c 2 $B/selcost $1 $2 3 > $O/selcost_$3.csv
done
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
has seed && mkdir -p $O/seeds && for k in 1 2; do
  for imp in ${IMPS:-native avl bender}; do
    run seeds/${imp}_random_seed$k.csv seeds/tails_${imp}_random_seed$k.csv env SEED=$k $B/compare $imp random 10000000 3
  done
done
true
