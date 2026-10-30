#!/bin/bash
# The cross-check of the generated code against Lean's machine semantics, and the conformance
# checks against the specification, as cited in the paper (Appendix E) and rust/README.md
# (written 2026-10-27 from the commands of the earlier runs, whose scripts were not committed):
#
#  1. xrun: 9 operation files of gen_ops.py (20 to 4,000 operations, mix and churn, 13,920 in all),
#     each run by `lake exe xrun` (OM.Machine.exec) and by the generated code; the outputs (status,
#     steps, answer and peak bit length per operation) must be byte-identical;
#  2. check: random operation sequences against a plain list (the specification): 200,000
#     operations with seed 7 in each mode grow, mix, churn (the README's command), and 300,000 with
#     seeds 1, 2, 3 in each mode (the regression form used on 2026-10-19);
#  3. replay of the 23 stress workloads of the prototype (trace.py --preset proof, 200,000
#     operations each, an order query after each update);
#  4. replay of 1,100 fuzz traces (trace.export_fuzz seeds 1..1000 short, 1..100 long).
#
# Needs: lean/.lake/build/bin/xrun (lake build xrun), rust/target/release/{xrun,check,replay}.
# Usage: scripts/conformance.sh [DATE] (logs: results/*_DATE.txt); TMP= holds the traces;
# ONLY_XRUN=1 stops after the cross-check (used by ../scripts/reproduce.sh).
set -u
cd "$(dirname "$0")/.."
D=${1:-$(date +%F)}
T=${TMP:-/tmp/om-conformance}
mkdir -p $T/ops $T/traces $T/fuzz
R=results
LX=../lean/.lake/build/bin/xrun
B=./target/release
fail=0

# 1. xrun
{
  echo "# xrun cross-check, $D: lake exe xrun ($LX) against target/release/xrun"
  i=0; tot_ops=0; tot_steps=0
  for spec in "20 1 mix" "100 2 mix" "300 3 churn" "500 4 mix" "1000 5 churn" "2000 6 mix" "2000 7 churn" "4000 7 mix" "4000 8 churn"; do
    i=$((i+1))
    set -- $spec; want=$1
    python3 scripts/gen_ops.py $spec > $T/ops/ops$i.txt; ge=$?
    # the operation file must be complete and well formed: exactly $want lines of f / a x / d x / o x y
    bad=$(grep -cvE '^(f|a [0-9]+|d [0-9]+|o [0-9]+ [0-9]+)$' $T/ops/ops$i.txt)
    $LX $T/ops/ops$i.txt > $T/ops/lean$i.out; le=$?
    $B/xrun $T/ops/ops$i.txt > $T/ops/rust$i.out; re=$?
    ops=$(wc -l < $T/ops/ops$i.txt)
    steps=$(awk '/^init ok/ {s += $3} /^ok / {s += $2} END {print s}' $T/ops/lean$i.out)
    lines=$(wc -l < $T/ops/lean$i.out)
    peak=$(tail -1 $T/ops/lean$i.out | awk '{print $NF}')
    notok=$(grep -vc '^init ok\|^ok ' $T/ops/lean$i.out)
    if [ $ge -ne 0 ] || [ "$bad" -ne 0 ] || [ "$ops" -ne "$want" ] || [ "$lines" -ne $((want + 1)) ] || [ "$notok" -ne 0 ]; then
      r=INVALID; fail=1
    elif [ $le -eq 0 ] && [ $re -eq 0 ] && cmp -s $T/ops/lean$i.out $T/ops/rust$i.out; then r=IDENTICAL; else r=DIFFERENT; fail=1; fi
    echo "file $i (gen_ops.py $spec): $ops operations (expected $want, malformed $bad, generator exit $ge), $lines output lines, $steps steps (incl. init), peak $peak bits, non-ok lines $notok, exit lean $le rust $re: $r"
    tot_ops=$((tot_ops+ops)); tot_steps=$((tot_steps+steps))
  done
  echo "total: $tot_ops operations, $tot_steps steps"
  if [ "$tot_ops" -ne 13920 ]; then echo "INVALID: expected 13920 operations in all"; fail=1; fi
} > $R/xrun_$D.txt 2>&1
cat $R/xrun_$D.txt
if [ -n "${ONLY_XRUN:-}" ]; then
  echo "overall (xrun only): $([ $fail -eq 0 ] && echo PASS || echo FAIL)"; exit $fail
fi

# 2. check
{
  echo "# check against the specification, $D"
  for m in grow mix churn; do $B/check 200000 7 $m || { echo "FAILED: check 200000 7 $m"; fail=1; }; done
  for s in 1 2 3; do for m in grow mix churn; do $B/check 300000 $s $m || { echo "FAILED: check 300000 $s $m"; fail=1; }; done; done
} > $R/check_$D.txt 2>&1
agree=$(grep -c "all answers agree" $R/check_$D.txt); echo "check: $agree of 12 runs agree"
grep FAILED $R/check_$D.txt; [ "$agree" -eq 12 ] || fail=1

# 3. the 23 stress workloads
(cd ../prototype && python3 -c "import stress; print('\n'.join(stress.WORKLOADS))" \
  | xargs -P 8 -I{} sh -c "python3 trace.py $T/traces/{}.jsonl {} 200000 --preset proof > $T/traces/{}.log 2>&1 || echo TRACE FAILED {}") \
  > $T/traces_gen.txt 2>&1; ge=$?
cat $T/traces_gen.txt
# every workload must have been generated: exit 0, no failed trace, 23 trace files
nt=$(ls $T/traces/*.jsonl 2>/dev/null | wc -l)
if [ $ge -ne 0 ] || grep -q "TRACE FAILED" $T/traces_gen.txt || [ "$nt" -ne 23 ]; then
  echo "INVALID: workload generation (exit $ge, $nt of 23 traces)"; fail=1
fi
$B/replay $T/traces/*.jsonl > $R/replay_workloads_$D.txt 2>&1; rc=$?; [ $rc -eq 0 ] || fail=1
nr=$(grep -c ' ops ' $R/replay_workloads_$D.txt); [ "$nr" -eq 23 ] || fail=1
echo "workloads: exit $rc, traces $nr (expected 23), mismatches $(grep -c MISMATCH $R/replay_workloads_$D.txt)"

# 4. the fuzz traces
(cd ../prototype && python3 - <<EOF
import trace, concurrent.futures as cf
def job(a):
    i, long = a
    return trace.export_fuzz(f"$T/fuzz/fuzz{'L' if long else ''}{i}.jsonl", i, long=long)
jobs = [(i, False) for i in range(1, 1001)] + [(i, True) for i in range(1, 101)]
with cf.ProcessPoolExecutor(8) as ex:
    rs = list(ex.map(job, jobs, chunksize=8))
print(len(rs), "traces,", sum(r["records"] for r in rs), "records,", sum(r["rebuilds"] for r in rs), "rebuilds")
EOF
) > $T/fuzz_gen.txt 2>&1; ge=$?
cat $T/fuzz_gen.txt
# the generator must succeed and produce all 1,100 traces
nf=$(ls $T/fuzz/*.jsonl 2>/dev/null | wc -l)
if [ $ge -ne 0 ] || [ "$nf" -ne 1100 ]; then echo "INVALID: fuzz generation (exit $ge, $nf of 1100 traces)"; fail=1; fi
{ cat $T/fuzz_gen.txt; $B/replay $T/fuzz/*.jsonl; } > $R/replay_fuzz_$D.txt 2>&1; rc=$?; [ $rc -eq 0 ] || fail=1
nr=$(grep -c ' ops ' $R/replay_fuzz_$D.txt); [ "$nr" -eq 1100 ] || fail=1
echo "fuzz: exit $rc, traces $nr (expected 1100), mismatches $(grep -c MISMATCH $R/replay_fuzz_$D.txt), lines $(wc -l < $R/replay_fuzz_$D.txt)"
echo "overall: $([ $fail -eq 0 ] && echo PASS || echo FAIL)"
exit $fail
