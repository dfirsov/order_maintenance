#!/bin/sh
# Reproduces results/: splices the linear startDrain into the extracted program (LinSD.lean),
# builds the original and the variant crate in WORK (default /tmp/om-lin), compares their memory
# digests on four random operation mixes, and times the variant on the four `compare` workloads.
#   experiments/linear-drain-start/run.sh [WORK]
set -e
E="$(cd "$(dirname "$0")" && pwd)"
R="$(cd "$E/../.." && pwd)"
W="${1:-/tmp/om-lin}"
mkdir -p "$W"
(cd "$R/lean" && lake build OM.Extract.Rust && lake env lean --run "$E/LinSD.lean" "$W/gen_lin.rs")
for v in orig lin; do
  rm -rf "${W:?}/$v"; mkdir -p "$W/$v"
  cp -r "$R/rust/Cargo.toml" "$R/rust/Cargo.lock" "$R/rust/rust-toolchain.toml" "$R/rust/src" "$W/$v/"
  cat "$E/digest.rs" >> "$W/$v/src/rt.rs"
  cp "$E/dig.rs" "$W/$v/src/bin/"
done
cp "$W/gen_lin.rs" "$W/lin/src/gen.rs"
for v in orig lin; do (cd "$W/$v" && cargo build -q --release --offline); done
c=0
for cfg in "grow 1" "churn 2" "mix 3" "hot 4"; do
  set -- $cfg
  for v in orig lin; do
    taskset -c $((2 + c % 4)) "$W/$v/target/release/dig" 300000 $2 $1 1000 > "$W/dig_${v}_$1.txt" 2> "$W/dig_${v}_$1.err" &
    c=$((c + 1))
  done
done
wait
for m in grow churn mix hot; do
  same=NO; cmp -s "$W/dig_orig_$m.txt" "$W/dig_lin_$m.txt" && same=yes
  echo "$m: $(cat "$W/dig_orig_$m.err") | linear: $(sed 's/.*: max/max/' "$W/dig_lin_$m.err") | digests identical at $(wc -l < "$W/dig_orig_$m.txt") checkpoints: $same"
done > "$E/results/digest_check.txt"
cat "$E/results/digest_check.txt"
set -- 2 3 5 6
for w in random hammer append front; do
  taskset -c $1 "$W/lin/target/release/compare" om $w 10000000 3 > "$E/results/lin_$w.csv" &
  shift
done
wait
