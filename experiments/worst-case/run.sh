#!/bin/sh
# Reproduces results/: the K_R = 1 profile (a = 5, s = 16, T = 12L², H = L/2 + 1) with the verified
# and with the linear startDrain, on the repository's runtime and with runtime.patch.
#   experiments/worst-case/run.sh [WORK]
set -e
E="$(cd "$(dirname "$0")" && pwd)"
R="$(cd "$E/../.." && pwd)"
W="${1:-/tmp/om-worst}"
mkdir -p "$W"
cd "$R/lean" && lake build OM.Extract.Rust
lake env lean --run "$E/Splice.lean" "$W/gen_kr1.rs" orig 1 5 16 12 2
lake env lean --run "$E/Splice.lean" "$W/gen_kr1_lin.rs" lin 1 5 16 12 2
mk() {  # mk NAME GEN [patch]
  rm -rf "${W:?}/$1"; mkdir -p "$W/$1"
  cp -r "$R/rust/Cargo.toml" "$R/rust/Cargo.lock" "$R/rust/rust-toolchain.toml" "$R/rust/src" "$W/$1/"
  cp "$2" "$W/$1/src/gen.rs"
  if [ -n "$3" ]; then (cd "$W/$1" && patch -s -p2 < "$E/runtime.patch"); fi
  (cd "$W/$1" && cargo build -q --release --offline)
}
mk kr1 "$W/gen_kr1.rs"
mk kr1_lin "$W/gen_kr1_lin.rs"
mk kr1_lin_rt "$W/gen_kr1_lin.rs" patch
for v in kr1 kr1_lin kr1_lin_rt; do
  for m in grow churn mix; do "$W/$v/target/release/check" 300000 5 $m | head -1; done
done
cd "$W"
run4() {  # run4 VARIANT [workloads]
  v=$1; shift; set -- ${*:-random hammer append front}; c=2
  for w in "$@"; do taskset -c $c "$W/$v/target/release/compare" om $w 10000000 3 > "$E/results/${v}_$w.csv" & c=$((c + 1)); [ $c = 4 ] && c=5; done
  wait
}
run4 kr1 random hammer
run4 kr1_lin
run4 kr1_lin_rt
