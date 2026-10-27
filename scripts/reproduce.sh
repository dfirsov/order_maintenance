#!/bin/bash
# The central checks behind the paper, in one place:
#   1. build the Lean development (OM, and the executables xrun and extract);
#   2. the axiom audit of the main theorems (lean/Audit.lean): only propext, Classical.choice,
#      Quot.sound; and no sorry, admit, native_decide or added axiom in lean/OM;
#   3. a fresh transpilation of the machine program, compared byte for byte with rust/src/gen.rs;
#   4. the Lean-vs-Rust cross-check on the nine operation files of the paper (Appendix E):
#      13,920 operations, 7,708,854 steps, identical status, steps, answers and peak bit lengths.
# The larger conformance checks and the benchmarks are in rust/scripts/conformance.sh and
# experiments/lean-design/results/; they take longer and are not run here.
# Usage: scripts/reproduce.sh            (about 10 minutes from a Mathlib cache, 24 cores)
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT=$(pwd)
TMP=${TMP:-$(mktemp -d)}
mkdir -p "$TMP"
command -v cargo >/dev/null || export PATH="$HOME/.cargo/bin:$PATH"
command -v lake >/dev/null || export PATH="$HOME/.elan/bin:$PATH"
echo "== 1. lake build"
(cd lean && { lake exe cache get >/dev/null 2>&1 || true; lake build OM xrun extract; } > "$TMP/build.txt" 2>&1) \
  || { tail -20 "$TMP/build.txt"; echo "build FAILED"; exit 1; }
tail -1 "$TMP/build.txt"

echo "== 2. axiom audit"
(cd lean && lake env lean Audit.lean) > "$TMP/axioms.txt" 2>&1
cat "$TMP/axioms.txt"
# every theorem must report its axioms, and they must be among propext, Classical.choice, Quot.sound
python3 - "$TMP/axioms.txt" <<'PY' || { echo "axiom audit FAILED"; exit 1; }
import re, sys
text = open(sys.argv[1]).read()
deps = re.findall(r"depends on axioms: \[([^\]]*)\]", text)
ok = {"propext", "Classical.choice", "Quot.sound"}
bad = [d for d in deps if not {a.strip() for a in d.split(",")} <= ok]
sys.exit(0 if len(deps) == 10 and not bad and "error" not in text else 1)
PY
if grep -rnE '\bsorry\b|\badmit\b|native_decide|^\s*axiom\b' lean/OM --include=*.lean; then
  echo "source audit FAILED"; exit 1
fi
echo "axiom audit: 10 theorems, only standard axioms; no sorry/admit/native_decide/axiom in lean/OM"

echo "== 3. fresh transpilation"
lean/.lake/build/bin/extract "$TMP/gen.rs"
cmp "$TMP/gen.rs" rust/src/gen.rs && echo "rust/src/gen.rs is byte-identical to a fresh transpilation"

echo "== 4. Lean-vs-Rust cross-check"
(cd rust && cargo build --release --offline --bin xrun)
(cd rust && ONLY_XRUN=1 TMP="$TMP" scripts/conformance.sh "$(date +%F)-reproduce")
grep -q DIFFERENT "rust/results/xrun_$(date +%F)-reproduce.txt" && { echo "cross-check FAILED"; exit 1; }
echo "== all checks passed (logs in $TMP and rust/results/xrun_$(date +%F)-reproduce.txt)"
