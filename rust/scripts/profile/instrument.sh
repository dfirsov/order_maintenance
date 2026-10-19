#!/bin/sh
# A profiling copy of the crate: every generated function records how often it was called and its
# largest inclusive step count, and `pieces` reports, per decade, the slowest operation and its
# pieces (job steps, drain starts, core insertions). The step counts are those of the unmodified
# code. Usage: scripts/profile/instrument.sh DIR, then in DIR:
#   cargo build --release --offline && ./target/release/pieces random 50000000
set -e
R="$(cd "$(dirname "$0")/../.." && pwd)"
D="$1"; [ -n "$D" ] || { echo "usage: $0 DIR"; exit 1; }
mkdir -p "$D/src/bin"
cp -r "$R/Cargo.toml" "$R/Cargo.lock" "$R/rust-toolchain.toml" "$D/"
cp "$R"/src/*.rs "$D/src/"
cp "$R/scripts/profile/pieces.rs" "$D/src/bin/"
python3 - "$D/src/gen.rs" <<'PY'
import re, sys
p = sys.argv[1]; s = open(p).read()
names = dict((n, nm) for nm, n in re.findall(r'/// `([^`]*)`\n(?:#\[allow[^\n]*\]\n)?fn f(\d+)\(', s))
pat = re.compile(r'fn f(\d+)\(args: \[W; (\d+)\], m: &mut M\) -> R<\[W; (\d+)\]> \{')
def rep(mo):
    n, a, k = mo.groups()
    return (f'fn f{n}(args: [W; {a}], m: &mut M) -> R<[W; {k}]> {{ let c0 = m.cost; let r = f{n}_body(args, m); '
            f'unsafe {{ let c = m.cost - c0; CNT[{n}] += 1; if c > MAXC[{n}] {{ MAXC[{n}] = c; }} }} r }}\n'
            f'#[allow(unused_mut, unused_variables, unused_assignments, non_snake_case, unreachable_code)]\n'
            f'fn f{n}_body(args: [W; {a}], m: &mut M) -> R<[W; {k}]> {{')
s = pat.sub(rep, s)
groups = {g: [int(n) for n, nm in names.items() if nm == g] for g in ['jobStep', 'startDrain', 'insertAfter']}
s = s.replace('use crate::rt::*;', 'use crate::rt::*;\npub static mut CNT: [u64; 256] = [0; 256];\n'
              'pub static mut MAXC: [u64; 256] = [0; 256];\n'
              + ''.join(f'pub const G_{g.upper()}: &[usize] = &{v};\n' for g, v in groups.items()), 1)
open(p, 'w').write(s)
PY
