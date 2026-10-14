"""Mutation testing of the trace replay: does it catch bugs injected into the Lean model?

    python3 mutate_model.py LEAN_DIR TRACE_DIR [-j JOBS]

LEAN_DIR is a copy of lean/ (its .lake/packages may be a symlink to the original's, so that
Mathlib is not rebuilt); the mutants are applied there, one at a time, and reverted. Each
mutant is built and replayed against every trace in TRACE_DIR (write them with
`prototype/trace_campaign.py TRACE_DIR 3000 --fuzz 40`). A mutant is KILLED if some trace fails
to replay; every mutant below changes behaviour, so each should be killed.
"""
from __future__ import annotations

import glob
import os
import subprocess
import sys

MUTANTS = [
    ("M01 averaging rounds up", "OM/Model/Core.lean",
     "  return (a + b) / 2", "  return (a + b + 1) / 2"),
    ("M02 group split prefers the right sibling on ties", "OM/Model/Core.lean",
     "if Lg.size ≤ Rg.size then do", "if Lg.size < Rg.size then do"),
    ("M03 chunk split prefers the right sibling on ties", "OM/Model/Core.lean",
     "let left := (← getC X.l).size ≤ (← getC X.r).size",
     "let left := (← getC X.l).size < (← getC X.r).size"),
    ("M04 drain partition boundary strict", "OM/Model/Top.lean",
     "if acc + wt kids[i]! ≤ total / 2 then", "if acc + wt kids[i]! < total / 2 then"),
    ("M05 drain threshold off by one", "OM/Model/Top.lean",
     "V.weight + 2 > 2 * P.a ^ V.height", "V.weight + 2 > 2 * P.a ^ V.height + 1"),
    ("M06 one sweep step fewer", "OM/Model/Top.lean",
     "if k < (← getP).s then", "if k + 1 < (← getP).s then"),
    ("M07 rebuild trigger strict", "OM/Model/Wrapper.lean",
     "om.cur.count ≥ N / 2", "om.cur.count > N / 2"),
    ("M08 next capacity floor", "OM/Model/Wrapper.lean",
     "4 * max (om.live + mirrored) 16", "4 * max (om.live + mirrored) 17"),
    ("M09 FALLBACK group size", "OM/Model/Core.lean",
     "def fbGS (P : Params) : Nat := max 1 (P.G / 2)",
     "def fbGS (P : Params) : Nat := max 1 (P.G / 2 + 1)"),
    ("M10 PQ +1 move ignores bucket sharing", "OM/Model/PQ.lean",
     "let p := if alone then st.nbPrev.getX old else old", "let p := st.nbPrev.getX old"),
    ("M11 top averaging rounds up", "OM/Model/Top.lean",
     "return (lo1 + hi - 1) / 2", "return (lo1 + hi) / 2"),
    ("M12 table insert after lands before", "OM/Model/Top.lean",
     "(if before then i else i + 1)", "(if before then i else i)"),
    ("M13 rebuild copies dead elements", "OM/Model/Wrapper.lean",
     "  if e.live then\n    let (y, n')", "  if true then\n    let (y, n')"),
    ("M14 one reservation step fewer", "OM/Model/Core.lean",
     "  reservation P.K_R", "  reservation (P.K_R - 1)"),
    ("M15 chain labels off centre", "OM/Model/Top.lean",
     "let center := 1 <<< (P.beta - 1)", "let center := 1 <<< (P.beta - 2)"),
    ("M16 quiet siblings re-split in reverse order", "OM/Model/Core.lean",
     "quiet := quiet ++ [s]", "quiet := [s] ++ quiet"),
    ("M17 finished ghost stays in entries' table lists", "OM/Model/Top.lean",
     "if tabs.contains v then setInTables e (h - 1) (tabs.erase v)",
     "if tabs.contains v then setInTables e (h - 1) tabs"),
    ("M18 no FALLBACK after a failed background guard", "OM/Model/Core.lean",
     "onGuard (background y) fallback", "onGuard (background y) (pure ())"),
    ("M19 PQ pops the oldest chunk of a bucket", "OM/Model/PQ.lean",
     "  let c := st.pqHead.getX st.pqHi\n",
     "  let c := Id.run do\n    let mut c := st.pqHead.getX st.pqHi\n"
     "    for _ in [0:st.pqNext.size] do\n"
     "      if st.pqNext.getX c != NIL then c := st.pqNext.getX c\n    return c\n"),
    ("M20 drain-step range update swapped", "OM/Model/Top.lean",
     "else if left then modN v fun n => { n with first := cy.next }",
     "else if left then modN v fun n => { n with first := cy.prev }"),
]


def run(cmd, cwd, env=None):
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, env=env)


def main() -> int:
    args = sys.argv[1:]
    jobs = "16"
    if "-j" in args:
        i = args.index("-j")
        jobs = args[i + 1]
        del args[i:i + 2]
    lean_dir, trace_dir = os.path.abspath(args[0]), os.path.abspath(args[1])
    traces = sorted(glob.glob(os.path.join(trace_dir, "*.jsonl")))
    binary = os.path.join(lean_dir, ".lake/build/bin/replay")
    env = dict(os.environ, LEAN_ABORT_ON_PANIC="1")

    def replay_all() -> bool:
        p = subprocess.run(f"printf '%s\\n' {' '.join(traces)} | xargs -P {jobs} -n 8 {binary}",
                           shell=True, capture_output=True, text=True, env=env)
        return p.returncode == 0

    if run(["lake", "build", "replay"], lean_dir).returncode != 0 or not replay_all():
        print("the unmutated model does not build or does not replay")
        return 2
    survived = 0
    for name, rel, old, new in MUTANTS:
        path = os.path.join(lean_dir, rel)
        src = open(path).read()
        if src.count(old) != 1:
            print(f"{name}: pattern found {src.count(old)} times, skipped")
            survived += 1
            continue
        open(path, "w").write(src.replace(old, new))
        try:
            b = run(["lake", "build", "replay"], lean_dir)
            if b.returncode != 0:
                verdict = "NOBUILD"
            else:
                verdict = "SURVIVED" if replay_all() else "KILLED"
        finally:
            open(path, "w").write(src)
        survived += verdict != "KILLED"
        print(f"{verdict:9} {name}", flush=True)
    run(["lake", "build", "replay"], lean_dir)
    print(f"{len(MUTANTS) - survived}/{len(MUTANTS)} mutants killed")
    return 1 if survived else 0


if __name__ == "__main__":
    sys.exit(main())
