"""Mutation testing: does the test battery catch deliberately injected bugs?

Each mutant is one textual edit to one algorithm file. The prototype is copied
to a temporary directory, the edit applied, and battery.py run there.
"Killed" = battery fails (assertion, crash, fallbacks, headroom, timeout).
Controls are edits that should *survive*: removing a guard that a correct
algorithm never trips.

    python3 mutate.py [-j jobs]
"""
from __future__ import annotations

import concurrent.futures as cf
import os
import shutil
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
FILES = ["core.py", "pq.py", "top_wbbt.py", "top_simple.py", "wrapper.py", "guards.py",
         "spec.py", "stress.py", "test_om.py", "top_stress.py", "battery.py", "fuzz.py"]

# (id, file, old, new, description, expected) ; expected = "kill" or "survive"
MUTANTS = [
    ("M01", "core.py", "        if a + 1 >= b:\n            raise GuardFailure(why)\n        st = self.stats",
     "        if a >= b:\n            raise GuardFailure(why)\n        st = self.stats",
     "label averaging allows equal labels", "kill"),
    ("M02", "core.py", "        if v >= (1 << B) or v <= a:\n            raise GuardFailure(why)",
     "        if v <= a:\n            raise GuardFailure(why)",
     "push-label guard removed (labels may exceed B bits)", "kill"),
    ("M03", "core.py", "            if L_.next != g:\n                raise GuardFailure(\"group split: left sibling not adjacent\")\n            e = G.first",
     "            if L_.next != g:\n                raise GuardFailure(\"group split: left sibling not adjacent\")\n            e = G.last",
     "group split moves the wrong element left", "kill"),
    ("M04", "core.py", "        X.size -= s            # x is SPLITTING",
     "        X.size -= 0            # x is SPLITTING",
     "chunk split forgets to decrease the source size", "kill"),
    ("M05", "core.py", "        if G.last == x:\n            G.last = y\n        G.size += 1",
     "        G.size += 1",
     "insert after a group's last element does not extend the group", "kill"),
    ("M06", "pq.py", "                p = old if len(b) > 1 else self.nb_prev[old]",
     "                p = self.nb_prev[old]",
     "PQ increment links the bucket in the wrong place", "kill"),
    ("M07", "pq.py", "        s = self.hi\n        c = next(iter(self.bucket[s]))",
     "        s = self.lo\n        c = next(iter(self.bucket[s]))",
     "reservation serves the emptiest instead of the fullest chunk", "kill"),
    ("M08", "core.py", "        elif G.st == OVERFLOW:\n            s = G.src\n        else:\n            return\n        for _ in range(self.P.K_G):",
     "        else:\n            return\n        for _ in range(self.P.K_G):",
     "inserts into overflow groups no longer drive the source's split", "kill"),
    ("M09", "wrapper.py", "        if self.nxt is not None and self.cursor_set and (hx is None or hx in self.nxt_idx):",
     "        if self.nxt is not None and self.cursor_set and (hx is None or hx not in self.nxt_idx):",
     "rebuild mirrors inserts after the wrong elements", "kill"),
    ("M10", "wrapper.py", "            if self.cur.count >= N // 2 or (N > N_MIN and self.live < N // 8):",
     "            if self.cur.count >= N or (N > N_MIN and self.live < N // 8):",
     "growth rebuild triggers too late", "kill"),
    ("M11", "top_wbbt.py", "            t, left = V.t1, True",
     "            t, left = V.t2, True",
     "top drain sends LEFT chunks to the right target", "kill"),
    ("M12", "top_wbbt.py", "        if h > 1:\n            while 0 < k < len(kids) and self._same_drain(kids[k - 1], kids[k]):\n                k += 1",
     "        if h > 1:\n            while False:\n                k += 1",
     "top drain partition may separate an active drain's targets", "kill"),
    ("M13", "top_wbbt.py", "        for T in V.in_tables:\n            Tn = self.nodes[T]\n            Tn.order.remove(v)\n            del Tn.lab[v]\n            Tn.side.pop(v, None)\n",
     "",
     "finished drain stays in its parents' tables", "kill"),
    ("M14", "top_wbbt.py", "                for _ in range(self.s):",
     "                for _ in range(1):",
     "top drains get 1 sweep step per insertion instead of s", "kill"),
    ("M15", "top_wbbt.py", "            if V.last == x:\n                V.last = z\n            yield",
     "            yield",
     "top job forgets to extend ranges to the right", "kill"),
    ("M16", "top_wbbt.py", "        ty = self.core.C[x].tag - f1x + ly[px[1]]",
     "        ty = self.core.C[x].tag - f1x + lz[px[1]]",
     "new left chunk gets the right chunk's label", "kill"),
    ("M17", "top_wbbt.py", "        if T.draining:\n            T.side[new] = T.side[e]",
     "        if False:\n            T.side[new] = T.side[e]",
     "entries added to a draining table get no side", "kill"),
    ("M18", "top_wbbt.py", "            V.weight += 2",
     "            V.weight += 1",
     "top weights undercount insertions", "kill"),
    ("M19", "core.py", "        if C.st == QUIET:\n            self.pq.adjust(c, old, C.size)",
     "        if C.st == QUIET and d > 0:\n            self.pq.adjust(c, old, C.size)",
     "PQ not told about chunk shrinkage", "kill"),
    ("M20", "core.py", "            if self.Gs[s].size >= self.P.G:\n                self._start_group_split(s)",
     "            pass",
     "EQUIVALENT: newly quiet oversized groups start splitting on their next insert anyway", "survive"),
    # controls: guards a correct algorithm never trips
    ("C01", "top_wbbt.py", "        tag = self.core.C[y].tag - old + new\n        self._guard_tag(y, tag)",
     "        tag = self.core.C[y].tag - old + new",
     "CONTROL: drain-step tag guard removed", "survive"),
    ("C02", "core.py", "            if L_.next != g:\n                raise GuardFailure(\"group split: left sibling not adjacent\")\n",
     "",
     "CONTROL: group-split adjacency guard removed", "survive"),
    ("C03", "core.py", "            if Y.next != x:\n                raise GuardFailure(\"chunk split: left sibling not adjacent\")\n",
     "",
     "CONTROL: chunk-split adjacency guard removed", "survive"),
]


def run_mutant(m, timeout: int = 900) -> tuple:
    mid, fname, old, new, desc, expected = m
    d = tempfile.mkdtemp(prefix=f"mut_{mid}_")
    try:
        for f in FILES:
            shutil.copy(os.path.join(HERE, f), d)
        if mid != "ORIG":
            path = os.path.join(d, fname)
            src = open(path).read()
            if src.count(old) != 1:
                return (mid, desc, expected, "BAD-PATTERN", 0.0, "")
            open(path, "w").write(src.replace(old, new))
        t0 = time.time()
        try:
            p = subprocess.run([sys.executable, os.path.join(d, "battery.py")], cwd=d,
                               capture_output=True, text=True, timeout=timeout,
                               env={**os.environ, "PYTHONPATH": d})
            killed = p.returncode != 0
            out = (p.stdout + p.stderr).strip().splitlines()
            why = out[-1][:110] if out else ""
        except subprocess.TimeoutExpired:
            killed, why = True, "timeout"
        return (mid, desc, expected, "killed" if killed else "survived", time.time() - t0, why)
    finally:
        shutil.rmtree(d, ignore_errors=True)


def main() -> None:
    jobs = int(sys.argv[sys.argv.index("-j") + 1]) if "-j" in sys.argv else 4
    only = [a for a in sys.argv[1:] if a[0] in "MC" and a[1:].isdigit()]
    todo = [("ORIG", "", "", "", "unmodified prototype", "survive")] + \
        [m for m in MUTANTS if not only or m[0] in only]
    with cf.ProcessPoolExecutor(jobs) as ex:
        results = list(ex.map(run_mutant, todo))
    ok = True
    for mid, desc, expected, outcome, secs, why in results:
        good = (outcome == "killed") == (expected == "kill")
        ok &= good
        print(f"{'ok ' if good else 'BAD'} {mid} {outcome:9s} {secs:6.1f}s  {desc}" + (f"  [{why}]" if outcome == "killed" else ""))
    print("ALL AS EXPECTED" if ok else "SOME MUTANTS DID NOT BEHAVE AS EXPECTED")


if __name__ == "__main__":
    main()
