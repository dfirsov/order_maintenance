"""Export operation traces for the Lean model's replay test (lean/OM/Test/Replay.lean).

    python3 trace.py OUT.jsonl WORKLOAD N [--preset default|proof|tiny|tinytop|beta3] [--seed S] [--K_B K]

Runs a stress workload (stress.WORKLOADS) on the full structure and writes one JSON value
per line:

* a header: the workload, K_B, and the parameters of every core created during the run;
* one record per operation, with what the prototype answered and checkpoints of its state:
    ["i", x, h, key, counters, digests]   insert after handle x (-1: insert_first), got handle h
    ["d", x, counters, digests]           delete handle x
    ["o", x, y, answer]                   order query (one random query after each update)
    ["f", digests]                        final state
  `key` is (tag, group label, element label) of the new element in cur; `counters` is
  [fallbacks of cur, fallbacks of nxt (-1: none), rebuilds]; `digests` is null (not taken)
  or [digest of cur, digest of nxt (-1: no nxt or not yet copying)]. Digests are taken after
  each of the first 2000 updates, then every 500 updates, and every 5000 from 20000 on.

A digest hashes the keys of all elements of a core in list order. The Lean model must
reproduce every answer, key, counter and digest exactly.
"""
from __future__ import annotations

import json
import random
import sys

import stress
from core import Params
from wrapper import OrderMaintenance

MOD = (1 << 61) - 1


def digest(core) -> int:
    h = 0
    for e in core.elements():
        for v in core.key(e):
            h = (h * 1000003 + v) % MOD
    return h


def tiny(N: int) -> Params:
    """Element and group labels far too narrow: guards fail constantly (FALLBACK)."""
    P = Params.for_capacity(N, top="wbbt")
    P.B_e, P.B_g, P.D_e, P.D_g = 7, 6, 4, 4
    return P


def tinytop(N: int) -> Params:
    """Top labels far too narrow: top-table and tag guards fail (FALLBACK)."""
    P = Params.for_capacity(N, top="wbbt")
    P.top_beta = 6
    return P


def beta3(N: int) -> Params:
    """Top labels of 3 bits: FALLBACK's tree gives unsorted tags and is renumbered."""
    P = Params.for_capacity(N, top="wbbt")
    P.top_beta = 3
    return P


PRESETS = {
    "default": lambda N: Params.for_capacity(N, top="wbbt"),
    "proof": Params.proof,
    "tiny": tiny,
    "tinytop": tinytop,
    "beta3": beta3,
}


class Recorder(OrderMaintenance):
    def __init__(self, *, K_B: int, params, qseed: int) -> None:
        super().__init__(K_B=K_B, params=params)
        self.log: list = []
        self.qrng = random.Random(qseed)
        self.handles: list[int] = []      # live handles, for random queries
        self.pos: dict[int, int] = {}
        self.ops = 0

    def _counters(self) -> list[int]:
        return [self.cur.stats.fallbacks,
                self.nxt.stats.fallbacks if self.nxt is not None else -1,
                self.rebuilds]

    def _digests(self, force: bool = False):
        if not force and self.ops >= 2000 and self.ops % (500 if self.ops < 20000 else 5000):
            return None
        d2 = digest(self.nxt) if self.nxt is not None and self.cursor_set else -1
        return [digest(self.cur), d2]

    def _query(self) -> None:
        if len(self.handles) < 2:
            return
        x, y = self.qrng.choice(self.handles), self.qrng.choice(self.handles)
        self.log.append(["o", x, y, super().order(x, y)])

    def _ins(self, x: int | None) -> int:
        h = super().insert_first() if x is None else super().insert_after(x)
        self.pos[h] = len(self.handles)
        self.handles.append(h)
        self.log.append(["i", -1 if x is None else x, h, list(self.cur.key(self.cur_idx[h])),
                         self._counters(), self._digests()])
        self.ops += 1
        self._query()
        return h

    def insert_first(self) -> int:
        return self._ins(None)

    def insert_after(self, x: int) -> int:
        return self._ins(x)

    def delete(self, x: int) -> None:
        super().delete(x)
        i = self.pos.pop(x)
        last = self.handles.pop()
        if last != x:
            self.handles[i] = last
            self.pos[last] = i
        self.log.append(["d", x, self._counters(), self._digests()])
        self.ops += 1
        self._query()


def params_record(core) -> dict:
    P, top = core.P, core.top
    d = {k: getattr(P, k) for k in ("N", "L", "G", "T", "theta", "B_e", "B_g", "D_e", "D_g",
                                    "K_G", "K_C", "K_R")}
    d.update(a=top.a, s=top.s, beta=top.beta, H=top.H)
    return d


def export(path: str, workload: str, n: int, preset: str = "default", seed: int = 1,
           K_B: int = 4) -> dict:
    om = Recorder(K_B=K_B, params=PRESETS[preset], qseed=seed + 1000)
    rng = random.Random(seed)
    wl = stress.WORKLOADS[workload]()
    live: list[int] = []
    for i in range(n):
        wl(rng, om, live, i)
    om.log.append(["f", om._digests(force=True)])
    params = {}
    for c in om.cores():
        params[c.P.N] = params_record(c)
    header = {"workload": workload, "n": n, "preset": preset, "seed": seed, "K_B": K_B,
              "params": sorted(params.values(), key=lambda d: d["N"])}
    with open(path, "w") as f:
        f.write(json.dumps(header) + "\n")
        for rec in om.log:
            f.write(json.dumps(rec, separators=(",", ":")) + "\n")
    st = [c.stats for c in om.cores()]
    return {"records": len(om.log), "fallbacks": sum(s.fallbacks for s in st),
            "rebuilds": om.rebuilds}


def export_fuzz(path: str, seed: int, long: bool = False) -> dict:
    """A fuzz.py trial (random small parameters, WBBT top, random operation mix) as a trace."""
    import fuzz
    rng = random.Random(seed)
    make, desc = fuzz.random_params(rng, "wbbt")
    ops = rng.randint(5000, 30000) if long else rng.randint(200, 1500)
    p_first = rng.choice([0.0, 0.02, 0.2])
    p_del = rng.choice([0.0, 0.05, 0.2, 0.45])
    p_ins = rng.uniform(0.3, 0.95 - p_del)
    mode = rng.choice(["uniform", "hammer", "sequential", "mixed"])
    K_B = rng.choice([2, 2, 3, 4, 6])
    sched = rng.choice(["steady", "steady", "wipe", "bursts"])
    period = rng.choice([50, 200, 600])
    om = Recorder(K_B=K_B, params=make, qseed=seed + 1000)
    live: list[int] = []
    for i in range(ops):
        if sched == "wipe":
            p_ins, p_first, p_del = (0.9, 0.05, 0.0) if (i // period) % 2 == 0 else (0.0, 0.0, 0.95)
        elif sched == "bursts":
            p_ins, p_first, p_del = ((0.6, 0.3, 0.0) if (i // period) % 3 == 0 else
                                     (0.1, 0.0, 0.8) if (i // period) % 3 == 1 else (0.45, 0.05, 0.4))
        r = rng.random()
        if not live or r < p_first:
            live.append(om.insert_first())
        elif r < p_first + p_ins:
            x = (live[0] if mode == "hammer" else live[-1] if mode == "sequential" else
                 (live[0] if rng.random() < 0.3 else live[-1] if rng.random() < 0.5
                  else rng.choice(live)) if mode == "mixed" else rng.choice(live))
            live.append(om.insert_after(x))
        elif r < p_first + p_ins + p_del:
            j = rng.randrange(len(live))
            live[j], live[-1] = live[-1], live[j]
            om.delete(live.pop())
    om.log.append(["f", om._digests(force=True)])
    params = {c.P.N: params_record(c) for c in om.cores()}
    header = {"workload": f"fuzz{seed}", "n": ops, "preset": "fuzz", "seed": seed, "K_B": K_B,
              "desc": desc, "params": sorted(params.values(), key=lambda d: d["N"])}
    with open(path, "w") as f:
        f.write(json.dumps(header) + "\n")
        for rec in om.log:
            f.write(json.dumps(rec, separators=(",", ":")) + "\n")
    return {"records": len(om.log), "fallbacks": sum(c.stats.fallbacks for c in om.cores()),
            "rebuilds": om.rebuilds}


def main() -> None:
    args = sys.argv[1:]
    opts = {"--preset": "default", "--seed": "1", "--K_B": "4"}
    pos = []
    while args:
        a = args.pop(0)
        if a in opts:
            opts[a] = args.pop(0)
        else:
            pos.append(a)
    out, workload, n = pos[0], pos[1], int(pos[2])
    r = export(out, workload, n, opts["--preset"], int(opts["--seed"]), int(opts["--K_B"]))
    print(out, r)


if __name__ == "__main__":
    main()
