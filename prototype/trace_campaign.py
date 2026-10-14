"""Write traces of every stress workload under every preset, for the Lean replay test.

    python3 trace_campaign.py OUTDIR [N] [-j JOBS] [--fuzz TRIALS] [--replay BIN [--keep]]

Presets `default` and `proof` run N operations (default 20000); `tiny`, `tinytop` and `beta3`,
which force FALLBACK constantly, run N/4. `--fuzz` adds TRIALS fuzz.py-style traces (random small
parameters, 200-1500 operations) and TRIALS/10 long ones (5k-30k operations).
Then: `lake exe replay OUTDIR/*.jsonl` in lean/. With `--replay BIN` (the built
`lean/.lake/build/bin/replay`), each trace is replayed as soon as it is written, with panics
aborting, and deleted if it replays exactly (unless `--keep`).
"""
from __future__ import annotations

import concurrent.futures as cf
import os
import subprocess
import sys

import stress
import trace


REPLAY = None
KEEP = False


def job(args):
    out, wl, n, preset = args
    try:
        if preset == "fuzz":
            r = trace.export_fuzz(out, n, long=wl == "long")
        else:
            r = trace.export(out, wl, n, preset)
    except Exception as ex:          # a prototype crash is a finding too
        return out, None, f"{type(ex).__name__}: {ex}"
    if REPLAY:
        p = subprocess.run([REPLAY, out], capture_output=True, text=True,
                           env=dict(os.environ, LEAN_ABORT_ON_PANIC="1"))
        line = (p.stdout.strip().splitlines() or ["(no output)"])[0]
        if p.returncode != 0:
            return out, r, f"REPLAY {line} {p.stderr.strip()[:300]}"
        r["replay"] = line.split(": ", 1)[-1]
        if not KEEP:
            os.remove(out)
    return out, r, None


def _init(replay, keep):
    global REPLAY, KEEP
    REPLAY, KEEP = replay, keep


def main() -> None:
    args = sys.argv[1:]
    jobs = os.cpu_count() or 4
    if "-j" in args:
        i = args.index("-j")
        jobs = int(args[i + 1])
        del args[i:i + 2]
    fz = 0
    if "--fuzz" in args:
        i = args.index("--fuzz")
        fz = int(args[i + 1])
        del args[i:i + 2]
    replay = None
    if "--replay" in args:
        i = args.index("--replay")
        replay = os.path.abspath(args[i + 1])
        del args[i:i + 2]
    keep = "--keep" in args
    if keep:
        args.remove("--keep")
    outdir = args[0]
    n = int(args[1]) if len(args) > 1 else 20000
    os.makedirs(outdir, exist_ok=True)
    tasks = []
    for preset, k in (("default", n), ("proof", n), ("tiny", n // 4), ("tinytop", n // 4),
                      ("beta3", n // 4)):
        for wl in stress.WORKLOADS:
            tasks.append((os.path.join(outdir, f"{wl}.{preset}.jsonl"), wl, k, preset))
    for seed in range(fz):
        tasks.append((os.path.join(outdir, f"fuzz{seed}.jsonl"), "short", seed, "fuzz"))
    for seed in range(fz // 10):
        tasks.append((os.path.join(outdir, f"fuzzlong{seed}.jsonl"), "long", 100000 + seed, "fuzz"))
    bad = 0
    with cf.ProcessPoolExecutor(jobs, initializer=_init, initargs=(replay, keep)) as ex:
        for out, r, err in ex.map(job, tasks):
            print(out, r if err is None else "ERROR " + err, flush=True)
            bad += err is not None
    print(f"{len(tasks) - bad}/{len(tasks)} traces written")


if __name__ == "__main__":
    main()
