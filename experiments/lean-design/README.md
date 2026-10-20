# Experiment: the verified algorithm, implemented natively (2026-10-20, not verified)

`src/lean.rs` implements the algorithm of the verified machine program directly in Rust, like the
two baselines, instead of extracting it from Lean. Its purpose is to separate the cost of the
algorithm from the cost of the extracted program's representation and runtime.

**`Native<Wide>` makes the same decisions as the verified program.** It has:
- the same core (elements → groups → chunks, reservation process, top structure with ghost drains);
- the same wrapper (deletion by tombstones, growth by incremental global rebuilding, handles with
  one slot per core parity);
- the same parameters (`Params::verified` is `proofParams N` of `lean/OM/Impl/Params.lean`:
  K_R = 8, a = 8, s = 11, β = 64, T = 3L², H = L/3 + 1);
- the proof's label widths (group labels up to about 1,000 bits, as 16-word integers).

What differs is only the representation:
- records instead of an array per field;
- fixed-width words: 128-bit element labels, `Wide` group labels, tags of H 64-bit fields;
- top tables as inline arrays;
- its own memory handling (below);
- no FALLBACK: a failed guard panics. It never failed.

## Same decisions as the verified algorithm: trace equivalence (`results/traces/`)

`prototype/trace.py --preset verified` writes traces with the verified program's parameters. A
trace records every operation, the handle and key of each inserted element, the answer of an order
query after each update, the counters, and digests of all keys of both cores.

Two programs replay every trace, and both must reproduce all of these exactly:
- **the Lean model** (`lake exe replay`); the verified machine program refines it by proof;
- **`Native<Wide>`** (`cargo run --release --bin trace`).

| traces | operations | Lean model | native |
|---|---|---|---|
| all 23 prototype workloads × 2·10⁵ operations | 4.6·10⁶ | 23/23 exact | 23/23 exact |
| random, hammer, churn, delete_burst, yoyo × 2·10⁶ | 10⁶ × 10 | 5/5 exact | 5/5 exact |

The workloads include deletion-heavy ones: churn alone performs 804 rebuilds at 2·10⁶. `harmonic`
is run only at 2·10⁵, because the workload rescans all elements whenever its anchors run out, which
takes hours at 2·10⁶. The replay outputs are `results/traces/{native,lean}.txt` (the native list
also has an early 2·10⁴ trace); `results/traces/run.sh` reproduces them.

`check` is a second, independent check, run on the fixed-capacity configuration: it compares with
the list after every operation and runs a full structural check at checkpoints.

## Results (`results/`, `summarize.py`)

The method is that of `rust/results/compare`: per-operation minimum over three in-process runs, on
performance cores. Memory is mapped lazily, so page faults are included, as for every row there.
Times are mean / p99.99 / slowest. The configurations:

* **native**: the verified algorithm, as above;
* **AVL**: the textbook balanced tree (`rust/src/avl.rs`), O(log n) worst case; *mapped before the
  run* = its arrays touched in advance;
* **amortized**: Bender et al.'s algorithm (`rust/src/baseline.rs`);
* **ablation** rows (not the algorithm; they show where the time goes):
  * *one core, no rebuilding*: a single core of capacity 2N + 4, with the verified parameters and
    label widths, without the wrapper;
  * *K_R = 1*: the parameter profile of `../worst-case`;
  * *128-bit labels*: group labels of 128 bits, narrower than the proof's.

Insertions, 10⁶–10⁷ elements:

| configuration | random | hammer | append | front |
|---|---|---|---|---|
| native (the verified algorithm) | 850 ns / 3.2 µs / 10.1 µs | 81 ns / 2.2 µs / 6.4 µs | 82 ns / 2.0 µs / 5.5 µs | 79 ns / 2.2 µs / 6.2 µs |
| AVL tree | 561 ns / 3.9 µs / 5.8 µs | 33 ns / 2.6 µs / 3.6 µs | 31 ns / 2.7 µs / 3.9 µs | 61 ns / 2.7 µs / 3.7 µs |
| AVL tree, arrays mapped before the run | 554 ns / 2.0 µs / 3.0 µs | 30 ns / 90 ns / 1.1 µs | 28 ns / 91 ns / 1.1 µs | 59 ns / 126 ns / 1.2 µs |
| amortized (Bender et al.) | 488 ns / 8.9 µs / 11.8 µs | 24 ns / 2.7 µs / 564.4 µs | 24 ns / 2.7 µs / 554.7 µs | 24 ns / 2.7 µs / 573.2 µs |
| ablation: one core, no rebuilding | 583 ns / 2.2 µs / 4.4 µs | 42 ns / 1.2 µs / 2.2 µs | 43 ns / 1.3 µs / 2.5 µs | 42 ns / 1.3 µs / 2.0 µs |
| ablation: native, profile K_R = 1 | 837 ns / 2.8 µs / 8.0 µs | 79 ns / 1.6 µs / 5.8 µs | 80 ns / 1.6 µs / 5.5 µs | 79 ns / 1.6 µs / 5.7 µs |
| ablation: native, K_R = 1, 128-bit group labels | 778 ns / 2.6 µs / 7.8 µs | 71 ns / 1.3 µs / 5.4 µs | 72 ns / 1.2 µs / 5.2 µs | 70 ns / 1.3 µs / 5.7 µs |
| ablation: one core, K_R = 1, 128-bit labels | 526 ns / 1.7 µs / 2.6 µs | 37 ns / 1.0 µs / 1.5 µs | 38 ns / 1.0 µs / 1.6 µs | 37 ns / 1.0 µs / 1.4 µs |

Insertions, 10⁷–10⁸ elements:

| configuration | random | hammer |
|---|---|---|
| native (the verified algorithm) | 1.1 µs / 4.1 µs / 12.7 µs | 86 ns / 2.6 µs / 7.6 µs |
| AVL tree | 926 ns / 4.2 µs / 6.6 µs | 33 ns / 2.6 µs / 3.8 µs |
| AVL tree, arrays mapped before the run | 927 ns / 3.0 µs / 5.0 µs | 30 ns / 92 ns / 2.7 µs |
| amortized (Bender et al.) | 697 ns / 10.8 µs / 14.0 µs | 23 ns / 2.5 µs / 5.2 ms |
| ablation: one core, no rebuilding | 757 ns / 2.9 µs / 5.7 µs | 39 ns / 1.2 µs / 2.4 µs |

Warm order queries (one on a random pair after each insertion), 10⁶–10⁷ elements:

| configuration | random | hammer |
|---|---|---|
| native (the verified algorithm) | 494 ns / 664 ns / 808 ns | 504 ns / 720 ns / 1.0 µs |
| AVL tree | 522 ns / 1.2 µs / 1.7 µs | 323 ns / 807 ns / 1.1 µs |
| amortized (Bender et al.) | 196 ns / 368 ns / 447 ns | 157 ns / 298 ns / 524 ns |

Cold caches (`src/bin/cold.rs`, a copy of `rust/src/bin/cold.rs`: 128 MB evicted before each measured
operation; the baselines' rows are `rust/results/cold`, same machine and day). Slowest insertion in
the decades up to 10⁶ / 10⁷ / 10⁸, without page faults and, in parentheses, with them; cold query
mean / slowest at 10⁷–10⁸:

| configuration, workload | slowest insertion | cold query |
|---|---|---|
| native, random | 11.2 µs (13.0) / 9.7 µs (12.3) / 8.9 µs (10.1) | 876 ns / 1.2 µs |
| native, hammer | 10.7 µs (15.3) / 11.3 µs (14.2) / 11.4 µs (14.6) | 1.8 µs / 2.3 µs |
| AVL tree, random | 5.4 µs (10.7) / 6.3 µs (6.3) / 5.8 µs (5.8) | 5.5 µs / 9.0 µs |
| AVL tree, hammer | 3.3 µs (4.9) / 4.4 µs (4.5) / 5.3 µs (5.3) | 4.4 µs / 6.7 µs |
| amortized, random | 11.8 µs (18.0) / 15.6 µs (18.4) / 22.3 µs (27.0) | 492 ns / 778 ns |
| amortized, hammer | 48.5 µs / 545.4 µs / 5.0 ms | 786 ns / 1.1 µs |

## What the results say

* **Native vs AVL.** The verified algorithm, implemented natively, is within a small constant factor
  of the balanced tree:
  * mean: 1.2× (random insertion at 10⁸) to 2.6× (clustered insertion);
  * p99.99: about equal (better than the tree as measured, worse than the tree with pre-mapped
    arrays);
  * slowest insertion: 1.4–2× the tree's warm, 1.5–3× cold.
  * Cold order queries are 2.4–6× faster than the tree's: a query is a constant number of accesses,
    while the tree's grows with depth.
* **Native vs the verified program.** The extracted verified program's slowest insertion at 10⁷ is
  0.31 ms, against 6–10 µs here; its mean is 4.5 µs, against 0.85 µs. The gap is the extracted
  program's representation and runtime (words of unbounded size, an array per field, step counting),
  not the algorithm.
* **Where the time goes (ablation).**
  * The parameter profile and the label width together change the native mean by at most 12%
    (and the slowest insertion by about 20%).
  * Global rebuilding is the main cost: the single core alone is 1.5–2× faster on the mean, with a
    2–3× lower slowest insertion. While a rebuild runs, an operation performs up to six core
    insertions: its own, the mirror into the new core, and four copy steps.
  * The single core is not the algorithm. It works only for a capacity fixed in advance, and its own
    theorem is not proved.

## Memory handling (trusted, like the verified program's runtime)

The slowest operations are decided by memory management as much as by the algorithm. Each of the
following was found by measuring single slow operations:

* **One mapping per core array, never touched before use.** Every operation first performs at most
  one memory action, round robin among those with something to do:
  * map a page ahead in the current core, the next core or the handle array;
  * prepare the spare mapping for the next core: one array mapped per action (one 1-TB-scale
    `mmap` costs 5–6 µs), then 16 pages mapped ahead per array.

  So page faults and system calls fall on ordinary operations, not on the heavy ones (drain starts,
  chunk-split starts, rebuild starts). A fresh page whose page tables are not yet allocated costs
  3–5 µs (13 µs seen) on this machine (Linux 7.0).
* **Retired cores are kept, not given back to the system.** A retired core's mapping becomes the
  spare of a later core when it fits (no system call; its queue arrays are cleared with
  `MADV_DONTNEED`).
  * Giving pages back cost up to 34 µs in single operations (`munmap`, `MADV_DONTNEED`).
  * The verified program's runtime also keeps retired blocks in its own pool.
  * Memory stays O(largest size reached): while growing, the retired cores' sizes form a geometric
    sum.
* The remaining slowest operations do algorithmic work in the new core during a rebuild. These are
  its first chunk splits and drain starts, with K_R = 8 job steps in each of up to six core
  insertions.
* Random kernel stalls of about 290 µs on single page faults, about 1 per 3,000 faults (also seen in
  a 20-line test program), are removed by the minimum over three runs.

The first version of this experiment measured only the fixed-capacity variant (one core, no
rebuilding, insertion only, K_R = 1, 128-bit labels) and summarized it as "the design beats AVL".
That was wrong as a statement about the algorithm. That variant is the last ablation row above.

## Files

* `src/lean.rs`: `Core<GL>` (one core), `Native<GL>` (the full structure), `Params::verified` and
  `Params::profile`, `Wide`.
* `src/avl.rs`: a copy of `rust/src/avl.rs`, with arrays optionally mapped before use.
* `src/bin/compare.rs`, `src/bin/cold.rs`: copies of the harnesses of `rust/src/bin`, with the
  configurations above.
* `src/bin/trace.rs`: the trace replay. `src/bin/check.rs`: the differential check of the
  fixed-capacity configuration.
* `src/bin/faults.rs`, `src/bin/spikes.rs`: diagnostics (which operations take page faults; the
  slowest operations of `Native` and what happened in them).
* `results/run.sh`, `run_1e8.sh`, `run_queries.sh`, `cold/run.sh`, `traces/run.sh`: reproduce
  `results/`.
* `results/summarize.py`: prints the tables above.
