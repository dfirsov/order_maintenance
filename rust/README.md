# Rust code generated from the verified machine program

`src/gen.rs` is printed from the machine programs of `lean/OM/Impl` (`initWS`, `insertWS`,
`deleteWS`, `orderWS`) by the printer `lean/OM/Extract/Rust.lean`, statement for statement:

```
cd lean && lake exe extract      # writes ../rust/src/gen.rs
```

The printer is trusted (not verified). `src/rt.rs` is the runtime: words of arbitrary precision,
arrays with capacities (an access beyond the capacity panics, as a machine error), and the
operators with the semantics of `lean/OM/Machine/Exec.lean`. The generated code counts the
machine's steps (`m.cost`) and the bit length of the largest value computed (`m.peak`).

`src/lib.rs` is the interface: `Om::new(kb)`, `insert_first`, `insert_after(x)`, `delete(x)`,
`order(x, y)`. Handles are the insertion counter.

```
cargo run --release --bin check -- 200000 7 grow    # ops, seed, mode (grow | mix | churn)
```

`check` runs random operation sequences against a plain list implementation of the
specification and reports the steps per operation, the peak bit length, and the memory.

```
cargo run --release --bin replay -- TRACE.jsonl...       # prototype traces (prototype/trace.py)
cargo run --release --bin growth -- 4000000 50000 1      # results/growth.csv; plot: results/plot_growth.py
cargo run --release --bin usage                          # memory in use against the capacities
cargo run --release --bin compare -- om hammer 10000000  # per-operation time (also: bender; random|append|front)
results/compare/run.sh && python3 results/compare/summarize.py   # the comparison below
cargo run --release --bin maxop -- 10000000              # the operations with the most steps
cargo run --release --bin spikes -- 10000000             # the slowest operations in time
```

`src/baseline.rs` is the amortized algorithm of Bender et al. (ESA 2002) used for comparison. It is
not verified; a unit test checks it against a plain list (`cargo test`).

**Cross-check with the machine semantics.** `lake exe xrun OPS` (in `lean/`) runs the operations
with the machine's own semantics `OM.Machine.exec`; `xrun OPS` (here) runs the generated code.
Both print, per operation, the status, the exact number of steps, the answer and the peak bit
length, so their outputs must be identical:

```
python3 scripts/gen_ops.py 4000 7 mix > ops.txt
(cd ../lean && lake exe xrun ../rust/ops.txt) > lean.out
cargo run --release --bin xrun -- ops.txt > rust.out && diff lean.out rust.out
```

## Results (2026-10-16)

**Faithfulness of the printer and the runtime.** On 9 operation files (20 to 4,000 operations,
mixed and delete-heavy, through many rebuilds; 4.3 million machine steps in the two longest alone),
the generated code and Lean's `exec` printed identical lines: the same answers, the same number of steps for every
operation, the same peak bit length.
Re-run on 2026-10-22, after the queue's unused counter `pqScan` was removed (one scalar array
fewer per core): 9 files, 13,920 operations, 7.7 million steps, identical. Compared with the code
before the removal, answers and peaks are the same, initialization takes 2,099 steps instead of
2,101, and the operations that allocate a new core take 2 steps fewer; all other step counts are
unchanged.

**Correctness.** The generated code returned the specification's answers on every operation
tried:
* 620,000 random operations (`check`, modes grow, mix and churn);
* the 23 stress workloads of the prototype, 200,000 updates each with an order query after each
  (`trace.py --preset proof`; 9.2 million records; `results/replay_workloads.txt`);
* 1,100 fuzz traces (random operation mixes with wipes, bursts and hammering; 4.5 million records;
  `K_B` raised to 4 where the trace used 2 or 3; the answers do not depend on `K_B`).

The prototype's `proof` preset predates M5's parameters, so only the answers the specification
determines are compared (handles and order answers), not the prototype's internal keys.

**Steps.** On the prototype's workloads (200,000 elements), the largest number of machine steps for
one update was 200,469 (workload `harmonic_half`); growing to 10⁷ elements it was 250,929. The proved
bound is `opB 4 = 1,133,561,742`, about 4,500 times more. An order query always took 65 steps.

The largest step count grows slowly with the size, by about 60,000 steps per decade (127,759 at 10⁵
elements, 190,189 at 10⁶, 250,929 at 10⁷, 314,088 at 5·10⁷; `maxop`, `compare`); it does not flatten
in the range we can run. Profiling the generated code (inclusive steps
per procedure) shows why: the most expensive operations run during a rebuild (the operation's own
insertion and `K_B` copy insertions into the next core), and 95% of their steps are drain starts in
the top structure (`startDrain`, mostly its list searches), two at 10⁵, three at 10⁶, four at 10⁷.
The top tree gains about one level per decade (branching parameter 8), and a job's walk can start a
drain at each level it passes. `scripts/profile/instrument.sh` builds a profiling copy whose
`pieces` reports the pieces of the slowest operations (`results/pieces_random.csv`,
`results/pieces_hammer.csv`, to 5·10⁷ elements; plot: `results/plot_pieces.py`):
* the largest single job step (essentially one drain start) flattens at 64,048 steps (random) and
  69,714 (hammer) from 10⁶ elements on;
* the most job steps in one operation reach 48 (six core insertions × `K_R`) at 10⁷ and cannot grow;
* the drains started in the slowest operation grow by one per decade: 1, 2, 3, 4, 5 from 10⁴ to 5·10⁷
  (random). Only this factor grows, and it is bounded by the previous one; multiplying the observed
  maxima suggests a realistic ceiling of about 48 × 70,000 ≈ 3.4 million steps (an extrapolation).

The growth is bounded, as the theorem says: an operation performs at
most `K_B + 3 = 7` core insertions (its own, a mirrored one, `K_B + 1` copies), each with at most
`K_R = 8` job steps. But during a rebuild the copies all advance the next core's job, so one operation
can take a job's walk through many levels, and the bound is reached only when the top tree has dozens
of levels, far beyond any list that fits in memory. The plateau cannot be observed.

**Word size.** The largest value computed grows with the capacity, as expected: 301 bits for a few
live elements (workload `flicker`), 660 at 160,000 (`random`), 780 at 4 million (`L = 24`). These are the
group labels. (Before the label widths of the proof parameters were narrowed, `docs/LEAN.md` §15: 552,
1,233 and 1,461 bits.) The steps of the staircase come when a rebuild starts (`results/growth.png`,
bottom).

**Time.** 1–4 µs per operation (3.9 µs on average while growing to 4 million elements; the narrower
labels did not change it, since time is dominated by memory traffic). The time
per machine step grows from about 2 to 5 ns over that range, mostly from cache misses as the
structure grows; it drops after each swap.

**Memory.** The proved capacities are far larger than what is used. At 4 million elements: 1,988
top-structure nodes against a node capacity of 9.2 million, and lists of at most 21 entries in
slots of 162 or 322 (`results/usage.txt`). The arrays' capacities total 33.8 billion cells, but the
runtime allocates blocks of 4,096 cells only when they are first written, so 57 million cells are in
use (about 14 per element; resident memory 0.9 GB).

## The runtime and time per operation (2026-10-19)

The first time measurements at 10⁷ elements showed single operations of 0.2–0.5 s, although none
took more than 251,000 steps. The runtime did not provide what the model assumes:
* creating an array took time proportional to its capacity (its block table was built eagerly),
  and replacing a core freed all its memory at once;
* glibc's `free` and `malloc` occasionally did work proportional to the heap (consolidating and
  sorting free chunks, trimming), up to several milliseconds in a single operation.

`rt.rs` now gives every operation a constant amount of memory management: large block tables are
mapped from lazily zeroed memory (`mmap`), blocks come from the runtime's own pool (carved from
lazily mapped 2 MB slabs, recycled through an intrusive free list), retired memory is collected
with four cleanup actions per update (`M::collect`), and glibc's heap trimming is off. Words above 2⁶⁴ are shared
(reference-counted `BigUint`), and arrays store the shared value, so loading or copying a word
never allocates: an order query allocates nothing (it made 38 allocations before), an insertion
23 on average (74 before); queries became about 3 times faster while the structure fits in the
cache. (Flat arrays, one lazily mapped region per array instead of the block table, gained only
3–8% and were not adopted: at large sizes the time goes to the cache lines a query touches, one
per field array and two per large value.) Shared words are freed when their last copy goes,
many at a time when a retired core's values are released, and glibc's `free` then paused single
operations for up to 14 ms; `src/alloc.rs` is therefore the global allocator: constant-time
size-class free lists for objects up to 4 KB (memory reused, never returned), the system allocator
above that. The program and
its step counts are unchanged: the generated code still prints exactly what Lean's `exec` prints
(9 operation files, 8.6 million steps), and all 23 prototype workloads replay with the same steps
and peaks. The slowest operation at 10⁷ elements went from 0.47 s to about 0.5 ms; what remains is
the operations with the most steps, page faults when a rebuild starts (bounded by the number of
arrays), and the noise of the operating system (about 0.3 ms).

Runtime fixes (2026-10-26): monitoring reads now check the logical array capacity in release
builds too. Replacing a large value with a small one releases its reference and recycles its
arena slot, so repeated overwrites cannot grow the arena beyond one slot per array cell.
Slab records and retirement queues use linked lists to avoid copying existing entries when
they grow. Cleanup charges empty-list removal against its budget as well as blocks, value
segments and tables. Six runtime regression tests run with `cargo test` and `cargo test --release`.
These changes do not establish a wall-clock bound for allocation or operating-system calls.

## Comparison with two unverified implementations (2026-10-19)

`compare` times every operation of four insertion workloads (`random`: after a random element;
`hammer`: always after the first element; `append`; `front`) and, with a fifth argument, random
order queries after every insertion, for this code and for two baselines written for comparison
(not verified; unit tests check them against a plain list):
* `src/baseline.rs`: the amortized O(1) algorithm of Bender et al. (ESA 2002): groups of at most 64
  elements, tag-range relabeling of 62-bit group tags with T = 1.4;
* `src/avl.rs`: the textbook O(log n) solution, an AVL tree with parent pointers; a query compares
  the paths to the lowest common ancestor (no deletion: the workloads do not delete).

Every workload runs three times in one process; the workloads are deterministic, so the k-th
operation is the same in every run, and its time is taken as the minimum over the runs
(interruptions of 4–7 ms by the operating system hit single runs at random, but practically never
the same operation in all three). Per decade of the list size we report the slowest operation and
the median of the runs' means. Intel Core Ultra 9 285K, Linux 7.0, performance cores only, one core
per run (`results/compare/run.sh`, `summarize.py`, `summary.csv`, `compare.png`, `queries.png`).

Slowest insertion (over the four workloads) and mean random insertion:

| elements | this code: slowest | amortized: slowest | AVL: slowest | this code: mean | amortized: mean | AVL: mean |
|---|---|---|---|---|---|---|
| 10⁵ | 0.13–0.15 ms | 4.1–4.3 µs | 2.7–3.0 µs | 1.38 µs | 38 ns | 62 ns |
| 10⁶ | 0.22–0.24 ms | 46–55 µs | 3.1–3.6 µs | 3.35 µs | 98 ns | 123 ns |
| 10⁷ | 0.29–0.31 ms | 0.56–0.58 ms | 3.3–5.2 µs | 4.58 µs | 534 ns | 607 ns |
| 5·10⁷ | 0.30–0.38 ms (hammer, random) | | | 5.96 µs | | |
| 10⁸ | (not run: memory) | 5.3 ms | 3.3–7.0 µs | | 712 ns | 954 ns |

The slowest-insertion columns of the baselines need two qualifications (next section): the AVL
figures are mostly page faults, not the tree, and the amortized figures are from the clustered
workloads; on random insertions its slowest stays at 3–14 µs.

Order queries (mean): this code 97 ns at 10³, 134 ns at 10⁵, 706 ns at 10⁶, 1,376 ns at 10⁷; AVL 36,
59, 106, 515 ns; amortized 12, 14, 31, 193 ns.

* Worst case: the amortized baseline's slowest insertion relabels a whole tag range and grows
  linearly with the size; this code's grows only with the number of drain starts (above) and is the
  smaller of the two from about 10⁷ elements on. In every decade from 10⁵ to 5·10⁷ this code's slowest
  operation is the one with the most machine steps. The AVL tree's slowest insertion (O(log n), tiny
  constants) is far below both.
* Average: both baselines are much faster. Against the amortized one, the factor depends on its cache
  behaviour: 36 times at 10⁵ and 9 times at 10⁷ on random insertions, about 100 times on the
  sequential workloads, where it stays in the cache (about 23 ns at every size). Our cost: about 1,360
  machine steps per insertion on average (deamortization does a share of future work every time:
  split moves, top jobs, and while the list grows, 2.35 core insertions per user insertion because of
  rebuild copies), in unoptimized generated code (arbitrary-precision words, step counting).
* Queries: 65 machine steps always, against 25–78 node visits for the tree between 10³ and 10⁷; in time
  both grow about 14-fold over that range, dominated by cache misses, and the tree stays 2.3–6.7 times
  faster. We did not observe a size at which the constant-time query wins: our query touches one cache
  line per field array of the machine program and two per large word.

## Page faults and cold caches (2026-10-20)

**Page faults.** The slowest AVL insertions above visited only 2 nodes: they are page faults, taken
when a node array (reserved with `Vec::with_capacity`, mapped by the system on first touch) reaches a
fresh 4 KB page, about one insertion in a thousand at about 2.6 µs. Allocation is deterministic, so
the same insertion faults in every run and the per-operation minimum keeps it. With the arrays
touched beforehand (a variant of `Avl::new` filling and clearing each vector; not committed), the
slowest AVL insertion is the deepest one and grows with log n and cache misses:

| elements | hammer: as above | hammer: pre-touched | random: as above | random: pre-touched |
|---|---|---|---|---|
| 10⁵ | 2.9 µs (2 nodes) | 0.21 µs (15 nodes) | 2.8 µs (3) | 0.19 µs (4) |
| 10⁶ | 3.1 µs (2) | 0.32 µs (20) | 3.5 µs (9) | 0.74 µs (9) |
| 10⁷ | 3.2 µs (2) | 1.26 µs (23) | 5.7 µs (16) | 3.8 µs (22) |

This code pays page faults too (its pool and tables are mapped lazily), but a few microseconds are
negligible against its 0.13–0.38 ms. The amortized baseline's slowest random insertion (3–14 µs) is
probably also mostly page faults. Each baseline's adversary differs: clustered insertion for the
amortized one (it relabels a dense range), while for the tree clustered insertion is close to its
best case (the same path every time, in the cache); its worst is random insertion into a large tree
with cold caches.

**Cold caches.** `cold` (`src/bin/cold.rs`, `results/cold/run.sh`, one run at a time on one
performance core) reads a 128 MB buffer (4 KB pages) before every measured operation, evicting the
structure from L2, L3 and the TLBs (instruction cache and branch predictors stay warm; an empty
operation measured this way takes about 12 ns). A warm run records the work of every insertion; per
decade, the 500 insertions with the most work, 500 evenly spaced ones and one random query after
each of the latter (cold, then again warm) are measured in two more runs. Page faults are recorded:
the time of an operation is its minimum over the runs without a fault, or over both runs if it
faulted in both (this code's heaviest insertions allocate and fault in every run, so they are kept).

Slowest insertion, cold (this code including page faults; the baselines without, which add 2–20 µs):

| elements | this code (4 workloads) | amortized: clustered | amortized: random | AVL (worst workload) |
|---|---|---|---|---|
| 10⁵ | 0.20–0.22 ms | 6.0–6.4 µs | 10 µs | 4.2 µs |
| 10⁶ | 0.29–0.33 ms | 47–48 µs | 12 µs | 5.4 µs |
| 10⁷ | 0.34–0.35 ms | 0.55 ms | 16 µs | 6.4 µs |
| 10⁸ | (not run) | 5.0 ms | 22 µs | 8.7 µs |

Order queries, cold (mean / slowest of 500 per decade):

| elements | this code | AVL | amortized |
|---|---|---|---|
| 10⁵ | 4.3–4.6 / 6.3–6.6 µs | 1.7–2.0 / 2.4–2.8 µs | 0.7–0.8 / 1.0–1.2 µs |
| 10⁶ | 4.9–5.6 / 7.5–8.7 µs | 2.4–2.7 / 4.5–5.6 µs | 0.7–0.8 / 1.0 µs |
| 10⁷ | 4.0–6.7 / 5.5–9.7 µs | 3.2–3.6 / 4.0–8.0 µs | 0.6–0.8 / 1.0 µs |
| 10⁸ | (not run) | 4.3–5.5 / 6.7–9.0 µs | 0.5–0.8 / 0.8–1.1 µs |

(Ranges are over the workloads run: all four for this code, random, hammer and front for the
baselines; the amortized clustered column is hammer and front. Warm, the same queries take 0.1–0.25 µs, 0.04–0.2 µs and 0.01 µs.)

* Insertions: the tree's slowest cold insertion (at most 52 node visits at 10⁸) stays 50–60 times
  below this code's. Cold caches double the tree's worst case but change this code's little (0.31 →
  0.35 ms at 10⁷): its heaviest insertions stream through so much memory that they miss the cache
  when warm too. The amortized baseline's clustered worst case does not change: relabeling dominates.
* Queries: cold, this code's query does not grow with the size (65 steps; tens of cache lines over
  the field arrays and the shared large words), while the tree's grows with its depth (its mean
  triples from 10⁵ to 10⁸). On random insertions at 10⁷ this code's slowest cold query is below the
  tree's (5.5 against 8.0 µs) and the means are within 10% (4.0 against 3.6 µs); on the clustered
  workloads the tree is still about twice as fast. Not yet measured: this code cold at 5·10⁷
  (about 10 GB), which would show whether the means cross. The amortized baseline compares two
  64-bit tags (about two cache misses) and is fastest throughout.
