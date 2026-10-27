# Revision runs 2026-10-27b: only the operation inside the timed interval

A reviewer pointed out that `compare`'s random-insertion workload chose its argument inside the
timed interval: `live[(rnd() % live.len()) as usize]` ran between `t0 = Instant::now()` and
`t0.elapsed()`. At 10⁸ elements `live` holds 800 MB, so the read is almost always a cache and TLB
miss. It is also on the critical path, because the insertion needs its result. Every
implementation paid this cost, which made the gaps between them look smaller. This note records
the fix, the size of the overhead, and the re-run of every affected configuration. The algorithm
code is unchanged (`src/lean.rs`, `src/avl.rs`, `rust/src/*`). The new results are in
`results/rev-2026-10-27b/`, laid out like `results/rev-2026-10-27/rep2/`, and nothing older was
overwritten.

Machine and protocol as in `REVISION-2026-10-27.md`: Core Ultra 9 285K, every run pinned with
`taskset -c 2`, one configuration at a time, no build during the timings. Same commands and
arguments as replicate 2 (`results/rev-2026-10-27b/run.sh`).

## 1. Audit of the timing drivers

| driver (paper use) | inside the timed interval before | change |
|---|---|---|
| `compare.rs` (insertions, warm queries) | random insertion: `rnd()` and the read `live[rnd() % len]`; for every workload, the `match` on the workload *string* (`"random"`, `"hammer"`, ...) | **fixed.** The workload name is parsed once into an enum. The argument (`Option<u64>`) is computed before `w0`/`t0`, and the interval holds only `match x { Some(x) => s.insert_after(x), None => s.insert_first() }`. The time, work and `live` pushes were already after `elapsed()`. The query loop was already clean: the pair is drawn before `t0`, and `sink` and the pushes come after. |
| `deletes.rs` (churn, teardown) | nothing beyond the operation: `pick_delete`/`pick_insert` (RNG, `swap_remove_back`) run before `timed()`, and the pushes come after `elapsed()` | unchanged |
| `cold.rs` (cold queries) | nothing beyond the operation: the argument and the query pair are chosen before `timed()`, and the eviction and both `getrusage` calls are outside `t0 … elapsed()` | unchanged, not re-run |
| `longrun.rs` (long history) | nothing beyond the operation: the index and `swap_remove` come before `t0`, and `live` holds 10³ entries | unchanged |

Some work remains in every interval, for every driver and every implementation alike. One part is
the timer pair itself, about 10 ns (`empty` below). The other is the dispatch on the
implementation enum plus, in `compare`/`deletes`/`cold`, the branch on `Option` that selects
`insert_after` or `insert_first`. Both branches always go the same way, so they predict
perfectly.

**Same workload.** The order of `rnd()` calls is unchanged, so the operation sequence is too.
`summarize.py` compares every main CSV with its replicate-2 counterpart, row by row, on `ops`,
`mean_work` and `max_work` (`work_of_slowest` depends on which operation was slowest, so it is
left out). Result: **24 of 24 files identical**. Each driver also still asserts that the work is
the same in all 3 in-process runs. A run of old and new binaries at 10⁶ on all six configurations
also gave identical work columns. `TAILS` output is unchanged.

**Seed.** `compare` now reads an optional environment variable `SEED=k`. When it is unset, the
seed is the published one. When it is set, `random` uses the splitmix64 hash of k as the seed
(`insertion_seed`). The query pairs are not affected.

## 2. The overhead that was inside the interval

`src/bin/selcost.rs` (new) replays the old in-interval work with no data structure. It grows
`live` over the same decade with the same generator and seed, times each step exactly as `compare`
does, and repeats this 3 times. Values in ns: mean (median of 3 runs) / run p99.99 (median) /
slowest per-step minimum.

| decade | empty interval | `rnd()` only | `rnd()` + read `live[i]` | old body (string match + read) | old − empty, mean |
|---|---|---|---|---|---|
| 10⁶–10⁷ (`live` 8–80 MB) | 10.0 / 46 / 13 | 11.8 / 31 / 13 | 75.2 / 393 / 310 | 67.2 / 387 / 327 | 57 |
| 10⁷–10⁸ (`live` 80–800 MB) | 9.8 / 15 / 31 | 11.7 / 20 / 23 | 155.3 / 922 / 360 | 154.7 / 917 / 356 | 145 |

Standing alone, part of `live` fits in L3 (36 MB) at 10⁷, so this measurement understates the
cost there. The drop in the benchmark means themselves is the in-situ figure (random insertion,
rep2 → new, ns):

| | 10⁷–10⁸ | 10⁶–10⁷ |
|---|---|---|
| native | 1166 → 1001 (−165) | 888 → 706 (−182) |
| AVL | 934 → 769 (−165) | 623 → 435 (−188) |
| amortized | 704 → 542 (−162) | 547 → 370 (−177) |
| clustered insertion, all three | ±1–2 ns | ±1–2 ns |

So the old figures carried a constant of about **165 ns at 10⁸ and about 180 ns at 10⁷** on every
random insertion, for every implementation. That is 18–48% of the corrected means. The
clustered-insertion means stay within ±2 ns, which also shows that the session is comparable to
replicate 2. The constant is small next to the tails (p99.99 ≈ 4–12 µs, slowest 5–15 µs), and the
tails moved by no more than the usual noise.

## 3. Table 2 (`tab:eval-summary`) and `tab:native`

Paper format, µs: mean / run p99.99 (median of the 3 runs) / slowest repeatable time (largest
per-operation minimum). Each cell shows replicate 2 (the values now in the paper) → **new**.
Table 2 consists of the first two rows and the cold-query row, plus memory.

| row | native | AVL | amortized |
|---|---|---|---|
| random insertion | 1.17 / 5.4 / 13.3 → **1.00 / 5.3 / 12.1** | 0.93 / 5.7 / 6.9 → **0.77 / 5.5 / 7.2** | 0.70 / 11.9 / 14.1 → **0.54 / 12.3 / 15.3** |
| clustered insertion | 0.084 / 2.7 / 7.4 → **0.085 / 2.9 / 6.3** | 0.031 / 3.2 / 3.4 → **0.030 / 3.2 / 3.6** | 0.023 / 3.5 / 5,022 → **0.022 / 3.4 / 5,050** |
| random churn: deletion | 0.30 / 3.9 / 5.9 → **0.29 / 3.7 / 11.0** | 0.69 / 3.9 / 5.8 → **0.71 / 4.0 / 7.0** | 0.19 / 1.2 / 0.38 → **0.19 / 1.2 / 0.39** |
| random churn: insertion | 0.72 / 4.1 / 5.4 → **0.73 / 4.2 / 5.3** | 0.67 / 5.4 / 6.7 → **0.68 / 5.4 / 6.0** | 0.33 / 9.8 / 12.7 → **0.33 / 9.8 / 12.1** |
| queue churn: deletion | 0.052 / 2.6 / 4.2 → **0.051 / 2.5 / 3.9** | 0.019 / 0.46 / 0.77 → **0.019 / 0.47 / 0.83** | 0.011 / 0.15 / 0.30 → **0.011 / 0.15 / 0.30** |
| queue churn: insertion | 0.053 / 2.3 / 6.3 → **0.053 / 2.3 / 5.6** | 0.027 / 3.2 / 3.2 → **0.027 / 3.4 / 3.4** | 0.022 / 3.7 / 552 → **0.022 / 3.7 / 557** |
| teardown: deletion | 0.38 / 3.6 / 6.8 → **0.39 / 3.1 / 7.8** | 0.72 / 4.1 / 5.7 → **0.73 / 4.2 / 5.9** | 0.19 / 1.3 / 0.71 → **0.19 / 1.3 / 0.76** |
| order query, warm | 0.44 / 1.7 / 0.79 → **0.44 / 1.6 / 0.76** | 0.40 / 2.0 / 1.5 → **0.40 / 1.9 / 1.4** | 0.14 / 1.1 / 0.39 → **0.13 / 1.1 / 0.37** |
| order query, cold | 0.93 / – / 1.4 (unchanged) | 5.9 / – / 8.4 (unchanged) | 0.50 / – / 0.88 (unchanged) |
| memory | unchanged (no allocation changed) | | |

Only the two insertion rows had a timed interval that changed, and only random insertion changed
materially.

* **Churn, teardown and warm queries** use unchanged timed code. These were re-run anyway: the
  `deletes` binary is unchanged, and the query interval of `compare` is unchanged. Treat their new
  values as a third replicate. Means agree with replicate 2 within 3%. The *slowest* values move
  as much as before. Native random churn deletion gave 5.9 (rep2), 9.4 (rep1) and 11.0 µs (now)
  with the same binary and workload. It is a single operation: in the new run the second-largest
  per-operation minimum is 6.0 µs, and no minimum is above 10 µs except that one. The paper's
  statement that the slowest repeatable time varies "by up to about 60%" between sessions should
  read "up to about 90%".
* **Cold queries**: `cold.rs` is unchanged, and the cold-insertion and cold-query intervals never
  held the selection, so it was not re-run. The cells are from replicate 1.

### Native / AVL ratios (rep2 → new)

| workload | mean | run p99.99 | slowest |
|---|---|---|---|
| random insertion, 10⁷–10⁸ | 1.25 → **1.30** | 0.93 → **0.96** | 1.94 → **1.68** |
| clustered insertion, 10⁷–10⁸ | 2.71 → **2.83** | 0.84 → **0.90** | 2.19 → **1.77** |
| random insertion, 10⁶–10⁷ | 1.43 → **1.62** | 0.97 → **0.86** | 1.81 → **1.99** |
| clustered insertion, 10⁶–10⁷ | 2.52 → **2.53** | 0.76 → **0.79** | 1.46 → **1.64** |
| range over the four | 1.25–2.71 → **1.30–2.83** | 0.76–0.97 → **0.79–0.96** | 1.46–2.19 → **1.64–1.99** |

The paper says "1.3–2.7 / 0.8–1.0 / 1.5–2.2". The corrected ranges are **mean 1.3–2.8, p99.99
0.8–1.0, slowest 1.6–2.0**. The mean ratio for random insertion rises because the shared ~170 ns
constant is gone (1.25 → 1.30 at 10⁸, 1.43 → 1.62 at 10⁷). The slowest-ratio range is noisy. In
replicate 1 it was 1.36–2.25, and the seeds below put it anywhere from 1.26 to 1.99 at 10⁷. A
range that covers all replicates and seeds is about 1.3–2.3, which is the safer wording for the
paper.

Other paper statements that depend on these numbers:
* §5 / `tab:eval-summary`: "1.3--2.7 times" → 1.3--2.8.
* Appendix: "Means differ by up to 5% between sessions, and the slowest repeatable time by up to
  about 60%". The means still agree within 3% where the code is unchanged. For the slowest time,
  see above.

## 4. Seeds

`SEED=1` and `SEED=2` were run for random insertion at 10⁷, all three implementations, 3 runs
each. Decade 10⁶–10⁷, µs: mean / run p99.99 / slowest.

| impl | default seed | SEED=1 | SEED=2 | spread (max/min − 1): mean, p99.99, slowest |
|---|---|---|---|---|
| native | 0.71 / 4.0 / 10.0 | 0.71 / 4.1 / 6.6 | 0.71 / 4.1 / 9.4 | 0.6%, 3.8%, 52% |
| AVL | 0.43 / 4.6 / 5.0 | 0.43 / 4.6 / 5.2 | 0.44 / 4.6 / 5.3 | 0.2%, 0.1%, 5.3% |
| amortized | 0.37 / 10.2 / 12.6 | 0.36 / 9.9 / 12.4 | 0.36 / 9.6 / 12.2 | 3.4%, 6.0%, 3.2% |

Native / AVL by seed (mean, p99.99, slowest): default 1.62, 0.86, 1.99; SEED=1 1.63, 0.88, 1.26;
SEED=2 1.63, 0.89, 1.78. Mean and p99.99 do not depend on the seed, within 6%. Native's slowest
repeatable insertion does: 6.6–10.0 µs. That matches its run-to-run behaviour (on the default seed: 8.7 µs in
rep 1, 10.6 µs in rep 2). The baselines' slowest varies by only 3–5%.

## 5. How the three implementations are sized

Every driver passes the same lifetime insertion limit to all three implementations. `compare` and
`cold` pass `n + 1`, `deletes` passes `2n + 2`, and `longrun` passes `n + rounds + 2`.

* **Native** (`Native::new(4, max_handles)`): the handle table is one anonymous `mmap` of
  `max_handles + 1` 12-byte records, with no swap reserved. It never grows, and going past the
  limit panics ("arena full"). Pages are mapped on demand: each operation's `upkeep` writes at
  most one page ahead of the records in use (two pages of slack), so page faults fall on ordinary
  operations. The cores are *not* sized from `max_handles`. They are created for the current list
  size, starting at 64, and rebuilt into larger or smaller cores as the list grows and shrinks.
  Their arrays are likewise mapped a page at a time.
* **AVL** (`Avl::new(cap)`): four `Vec::with_capacity(cap)` arrays (left, right, parent: `u32`;
  height: `u8`; 13 bytes per element). The memory is reserved up front through the allocator and
  never reallocated within `cap`. Pages are first touched by the `push` inside an insertion, with
  no prefaulting.
* **Amortized** (`Bender::new(1.4, cap)`): four element arrays with capacity `cap + 1` (prev,
  next, group, label) and six group arrays with capacity `cap / 32 + 2`. Groups split at 64
  elements, so the group count stays within that capacity. As with AVL, the memory is reserved up
  front, never reallocated, and first touched by the `push` inside an operation.

All three therefore get a preallocated, never-reallocating store sized from the known lifetime
limit. Only native prefaults ahead of use, and only native sizes its main structure (the cores)
from the current number of elements rather than from the limit.

## Run log and timing

Total measurement time: 27 min for the main pass (`run.sh`, started 2026-10-27 21:07) plus 2.4 min
for the query re-run (below). Per configuration (`results/rev-2026-10-27b/times.log`): selcost
6.7 s (10⁷) and 113 s (10⁸). Insertions at 10⁷: 1.4–25 s. At 10⁸: native random 355 s, AVL
random 281 s, amortized random 214 s, clustered 14–36 s. Queries 8–42 s, deletions 4–92 s, seed
runs 14–25 s each.

**Query re-run.** The first query pass ran right after the 10⁸ insertion runs, and its queries
came out 5–30% slower than replicate 2 (AVL warm query 0.52 vs 0.40 µs). Wall times were longer
too (38.6 vs 32.7 s). The query interval had not changed, so old and new binaries were run in turn
on `avl hammer 10⁷` with queries (2 × 2 runs). Both gave 271–272 ns, the same as replicate 2's
275 ns. The slowdown was therefore a transient machine state, possibly memory reclaim after the
13 GB run. The query part was re-run (`PARTS=q`), and it reproduced replicate 2 (wall times 8–42
s, as before). The table above uses the re-run. The first attempt is kept in
`results/rev-2026-10-27b/q-first/`, and both passes appear in `times.log`.

## Files

* `src/bin/compare.rs`: argument chosen before the timed interval, workload enum, optional `SEED`,
  doc comment updated.
* `src/bin/selcost.rs` (new): the cost of the old in-interval work alone.
* `results/rev-2026-10-27b/run.sh`: the revision script, parts `sel ins ins8 q del seed`.
* `results/rev-2026-10-27b/summarize.py`: work check, overhead, paper cells, ratios, seeds. It
  reuses `rev-2026-10-27/summarize.py`. Full tables:
  `python3 results/rev-2026-10-27/summarize.py results/rev-2026-10-27b`.
* `results/rev-2026-10-27b/`: `*_random*.csv`, `*_hammer*.csv`, `q_*.csv`, `del_*.csv` with their
  `tails_*` files, `selcost_1e7.csv`, `selcost_1e8.csv`, `seeds/`, `q-first/`, `times.log` and
  `start.txt`.
