# Re-run of the `om` comparison, 2026-10-27

**Setup.**
* Current code: `gen.rs` of 2026-10-22, and `rt.rs` and `alloc.rs` of 2026-10-26.
* `cargo build --release --offline` had nothing to rebuild.
* Every configuration ran alone, one after the other, pinned with `taskset -c 2` to a performance core, the machine otherwise idle, governor `powersave`.
* Three runs in one process, using per-operation minima as in `run.sh`.

```sh
taskset -c 2 ./target/release/compare om {random,hammer,append,front} 10000000 3 > om_<wl>.csv
taskset -c 2 ./target/release/compare om random 10000000 3 1 > om_random_queries.csv   # as ../queries/om.csv
taskset -c 2 ./target/release/compare om {hammer,random} 50000000 3 > om_<wl>_5e7.csv
taskset -c 2 ./target/release/compare bender <wl> 10000000 1 > bender_check_<wl>.csv   # check only
```

`runlog.txt` has the wall time and peak RSS of each run:
* 10^7: 53–129 s, 2.7–3.0 GB.
* 5·10^7: 323 s (hammer) and 882 s (random), 15.2–15.8 GB. The benchmark's own arrays account for about 1.2 GB of that.

## Steps: unchanged
`max_work` and `mean_work` equal the old CSVs on every row. The one exception is the 10–100 decade, whose mean is 0.1 step lower because new-core allocations take 2 steps fewer (README, 2026-10-22).

## Whole runs
Means are over all insertions of the run. "Slowest" is the largest per-operation minimum.

| run | mean (old → new) | slowest (old → new) | max steps | mean steps |
|---|---|---|---|---|
| random 10^7 | 4.44 → 4.36 µs | 305 → 299 µs | 250,929 | 1,132.4 |
| hammer 10^7 | 1.85 → 1.72 µs | 307 → 286 µs | 251,007 | 1,281.3 |
| append 10^7 | 1.91 → 1.79 µs | 305 → 287 µs | 247,520 | 1,344.9 |
| front 10^7 | 1.85 → 1.71 µs | 312 → 290 µs | 251,001 | 1,278.3 |
| random 10^7 + 1 query/insertion | 4.32 → 4.41 µs | 307 → 305 µs | 250,929 | 1,132.4 |
| hammer 5·10^7 | 2.18 → 2.10 µs | 298 → 288 µs | 251,928 | 1,510.7 |
| random 5·10^7 | 5.64 → 5.97 µs | 381 → 374 µs | 314,088 | 1,330.3 |

Queries (random, 10^7): every query took 65 steps. The mean query time in the last decade was 1,428 ns (it was 1,376 ns).

## Slowest insertion per decade
Where two files cover a decade, this takes the smaller value, as `summarize.py` does.

| elements | old | new |
|---|---|---|
| 10^5 | 0.13–0.15 ms | 0.12–0.14 ms (123–141 µs) |
| 10^6 | 0.22–0.24 ms | 0.21–0.22 ms |
| 10^7 | 0.29–0.31 ms | 0.29–0.30 ms (286–299 µs) |
| 5·10^7 | 0.30–0.38 ms | 0.29–0.37 ms (287 µs hammer, 374 µs random) |

Mean random insertion per decade, old → new:

| elements | old | new |
|---|---|---|
| 10^5 | 1.36 µs | 1.31 µs |
| 10^6 | 3.35 µs | 3.30 µs |
| 10^7 | 4.54 µs | 4.51 µs |
| 5·10^7 | 5.96 µs | 6.39 µs (+7%) |

## The paper's claims
1. **"0.13–0.15 ms at 10^5 to 0.30–0.38 ms at 5·10^7":** correct this to 0.12–0.14 ms → 0.29–0.37 ms. The slowest insertion is still similar across the four workloads up to 10^7, and on the two run at 5·10^7.
2. **"About 1,360 machine steps per insertion":** the step data is unchanged. Whole-run means are 1,132–1,345 at 10^7 and 1,330 / 1,511 at 5·10^7. Weighted by the number of operations over the six runs, the mean is 1,374. Since no single statistic gives 1,360, "about 1,100–1,500" is safer.
3. **"1.3·10^5 steps at 10^5, 3.1·10^5 at 5·10^7":** holds (127,474–128,034 at 10^5; 314,088 on random at 5·10^7).
4. **"An order query always takes 65 steps":** holds.

## Side notes
* The slowest insertion in time is not always the one with the most steps; the two differ by under 0.5%. This happens for append at 10^5, hammer and front at 10^6, and hammer at 5·10^7. The old CSVs show it too.
* Bender: `baseline.rs` changed on 2026-10-26. A one-run check at 10^7 on all four workloads gives step columns identical to the old CSVs and the same means, so the old bender rows stand.
