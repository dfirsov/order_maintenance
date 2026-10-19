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
elements, 190,189 at 10⁶, 250,929 at 10⁷; `maxop`). Profiling the generated code (inclusive steps
per procedure) shows why: the most expensive operations run during a rebuild (the operation's own
insertion and `K_B` copy insertions into the next core), and 95% of their steps are drain starts in
the top structure (`startDrain`, mostly its list searches), two at 10⁵, three at 10⁶, four at 10⁷.
The top tree gains about one level per decade (branching parameter 8), and a job's walk can start a
drain at each level it passes. A core insertion performs only `K_R = 8` job steps, so the growth
stops once the tree has about 8 levels (around 10¹⁰ elements); the theorem bounds every size.

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
lazily mapped 2 MB slabs, recycled through an intrusive free list), values of 2⁶³ and more live in
a per-array arena of limbs inside pool blocks (overwritten in place when they fit), retired blocks
return to the pool four per update (`M::collect`), and glibc's heap trimming is off. The program and
its step counts are unchanged: the generated code still prints exactly what Lean's `exec` prints
(9 operation files, 8.6 million steps), and all 23 prototype workloads replay with the same steps
and peaks. The slowest operation at 10⁷ elements went from 0.47 s to about 0.5 ms; what remains is
the operations with the most steps, page faults when a rebuild starts (bounded by the number of
arrays), and the noise of the operating system (about 0.3 ms).

## Comparison with an amortized algorithm (2026-10-19)

`compare` times every operation of four insertion workloads (`random`: after a random element;
`hammer`: always after the first element; `append`; `front`), for this code and for the amortized
baseline (`src/baseline.rs`: groups of at most 64 elements, tag-range relabeling of 62-bit group
tags with T = 1.4). Every workload runs three times in one process; the workloads are
deterministic, so the k-th operation is the same in every run, and its time is taken as the minimum
over the runs (interruptions of 4–7 ms by the operating system hit single runs at random, but
practically never the same operation in all three). Per decade of the list size we report the
slowest operation and the median of the runs' means. Intel Core Ultra 9 285K, Linux 7.0,
performance cores only, one core per run (`results/compare/run.sh`, `summary.csv`, `compare.png`).

| elements | this code: slowest operation | baseline: slowest (hammer/front/append) | this code: mean | baseline: mean |
|---|---|---|---|---|
| 10⁵ | 0.14–0.15 ms | 4.1–4.3 µs | 1.4–1.7 µs | 22–38 ns |
| 10⁶ | 0.22–0.24 ms | 46–55 µs | 2.5–2.9 µs | 22–98 ns |
| 10⁷ | 0.43–0.45 ms | 0.56–0.58 ms | 2.5–4.3 µs | 23–534 ns |
| 5·10⁷ | 0.29–0.38 ms (hammer, random) | | 3.2–5.5 µs | |
| 10⁸ | (not run: memory) | 5.3 ms | | 23–712 ns |

The baseline is about 100 times faster on average (it computes with machine words and counts
nothing). Its slowest insertion relabels a whole tag range and grows linearly with the size (it is
always the operation with the most work); the verified code's stays below half a millisecond and is
the faster of the two in the worst case from about 10⁷ elements on. The verified code's slowest
operation is the one with the most steps, except at 10⁷, where it is the start of a rebuild (about 300
page faults on the first writes into the new core's arrays, bounded by the number of arrays). The
baseline's `random` workload never triggers large relabelings (at most 98 units of work).
