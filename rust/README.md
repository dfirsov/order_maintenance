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
```

## Results (2026-10-16)

**Correctness.** The generated code returned the specification's answers on every operation
tried:
* 620,000 random operations (`check`, modes grow, mix and churn);
* the 23 stress workloads of the prototype, 200,000 updates each with an order query after each
  (`trace.py --preset proof`; 9.2 million records; `results/replay_workloads.txt`);
* 1,100 fuzz traces (random operation mixes with wipes, bursts and hammering; 4.5 million records;
  `K_B` raised to 4 where the trace used 2 or 3; the answers do not depend on `K_B`).

The prototype's `proof` preset predates M5's parameters, so only the answers the specification
determines are compared (handles and order answers), not the prototype's internal keys.

**Steps.** The largest number of machine steps for one update was 200,469 (workload
`harmonic_half`), against the proved bound `opB 4 = 1,133,561,742`: the bound is about 10⁴ times
loose on these workloads. An order query always took 65 steps.

**Word size.** The largest value computed grows with the capacity, as expected: 552 bits for a few
live elements, 1,233 at 160,000, 1,461 at 4 million (`L = 24`). The steps of the staircase come
when a rebuild starts (`results/growth.png`, bottom).

**Time.** 1–4 µs per operation (3.8 µs on average while growing to 4 million elements). The time
per machine step grows from about 2 to 5 ns over that range, mostly from cache misses as the
structure grows; it drops after each swap.

**Memory.** The proved capacities are far larger than what is used. At 4 million elements: 1,988
top-structure nodes against a node capacity of 9.2 million, and lists of at most 21 entries in
slots of 162 or 322 (`results/usage.txt`). The arrays' capacities total 33.8 billion cells, but the
runtime allocates blocks of 4,096 cells only when they are first written, so 57 million cells are in
use (about 14 per element; resident memory 0.9 GB).
