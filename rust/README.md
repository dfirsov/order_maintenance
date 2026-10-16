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
