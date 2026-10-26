# Visualizer

An interactive page for one insert-only core (`docs/SPEC.md` §4–5): insert elements one at a
time and watch the work of each operation (group splits, chunk splits, the reservation process,
and the top tree's jobs, drains and sweeps).

The top-tree view draws the weight-balanced tree twice over: solid edges are the live tree
(weights, and where new nodes go), dashed edges are stored paths that still run through a
ghost (they decide the tags). A drain shows as a node splitting into two fresh siblings, and
the sweep as its dashed edges disappearing one chunk at a time. Clicking a node shows its
weight against 2aʰ and its label table.

Online: <https://dfirsov.github.io/order_maintenance/viz/> (GitHub Pages, deployed from `main`).
Locally: open `index.html` in a browser. It needs no build or server (`file://` works).

| File | Contents |
|---|---|
| `om.js` | the core in JavaScript: `prototype/core.py`, `pq.py`, `top_wbbt.py` statement for statement, labels and tags as `BigInt`, plus an event log for the page |
| `index.html` | the page |
| `test/gen_traces.py` | runs the prototype core on fixed workloads and records every operation's result |
| `test/check.js` | replays those traces on `om.js` and compares them |

```
python3 test/gen_traces.py /tmp/om-traces && node test/check.js /tmp/om-traces
```

`check.js` compares, after every operation, the new element's key, the fallback count, the
step count (core plus top tree), the number of reservations and drains, and a digest of all
keys in list order. The configurations include the prototype defaults up to N = 8192, runs
past capacity, and parameters below the thresholds of `docs/SPEC.md` §7.1, so that fallbacks
happen.

What the page leaves out:

* **No wrapper.** There is no global rebuild and no growth. Deletion only marks a tombstone. The
  page shows where the wrapper of `docs/SPEC.md` §5.7 would start a rebuild: when the core has
  used N/2 slots, or when fewer than N/8 elements are live. The second rule only applies once
  N/8 elements have been live, since this core starts empty. After that point the page keeps
  inserting into the same core.
* **No `SimpleTop`.** The top level is always the weight-balanced tree, built eagerly.
* **Fixed top height.** H is fixed for the epoch from the capacity, as in the prototype. With
  `a = 2` the upper levels are a chain until the tree grows into them.

The "Small tree" preset uses branching parameter `a = 2`, so that drains in the top tree start
after a few chunks. The proofs use `a = 8`, which is the "Prototype defaults" preset.
