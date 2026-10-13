# Order maintenance in O(1) worst case

Goal: implement an O(1) worst-case order-maintenance algorithm (insert, delete,
order query on a list) and prove it correct in Lean 4.

| Path | Contents |
|---|---|
| `docs/SPEC.md` | design specification: algorithm, safety invariant, cost invariants, milestones |
| `prototype/` | executable Python prototype with differential tests and adversarial stress (see its README) |
| `papers/` | source papers: Dietz–Sleator 1987, Bender et al. 2002, Kopelowitz 2012, Brodal's slides |

Status: the Python prototype implements the full algorithm and passes all tests and stress
workloads. Next: extensive testing and measurement, then the Lean port.
