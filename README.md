# Order maintenance in O(1) worst case

Goal: implement an O(1) worst-case order-maintenance algorithm (insert, delete,
order query on a list) and prove it correct in Lean 4.

| Path | Contents |
|---|---|
| `docs/SPEC.md` | design specification: algorithm, safety invariant, cost invariants, milestones |
| `docs/TESTING.md` | testing and measurement report: fuzzing, mutation testing, per-operation cost, scaling, adversaries, parameter thresholds |
| `docs/PROOF.md` | the algorithm in conventional form, with pen-and-paper proof sketches of correctness and of the O(1) bound |
| `prototype/` | executable Python prototype with differential tests and adversarial stress (see its README) |
| `papers/` | source papers: Dietz–Sleator 1987, Bender et al. 2002, Kopelowitz 2012, Brodal's slides |

Status: the Python prototype implements the full algorithm. An extensive testing campaign
(`docs/TESTING.md`) found no correctness failures and a bounded cost per operation up to
3·10⁶ operations. Writing the proof sketch (`docs/PROOF.md`) then found a cost bug in the
rebuild sizing (`prototype/rebuild_attack.py`) and two proof gaps; fixes are proposed there
and not yet applied to the prototype. Next: apply the fixes, then the Lean port.
