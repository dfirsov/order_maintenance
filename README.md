# Order maintenance in O(1) worst case

Goal: implement an O(1) worst-case order-maintenance algorithm (insert, delete,
order query on a list) and prove it correct in Lean 4.

| Path | Contents |
|---|---|
| `docs/SPEC.md` | design specification: algorithm, safety invariant, cost invariants, milestones |
| `docs/TESTING.md` | testing and measurement report: fuzzing, mutation testing, per-operation cost, scaling, adversaries, parameter thresholds |
| `docs/PROOF.md` | the algorithm in conventional form, with complete pen-and-paper proofs of correctness and of the O(1) bound |
| `docs/LEAN.md` | design of the Lean formalization: deep-embedded word RAM with counted steps, two-level proof, milestones |
| `lean/` | Lean 4 development (`lake build` in `lean/`): list specification, machine model with cost semantics, program logic |
| `prototype/` | executable Python prototype with differential tests and adversarial stress (see its README) |
| `papers/` | source papers: Dietz–Sleator 1987, Bender et al. 2002, Kopelowitz 2012, Brodal's slides |

Status: the Python prototype implements the full algorithm. An extensive testing campaign
(`docs/TESTING.md`) found no correctness failures and a bounded cost per operation up to
3·10⁶ operations. Writing the proof sketch (`docs/PROOF.md`) then found a cost bug in the
rebuild sizing and two proof gaps. All three are fixed and re-tested, including a lemma
checker that measures every bound of the proof sketch (`docs/TESTING.md` §8: 0 violations).
The pen-and-paper proof is now complete (`docs/PROOF.md` v0.3). Every cost lemma has exact
constants, the conditions are checked for all `L ≥ 8` (`prototype/top_bounds.py`,
`prototype/lower_bounds.py`), and the exact bounds are measured in testing (`docs/TESTING.md` §9).
The Lean port has started: milestone M0 (machine model, cost semantics, program logic,
list specification) is done (`docs/LEAN.md` §7).
