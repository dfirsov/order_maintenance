# Order maintenance in O(1) worst case

**[Paper (arXiv:2610.38616)](https://arxiv.org/abs/2610.38616)**: *Order Maintenance in Worst-Case Constant Time, Verified*.

**[Interactive visualizer](https://dfirsov.github.io/order_maintenance/viz/)**: insert elements and watch groups, chunks and the top tree at work.

Goal: implement an O(1) worst-case order-maintenance algorithm (insert, delete,
order query on a list) and prove it correct in Lean 4.

| Path | Contents |
|---|---|
| `docs/SPEC.md` | design specification: algorithm, safety invariant, cost invariants, milestones |
| `docs/TESTING.md` | testing and measurement report: fuzzing, mutation testing, per-operation cost, scaling, adversaries, parameter thresholds |
| `docs/PROOF.md` | the algorithm in conventional form, with complete pen-and-paper proofs of correctness and of the O(1) bound |
| `docs/LEAN.md` | design of the Lean formalization: deep-embedded word RAM with counted steps, two-level proof, milestones |
| `lean/` | Lean 4 development (`lake build` in `lean/`): list specification, machine model with cost semantics, program logic, executable functional model (`OM/Model`), trace replay (`lake exe replay`) |
| `rust/` | Rust code transpiled from the verified machine program (`lake exe extract`), with a random checker against the specification |
| `prototype/` | executable Python prototype with differential tests and adversarial stress (see its README) |
| `viz/` | interactive visualizer of one core, ported from the prototype: **[open it in the browser](https://dfirsov.github.io/order_maintenance/viz/)** (see its README) |
| `papers/` | citations of the source papers: Dietz–Sleator 1987, Bender et al. 2002, Kopelowitz 2012, Brodal's slides |

Status: the Python prototype implements the full algorithm. An extensive testing campaign
(`docs/TESTING.md`) found no correctness failures and a bounded cost per operation up to
3·10⁶ operations. Writing the proof sketch (`docs/PROOF.md`) then found a cost bug in the
rebuild sizing and two proof gaps. All three are fixed and re-tested, including a lemma
checker that measures every bound of the proof sketch (`docs/TESTING.md` §8: 0 violations).
The pen-and-paper proof is now complete (`docs/PROOF.md` v0.3). Every cost lemma has exact
constants, the conditions are checked for all `L ≥ 8` (`prototype/top_bounds.py`,
`prototype/lower_bounds.py`), and the exact bounds are measured in testing (`docs/TESTING.md` §9).
The Lean port (`docs/LEAN.md` §7):
* **M0:** machine model, cost semantics, program logic and list specification.
* **M1:** the executable functional model replays 2,292 prototype traces (31 million records)
  exactly (`docs/TESTING.md` §10).
* **M2–M5:** Theorem A and the cost lemmas at Level F (the executable model).
* **M6:** the machine program. **Theorems A and B are proved for it** (`lean/OM/Impl/TheoremsM.lean`):
  it returns the specification's answers, and every operation takes at most a fixed number of machine
  steps (`opB 4 = 1,133,561,742`, the same for every `N` and history). The arrays of a core of capacity `N`
  have a total capacity of at most `40000·N` cells.
* **Theorem W** (word size) is proved for the machine program (`lean/OM/Impl/PeakRun.lean`): operation
  `i` computes no value at or above `2^(128·⌊log₂(i + 1)⌋ + 1286)`, so words of `O(log #ops)` bits
  suffice. On a machine with `w`-bit words that stops with an error on any larger value (`execW`),
  Theorems A and B hold verbatim for `t` operations and every `w ≥ 128·⌊log₂(t + 1)⌋ + 1286`
  (`lean/OM/Impl/PeakWord.lean`).

**Assumptions** (`docs/LEAN.md` §2.1): one step per instruction, and constant-time array allocation.
The allocation is not essential: `theoremAB_flat` (`lean/OM/Impl/FlatRun.lean`) runs a verified
translation of the program, with no `alloc` and at most 5× the steps, on a single zero-filled memory
of `memFlat t K_B` words (`O(log t)` bits) fixed before the run.
Words are unbounded naturals in `exec`; Theorem W bounds them, and the `w`-bit machine `execW` bounds
them by definition.

## Reproducing the central checks

`scripts/reproduce.sh` runs, in about ten minutes from a Mathlib cache:
1. the Lean build;
2. the axiom audit of the main theorems (`lean/Audit.lean`: only `propext`, `Classical.choice`
   and `Quot.sound`, and no `sorry` or added axiom);
3. a fresh transpilation compared byte for byte with `rust/src/gen.rs`;
4. the Lean-against-Rust cross-check on the paper's nine operation files.

The larger conformance checks are in `rust/scripts/conformance.sh`. The benchmarks and their raw
results are in `experiments/lean-design/results/` (see `REVISION-2026-10-27.md` there) and
`rust/results/compare/`.

## License

Copyright 2026 Denis Firsov. Licensed under the Apache License, Version 2.0 (`LICENSE`).

