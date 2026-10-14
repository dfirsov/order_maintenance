# Lean Formalization — Design

Status: **v0.3** (2026-10-14); M0 and M1 implemented in `lean/`. This note fixes the design of the
Lean 4 development. It supersedes `docs/SPEC.md` §9–§10 (Lean architecture and
milestones), which assumed a shallow cost monad.

**Goal.** A convincing, machine-checked proof that the algorithm of `docs/PROOF.md` answers
correctly and performs O(1) steps per operation in the worst case. The O(1) bound is the
priority. The speed of any executable Lean code is not a goal.

---

## 1. The idea in one paragraph

Running time is a property of an algorithm on a *machine model*, not of the language used
to reason about it. So we define a word RAM inside Lean: memory, instructions, and a cost
of one per instruction. We write the algorithm as a *program for that machine*: a syntax
tree in a small imperative language, given meaning by an interpreter that counts steps. We
then prove two things about that program:
* its answers match the list specification;
* starting from any reachable state, every operation finishes within an explicit constant
  number of machine steps.

Lean is only the meta-language. How fast Lean itself would evaluate the interpreter is
irrelevant, exactly as a paper proof about a RAM does not depend on the speed of the paper.

---

## 2. Theorems to prove

Fix the proof parameters of `PROOF.md` §2.9: `G = 2L`, `T = 3L²`, `K_G = K_C = K_R = K_B = 4`,
`a = 8`, `s = 11`, `β = 48`, `L ≥ 8`.

**Theorem A (correctness).** For every operation sequence `ops` whose arguments are live
elements (`PROOF.md` §1), running the program on `ops` returns the same answers as
`Spec.run ops`.

**Theorem B (constant time).** There is an explicit constant `C`, a numeral computed from the
parameters, with the following property. For every valid operation sequence and every
prefix of it, the machine steps of the next operation are at most `C`.

**Theorem W (word size).** Every value ever stored or computed by the program is below
`2^(c_w · L)` for an explicit constant `c_w`, where `L = ⌈log₂ N⌉` for the current core.
This justifies charging one step per word operation: words have `Θ(log N)` bits, and by
Lemma W, `N` stays within a constant factor of the recent maximum number of live elements.

The statement of B quantifies over all histories. Both A and B are about the *same*
program, the deep-embedded one of §3.

---

## 3. The machine model (`OM/Machine/`)

### 3.1 Memory and words

* A fixed, finite set of **array names**, one per field of the state layout (§5): for
  example `elem.next`, `grp.lab`, `top.slot0.label`. Each array maps `Nat → Nat` and has a
  capacity. Reading or writing outside the capacity is a machine error.
* **Allocation.** A core's arrays are allocated at capacity `N` (or a proved bound
  `O(N)`) in O(1) steps, and read as 0 until written. This is the standard assumption of
  *constant-time-initializable arrays* (Briggs–Torczon; Navarro 2014), which a real word
  RAM implements with O(1) overhead per access. It is a stated assumption of the model.
* **Words.** All values are `Nat`. The machine has a word-size parameter `w`. Theorem W proves
  that no value reaches `2^w`, with `w = c_w·L`. The interpreter does not truncate; it records
  the largest value seen, so Theorem W is a separate statement.
* **Locals.** Each procedure call has its own frame of word-valued local variables.
* **Word size.** `State.peak` records the largest value ever computed, including every
  intermediate value of every expression. Theorem W is a bound on `peak`.

### 3.2 Instructions (each costs 1)

As implemented in `lean/OM/Machine/Syntax.lean`:

```
e ::= n | x | A[e] | e op e | ¬e | msb e
      op ∈ { +, − (machine error if the result would be negative), *, /, %, <<<, >>>,
             <, ≤, =, ∧, ∨ }           -- comparisons and connectives return 1 or 0
s ::= skip | x := e | A[e] := e | alloc A e | s ; s | if e then s else s
    | for x < e do s                    -- the bound e is evaluated once, before the loop
    | call p(e…) → x…                   -- the callee's body is a subterm of the call
    | fail | catch s s
```

* `msb` (most significant bit), multiplication and division are standard unit-cost word-RAM
  operations. They are needed only to compute a new core's parameters (`L' = ⌈log₂ N'⌉`,
  `T' = 3L'²`, the chunk size `⌊⌊T/2⌋/⌊G/2⌋⌋`, `H'`) in O(1) during a rebuild.
* **No recursion, by construction.** A `call` carries the callee's body as a subterm, so a
  procedure cannot call itself: its syntax tree would be infinite. No ranking of procedures
  is needed. Arguments are evaluated in the caller's frame, the body runs in a fresh frame of
  locals, and the results are copied back.
* `alloc A e` gives array `A` capacity `e`, all cells reading 0, in one step. An access at an
  index `≥` the capacity is a machine error.
* `fail` is a failed algorithmic guard; it propagates, with the state reached, to the
  nearest `catch`, whose handler runs next (the FALLBACK of `PROOF.md` §2.8).
* There are **no `while` loops**. So the interpreter is a total, structurally recursive Lean
  function `exec : Stmt → State → Out`, where `Out` holds the final state, the cost, and a
  status (`ok`, `fail`, or machine error `err`). No fuel is needed.

### 3.3 Cost semantics

`exec` charges one unit per evaluated expression node, assignment, store, allocation,
branch, loop iteration, call, returned value and handler entry. Cost is part of the semantics. There is no way to annotate cost by
hand, and no way to compute outside the interpreter.

**Why this is convincing.** With a deep embedding, the only computation the algorithm can
do is interpreted instructions, each charged. A shallow embedding (ordinary Lean code in a
counting monad) would let pure Lean code between primitives do uncounted work. Ruling that
out would depend on review rather than proof.

### 3.4 What Theorem B reduces to

There is no recursion, and every loop bound is an expression. So the cost of one operation
is bounded by a sum over its loops of (iterations × body cost), evaluated in the current
state. The bodies are fixed programs with fixed costs. Theorem B therefore reduces to
invariants of reachable states:
* the O(n) paths are never taken: FALLBACK (K1) and the PQ slow path (K2);
* every data-dependent loop is bounded by a constant (K3). A data-dependent loop is one
  whose bound is read from the state: scanning a top table (at most 46 entries), copying a
  table at drain start, or walking a node's live children (at most 26).

These are exactly the facts that `PROOF.md` §4 proves. The counting itself becomes
mechanical, through a cost lemma for each procedure.

---

## 4. Two levels and a simulation

Reasoning directly about syntax trees for the whole algorithm would be painful. So the
development has two levels.

* **Level F (functional model, `OM/Model/`).** The algorithm as pure Lean functions on a
  structured state: records with finite maps or arrays, and explicit job records. It mirrors
  the Python prototype closely, and it is executable. It carries no cost. **All of the
  mathematics is proved here:**
  * INV-S, Theorem A;
  * invariants F, (P), (W1), (W3), (O), (S), (Q);
  * Lemmas G1–G4, C1–C3, Z, R, T0–T5, W;
  * the induction over time of `PROOF.md` §4.7.
  **As implemented (M1, `lean/OM/Model/`):** `State`, `PQ`, `Top`, `Core`, `Wrapper`. Code
  runs in `EStateM Err Core`; a failed guard throws and *keeps* the state reached, like the
  prototype's exceptions, and the handler runs FALLBACK on it. Records live in 1-based arrays
  with `NIL = 0` (memory that reads 0 until written, as on the machine). The prototype's
  generators become explicit program counters (`JobPc` for top insertion jobs, `Prep` for the
  deferred construction of a core). Every function is total: loops are `for` over bounded
  ranges, with no `partial` and no `while`. Instrumentation is omitted. `Err.bug` marks the
  places where the prototype would crash (assertions, missing keys).
* **Level M (machine program, `OM/Impl/`).** The same algorithm as a program of §3, a
  straightforward transliteration of Level F.
* **Simulation theorem.** For an encoding `enc : F.State → M.State`, running the program of
  operation `op` on `enc σ` yields `enc (F.op σ)`, with cost at most `cost_op(σ)`. Here
  `cost_op(σ)` is an explicit expression in a few size quantities of `σ`:
  * table sizes and child counts touched;
  * whether FALLBACK or the PQ slow path is taken;
  * the number of elements that FALLBACK scans.

  This is proved procedure by procedure, with a weakest-precondition calculus for the
  language (§6). Each proof is local and mechanical.
* **Theorem B** = simulation + Level-F invariants bounding those quantities on reachable
  states.
* **Theorem A** at Level M follows from Theorem A at Level F through the simulation.

Level F is executable, so it is differentially tested against the Python prototype before
any proof (§8). The Level-M interpreter is executable as well, so the transliteration is
tested too.

---

## 5. State layout (Level M; Level F uses the same fields as records)

The prototype uses Python lists inside nodes and hash maps for handles. The machine version
replaces every one of these with fixed fields, so that every primitive is O(1):

| Prototype | Machine layout |
|---|---|
| element/group/chunk lists | `next`, `prev` arrays (indices), plus per-record fields (`lab`, `size`, `state`, `src`, `l`, `r`, `first`, `last`, …) |
| priority queue | bucket arrays indexed by size, with doubly linked bucket lists and a doubly linked list of non-empty buckets (as `pq.py`) |
| a node's live children (Python list) | doubly linked list through `parent`, `child_first`, `child_last`, `sib_next`, `sib_prev` |
| a table: `order` list + `lab` dict + `side` dict | **entry-centric slots.** By invariant (Q) every entry lies in at most 2 tables, so each entry has two slots `slot[k] = (table, label, side, prev, next)`, linking the table's entries in label order. The table owner keeps `first`/`last`. Looking up an entry's label in a table, or inserting a neighbour, is O(1). The prototype's `order.index(e)` scan disappears. |
| `in_tables` list | the two slots themselves |
| chunk paths `p₁ … p_H` | array of size `m_cap × H` |
| jobs (Python generators) | one job record: phase (copy / walk), level `j`, current node `u`, sweep steps left, and `x, y, z` |
| wrapper hash maps `cur_idx`, `nxt_idx` | handle arrays with two slots per handle (one per core parity) and an epoch stamp (`PROOF.md` §2.7) |

**Capacities** are proved bounds:
* elements: at most `N`;
* groups and chunks: `O(N/G)` and `O(N/T)`;
* top nodes: at most `1 + 2·(drains) = O(m)`.

These are additional Level-F invariants, and running out of capacity is a machine error
that the proofs exclude.

---

## 6. Program logic (`lean/OM/Machine/Logic.lean`)

* `wp c Q s`: from `s`, `c` terminates normally and `Q` holds of the final state and cost.
  Since `exec` is deterministic and total, this is simply a predicate on `exec c s`.
* One rule per construct (`wp_assign`, `wp_store`, `wp_alloc`, `wp_seq`, `wp_ite`, `wp_call`,
  `wp_catch_ok`, `wp_catch_fail`), each an `↔` except the `catch` rules. For straight-line code
  `simp` with these rules produces the verification condition directly.
* The loop rule `wp_loop` takes an invariant `I k` indexed by the iteration and a cost bound
  for one iteration of the body; the loop costs at most `1 + cost(bound) + N·(1 + k_body)`.
* Triples `⦃P⦄ c ⦃Q⦄≤ k` with sequencing and consequence rules. Cost bounds that depend on
  the pre-state are expressed through ghost variables quantified outside the triple.
* The simulation proofs of §4 are triples of the form
  `∀ σ_F, ⦃σ_M = enc σ_F ∧ Inv σ_F⦄ p ⦃σ_M' = enc (F.p σ_F)⦄≤ cost_p σ_F`.

No separation logic is needed: arrays are named globals; different names never alias, and
aliasing within one array is a case split on indices.

**`Std.Do` / `mvcgen` (decided in M0).** Not used for now. Our language is deep-embedded and
deterministic, so `wp` needs no monadic machinery, and the `simp`-driven rules already yield
the verification conditions (see `OM/Machine/Examples.lean`). Using `mvcgen` would need a
second, monadic semantics and an adequacy proof. We revisit this in M6 if the Level-M proofs
turn out to be heavy.

---

## 7. Files and milestones

```
OM/
  Spec.lean                 list specification: insertAfter, insertFirst, delete, order
  Machine/Syntax.lean, Exec.lean, Logic.lean, Examples.lean
  Model/Params.lean         proof parameters; conditions I1–I10 (closed forms, from lower_bounds.py)
  Model/Labels.lean         §2.2 primitives and their guards
  Model/Core.lean           elements, groups, chunks, splits, family moves, reservation, PQ
  Model/Top.lean            WBBT with ghost drains, jobs
  Model/Fallback.lean, Model/Wrapper.lean
  Proof/Correct/…           INV-S, Lemmas 3.1–3.3, Invariant R, Theorem A (F)
  Proof/Cost/Zeroing.lean   Theorem Z
  Proof/Cost/Groups.lean, Chunks.lean, Reservation.lean, Wrapper.lean
  Proof/Cost/Top/…          T0–T5, (Q)
  Proof/Cost/Assembly.lean  the induction over time (§4.7)
  Impl/…                    Level-M programs, one file per Model file
  Proof/Sim/…               simulation theorems
  Main.lean                 Theorems A, B, W
  Test/…                    trace export and import, differential runner
```

| # | Deliverable | Proof content | Risk |
|---|---|---|---|
| M0 ✅ | Lake project with Mathlib; `Spec`; machine syntax, `exec`, cost; `wp` with soundness | wp soundness | low |
| M1 ✅ | Level F executable: core, top, fallback, wrapper; differential tests against the Python prototype pass on all stress workloads | — | low |
| M2 | **Theorem A** at Level F | INV-S preservation, guards, FALLBACK, Invariant R | medium |
| M3 | Theorem Z (warm-up, can start in parallel with M1) | standalone combinatorics | low |
| M4 | Lower-level cost lemmas G1–G4, C1–C3, R, the chunk count, W | invariant reasoning | medium |
| M5 | Top-structure lemmas T0–T5, (Q) | the largest proof | **high** |
| M6 | Level M programs and simulation; assembly; **Theorems B and W** | mechanical, but long | medium |

The order is chosen so that the riskiest mathematics (M5) is attacked on a validated
model, and the mechanical machine layer (M6) comes last, when Level F is stable.

---

## 8. Validation before proof

1. **Traces** (`prototype/trace.py`, `trace_campaign.py`). The Python prototype runs a stress
   workload and writes every operation with the prototype's answer and checkpoints of its
   state: the key (tag, group label, element label) of every new element, the fallback and
   rebuild counters, and digests that hash the keys of all elements of `cur` and `nxt` in list
   order (after each of the first 2000 updates, then periodically). Random order queries are
   interleaved.
2. **Level F replays them** (`lake exe replay`, `OM/Test/Replay.lean`) and must reproduce every
   answer, key, counter and digest exactly. Equal digests mean equal labels and tags for every
   element, so the replay checks the whole label state, not just the answers. Presets: the
   default and proof parameters, two presets with labels far too narrow (FALLBACK constantly,
   from the core and from the top structure), and fuzz traces with random small parameters
   and random `K_B`. Lean panics abort the replay.
3. **Level M replays a subset** through the interpreter (M6) and checks that the encoding
   commutes, and that the measured step counts stay within the `cost_op` expressions.

To make exact replay possible, the prototype's priority queue was made deterministic: within a
bucket, the most recently added chunk is popped first (previously: Python set order).

---

## 9. Trusted base and assumptions

* The Lean kernel, and Mathlib.
* The **definition** of the machine (§3). It is short and must be reviewed carefully. It is
  the cost model.
* The word-RAM assumptions:
  * unit cost per instruction, including `*` and `msb`;
  * words of `Θ(log n)` bits (justified by Theorem W and Lemma W);
  * constant-time-initializable arrays.
* The **user interface**: operations take handles of live elements (`PROOF.md` §1). Invalid
  calls are outside the theorem.

Not covered:
* the running time of compiled Lean code;
* memory reclamation of retired cores (the model simply stops using them);
* concurrency.

---

## 10. Open choices

1. **Mathlib version.** Pin the release matching Lean 4.35.0.
2. **Parameters.** Concrete numerals for the proof preset (`a = 8`, `s = 11`, …), with only
   `L` symbolic. This keeps I1–I10 provable by `omega`/`nlinarith` plus a few closed forms.
   Generalizing to symbolic `a, s` is possible later.
3. **`Nat` labels.** Keep the bit-width bound a separate invariant (Theorem W) rather than
   working in `Fin (2^w)`. This keeps the correctness proofs free of overflow reasoning.
4. **Default vs proof preset.** Only the proof preset is formalized. The default preset stays
   an empirical artifact of the prototype.

---

## 11. Existing frameworks (surveyed 2026-10-14)

No existing Lean 4 framework gives what §3 needs: a cost model that holds **by construction**
for a word-RAM language with arrays, together with a program logic. What exists, and how we
use it:

| Framework | What it is | Cost by construction? | Use for us |
|---|---|---|---|
| CSLib `TimeM` (`Cslib.Algorithms.Lean.TimeM`) | shallow writer monad, manual `tick` | no; its docs say the time field "is NOT verified against actual cost" | none; this is the weakness §1 avoids |
| CSLib query models / Algolean `Prog` | free monad over declared queries, costs derived from the queries | yes for queries, but pure Lean code between queries is free | design reference; work in progress |
| CSLib Boole | Boogie-like imperative language with Lean VCs | no cost semantics yet (on the roadmap) | watch |
| Lean core `Std.Do` / `mvcgen` | VC generator for monadic `do` code | no cost | considered in M0, not adopted (§6) |
| Loom / Velvet (VERSE lab) | shallow monadic verifiers, Dafny-style, SMT backed | no cost | not needed |
| Iris-Lean | separation logic | no time credits yet | not needed (§6) |
| Isabelle AFP *Hoare Logics for Time Bounds* (Haslbeck, Nipkow) | IMP with time, three logics, sound and complete VCGs | yes | closest design template for §3 and §6 |
| Isabelle-LLVM with time (Haslbeck, Lammich) | refinement down to LLVM with resource currencies | yes, real code | gold standard; another prover |
| CFML / Iris time credits (Rocq) | separation logic with time credits | yes | amortized analyses; not needed for worst case |
| calf / decalf (Agda) | cost-aware type theory | yes | conceptual reference |

Consequences:
* We build the small deep-embedded machine of §3 ourselves, following the Isabelle IMP-with-time
  design. It is a few hundred lines.
* M0 considered `Std.Do`/`mvcgen` as the VC engine; our own `wp` rules sufficed (§6).
* CSLib's roadmap asks for an explicit RAM model; ours could be contributed there later.
