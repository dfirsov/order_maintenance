# Lean Formalization — Design

Status: **v0.5** (2026-10-15); M0–M5 done in `lean/` (M2: §12, M4: §13, M5: §14). This note fixes the design of the
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

Fix the proof parameters of `PROOF.md` §2.9: `G = 2L`, `T = 3L²`, `K_G = K_C = K_B = 4`,
`a = 8`, `s = 11`, `L ≥ 8`. M5 changed three of them (§14): `β = 64` (was 48), `K_R = 8`
(was 4), and `H = ⌊L/3⌋ + 1`.

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

### 2.1 Status: what is proved, under which assumptions

**Proved** (`lean/OM/Impl/TheoremsM.lean`, `Memory.lean`; axioms: `propext`, `Classical.choice`,
`Quot.sound`; no `sorry`):
* **Theorem A** (`theoremAB_M`): for every valid operation sequence, the machine program returns
  exactly `Spec.run`'s answers.
* **Theorem B** (`theoremAB_M`, `opB_four`): initialization takes at most 6,648 machine steps, and
  every operation at most `opB 4 = 1,133,561,742` steps, for every `N` and every history.
* **Memory** (`core_mem`, `reach_mem`): the arrays of a core of capacity `N` hold at most
  `40000·N` cells; during a rebuild the next core has capacity `N' ≤ 4N`.

**Assumed** (the cost model, §3; these are definitions, not hypotheses of the theorems):
1. **Unit-cost words of unbounded size.** A machine word is a Lean `Nat`. Every instruction costs
   one step, whatever the size of its operands. This is the main assumption: a unit-cost machine
   with unbounded words can in principle cheat by computing with huge numbers. Theorems A and B are
   true statements about this machine; whether its step count models a real word RAM depends on the
   values staying small. **Theorem W is not proved** (see below).
2. **Constant-time allocation.** `alloc A n` gives array `A` capacity `n`, every cell reading 0, in
   one step (constant-time-initializable arrays).
3. **Unit-cost `*`, `/`, `%`, shifts and `msb`**, as in the standard word RAM.

**Not proved: Theorem W (word size).** The intended statement: every value the program stores or
computes is below `2^(c·L)`, `L = ⌈log₂ N⌉`, or (for a handle) at most the number of operations so
far. Handles are the insertion counter, so they need `log(#ops)` bits, as in the usual word-RAM
convention that a word holds an index into the input. The evidence is informal: every shift in the
program is `1 <<< e` with `e` a parameter of size `O(L)` or a height times `β` (`O(L)`); labels are
checked against `2^B` before they are stored; other stored values are indices, counts and sizes,
bounded by the capacities (`O(N)`). A proof would need a new invariant: every field of every record,
live or dead, is bounded, kept by every Level F function (about 70 write sites); the intermediate
values of expressions and loop locals would remain on top of that. The machine already records the
largest value it computes (`State.peak`), so the bound can be measured on the stress workloads.

**Not covered:** the running time of the Lean code itself, memory reclamation of a retired core
(its arrays stay allocated until the slot is reused), and calls with invalid handles.

**Executable code.** The same machine program, printed as Rust by an unverified printer and checked
against the machine semantics, is in `rust/` (§16).

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
* **Words.** All values are `Nat`, of unbounded size, and every instruction costs 1 whatever its
  operands. The interpreter does not truncate. It records the largest value seen, so a word-size
  bound (Theorem W) is a separate statement about the same runs. Theorem W is not proved (§2.1):
  unit-cost unbounded words are an assumption of the model.
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
| M2 ✅ | **Theorem A** at Level F (§12) | INV-S preservation, guards, FALLBACK, Invariant R | medium |
| M3 ✅ | Theorem Z (warm-up, can start in parallel with M1): `OM/Proof/Cost/Zeroing.lean` | standalone combinatorics | low |
| M4 ✅ | Lower-level cost lemmas G1–G4, C1–C3, R, the chunk count, W (§13), against the top structure's contracts | invariant reasoning | medium |
| M5 ✅ | Top-structure lemmas T0–T5, (Q); the contracts; the parameter rule (§14) | the largest proof | **high** |
| M6 | Level M programs and simulation; assembly; **Theorems A and B at Level M** ✅, memory ✅ (§15); **Theorem W** not proved (§2.1) | mechanical, but long | medium |

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
* The cost model's assumptions (§2.1):
  * unit cost per instruction, including `*`, `/`, shifts and `msb`;
  * words are unbounded naturals at unit cost. The intended justification, words of
    `O(log N + log #ops)` bits, is Theorem W, which is **not proved**;
  * constant-time-initializable arrays.
* The **user interface**: operations take handles of live elements (`PROOF.md` §1). Invalid
  calls are outside the theorem.

Not covered:
* the running time of compiled Lean code;
* memory reclamation of retired cores (the model stops using them; their arrays stay allocated
  until their slot is reused);
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

---

## 12. M2: Theorem A at Level F

**Statement** (`OM.Proof.theoremA`, `lean/OM/Proof/Correct/Wrapper.lean`). Let `mk : Nat → Params`
give a core's parameters for each capacity and satisfy `CoreP (mk N)` for every `N`. Then
`OM.init mk KB` succeeds, and for every sequence `ops` that is valid from the empty list,
`om.runOps mk ops = .ok (OM.Spec.run OM.Spec.State.empty ops)`. In words: the structure never
fails and gives exactly the specification's answers. Axioms used: `propext`,
`Classical.choice`, `Quot.sound`.

**Parameter conditions** (`CoreP P := FbOK P ∧ RoomP P`, §3.4 of `PROOF.md`):

* `FbOK`: FALLBACK's gaps are at least 1. Group size `⌊G/2⌋` is below `2^B_e`, and groups per
  chunk are below `2^B_g`.
* `RoomP`: `1 ≤ D_e < 2^B_e / (⌊G/2⌋ + 1)`. After FALLBACK, every element has room for one
  insertion after it, so the retried insertion succeeds.

`Params.for_capacity` in `prototype/core.py` satisfies both by a wide margin.

**Proof structure.**

| File | Content |
|---|---|
| `Inv.lean`, `Lists.lean`, `Monad.lean`, `Frame.lean`, `Good.lean` | INV-S, Lemma 3.1 (`order_iff`), linked lists, `Pres`/`Good` with tactics |
| `Insert.lean`, `GroupSplit.lean`, `GroupMove.lean`, `ChunkSplit.lean`, `Reservation.lean` | Lemma 3.2: each step of `background` keeps INV-S (`good_background`); a failed guard changes no element records |
| `Fallback.lean` | Lemma 3.3: from any well-formed element list, FALLBACK succeeds and establishes INV-S with the same list and room after every element (`fallback_run_room`) |
| `CoreInsert.lean` | `insertAfter_run`: insertion with retry after FALLBACK; `order_correct`; `markDead_inv` |
| `Init.lean` | `NoErr` (always succeeds); fresh cores; `prepareStep` |
| `Handles.lean`, `Wrapper.lean` | live handles `liveH`; Invariant R (`WInv`); mirrored operations, copying, swap; Theorem A |

**Invariant R.** `cur` satisfies INV-S with a dead sentinel at the head. Its live handles, in
list order, are the specification's list, and `curIdx` maps each handle to its element. A
rebuild core `nxt` is in one of two states:
* being prepared: it holds the sentinel alone;
* copying: the cursor splits `cur`'s list into `pre ++ post`, and `nxt`'s live handles are
  exactly those of `pre`, mapped by `nxtIdx`.

Mirrored insertions and deletions keep this. A mirrored insertion happens exactly when its
anchor lies in `pre`.

**Model changes made for the proof.** Every one replays all traces exactly.
* Guards replace invariant assumptions: alive checks in group and chunk steps, self-checking
  moves, and the family check in `unitOK`, which covers the first member.
* FALLBACK in closed form (`fbLayout`). `relabelAll` checks that tags increase along the
  chunk list and otherwise numbers the chunks `1, 2, 3, …`. The tree rebuild runs under
  `tryCatch`, so the check always runs.
* `walkList` (fuel-bounded) replaces the imperative list walks.
* `initCore = set initState; initTop`.
* The wrapper's rebuild loop became the recursive `rebuildLoop`. The mirror steps are split
  out (`mirrorInsert`, `mirrorDelete`). `OM.apply` and `OM.runOps` give the specification's
  interface.

---

## 13. M4: lower-level cost lemmas at Level F

**Status.** M4 is done, relative to the top structure's contracts, which are M5's job.
Everything lives in `lean/OM/Proof/Cost/` and is part of the default build. It compiles with no
`sorry`. The axioms are the standard three.

**Main statements.**
* `wrapper_cost` (`Wrap.lean`) is the summary. The structure initializes into a state
  satisfying `WC`, and every valid operation keeps `WC`.
  * `WC` is the wrapper's cost invariant: Invariant R, both cores' cost invariants, and
    Lemma W's record of a rebuild in progress.
  * `WC.cores`: in every such state, `cur` is a core in service with room for an insertion,
    and so is `nxt` once its preparation is over. So every core insertion the wrapper makes
    takes no FALLBACK.
* `insertAfter_cost` (`CoreCost.lean`) is Lemma K1 for insertions. From `CostInv`, inserting
  after a listed element runs exactly `insertElem` then `background`, with no FALLBACK and no
  failed guard, and `CostInv` holds again.
* `markDead_cost` and `order_cost` cover deletions and queries.
* `costInv_fresh`, `gval_fresh`, `lowinv_initCore` and `prepareStep_low` (`Fresh.lean`): a
  fresh core satisfies `CostInv` once its top structure is ready.
* `gparams_proof`, `cparams_proof`, `lparams_proof` (`Params.lean`): the parameter rule
  `proofParams N` satisfies every lower-level parameter condition. It uses `L = max 8 (bits
  of N)`, `G = 2L`, `T = 3L²`, `θ = 2L²` and all `K = 4`. The label widths are
  `D = 2^(halvings)` and `B = halvings + pushes + 2`, all `O(L)`.

**The cost invariant** (`CostInv`):
* `LowInv` (`ResStep.lean`), the invariants below the top structure:
  * INV-S;
  * `GInv`, Lemmas G1–G4 (`Groups.lean`);
  * `CInv`, Lemmas C1–C2 (`Chunks.lean`);
  * `LInv`, Lemma C3 (`Labels.lean`), with its parameter conditions;
  * `PQC`, the queue holds exactly the quiet chunks above `θ`, keyed by size
    (`Sched.lean`);
  * `CountInv`, the chunk count (`Count.lean`);
  * `CParams`.
* `TI`, the top structure's invariant.
* The zeroing game `GameInv` (`Game.lean`, Lemma R through Theorem Z), with the round
  accounting `RoundOK` (`ResCost.lean`).

Undriven insertions are tracked by ghost functions `δ` (per group or chunk) and `δu` (units
added by a group removal). `CostInv` has none; between an insertion and its drives, at most
one exists.

**The top structure enters through contracts** (`TopIface.lean`, `Fresh.lean`). M5 must prove
them.
* `TopContract TI μ J cap`:
  * `TI` depends only on the top fields and the chunk list (`TopSame`);
  * starting a chunk split's job succeeds, with `1 ≤ μ ≤ J`;
  * each job step succeeds, and `μ` decreases while the job continues;
  * the structure has room for chunks below `cap`.
* `PrepContract TI PI ν`: eager construction gives `TI`; lazy construction gives `PI` with
  `ν ≤ H + 1`; each preparation step succeeds and either finishes (`TI`) or decreases `ν`.

The parameters of the zeroing game must satisfy I5,
`θ + R·(H_{n−1} + 1) ≤ T` with `R ≥ J / K_R + 1`. It stays a hypothesis because `J` and `H`
come from M5. The capacity conditions `2 + 2·⌊(count + 1)/(θ + 1 − c_max)⌋ ≤ n + 1, cap` are
also hypotheses; Lemma W will discharge them.

**Proof structure.**

| File | Content |
|---|---|
| `Runs`, `Groups`, `GSteps`, `GMove` | runs of groups; G1–G4; the group phase (`groupPhase_ok`) with extra invariants threaded through `XGroup` hooks |
| `Chunks`, `CPhase`, `CSteps`, `CMove`, `CDrive` | C1–C2; the chunk drive (`cinv_drive`) with `CXSteps` hooks; `FamBound`: what the drive knows of the family |
| `Labels`, `LMove`, `LPop`, `LRoom`, `LHooks` | C3 across every step; room for split starts (`split_room`) and pushes (`push_room`); the C3 hooks |
| `PQ`, `TopFrame`, `Reserve`, `Game` | the queue (K2: `pqAdjust_inc` never scans); what the top structure may change; Lemma R's game |
| `Sched`, `TopIface`, `Count` | `PQC`; frames `CFrame`/`DFrame`; the contracts; the chunk count |
| `ResLoop`, `Pop`, `ResStep`, `ResCost` | the reservation loop; pops; `LowInv`; `reservation_cost` with the round accounting |
| `Budget`, `InsStep`, `BgParts`, `Background`, `CoreCost` | chunk budgets; the insertion step; the chunk phase; `background_ok`; `insertAfter_cost` |
| `Fresh`, `Params` | fresh cores; the parameter rule |

**Deviations from `PROOF.md`** (all recorded here; none weakens the bound):
* **C3 is coarser.** It keeps one halving counter per chunk, `hv ≤ 2·(cs + rs)` (child and
  root split starts), instead of per-gap halving histories. Pushes are counted per end and
  per arriving group. The label width becomes `B_g ≈ 30L + 47 + log₂(8g'+8)`. That is still
  `Θ(L)`, but larger than PROOF.md's `≈ 9L`.
* **The arrivals bound of C3 is untruncated.** For a splitting chunk `x`:
  `arrivals + 3·units(x) + 3·δ(family) + 3·s₀(x) ≤ 3·(unitsOf(s₀(x)) + |family|) + 3·δu(x)`.
  Moves, insertions, removals and the end of a drive all preserve it exactly.
* **The game's variables are the chunk indices `1 … n`**, with `n` fixed per core. The
  chunk count bounds the indices that occur.
* **Round accounting** (`RoundAt`/`RoundOK`). In a round, `ip·K_R ≤ js + (K_R − j)` while a
  job runs, and `ip·K_R ≤ J + (K_R − j)` otherwise (at iteration `j` of a reservation).
  This gives `ip + 1 ≤ J/K_R + 1 = R` at every insertion.
* **The chunk count** keeps ghost sizes `e c ≤ c_max` at which quiet chunks became quiet:
  `pops·(θ + 1 − c_max) + Σ_quiet (size − e) ≤ count` and `|C| = 2 + 2·pops`.

**Lemma W in Lean** (`Wrap.lean`). A rebuild in progress carries:
* the count `c₀` and live count `live₀` at the trigger;
* the insertions `I` and deletions `D` since the trigger.

The work left `Φ` is the preparation steps left plus `cur`'s count before the cursor is set,
then the elements from the cursor on. It satisfies `Φ + (K_B − 1)·I ≤ H' + c₀`: each insertion
adds at most 1 to `Φ`, and each operation's `K_B` budgeted steps remove one each
(`rebuildLoop_cost`). `nxt`'s fill satisfies `|nxt| ≤ 1 + |live copies| + D` and
`live + D = live₀ + I`, so `|nxt| ≤ 1 + live₀ + I`. These give room in `cur` (`WC.cur_room`),
room in `nxt` (`WC.nxt_room`), a quiet new `cur` after the swap, and `N' ≤ 4N`.

**What the cost proof assumes** (`CostSetup`):
* the two contracts, for every capacity;
* the parameter conditions (`proofParams` satisfies the lower-level ones);
* I5 for the game;
* `2 + 2·⌊N/(θ + 1 − c_max)⌋ ≤ n + 1, cap`;
* the preparation budget `H(N') + 1 ≤ L(N) + 2` for `N' ≤ 4N`;
* `L + 6 ≤ N/2` for `N ≥ 64`;
* `K_B ≥ 4` (an argument of `OM.init`).

**Discharged in M5** (§14): the contracts, `J`, `H`, I5, the capacity conditions and the
preparation budget all hold for `proofParams` (`costSetup`).

---

## 14. M5: the top structure at Level F

**Status.** M5 is done. Everything lives in `lean/OM/Proof/Top/` and is part of the default
build (`OM.lean` imports `OM.Proof.Top.Setup`). It compiles with no `sorry`. The axioms are
the standard three.

**Main statements** (`Setup.lean`).
* `costSetup : CostSetup proofParams TopInv topPI topMu topNu topPP topJ capT nfP RfP`:
  every assumption of the cost proof (§13) holds for the proof parameters.
* `wrapper_cost_proof`: `wrapper_cost` (§13) with no assumptions left. The structure starts in
  a state satisfying the cost invariant, and every valid operation keeps it.
* `theoremA_proof`: Theorem A (§12) for `proofParams`.

The two contracts:
* `topContract' : TopContractP TopInv topMu topJ capT` (`PresStart.lean`). A job is bounded by
  `topJ P = 13H + 2` steps; the structure holds `capT P = W_{H−1} − 1` chunks.
* `prepContract : PrepContract TopInv topPI topNu topPP` (`PrepContract.lean`). The initial
  chain `1 → 2 → … → H` above chunk 1 is built in `H + 1` steps.

**The invariant** (`Inv.lean`). `TopInv s` holds when `TopParams s.P` holds and
`InvJ (finS (ts s) s.resJob) cl ord dr n0 s.resJob` holds for the chunk list `cl`, some level
orders `ord`, insertion counts `dr` and initial table sizes `n0`. It is stated for the state
with the running job's path copy completed (`finS`). `InvJ` has five parts:
* `Shape` (§4.5.1 of `PROOF.md`): the live tree, ghosts and targets, tables, stored paths,
  range pointers and tags;
* `Timing`: stored versus true weights (F1) and the drain timing of Lemma T3;
* `Room`: label room in every table (see the deviations);
* `JobOK`: the running job's position;
* `cap`: nodes of height `H − 1` never drain.

**Proof structure.**

| Files | Content |
|---|---|
| `Inv`, `Shape`, `Struct`, `Views`, `Lists`, `Sorted`, `Labels`, `T0` | the invariant; consequences of the order invariant; list lemmas; label gaps; Lemma T0 |
| `Frame`, `Step`, `Loops`, `CopyRest`, `PresCopy`, `PresWalk` | what a job step changes; the job step (`top_step`); the path copy and the upward walk |
| `RunDrain`, `PresDrain`, `RunFinish`, `PresFinish` | funding a drain and finishing it |
| `RunIns`, `InsViews`, `InsShape`, `InsTime`, `PresIns`, `InsStart` | a chunk split's insertion into the tree and the start of its job (`top_start`) |
| `RunStart`, `StartViews`, `StartData`, `StartCtx`, `StartFrame`, `StartParts`, `StartCount`, `StartRoom`, `StartRun`, `StartTS`, `StartShapeT`, `StartShape`, `StartTime`, `PresStart` | a drain's start (`SDOK`): the cut, the two new nodes, their tables, and all of `InvJ` afterwards |
| `Contract` | `TopContractP` from the pieces |
| `PrepRun`, `PrepStage`, `PrepInv`, `PrepContract` | the initial chain: runs of `initStep`, construction stages, `TopInv` for the chain |
| `TopParams`, `Setup` | the parameter conditions for `a = 8`, `s = 11`, `β = 64`; `CostSetup` |

**Deviations from `PROOF.md`** (none weakens the bound):
* **The job measure is state-based.** `topMu` is the number of steps left in the running job
  (`jobLeft`), computed from the current state, not from a history.
* **Label room is a potential argument.** Lemma T5's insertion histories are replaced by
  `Room`. Each table `X` records its initial size `n0 X ≤ n0max` and its insertion events
  `dr X`. Its gaps are at least `2^β/(n0 + 1)/2^dr`. The potentials `pot1` and `pot2` bound
  `dr` through the true weights: a table at height `h ≥ 2` loses `γ_{h−1}` potential per
  insertion event. They give `dr + 1 ≤ Dmax`, and room needs `2^Dmax·(n0max + 1) ≤ 2^β`.
  This needs `β ≥ 62` (worst at height 3, constant from height 4), so `β = 64` (was 48).
* **The contracts are per parameter.** `TopContractP TI μ J cap` takes `J, cap : Params → Nat`.
  `TIat TI P` fixes the parameters of a core. `PrepContract` takes a condition `PP` on the
  parameters (`topPP P := TopParams P ∧ 3 ≤ H`), and `CostSetup` requires `PP (mk N)`.
* **Invariant additions.** These are not in `PROOF.md`: chain nodes `u ≤ H` have height `u`
  (`Timing.chain`); every live node has a chunk below it (`tw1`); `n0 ≤ n0max` (`Room.n0le`);
  and `InvJ.cap`.
* **`TopParams`** lists what the proof needs of `a`, `s`, `β`: `s ≥ 3`, `λ_h ≥ 2 + 2K_h`
  (I6), the room condition above (our form of I7), `Π_{h−1} ≤ W_h` and `γ_h ≥ 1`.
  `topParams_8` proves them at every height for `a = 8`, `s = 11`, `β = 64`.
* **`K_R = 8`** (was 4). Then `R = ⌊(13H + 2)/8⌋ + 1 ≤ L`, and I5 follows for every `L ≥ 8`
  from `H_m ≤ 1 + ln m` with `m < 2^(L−2)`. With `K_R = 4`, I5 still holds numerically, but
  with about 5% to spare at `L = 8`.
* **`H = ⌊L/3⌋ + 1`.** Then `2·8^(H−1) − 1` holds the chunks (`capc_proof`, using
  `θ + 1 − c_max ≥ 8`), and the preparation budget `H(N') + 1 ≤ L(N) + 2` holds for `N' ≤ 4N`.
* **The model's `startDrain`** computes the cut, weights, tables and sides with named pure
  functions (`drainCut`, `drainWt`, `drainPr`, `drainEntries`, `drainSide`). The replay
  campaign against the prototype passed 335/335 after this change.

**Left to M6.** Level M programs, their simulation of Level F, and Theorems A, B and W at
Level M.

---

## 15. M6: Level M (in progress)

**Approach: a certified translator instead of per-procedure machine proofs.** §4 planned to
prove each machine procedure against Level F with `wp`. That would repeat the same memory
reasoning for about 140 procedures, so M6 inserts a small language between the two
(`lean/OM/Impl/`):

* `Lang.lean`: the **core language**. Expressions are numbers, locals, record fields
  (`Fld`), table sizes and parameters. Statements are assignments, field writes, `push`,
  sequencing, `if`, bounded `for`, calls, `fail` (a guard), `bug` (an unreachable state) and
  `catch`. Its semantics `evalF` runs directly on Level F's `Core` and returns the outcome and
  **the machine cost**.
* `Compile.lean`: the **compiler** to machine `Stmt`, and the **encoding** `Enc p κ s m`: the core
  in slot `p` occupies the machine arrays `1000·p + code`, one per field, with capacities `κ`.
  Every default record reads 0 (Booleans are stored as `dead` bits), so freshly allocated memory
  already holds default records.
* `Sim.lean`: **one theorem, `sim`**, for every program of the language. If `m` holds `s`, the
  compiled code ends exactly as `evalF` says: same outcome, a machine state that holds the new
  core, same locals, and the same number of steps.
* Per Level F function, a **transcription** into the language and an **agreement lemma**: on
  every successful run of the Level F function, `evalF` of the transcription produces the same
  state, within a stated number of steps. These are pure Level F proofs. A write that the
  encoding cannot represent makes `evalF` return `bug`, so each agreement lemma also shows that
  every index stays within its capacity.

**Choices recorded here.**
* Machine array names are numbers (`Arr := Nat`), so that distinct arrays differ by arithmetic.
* Level F's truncated `-` becomes `Exp.monus a b = max(a,b) − b`, with `max` computed without
  branches. Neither subtraction can underflow.
* The machine has no `break`. The priority queue's downward scan (Level F's slow path, `O(s)`)
  keeps its loop, guarded by the fast-path test. Its agreement lemma covers the case where no
  scan is needed. The algorithm only adjusts a chunk's size by `+1` (the `−1` call is
  unreachable under invariant F), and that adjustment never scans (K2).
* Capacities are invariants of each module. For the queue, `PQCaps`: stored chunks are below the
  chunk capacity, and stored buckets are below the bucket capacity. Each agreement lemma assumes
  them and re-establishes them.

**Done.**
* The language (with list fields, paths, optional records), the compiler, and `sim` for every
  construct.
* The priority queue (`PQ.lean`) and the element procedures (`Elem.lean`).
* Loops: `evalF_loop` (with a state invariant) and `evalF_loop_pure` (a fold over the iterations,
  for loops that only change locals) (`Loop.lean`).
* A list library (`ListLib.lean`): find, lookup, `assocSet`, insert at an index (append, then swap
  into place), copy. Each is proved against Level F's list function.
* `startDrain` (`Cut.lean`, `Side.lean`, `TopTab.lean`, `StartDrain.lean`). `startDrainS_ok`: from
  `t` the program reaches exactly Level F's `sdS t v side`, within `sdCost` steps (polynomial in
  the lengths of `v`'s children, table and tables, all at most 160 by `TabLen`). `startDrainS_noop`
  covers the two cases where `startDrain` changes nothing. On the way: the cut (`drainCut`),
  `roomNextTo` and `tableInsert` each agree with Level F.

* Groups (`Group.lean`, `GroupStep.lean`): linking and unlinking, first/last moves, the label
  primitives, `newGroup` (reuse a freed group or push), `startGroupSplit`, removal, element moves,
  `groupSplitStep`, the drive loop and `driveGroup`.
* Chunks (`ChunkStep.lean`): removal, the moved unit (one group, or three), the new labels on the
  receiving side, `moveGroupsLeft/Right`, the size transfer, `chunkSplitStep` (both moves and the
  removal), the drive loop and `driveChunk`.
* `.bug` for unreachable branches. `groupSplitStep`'s cross-chunk branch compiles to `bug`. Under
  invariant F it never runs, just like FALLBACK. The agreement lemmas hold on runs where Level F
  succeeds, so they never reach it.

* Reservation (`Reserve.lean`, `Job.lean`, `Finish.lean`, `ListErase.lean`, `Reservation.lean`):
  `insertAround` (the program computes a table's two labels right before inserting into it; the
  tables are distinct, so the labels agree with Level F's precomputed lists), `linkChunkPair`,
  `markSplit`, `splitChunkStart`; the job's copy step, `drainStep` (move, finish, dead),
  `finishDrain`, the funding loop, `afterDrain`, the walk, and the job dispatcher; the reservation
  loop (a stop flag replaces `return`). The list library gained `eraseIdxP` and `filterP`
  (`assocErase`).
* `chunkSize`, `background`, `insertAfter` (`Background.lean`).

**Agreements as hypotheses.** A part that calls other parts is proved from *agreement
predicates* for them (`DSAgree` for `drainStep`, `SDAgree` for `startDrain`, `JobAgree`,
`SplitAgree`, `ResAgree`): for every successful Level F run of the callee, the Level M procedure
reaches the same state. Each predicate is then derived from the callee's case lemmas and Level F's
run lemma for that case. `background` is stated along Level F's trace of its five parts.

**Choices.** The machine has no exponentiation: the walk computes `a^h` by a loop of `h ≤ H`
multiplications. It has no bitwise or: a sweep step's tag fields
`(pv <<< h·β) ||| (vb <<< (h−1)·β)` occupy disjoint bits (labels are below `2^β`), so the program
adds them. Path rows have the fixed width `κ.pw`, so `drainStep`'s guard on the row length reads
`h < H`; under the invariant rows have length `H + 1`. A program without `jobSet`, `jobClear`
or `pcSet` keeps `resJob` (`NoJob.lean`, one syntactic lemma for all programs). In
`insertAfter` the guard handlers are `bug`: on the states of the cost invariant FALLBACK never runs
(`insertAfter_cost`).

**One program for every capacity.** The cores grow (`N' = 4·max(live, 16)`), but the machine
program is fixed, so the compiled code must not depend on a core's capacities. It used to embed the
path width `κ.pw = H + 1` (which grows with `N`) and the list strides `κ.lcap`. Now a path address
uses the row width read at run time from the parameter cell (`rowW p`), with `κ.pw = H + 1` an
invariant of the encoding (`Enc.pwH`). The free-group stack, the one list whose length is not
bounded by a constant, has stride 0 (`LK.stride`; it has one record, `Enc.frec`). The code
depends on `κ` only through the strides of the per-node and per-chunk lists, whose bounds (160
table entries, and so on) are constants.

**Kernel timeouts.** Rewriting or splitting the status `match` inside a hypothesis about
`driveGroup` times out the kernel. The fix: goal-side lemmas per status
(`driveGroup_split/ovf/quiet/dead`, proved by `unfold; rw`), then `rw [lemma] at h`.

**How `startDrain` is matched.** The program builds `v`'s side list first, directly in `v`'s side
list, because the later steps look sides up. Level F only writes it at the end. So after the side
list, every program state is Level F's stage `sd_k` with `v`'s side list already set
(`phiS v side sd_k`). Every later stage touches other nodes or other fields, so it commutes with
`phiS`, and the last step sets `v`'s side list anyway. The program never stores Level F's temporary
lists. `left` and `right` are built directly in the new nodes' tables, and the cut and the entry
tests are recomputed from `v`'s lists.

**Also in M5.** `TabLen` in `InvJ`: every table and side list has at most 160 entries
(`TopParams.tab`, proved for `a = 8`). The Level M loops rely on this for their constant cost.

* Construction (`Init.lean`): a new core in fresh memory (`freshC P`, every array empty) is pushed
  and written into `initState P`; `initStep` (first, middle and last steps), the eager loop, lazy
  and eager `initCore`, and `prepareStep`. The agreement for `initStep` follows from Level F's
  `Stage` invariant.

**The glue (next).** The agreement lemmas take the hypotheses of Level F's run lemmas. Level F's
proofs establish exactly those hypotheses at five places: `PresDrain` (`drainStep_move`),
`PresFinish` (`drainStep_finish`), `StartRun` (`startDrain_run`), `InsStart` (`insertAround_run`)
and `Step` (the copy step). The plan:
1. export the hypotheses at each place as a lemma from the top invariant;
2. a Level M contract `TopContractM`, `TopContract` plus the Level M agreements (`SplitAgree`
   at a split start, `JobAgree` at every job step), proved from the top invariant;
3. the same for the core's parts (`chunkSize`, group and chunk splits, the queue), from the cost
   invariant `CostInv`;
4. capacities (`Caps`) as functions of `N`, and their invariants;
5. the wrapper as machine code: each epoch's core in fresh arrays of its parity's slot, the handle
   maps as per-epoch arrays of capacity `nextHandle + N_cur + N'`;
6. Theorems A, B and W at Level M.

**Glue, steps 1 and 2 (done, `GlueTop.lean`).** Each place's hypotheses are exported from the
invariant: `Shape.drain_move_hyps`, `Shape.drain_finish_hyps`, `ins_hyps` (copied from
`top_start`'s proof), and inside `sdAgree_walk` (from `sr_hyps` and `sp_side`). The Level M side
conditions are collected in `TopCaps κ s`: record counts plus 2 below the capacities, chunk indices
below the node capacity, list capacities above the invariant's bounds (tables of at most 160
entries, entries in at most two tables). Then:
* `jobAgree`: under `TopInv`, outside a preparation, with `TopCaps`, every job step agrees at cost
  at most `jobBound = sdBound + dsBound + 300`. The five cases are copy (`copyAgree`), walk from a
  chunk, walk at a node (`walkAgree`: `startDrain` where a drain starts, else the funding loop's
  sweep step), after a drain start, and funding (`dsAgree_fund`: a ghost's sweep step moves a chunk
  or ends the drain).
* `splitAgree_top`: under `TopInv` with no job, a split start agrees at cost at most
  `splitBound`. Besides `TopCaps` it needs the path rows beyond the chunks to be zero (fresh memory).
* The bounds are constants: `dsBound`, `sdBound = sdCost 160 160 2 160 160 160`, `splitBound`.
  Every loop in these programs runs over a table, a side list, a child list or an entry's tables,
  and the invariant bounds each of these by a constant.

Level M takes the same branch as Level F at each step, so an agreement is needed only where its
branch runs: `walkS_agree` and `afterDS_agree` take each agreement under its branch's condition.

**Glue, step 3 (done, `GlueCore.lean`).** The same method for the core's parts. Each place in
Level F's cost proof is followed, and its run lemma is paired with the Level M lemma for the same
branch:
* `DriveInv.stepAgree`, `ginv_driveAgree`, `groupPhaseAgree`: group split steps, group drives,
  and the group phase (split start and drive).
* `CDriveInv.stepAgree`, `cinv_driveAgree`, `driveChunkAgree`: chunk split steps and the chunk
  phase. A chunk step costs at most 700, not 350: the move lemmas prove 700.
* `resInv_step` (the step of `reservation_cost`, as a lemma), `reservationAgreeOf`,
  `reservationAgree_top`: the reservation loop.
* `bgAgree` and `insertAgree`: the background work and a whole insertion, under the cost
  invariant `CostInv`, at cost at most `insBound P = bgBound P + 220`.

The drives also return the array sizes after them. Level F's loop lemma is rerun with the size
frames added to its invariant, so that the capacities can be checked at the next part.

The capacities are hypotheses so far: `GCaps` for the group and chunk programs, `InsCaps` at the
start of an insertion, and, for the reservation, a predicate `Mc` that gives `TopCaps`, `PQCaps`,
no preparation in progress, and zero path rows beyond the chunks, and that each round keeps.
Step 4 provides them.

**Capacities, step 4 (`Caps.lean`).** Level F bounds the element and chunk counts already:
`E.size = count + 1`, and `C.size ≤ cb P = 2 + 2·⌊N / (θ + 1 − c_max)⌋` (`CountInv.chunks`). The
other bounds are new:
* nodes, by a potential, `NodeB`: `nodes.size + topMu ≤ nb0 + topJ · C.size`. A drain start adds 2
  nodes and lowers the job measure `jobLeft` by `s ≥ 3` (`walk_nodes`). No other step adds nodes:
  the frame chains `NS` (node count) and `TP` (preparation state) are generated from `TopFrame`'s
  chain. A split start adds 2 chunks and a job of measure at most `topJ`. So `nodes = O(topJ ·
  N / L²) = O(N / L)`.
* groups: `Gs.size ≤ 2 + 2·count`. Only a group split start allocates groups (at most 2), and an
  insertion runs at most one. Free groups are reused, which only helps.
* zero path rows beyond the chunks, `PZ`: every path write is at a chunk of the list (the copy
  step, the sweep step's chunk) or at a new chunk (`insertAround`).
* chunk sizes: a live chunk's size is its element count (`CInv.csz`), at most `count`.

These are collected in `Mc κ P` (with the queue's `PQCaps`, no preparation in progress, and
`count ≤ N`). The capacity conditions `CapsOK κ P` are inequalities between the capacities and
functions of `P` (`nbMax P`, `cb P`, `N`, and constants). Then `insertAgreeM`: under `CostInv`,
`count = |L|`, `count + 1 ≤ N`, `Mc κ P s` and `CapsOK κ P`, an insertion agrees at cost at most
`insBound P`, and the result satisfies `CostInv`, `Mc κ P` and the new count.

**The wrapper, step 5 (`WrapM.lean`, `RebuildM.lean`, `OpsM.lean`, `InitM.lean`).** The machine
state holds the wrapper state as follows (`WEnc om m p`): `cur` in slot `p`, `nxt` in slot `1 − p`,
eight scalar cells from array 2000 (parity, whether `nxt` exists, cursor, cursorSet, live,
nextHandle, rebuilds, `K_B`), and the handle maps in arrays `2010 + q`. The capacity of the map of
`cur` is at least `nextHandle + (N − count)`, and that of `nxt` at least `nextHandle + (N − count) +
(N' − count')`. So every handle the wrapper will hand out before the next swap fits. The code tests
the parity once (`byPar`) and runs the code specialized to it. A swap flips the parity cell.
* The core calls (`wp_coreCall`) run the compiled core procedures in their slot; a slot's code
  leaves the other slot and the wrapper's arrays alone (`Enc.of_other`).
* Each piece of the wrapper is proved at the machine level against Level F's function: the order
  query, deletion and insertion in `cur`, their mirroring in `nxt` (`mirrorDelW_ok`,
  `mirrorInsW_ok`), the swap, a preparation step and a copy step, one iteration of the rebuild loop
  (`iterW_ok`), the loop (`loopW_ok`: `K_B + 1` iterations of a `for` loop; a local `bud` holds the
  budget, and the swap sets it to 0), the start of a rebuild (`startW_ok`: the trigger, the next
  capacity, a new core built lazily in slot `1 − p`, a zero handle map), and the whole rebuild step
  (`rebuildW_ok`).
* Each core call needs the core's cost invariant and facts about its arguments, at intermediate
  states of an operation that Level F's cost proof does not expose. `WrapSafe.lean` replays
  `rebuildLoop_cost` and records them along the run (`RLSafeF`, `rebuildLoop_safe`). It also adapts
  `rebuildStep_cost`, `insert_cost` and `delete_cost` into `rebuildStep_safe`, `insert_safe` and
  `delete_safe`, whose proofs are copies of the cost proofs with the rebuild step's call replaced.
* The Level M side conditions of the cores are carried alongside Level F's invariant:
  `MX om` = `Mc` for `cur`, and for `nxt` `PrepM` during its preparation or `Mc` once it is in
  service. The Level M invariant is `MInv om Sp = WC … om Sp ∧ MX om` (`OpsM.lean`). Every step keeps
  `MX`: an insertion or a deletion keeps `Mc` (`insertAgreeM`, `markDeadAgreeM`), a preparation step
  keeps `PrepM` or ends with `Mc` (`prepAgreeM`), a new core satisfies `PrepM` (`prepM_start`), and
  the eagerly built first core satisfies `Mc` (`eager_M`).
* `insertW_ok`, `deleteW_ok`, `orderW_okM` and `initW_ok`: each operation returns Level F's answer,
  keeps `MInv` (and `K_B`), and its machine code runs in at most `insW K_B`, `delW K_B`, 100 and
  `initB` steps. These bounds do not depend on `N`: the insertion bound `insBound P` depends only on
  the `K` parameters, which are constants of the proof parameters (`insB = 94462311`).

**Theorems A and B at Level M (`TheoremsM.lean`).** The machine program is `initWS` (with `K_B` in
local `kb`), then `opS op` for each operation (its arguments as literals; an order query leaves
its answer in local `r`). A reachable machine state holds a wrapper state with `MInv` (`Reach`).
* `init_reach`, `step_reach`: initialization reaches such a state; from one, each valid operation
  returns the specification's answer, reaches such a state again, and takes at most `opB K_B` steps.
* `theoremAB_M`: for `K_B ≥ 4` and every valid operation sequence, the machine returns exactly
  `Spec.run`'s answers, initialization takes at most `initB = 6648` steps, and every operation takes
  at most `opB K_B` steps, with `opB 4 = 1133561742` (`opB_four`). The axioms are `propext`,
  `Classical.choice` and `Quot.sound`.

The constant is large because the loops of the top structure run over tables, side lists and child
lists of up to 160 entries, and a drain start nests several of them (`sdBound`). It is a numeral
fixed by the proof parameters, the same for every `N` and every history.

**Memory (`Memory.lean`).** `memOf κ` counts the cells of all the arrays `Enc` asks for. For the
proof parameters it is `5344 + 37N + 671·cb + cb·H + 2596·nbMax + 2H` (`memOf_eq`), with
`nbMax = H + 2 + (13H + 2)·cb` and `cb ≤ 2 + 16N/L²`, so `nbMax = O(N/L)`. `core_mem`: at most
`40000·N` cells for `N ≥ 64` (measured: about `13700·N` at `N = 64`, `2000·N` at `N = 10⁹`; the
per-node lists of 162 or 322 entries dominate). `reach_mem`: in a reachable state, `cur`'s slot holds
at most `40000·N` cells, and during a rebuild `nxt`'s slot at most `40000·N'` with `N' ≤ 4N`. The
handle maps are allocated with `nextHandle + (N − count) + N'` cells, which grows with the number of
insertions (handles are the insertion counter).

**Not proved: Theorem W** (§2.1). Unit-cost unbounded words remain an assumption of the cost
model.

---

## 16. Executable code: the machine program as Rust

The machine program the theorems are about (`initWS`, `insertWS`, `deleteWS`, `orderWS`) is printed
as Rust, statement for statement, by `lean/OM/Extract/Rust.lean` (`lake exe extract`, writing
`rust/src/gen.rs`). Details and results: `rust/README.md`.

**The printer.** A machine local becomes a Rust variable (or a field of the persistent top-level
frame); a machine array becomes an index into the runtime's memory; a `call` becomes a call of a Rust
function, one per distinct callee; `fail` returns `Err(Fail)` up to the nearest `catch` (a closure).
Every statement adds the cost `exec` charges for it, and every expression node records its value in
the peak, so the generated code counts the machine's steps exactly.

**The runtime** (`rust/src/rt.rs`). Words are natural numbers of arbitrary precision (`u64`, and a
`BigUint` above 2^64): the values need about `60·L` bits (§2.1), so fixed 64-bit words would not do.
An access beyond an array's capacity or a subtraction below 0 panics (a machine error). An array's
cells live in blocks allocated when first written, so memory follows the cells used (at 4 million
elements: 57 million cells in use, against capacities totalling 33.8 billion).

**What is trusted.** The printer (about 330 lines of Lean) and the runtime (about 300 lines of Rust)
are not verified. They are checked against the machine semantics: `lake exe xrun` runs operation
files with `OM.Machine.exec` itself, and the generated code must print the same answers, the same
step count for every operation and the same peak bit length. It did on every file tried (4.3 million
steps in the two longest).

**Results.** The generated code agrees with the specification on 620,000 random operations, on the
prototype's 23 stress workloads (9.2 million records) and on 1,100 fuzz traces. The most expensive
update took 200,469 steps: the proved bound `opB 4 = 1,133,561,742` is about 10⁴ times loose on these
workloads. Operations take 1–4 µs. The time per machine step grows from about 2 to 5 ns as the
structure grows to 4 million elements, mostly from cache misses; the peak bit length follows the
predicted staircase (1,119 to 1,461 bits), stepping up when a rebuild starts.

