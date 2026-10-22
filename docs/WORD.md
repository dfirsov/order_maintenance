# Theorem W (word size): plan

Status (2026-10-22): groundwork only. `lean/OM/Proof/Word/Defs.lean` defines the stored-value
predicate and proves that the proof parameters lie below the candidate bound. No preservation
proofs exist yet. Nothing here is used by Theorems A and B.

## 1. Statement

Decided on 2026-10-16: a value is either below `2^(c·L)`, or a handle, and handles are bounded by
the number of operations (the insertion counter, as in the usual word RAM, where a word holds an
index into the input).

**Candidate bound: `wK P = 64·L`** (`Defs.lean`). It was checked against the parameter formulas,
and `params_room` proves, for every `N` (with `L = pL N ≥ 8`):

| Quantity | Proved bound | At L = 8 | Asymptotically |
|---|---|---|---|
| `B_e` (element labels) | `≤ 6L` (`Be_le`) | 28 | ≈ 2.7L |
| `B_g` (group labels) | `≤ 40L` (`Bg_le`; `HC ≤ 30L+64`, `PC ≤ 27L+56`, `log₂ PC ≤ L+1`) | 300 | ≈ 31L |
| `(H+2)·β` (a digit shifted past the top table) | `≤ 64L` | 320 | ≈ 21L |
| `UG`, `HC` (label steps `D = 2^UG`, `2^HC`) | `< 64L` | | |
| `N` | `< 2^L` (`N_lt`) | | |
| capacities | `≤ 40000·N < 2^(L+16)` (`core_mem`) | | |

`params_wB` proves that every parameter is below `2^wK`. The widest stored value is a group label
(`B_g` bits, measured ≈ 30L). The widest intermediate values are `2^B_g` (the `after` guard), `a + b`
for two labels (`B_g + 1` bits), and a digit times `2^(hβ)` (`(H+1)β` bits). All of these fit in
`64L`, with room to spare. With more work, `40L` is likely provable.

**Level F (stored values)**:
```
WB (wK P) s                       -- every field of every record, live or dead, < 2^(64L); handles excepted
OMB (wK P) n om                   -- both cores WB; element indices < 2^(64L); handles, live, nextHandle,
                                  --   rebuilds ≤ n = number of operations so far
```
The intended theorem: `OMB` holds on every reachable wrapper state. Both definitions are in `Defs.lean`.

**Machine (the peak)**: for `Reach KB m Sp` reached after `n` operations, running `opS op` gives
`m'.peak < 2^(2·64·L) + 4·n` (the constant is to be fixed). Here `L` is the larger of the two
cores' `L`, so `L(nxt) ≤ L(cur) + 2` by `N' ≤ 4N` (`reach_mem`). The `n` term covers the handles,
the handle-map capacity `nextHandle + N` (`WEnc.roomC`), and the counters.

## 2. Inventory of Level F write sites

There are about 230 numeric write sites in about 45 functions (`OM/Model/*.lean`). `Bool`, `St` and
`Side` fields are encoded as 0–3, so they need nothing. FALLBACK (`fallback`, `fbLayout`, `build`,
`relabelAll`, `tagOf`, `renumber`; about 25 sites) never runs on reachable states (`insertAfter_cost`)
and is not compiled to the machine (`insertAfterP` turns a failed guard into `bug`), so it is
**excluded**. `newElem` is dead code.

Classes:
* **R**: the value is `NIL`, a constant, a value read from the state, or a sublist of a stored list.
  It is bounded by `WB` itself (induction), so no existing invariant is needed.
* **F**: a fresh index (`E.size`, `Gs.size`, `C.size`, `nodes.size`, or `freeG`'s head). It is
  below the capacity: the record counts in `Caps.lean` (`CapsOK`, `NodeB`, `CountInv.chunks`,
  `E.size = count + 1 ≤ N + 2`).
* **Lab**: a label. Bounded locally by the guards: `after` checks `< 2^B`; `between` gives a value
  below a stored label (WB); `before` gives `b − D ≤ b`; the centre is `2^(B−1)`; `roomNextTo` gives
  `(lo+hi−1)/2 < hi ≤ 2^β`; `evenTable` gives `(i+1)·⌊2^β/(n+1)⌋ ≤ 2^β`. It needs `B ≤ K` from
  `params_room`.
* **Sz**: a size, count or weight. It needs an existing cost invariant.
* **Tag**: a chunk tag. It needs the top structure's tag invariant.
* **Ctr**: a counter that grows with history. **Flagged**.

| Function (file) | Numeric sites | Values written | Class / source of the bound |
|---|---|---|---|
| `newGroup`, `newChunk` (Core) | 3 | `chk := c`, defaults, `freeG := rest` | R |
| `chunkSize` (Core) | 1 | `size ± 1` | Sz: chunk sizes ≤ T + slack (`CInv`, Lemma C; `cparams_proof`) |
| `linkElem` (Core) | 11 | `grp`, `prev := x`, `next` (R); `lab` (Lab); `prev/next/tail/last := y` (F); `G.size + 1`, `count + 1` (Sz) | group sizes: `GInv.quiet/split/ghO/ghS`, Lemma G; count: `E.size = count + 1`, `Caps` |
| `insertElem` (Core) | (label for `linkElem`) | `after` / `between` | Lab |
| `linkGroupPair` (Core) | 17 | sibling links, `src`, `l`, `r`, `firstGroup`; `labL`, `labR` | R / F (new groups); Lab (`labBefore`, `labAfter`) |
| `unlinkGroup` (Core) | 10 | links, `NIL`, `freeG := g :: …` | R |
| `moveFirstLeft`, `moveLastRight` (Core) | 14 | `first/last`, `grp`, `lab` | R; Lab (centre / `after` / `before`) |
| `removeGroup`, `removeChunk` (Core) | 2 | `src := NIL` | R |
| `groupSplitStep` (Core) | 2 | `size − 1`, `size + 1` | Sz: Lemma G (family sizes) |
| `moveGroupsLeft/Right` (Core) | 14 | chunk `first/last`, group `chk`, `lab` | R; Lab (`pushBackLabs`, `pushFrontLabs`) |
| `moveSizes` (Core) | 2 | `size − moved`, `size + moved` | Sz: Lemma C (family sizes, `CInv`) |
| `linkChunkPair`, `markSplit` (Core) | 14 | links, `l/r/src`, `resJob := {x,y,z,copy 1}` | R / F |
| `reservation` (Core) | 1 | `resJob := jobStep …` | R (job fields below) |
| `initState`, `initTop` (Core) | 18 | 1, centres `2^(B−1)`, `prep` | proved: `initState_wB` |
| `resetTop`, `newNode` (Top) | 5 | empties; `height := h ≤ H` | R |
| `setPath`, `setPathAt`, `setLpar`, `setInTables` (Top) | 5 primitives | node indices, index lists | R / F |
| `guardedSetTag` (Top), called from `insertAround`, `drainStep` | 3 | `tx − f1x + ly`; `tag − old + new` | **Tag**: `Shape.tags` (`tag c = tagF c`) and table labels `< 2^β` (`GapsGe`) give `< 2^(Hβ)`; `insertAround` needs a small arithmetic lemma, because `y`'s path is copied later |
| `tableInsert` (Top) | 2 | `(new, lab)`, `side` | Lab (`roomNextTo`), R |
| `initStep` (Top) | 15 | node fields, centre `2^(β−1)`, `prep.h + 1 ≤ H + 1`, `prep.tag ||| c·2^((h−1)β)`, `C.tag := prep.tag` | R / F / Lab; the prep tag `< 2^(Hβ)` by induction on `h` |
| `startDrain` (Top) | 25 | two new nodes, tables (`evenTable`), `addTable`, `setParent`, children, `weight := Σ`, `livePar`, `overflowOf`, `t1/t2`, `side` | R / F / Lab; weights Sz: `Timing.wts` (stored weight = true weight `tw ≤ #chunks`) |
| `dropTable`, `dropEntry`, `release`, `finishDrain` (Top) | 5 | sublists, `NIL`, `[]` | R |
| `drainStep` (Top) | 10 | tag (Tag), path entry `t`, `first/last` | R; Tag |
| `insertAroundFinish`, `joinChunk` (Top) | 5 | tables, path row `NIL`s, `lpar`, children, job | R |
| `walkBody` (Top) | 1 | `weight + 2` | Sz: `Timing.wts` (stored weight + pending 2 = true weight `tw ≤ #chunks`); for non-roots also `wA`/`wB` (`≤ Wd h + 2 = 2a^h + 2 ≤ 2^(L+5)`) |
| `fundLoop`, `afterDrain`, `jobStep` (Top) | 8 | job pc (`k + 1 ≤ s`, `l + 1 ≤ H + 1`), path copy, `first/last := y/z` | R |
| `pqLinkAfter`, `pqAdd`, `pqDel` (PQ) | 24 | bucket links, chunk links, `pqWhere := s`, `pqHi/pqLo` | R / F; bucket `s` = a quiet chunk's size: Sz (`PQC`, Lemma C) |
| `pqInsertScan` (PQ) | 1 | `pqScan + 1` | **Ctr, flagged** |
| `copyAtCursor`, `mirrorInsert/Delete`, `swap` (Wrapper) | 6 | `nxtIdx`, `cursor`, `cur/curIdx := nxt/nxtIdx` | F (element index), R |
| `rebuildStep` (Wrapper) | 2 | new core, `rebuilds + 1` | `params_wB`, `initState_wB` + `initTop`; **Ctr** (≤ n) |
| `insert`, `delete` (Wrapper) | 5 | `Elem.h := hy`, `nextHandle + 1`, `curIdx`, `live ± 1` | handle and counters: **Ctr** (≤ n); F |

**Sites with no existing invariant:**
1. **`pqScan`** is the queue's slow-path counter (`pqInsertScan`; compiled as `.wsc .pqScan (.sc
   .pqScan + 1)` in `Impl/PQ.lean`). It is never read. `pqEnterIfAbove` can take the slow path, so
   the counter grows with history, and no invariant bounds it. There are two ways to deal with it:
   (a) remove it from Level F and Lang. It is instrumentation, and the change touches
   `Model/PQ.lean`, `Impl/PQ.lean` and the `SF` enumeration, about 100 lines. Or (b) prove
   `pqScan ≤ T·n`, a history bound like the handles'. **Recommended: (a).**
2. **`fallbacks`**: incremented only by FALLBACK. It stays 0 on reachable states, and it is never
   written by the machine program. This needs a one-line frame fact; it is new but trivial.
3. **Wrapper counters** (`live`, `nextHandle`, `rebuilds`) ≤ n, and handles `Elem.h < nextHandle`.
   The handle part exists (`CopyOK`, `Correct/Handles.lean`). The counter part is a trivial new
   induction (each operation adds at most 1).

Every other site is bounded either by `WB` itself (R), by record counts that are already proved (F),
by local guard arithmetic (Lab), or by an existing cost or top invariant (Sz, Tag). Two Sz/Tag
sites need small new arithmetic lemmas: the tag of a new chunk before its path is copied, and the
weight sums in `startDrain`.

`WB` is stated over **all** records, live or dead, because freed groups are reused (`freeG`). The
cost invariants speak only about live records, so they are used only at the moment of a write,
never as the invariant itself.

## 3. The machine side

**Peak and the simulation.** `State.peak` is ghost state, raised by `bump` with `Expr.maxv`, the
maximum over an expression and all its subexpressions, at every `assign` and `store` (and in the
other statements that evaluate expressions). `Enc` (`Impl/Compile.lean`) ignores `peak` entirely
(`Enc.bump`), and `sim` (`Impl/Sim.lean`) says nothing about it. So the existing proofs give no
peak information at all, and a peak bound needs new reasoning about every evaluated expression.

**What the expressions compute** (program text, not proof text):
* **Shifts (15).** `1 <<< B_e`, `1 <<< (B_e−1)`, `1 <<< B` (labels; `Elem`, `GroupStep`, `Group`,
  `Init` ×2, `ChunkStep`); `1 <<< β` (`TopTab`, `StartDrain`); `1 <<< (β−1)`, `1 <<< ((h−1)β)`
  (`Init.isBuild/isUp`); `1 <<< (hβ)`, `1 <<< ((h−1)β)` (`Job` drain step); `1 <<< (msb a · ht)` =
  `a^ht ≤ 2^(L+3)` (`Job.powS`); `1 <<< UG`, `1 <<< HC` (`Params`). Every shift amount is a parameter
  or `height·β` with height ≤ H, so every shifted value is `≤ 2^((H+1)β)` or `≤ 2^B_g`.
* **Multiplications.**
  - Lang programs, about 15: digit × power in the drain step (4); `h·β` (2); `msb a · ht`; `2·pw`;
    `ctr · 2^((h−1)β)` and `(h−1)·β` (`Init`); `idx · st` (`evenTable`); and boolean products
    `Exp.max` / `Exp.ifz` (3 uses).
  - Compiled list and path indices: `i·stride + j` (6 in `Compile.lean`), each below the array
    capacity, which is at most `40000·N`.
  - `Params`: 16, all polynomials in `L` and `N`, plus `tsubE`'s boolean products.
  - `RebuildM`: 1, `4·(live + …)` in the next capacity.
  - Allocation sizes in `Fresh`: `lrec·lcap`, `kC·kW`, each at most `40000·N`.
* **msb (3)**, all in `Params`: `L = msb N + 1`, `log₂(G + kG)`, `log₂ PC`.
* **Machine-only code.** `WrapM`, `RebuildM`, `OpsM`, `InitM` and `NewCore` have no shifts. The
  only multiplication is the one in `RebuildM`; otherwise there are additions and subtractions on
  the counters, the handles, the cursor and the parity (`wa 0`, 0/1; there is no epoch stamp at
  Level M). The handle maps `wIdx` are indexed by handles. Their capacity is
  `nextHandle + (N − count)` (`WEnc.roomC`), so the allocation size and the indices are `≤ n + N`.

## 4. Two approaches for the intermediate values

**(i) A separate peak function.** Define `Exp.pk κ s L e`, which mirrors `Expr.maxv` of the
compiled expression, and `pkF κ c s L`, which mirrors `evalF`'s run and takes the maximum of `pk`
over every evaluated expression. Extend `sim` once: if `evalF` returns `ok`, then
`m'.peak = max m.peak (pkF …)`. This is the same pattern `sim` already uses for the cost. Then prove
`pkF ≤ M` for each procedure, given `WB` and bounds on the locals. Proofs follow the program's run,
reusing the values that the agreement lemmas establish.
* *Pros*: no existing proof changes; the obligations sit in new files; the per-procedure proofs can
  cite the agreement lemmas.
* *Cons*: it duplicates the run structure of each procedure (a second walk through 86 agreement
  theorems' worth of programs); the locals need their own bounds at every program point.
* *Variant (i′)*: a generic lemma bounding the whole expression. If every leaf (local, field read,
  parameter, size, literal) is below `2^K`, and every shift amount is a parameter or a height times
  β, then an expression of depth `d` has peak below `2^(c_d·K)`. With it, the per-procedure work
  shrinks to "every local is below `2^K` at every program point", an invariant over about 230
  assignments. Most of them are reads, so they are automatic; the arithmetic ones are the same
  Lab/Sz cases as §2.

**(ii) A check folded into `evalF`.** Add `wmax : Nat` to `Caps`, and make `evalF` return `bug`
when an evaluated expression's `pk` exceeds `κ.wmax`. Then `sim` gives `m'.peak ≤ max m.peak
κ.wmax` almost for free, and the agreement lemmas, which already prove `≠ bug`, prove the bound
too.
* *Pros*: one mechanism, and the bound rides on proofs that already exist.
* *Cons*: every `evalF` evaluation lemma gains a side condition. There are about 780 call sites
  (`evalF_assign*` 295, `evalF_ite*` 260, `evalF_wr*` 126, `evalF_call*` 71, `evalF_loop*` 29). The
  agreement lemmas would also need `WB` and local bounds threaded through as hypotheses. That is a
  refactor of most of the 20.8k lines of `OM/Impl` that Theorems A and B depend on, so it carries a
  high risk of a long red build.

## 5. Effort estimate

The baselines are `Impl/Caps.lean` (1,093 lines; a predicate preserved by every Level F step, using
the `Pres`/`pres` framework, over a few record counts), the cost files (`Proof/Cost`, about 13k lines),
and `OM/Impl` (20.8k lines, 86 agreement theorems).

**(B) Stored values only** (Level F `WB` plus wrapper `OMB` on reachable states):
* `Pres` lemmas for the write primitives (`modE/G/C/N`, `setX`, `push`, list operations): about 400
  lines;
* per-function preservation for about 45 functions, mostly R/F/Lab, which `pres` automates:
  about 1,500–2,500 lines;
* Sz/Tag sites tied to the cost and top invariants, plus the two arithmetic lemmas: about 500–800
  lines;
* `pqScan` removal (a): about 100 lines;
* wrapper `OMB` and the counters, connected to `MInv`/`Reach`: about 400–700 lines.

**Total: about 3,000–4,500 lines.**

**(A) The full peak bound**, which is (B) plus the following:
* approach (i′): `pk`/`pkF` and the `sim` extension, about 600–1,000 lines; the generic expression
  lemma, about 300–500; local bounds through the Lang procedures, about 2,500–4,000;
* machine-only code (`Params`, `NewCore`, `InitM`, `WrapM`, `RebuildM`, `OpsM`), with a peak-tracking
  `wp` rule or a peak-monotone lemma: about 800–1,500 lines;
* the final theorem: about 200 lines.

**Total: about 7,500–11,500 lines.** Approach (ii) would be of similar size, but it rewrites
existing proofs instead of adding new ones.

**Recommendation.** Do (B) first, with the `Pres` framework at Level F, starting with removing
`pqScan`. Do it so that `WB` is exactly the leaf-bound hypothesis that (i′) needs, then do (A) with
approach (i′). Avoid (ii): it puts Theorems A and B at risk.
