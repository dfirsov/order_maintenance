# Theorem W (word size): plan

Status (2026-10-23): option (B) done (stages B1–B3). `theoremW_stored`
(`lean/OM/Proof/Word/Wrap.lean`) proves `OMB` on every wrapper state reached by initialization and
`t` valid operations: every value stored in either core is below `2^K`, `K = 64·L` for the larger `L`
of the two cores, handles excepted; element indices and the cursor are below `2^K`; handles and
counters are at most `t`. Not proved: the machine's peak (option A: the intermediate values of
expressions and the loop locals); its infrastructure (stage A1) is done, §7. Nothing here is used by
Theorems A and B. Design: §6.

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
Both definitions are in `Defs.lean`. **Proved** (`theoremW_stored`, `Word/Wrap.lean`): for `4 ≤ K_B < 2^512`
and every `om` with `ReachW K_B t om Sp` (reached by `OM.init` and `t` valid `OM.apply` steps),
`OMB (wKom om) t om`, where `wKom om = max (wK cur.P) (wK nxt.P) = 64·max(L_cur, L_nxt)`.

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
| `pqInsertScan` (PQ) | 0 | none (its counter `pqScan` was removed on 2026-10-22) | |
| `copyAtCursor`, `mirrorInsert/Delete`, `swap` (Wrapper) | 6 | `nxtIdx`, `cursor`, `cur/curIdx := nxt/nxtIdx` | F (element index), R |
| `rebuildStep` (Wrapper) | 2 | new core, `rebuilds + 1` | `params_wB`, `initState_wB` + `initTop`; **Ctr** (≤ n) |
| `insert`, `delete` (Wrapper) | 5 | `Elem.h := hy`, `nextHandle + 1`, `curIdx`, `live ± 1` | handle and counters: **Ctr** (≤ n); F |

**Sites with no existing invariant:**
1. **`pqScan`** (done, 2026-10-22). The queue's slow-path counter was incremented by `pqInsertScan`
   and never read, so it grew with the history and no invariant bounded it. It was removed from
   Level F (`Model/State.lean`, `Model/PQ.lean`), from `SF`, from the compiled layout and from the
   machine program (option (a)); the step bounds did not change.
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

**Recommendation.** Do (B) first, with the `Pres` framework at Level F (`pqScan`, the
one site that blocked it, is removed). Do it so that `WB` is exactly the leaf-bound hypothesis that (i′) needs, then do (A) with
approach (i′). Avoid (ii): it puts Theorems A and B at risk.

## 6. B: proof design

**Shape.** `WB K` is not added to the cost invariant, and no existing proof changes. Every write
lemma takes the bound of the value it writes as an explicit hypothesis; the bounds that need a
reachable state are discharged where the cost proof already holds that state's invariants:

* **The framework** (`Word/Pres.lean`). `HT K P0 m Q` is a Hoare triple at fixed parameters `P0`:
  from a state with `WB K`, every run of `m` (normal or ended by a guard) ends in such a state, and a
  normal result satisfies `Q`. Reads return bounded values (the result predicate of `get` is `WB K`
  itself), so a value read from the state and written back needs no invariant (class R). The tactic
  `ht` decomposes a computation like `pres`; `wbx`/`wbv` close the update goals component by
  component (`setX`, `modify`, `push`, `set!`, records updated with bounded values).
* **Classes R and Lab** (`Word/PQ.lean`, `Word/Core.lean`). Triples with no state hypothesis: every
  queue operation, `between`/`after`/`before`, `labBefore`/`labAfter`, the push labels, `moveElem`,
  `moveUnit`, `removeChunk`, `markDead`, `key`/`order`. Labels need only `LabRoom K P`
  (`B_e, B_g ≤ K`, `K ≥ 1`).
* **Class Sz** (`Word/Hooks.lean`). A live group's size is its run in the element list `L`
  (`GInv.sz`), a live chunk's is its element count (`CInv.csz`); both are at most `|L|`. A group move
  adds one element to a live sibling (`≤ |L| + 1`); a chunk move adds at most three live groups to a
  live sibling (`≤ 4·|L|`, `unit_live`). These facts are read inside the cost proof's own hooks for
  extra invariants: `XGroup`/`XSteps` for the group drive (`xgroup_wb`), `CXSteps` for the chunk
  drive (`cxsteps_wb`; `CXSteps.andRun` gets the move's labels from the run that `cxsteps_linv`
  provides), and `CostInv` for the insertion and its chunk-size update.
* **Class F.** The element index is `E.size`. A group phase allocates at most two groups, at its one
  split start; the hook predicate `XG` records the room (`Gs.size ≤ G0`, or every quiet group is below
  `G`, so no split can start). A chunk split adds two chunks; the room is read off the state after
  it, whose `CountInv` gives `C.size ≤ 2 + 2·count` (sizes only grow, `reservation_wb`).
* **Dead records.** `WB` covers every record by induction; the cost invariants are used only at the
  moment of a write, and every Sz/F write of a reachable step targets a live record (the hook
  contexts say so). A record freed and reused through `freeG` is rewritten by `allocGroup` with
  bounded values.
* **Composition** (`Word/Insert.lean`). `background_wb` and `insertAfter_wb` follow `background_ok`
  and `insertAfter_cost` line by line, running the phase lemmas (`groupPhase_ok`, `cinv_drive`,
  `reservation_ok` with `resInv_step`) with the extra hooks; each phase's end state is identified
  with the cost proof's by its run equation.
* **The top structure** enters through `TopWB K TI μ` (`Word/Insert.lean`): `start` (the run of
  `insertAround` from the state after `linkChunkPair`) and `step` (`jobStep`). Both take the top
  invariant of the state *after* the operation as a hypothesis (the reservation's iteration
  invariant `ResInv` holds there), and it bounds the tags the operation writes. `step` also takes
  room for two fresh nodes (`nodes.size + 2 ≤ 2^K`) and `C.size ≤ 2^K` (for the weights), and
  returns that `nodes.size + μ` does not grow; `start` returns `nodes.size` unchanged. With these,
  `reservation_wb` keeps a node budget `nodes.size + μ ≤ NB0 + J·C.size` (the shape of `NodeB`,
  `Impl/Caps.lean`): a split start adds two chunks and a job of measure at most `J` (from
  `RoundAt`), and a job step does not grow the sum.
* **Stage B2: `topWB`** (`Word/TopWB.lean`) proves `TopWB K (TIat TopInv P) topMu`, given
  `TopRoom K P` (`β ≤ K`, `H·β ≤ K`) and `K ≥ 1`. It follows the cost proof's own case analysis
  (`top_step`, `walk_run`, `fund_run`) and proves `WB` of the explicit final states the cost proof
  computes (`Word/TopB.lean`, `Word/TopStep.lean`): `copyC` (a copy step), `wiC` (the walk's weight
  update), `sdS` (a drain start, through its stages `sd1 … sd10`), `dsS` (a sweep), `fdS` (the end of
  a drain). By class:
  - **Tag**: a tag in the state after the step spells the chunk's path (`Shape.tags`), so it is
    below `2^(H·β)` (`tag_lt_of_topInv`, from `tagUp_lt` and `ShapeT.digit_lt`). A sweep writes the
    tag of `dsY ∈ cl`; a split writes those of the two new chunks, and `insertAroundFinish` leaves
    the chunk records alone (`cs_insertAroundFinish`), so their final tags are the written ones.
  - **Sz**: the walk's `weight + 2` is the true weight (`Timing.wts`; the walk node is on the
    pending chain), at most `|cl| < C.size` (`walk_weight`); a drain start's new weights are sums of
    children's stored weights, at most their true weights, which add up to the drained node's
    (`Shape.tw_kids`, `Shape.tw_one`; `walk_sum`).
  - **F**: the two fresh nodes of a drain start (the `step` hypothesis) and the new chunks of a split
    (the `start` hypothesis); the node budget across a step is `node_step`.
  - **Lab**: `roomL`/`roomNextTo` (below the upper neighbour: a label or `2^β`), `evenTable` (below
    `2^β`), the centre `2^(β-1)`.
  - **R**: node indices, entries, side keys (`drainSide_keys`), sublists (`filter`, `erase`,
    `assocErase`, `replace1`), `NIL`.
  The split's insertion (`Word/TopStart.lean`, `insertAround_wb`) uses `HT` triples for its
  read-only part (`ht_insertAroundPrep`, `ht_roomNextTo`) and its finish (`ht_insertAroundFinish`,
  `ht_tableInsert`).
* **The construction** (`Word/TopStart.lean`): `initStep_wb` follows the stages of `Stage`
  (`Top/PrepStage.lean`): a chain node of index `nodes.size = h`, the prep tag
  `chainTag P h < 2^(hβ)`, the next height `≤ H + 1`, and at the end the stored path and tag
  (`PrepRoom K P` adds `1 ≤ H`, `1 ≤ β` and `H + 1 < 2^K` to `TopRoom`). Then `prepareStep_wb` (on a
  core with `topPI`, or ready), `initCore_wb` (eager: the loop of stages, `wb_initLoop`; lazy:
  `wb_prepStart`) and `newCore_wb`. `room_wK` gives `LabRoom`, `TopRoom` and `PrepRoom` at
  `K = wK = 64·L` for the proof parameters.
* **Stage B3: the wrapper** (`Word/Serve.lean`, `Word/Wrap.lean`). Each core is bounded at its own
  word size `wK c.P` (fixed for the core's life; `WB.mono` lifts it to the larger one).
  - `InService.wb`: an insertion into a core in service keeps `WB (wK c.P)`. `InService` (Level M's
    context of every core insertion of the wrapper: `CoreOK` with `CostInv`, the room
    `count + 1 ≤ N`, and `Mc`) gives `insertAfter_wb_top` all its hypotheses: `NodeB` and
    `Gs.size ≤ 2 + 2·count` from `Mc`, `E.size ≤ count + 1` (`E_size_le`), and all numeric conditions
    are below `2^(2L + 8)` (`room_counts`). `newCore_wK`, `PrepM.wb`, `copy_wb` do the same for a
    fresh core, a preparation step and a copy step.
  - `WBW t om nx`: both cores bounded at their `wK`, the index arrays and the cursor at their core's
    `wK`, every handle stored in a core `≤ nextHandle` (the insertion frame `InsFrame.h`, through
    `InService.hframe`; preparation steps keep `E`, `pres_prepareStep`), the counters `≤ t`.
  - `loop_wb` follows the rebuild loop along Level M's loop context `RLSafe` (from `loop_M`):
    `PrepM` for each preparation step, `CopyOK` (hence `InService` at `nxt`'s tail) for each copy
    step, and the swap (at `cursor = NIL`; `curIdx := nxtIdx`). `rebuild_wb` adds the rebuild start
    (`wb_prepStart`). `mirror_wbw` and `mirrorDel_wbw` cover the mirrored operations (`MInv.mirror`).
  - `insert_step`, `delete_step`, `apply_step`, `init_step` keep `MInv` (as `insertW_ok`,
    `deleteW_ok` and `initW_ok` do at Level F) together with `WBW`; `reachW_inv` is the induction
    over `ReachW`, and `theoremW_stored` lifts `WBW` to `OMB (wKom om) t`.

**The statement** (`insertAfter_wb`): `CostInv` and the hypotheses of `insertAfter_cost`, `WB K s`,
`LabRoom K s.P`, `4·E.size + 8 ≤ 2^K`, `Gs.size + 2 ≤ 2^K`, `2·count + 4 ≤ 2^K`, `TopWB K TI μ`, the
node budget `nodes.size + μ ≤ NB0 + J·C.size` and `NB0 + J·(2 + 2·(count + 1)) + 2 ≤ 2^K` give `WB K`
after the insertion. `insertAfter_wb_top` is the instance at `TIat TopInv P`, `topMu`, `topJ P`, with
the budget `NodeB s` (`NB0 = nb0 P = H + 2`) and `TopRoom K P`. At `K = wK P = 64·L` the numeric
conditions follow from `count ≤ N`, `E.size = count + 1`, `Gs.size ≤ 2 + 2·count` and `NodeB`; the
last two are in `Mc` (`Impl/Caps.lean`), a predicate on Level F cores that the Level M invariant
`MX` carries for `cur` and, once copying has started, for `nxt` (`InService` bundles it with
`CoreOK` for every core insertion of the wrapper).

**Lines.** Stage B1: about 1,730 lines (`Pres` 483, `PQ` 58, `Core` 503, `Hooks` 313, `Insert` 371).
Stage B2: about 1,480 lines (`TopB` 540, `TopStep` 284, `TopStart` 448, `TopWB` 95; `Insert` +113
net: the new `TopWB`, the node budget in `reservation_wb`, the frame lemmas `ts_*` for `TopSame`).
Stage B3: about 730 lines (`Serve` 180, `Wrap` 551). **Total for (B): about 3,940 lines.**

**What remains**: option (A), the machine's peak (§3, §4): a bound on every intermediate value of an
expression and on the loop locals of the machine program, given `WB` as the bound of every value read
from memory (approach (i′) of §4). Estimate as in §5, minus (B): about 4,500–7,000 lines.

## 7. Option (A): status

Approach (i′) of §4, in four stages: A1 infrastructure, A2 the core-language procedures, A3 the
machine-only code, A4 the final theorem. **Stage A1 is done** (2026-10-27, about 1,870 lines, no
existing file changed except `OM.lean`; nothing is used by Theorems A and B):

* **The peak on Level F** (`Impl/Peak.lean`). `Exp.pk κ s L e` is `Expr.maxv` of the compiled
  expression, including the compiler's index arithmetic (`i·stride + j`, `c·(H+1) + j`, the parameter
  index); `Exp.maxv_compile` proves the equality whenever `e` evaluates. `pkF κ c s L` follows
  `evalF`'s run and takes the largest `pk` of every evaluated expression (loop bounds, call arguments,
  the expressions inside the compiled `push`, `lgrow`, `lshrink`, `prepInit`, `jobSet`, …). Rules for
  stage A2: `pkF_seq_ok/_le/_fail`, `pkF_ite`, `pkF_call`, `pkF_catch_ok/_fail`, `pkFor_le`,
  `pkF_loop_le` (a loop invariant).
* **The one-time extension of `sim`** (`Impl/PeakSim.lean`): `sim_peak` says that when `evalF κ c s L`
  ends `ok` or `fail`, the compiled run from a state holding `s` ends with
  `peak = max m.peak (pkF κ c s L)` (an equality). `sim` itself is unchanged.
* **The generic expression lemma** (`Impl/PeakBound.lean`). Widths are computed from the syntax:
  `Exp.wv Γ K KH S` (value) and `Exp.wp Γ K KH S` (peak), with `Γ x` the width of local `x`, `K` that
  of every value read from the core, `KH` that of the handle field `Elem.h`, and `S` a bound on every
  shift amount. `Exp.wd_sound`: under `MemW K KH κ s` (the leaves read from the core), `CapsW K κ`
  (the capacities, for the index arithmetic), `∀ x, L x < 2^(Γ x)` and `ShOK` (every evaluated shift
  amount `≤ S`; `shOK_of_noShl` for expressions without shifts), an expression that evaluates to `v`
  has `v < 2^wv` and `pk < 2^wp`. For a concrete expression `simp [Exp.wp, Exp.wv, BinOp.wd]` computes
  the width as a term in `K`, `S` and the `Γ` of its locals and `omega` compares it with a target (for
  example `pv·e1 + vb·e0` of the drain step gets `2K + 2` when `Γ e1 = Γ e0 = K + 1`). The closed form
  `Exp.wp_le_depth`: width `≤ 2^depth · (K + S)`. `lt_pow_max_add` splits a width `max K KH` into
  "below `2^K`, or at most twice a handle", the convention of §1.
* **The leaves from option (B)** (`Proof/Word/PeakLeaf.lean`): `memW_of_enc` derives `MemW K KH κ s`
  from `WB K s`, handles below `2^KH`, `K ≥ 3`, the encoding (sizes, list lengths, `pw = H + 1`) and
  capacities below `2^K`.
* **Machine-only code** (`Impl/PeakM.lean`, `Impl/PeakCall.lean`).
  - The peak is ghost: `exec_raise` (raising the initial peak raises the final one, nothing else
    changes), hence `peak_exec : (exec c s).st.peak = max s.peak (dpk c s)`, where `dpk c s` is the
    peak of the run from `s` with the peak reset to 0, i.e. the largest value the run computes;
    `exec_reset`, `peak_le_exec`.
  - `wpB B c Q s`: `wp` with a peak budget (the final peak is at most `max s.peak B`). Rules:
    `wpB_skip`, `wpB_assign_g`, `wpB_store_g`, `wpB_alloc_g` (the state-forgetting form of the
    `wp_*_g` rules the machine-only proofs use), `wpB_seq`, `wpB_ite`, `wpB_call`, `wpB_catch_ok`,
    `wpB_loop`, `wpB_of_wp` (a `wp` proof plus `dpk ≤ B`), `wpB.wp`, `wpB.peak_le`, `wpB_mono`. Each
    rule adds one side condition per evaluated expression, `maxv ≤ B`.
  - `wpB_coreCall`: `wp_coreCall` with a budget: a call of a compiled core procedure stays within `B`
    when its arguments' `maxvList` and the body's `pkF` are at most `B`. This is where stage A2's
    bounds enter stage A3.
  - The machine expression lemma `Expr.wdM_sound` (widths `Expr.wvM`/`wpM` per local and per array),
    stated only for the leaves the expression reads (`Expr.LeafB`), because the initial state of
    `theoremAB_M` has arbitrary locals and memory; `maxvList_lt` for argument lists.

**The proposed final theorem** (A4). Per operation, using the reset peak, so that the history's peak
(and the arbitrary `m₀.peak`) does not enter:

```
-- the machine states: after initialization, and after each operation
def runSt (m : State) : List Op → List State      -- m, then exec (opS op) of each, in order
-- Level F's wrapper states: OM.init K_B, then OM.apply of each operation (as in `ReachW`)

theorem theoremABW_M {m₀ : State} {KB : Nat} (hkb : m₀.loc "kb" = KB) (h4 : 4 ≤ KB) (h512 : KB < 2 ^ 512)
    (ops : List Op) (hv : Spec.Valid Spec.State.empty ops) :
    <the conclusion of theoremAB_M> ∧
    dpk initWS m₀ < 2 ^ W₀ ∧
    ∀ i < ops.length, ∃ om p, ReachW KB i om Sp_i ∧ WEnc om (runSt (exec initWS m₀).st ops)[i] p ∧
      dpk (opS ops[i]) (runSt (exec initWS m₀).st ops)[i] < 2 ^ (2 * (wKom om + 128) + c₀) + c₁ * (i + 1)
```
(pseudo-code: `Sp_i` is the specification state after the first `i` operations.)

* `m₀` is arbitrary except `kb`; `dpk` ignores `m₀.peak`, and `Expr.LeafB` lets the proof ignore
  locals and arrays that initialization does not read. `KB < 2^512` is the hypothesis of
  `theoremW_stored` (`2^512 ≤ 2^(64·L)`, `L ≥ 8`), since `K_B` itself is read and stored.
* **The capacity `L` varies over the history.** Operation `i` is bounded by the word size of the
  wrapper state *before* it (`wKom om = 64·max(L_cur, L_nxt)`); the `+ 128` covers a core created
  during the operation, whose `N' ≤ 4N` gives `L' ≤ L + 2` (`reach_mem`). The cumulative form
  follows by `peak_exec`: the peak after `t` operations is at most `max m₀.peak` of the bounds of
  the operations so far, i.e. `2^(c·L_max)` with `L_max` the largest `L` of the history (a retired
  core with a larger `L` did compute larger values earlier).
* **Handles**: an operation's arguments are handles (`opS` assigns them as literals), at most the
  insertion counter `≤ i`; the handle maps' capacity is `nextHandle + (N − count) ≤ i + N`
  (`WEnc.roomC`). With handles at width `KH = log₂(i+1) + 1`, `lt_pow_max_add` turns the width
  bound `max(2K + c₀, KH + c)` into the sum above.
* The constants `c₀`, `c₁`, `W₀` are fixed by stages A2–A3 (the widest expressions seen so far:
  digit × `2^(hβ)` and `ctr · 2^((h−1)β) + tg`, width `2K + 2` with `K = 64·L`, `S ≤ K`).

**Stage A2 is done** (2026-10-27). Its first part (about 4,900 lines in 15 new files, `Impl/PeakW`,
`PeakSafe`, `PeakHP`, `PeakFrame`, `PeakCore1`, `PeakCore2`, `PeakChunk`, `PeakDrive`, `PeakTop1`,
`PeakTop2`, `PeakDrain`, `PeakInit`, `Proof/Word/PeakPhase`, `PeakInitTop`, `PeakTop`; A1's
`PeakBound` (`MemW.fld` only below the capacity, `CapsW` gains `tbl`, `pw`, `arr`, `lcap2`) and
`PeakLeaf` (`vb_of_WB`, `gd_of_WB`) adapted; no other existing file changed except `OM.lean`; no
`sorry`; nothing is used by Theorems A and B) is described first; the spike and the completion
(`insertAfter`, about 1,900 more lines in 7 new files) follow below.

* **The invariant** `Gd K KH κ Γ s L`: `s` is encodable (`EncOK`), its stored values are bounded
  (`VB`: fields `< 2^K`, handles `< 2^KH`, lists, path rows, options, and `PRoom K s.P`: `β + 9 ≤ K`,
  `(H+1)·β ≤ K`, `log₂ a · H ≤ K`, …), and `L x < 2^(Γ x)`. `VB` is preserved by every write primitive with a bounded
  value (`VB.set/push/lset/pwr/rowReset/prep*/job*`). `gd_of_WB` gives `Gd` at entry from `Enc`,
  `WB K s` (option B), handles `< 2^KH` and `PRoom`.
* **Syntactic safety** `Stm.Safe K KH Γ W` with sharper widths (`Exp.vw`: `max`-shapes, 0/1
  factors, division by a literal; `Exp.wq`: peak) and `Stm.safe_run`: a safe statement keeps `Gd`
  and its peak is `< 2^W`. Closed by `safe_tac` for most procedures (the PQ, list helpers, `order`,
  `markDead`, label helpers, `newGroup`, group links, `drainSide`, …).
* **The other sites**, by a forward rule set `PK`/`PKok` (`PeakHP`) with frames (`evalF_frame_fld`,
  `evalF_frame_loc`, the index-aware `evalF_frame_fldAt`) and, for values whose bound is only known at
  the end of the operation, the last-write rule `PK.wr_fin`/`PKok.wr_fin_seq` with `Fin (FB f)`
  (the end state's field `f` is small, from option B): group and chunk splits (`groupPhasePeak`,
  `chunkPhasePeak`), `insertElem_pkok` (sizes and the count via `Fin`), `csP_pk`, the table
  procedures (`roomP_pk`, `tableInsert_pk`), the construction (`initCore_pkok`, `prepP_pkok`), the
  cut of a drain (`drainCut_pk`: weight sums at width `K + 9`), `finishDrain_pk`, the new tables of a
  drain start (`tab_pk`).
* **The wrappers** (`Proof/Word/PeakTop.lean`), in the form `wpB_coreCall` needs: `order_peak`,
  `markDead_peak`, `prepareStep_peak` (`PrepM s`), `initCore_peak` (`freshC P`):
  `pkF κ body s (setLocs 0 ps vs) < 2 ^ wPk K KH` with `wPk K KH = max (2K + 4) KH`, i.e. bound
  `2^(2K+4) + 2^KH` (**c = 2, d = 4**, handle term `2^KH`), given `Enc`, `WB K s`, handles `< 2^KH`,
  `PRoom K s.P`, `CapsW K κ`, `8 ≤ K`, arguments `< 2^K` and a normal run.

**What remained of A2 after its first part** (done since, see *The completion of A2* below; the
estimate then was about 3,000–4,000 lines): `insertAfter`, i.e.
* the drain start `startDrainS` (stages `insS` with `roomCall_pk`/`tableInsertCall_pk`, `stage3`
  with `tab_pk`, the weights of `chS` (sums at width `K + 9`, written through `Fin (FB (.n .weight))`
  with `evalF_frame_fldAt` for the two new nodes), a switch of `Γ` after `drainCut`);
* the job step `jobStepS`: `jcopyS` (`ja + 1`), `dsLabS` (`e1 = 2^(hβ)`, `old`/`new` at width
  `2K + 1`), `dsTagS`/`gstP` (tags through `Fin (FB (.c .tag))`), `walkS` (`wt + 2` through `Fin`
  or option B's `walk_weight`; `powS` needs `log₂ a · H ≤ K`, a new `PRoom` field);
* the reservation (`cinsBody`, `childS` with `r + 2`, `iaPrepS` tags, `insertAroundS`,
  `splitChunkStartS`, the loop) and `background`, `insertAfterP` (`catch … bug`);
* discharging the `Fin` hypotheses from option B's end-state bounds (`TopWB`, `reservation_wb`,
  the `linkElem` step) — the largest unknown.
For the corollary without Level F notions, `PRoom` and `CapsW` must come from the parameters
(`wK P`, `capsOf P`, stage A3), and `WB` from `theoremW_stored`'s reachability.

**Spike: the end-state bounds of `insertAfter`** (2026-10-27, `Proof/Word/PeakFin.lean`, about 400
lines, and `PRoom.aH`). The question was whether option (B) supplies the `Fin` bounds in the form
the last-write rule needs. It does. Nothing blocks, and no existing statement changes.
* *Where `Fin` comes from.* Option (B) bounds the end state of each *step*, not of every
  intermediate state, so `Fin` is taken at step granularity:
  - `fin_jobStep` (`jobAgree` + `jobStep_wb`);
  - `fin_split` (`splitAgree_top` + `split_wb`, which is the split branch of `reservation_wb`
    made into a lemma);
  - `fin_insertElem` (`insertElem_agree` + `insertElem_wb`).

  `evalF` is a function, so the agreement run's end state is the end state of every normal run
  (`Fin.of_run`).
* *From the step's end back to the write:*
  - `Fin.call` takes `Fin` into a callee;
  - `PKok.seq_fin` passes `Fin` back through the rest of the step;
  - the frames `FBat.back` (the rest writes no `f`) and `FBat.backAt` (the rest writes `f` only at
    another index) carry the bound across that rest;
  - the write itself is `PK.wr_finAt`, which is `PK.wr_fin` for a single index.

  `dsMut_fin` shows these pieces composing at the sweep. The syntactic side conditions of every
  top-level site hold by `decide` (`frame_chS`, `frame_dsTag`, `frame_split`).
* *Per site:*
  - **new-node weights** (`chS`): `Fin` of the job step. The second `chS` writes only at
    `u = v2`, and the locals `v1` and `v2` are kept from `newNodesS` onwards.
  - **sweep tag** (`dsTagS`, value width `2K + 2`): `Fin` of the job step, through `gstCall_pk`.
  - **split tags**: `Fin` of the split. The second `guardedSetTag` writes only at `z`
    (`gstCall_frame`), and nothing after it writes a tag.
  - **walk weight** `wt + 2` and **height** `ht ≤ H`: these need no `Fin`. They are bounded at the
    state *before* the step (`walk_lt`, from `walk_weight` and `Shape.htN`).
  - **`powS`**: `powS_pk`, with the new field `PRoom.aH : log₂ a · H ≤ K`.
  - **table labels**: already covered by `roomP_pk`, `tableInsert_pk` and `tab_pk`.
  - **new-node and new-chunk indices**: below the capacities (`CapsW`).
  - **job-record counters** (`ja + 1`, `jd + 1`): bounded by their guards.
* *Points that are not end-state bounds, all cheap:*
  - The reservation loop's peak proof must carry the joint invariant of `reservation_wb` and
    `reservationAgree_top` (`ResInv`, `WB`, the node budget, `Mc`). Neither theorem exports it, so
    the loop is re-proved.
  - `childS` and `stage7S` pass `r + 2` and `r + 1` (width `K + 1`) as call arguments. Each needs a
    hand proof from `r ≤ lcap .children = 162`, because `PKok.callS` wants widths `≤ K`.
  - `y ≠ z` and `v1 ≠ v2` come from the push semantics.
* `proom_wK`: `PRoom (wK P) P` for the proof parameters (`a = 8`: `3·(L/3 + 1) ≤ 64·L`).
* **Revised estimate for the rest of A2: about 2,500–3,500 lines.** The `Fin` discharge is now
  about 10 lines per site.

**The completion of A2: `insertAfter`** (2026-10-27, about 1,900 lines in 7 new files,
`Proof/Word/PeakJob`, `PeakSD`, `PeakStep`, `PeakSplit`, `PeakRes`, `PeakBg`, `PeakIns`; no existing
statement changed, only `OM.lean` and a doc comment of `PeakTop.lean`; no `sorry`; `#print axioms`:
`propext`, `Classical.choice`, `Quot.sound`; nothing is used by Theorems A and B).

* **The sweep step** (`PeakJob`): `dsLab_pk` (`e1 = 2^(hβ)`, `e0 = 2^((h−1)β)` below `2^K` from the
  guard `h < H` and `PRoom.Hb`; `old`, `new` at width `2K + 1`), `dsTag_pkok` (`tg = ty − old + new`
  at width `2K + 2`, through `gstCall_pk` with the end state's tag), `dsP_pkok`, `fund_pkok` (`k + 1`
  below `s` by the guard). Locals: `ΓT` (sweep), `ΓJ` (job step: `pw` at `K + 1`).
* **The drain start** (`PeakSD`): `chS_pkok` (the weight sum `ws ≤ j·(2^K − 1)` at width `K + 9`,
  written once, `PK.wr_finAt`), `stage56_pkok` (`v1 ≠ v2` from the push semantics, `newNodes_ne`; the
  second `chS` writes only at `v2`, `FBat.backAt`), `stage7_pk` (`r + 1`, with `r ≤ lcap children`
  from `findP_agree`, `findCall_le`, and `CapsW.lcap2`), `insS_pk`, `stage3_pk`, `startDrain_pkok`.
  The switch of `Γ` after the cut: `b` (a weight sum of the cut at `K + 9`) is reassigned to a child
  before `insS` uses the room labels `a`, `b` as call arguments, so `insS` runs at `ΓD2` (only `t`,
  `ws` at `K + 9`).
* **The job step** (`PeakStep`): `jcopy_pk` (`ja + 1 ≤ H`), `walk_pkok` (the weight `wt + 2` and the
  height `ht ≤ H` read before the step, `powS_pk`), `afterDS_pkok`, `jobStep_pkok`. Its hypotheses:
  the walk node's bounds at the state before the step (exactly `walk_lt`'s conclusion) and
  `Fin (FB weight)`, `Fin (FB tag)` (from `fin_jobStep`).
* **The split start** (`PeakSplit`): `iaPrep_pk`, `cins_pk`, `childS_pk` (`r + 2`),
  `insertAround_pkok` (the two tags through `gstCall_pk`; `y ≠ z` from the pushes; the second tag
  call writes only at `z`, `gstCall_frame`), `split_pkok`.
* **The reservation loop** (`PeakRes`): the joint invariant `RJ` = `ResInv ∧ WB K ∧` the node budget
  `∧ Mc` (re-proved as `rj_job`, `rj_split` from `resInv_step` and the step bounds of
  `reservation_wb`, which does not export its invariant); `resRound_peak` (a round's peak, and the
  invariant after it: the state after the round is Level F's, by `resAgree_job/_split/_empty` and
  determinism); `reservation_peak` (`PKok.loop` with the flag `dn`).
* **The background work** (`PeakBg`): `backgroundS_peak` (part by part along Level F's trace, the
  analogue of `backgroundS_agree`), `background_peak` (the merged context of `bgAgree` and
  `background_wb`: the group phase's hooks include `xgroup_wb`, so the chunk phase gets `WB K`).
* **The insertion** (`PeakIns`): `insertAfter_peakG` (the merged context of `insertAgree` and
  `insertAfter_wb`, the two `catch … bug`; the handle argument at width `KH` via `PKok.call`),
  `insertAfter_peakM` (at `TIat TopInv P`, as `insertAgreeM`), `InService.peak`, and the wrapper:

```
theorem insertAfter_peak {p m s L x hb} (hC : CapsW K (capsOf s.P)) (hK : 8 ≤ K)
    (hE : Enc p (capsOf s.P) s m) (hWB : WB K s) (hh : ∀ i, (s.E.getX i).h < 2 ^ KH) (hR : PRoom K s.P)
    (hS : InService s L) (hx : x ∈ L) (hKw : wK s.P ≤ K) (hbK : hb < 2 ^ KH)
    (he : evalF (capsOf s.P) insertAfterP.body s (setLocs 0 insertAfterP.params [x, hb]) = .ok s' L' n) :
    pkF (capsOf s.P) insertAfterP.body s (setLocs 0 insertAfterP.params [x, hb]) < 2 ^ wPk K KH
```

  The hypotheses of the other wrappers, with `κ = capsOf s.P`, plus: `InService s L` (the
  wrapper's Level M invariant for every core insertion: `cur`, the mirror into `nxt`, and the copy
  steps; `WrapM` already establishes it for `InService.insert`), `x ∈ L` (the operation is valid),
  `wK s.P ≤ K` (the word size of the operation is at least the core's; `room_wK`, `room_counts`
  are monotone in `K`, `InService.room_at`), and the handle argument `hb < 2^KH` (instead of
  `< 2^K`; it is an operation argument). `PRoom.mono` with `proom_wK` gives `PRoom K s.P`, and
  `WB.mono` with `theoremW_stored` gives `WB K s`. The bound is the same `2^(2K+4) + 2^KH`
  (**c = 2, d = 4** stay).

A2 took about 6,800 lines in all (the `insertAfter` part about 1,900 against the 2,500–3,500
estimated).

**Stage A3 is done** (2026-10-27, about 2,050 lines against the 1,500–2,300 estimated, in 6 new
files, `Impl/PeakMW`, `PeakParams`, `PeakWrapM`, `PeakRebuildM`, `PeakOpsM`, `PeakTheoremW`; no
existing file changed except `OM.lean`; no `sorry`; `#print axioms theoremW_op`, `theoremW_init`: `propext`, `Classical.choice`, `Quot.sound`;
nothing is used by Theorems A and B). The `wp` theorems of `WrapM`, `RebuildM`, `OpsM`, `InitM`,
`NewCore`, `Params` and `Fresh` keep their statements; each machine piece gets a peak theorem beside
them.

* **Peak-only proofs** (`PeakMW`). A piece's peak is proved as `wpB B c TT m` (postcondition `True`);
  the state facts the next piece needs come from the existing `wp` theorem of the previous piece
  (`wpB_and`, `wpB_seq_of`, `wpB_seq_ofQ`, `wpB_and2`), so the existing proofs are not re-run
  for their state. `dpk_le_of` turns a proof at the state with the peak reset into `dpk c m ≤ B`.
  The budget of an operation is **`BW K KH = 2^(2K+4) + 2^KH`**; a core procedure's peak
  `< 2^(wPk K KH)` is within it (`pk_BW`, `lt_pow_max_add`).
* **`CapsW (wK P) (capsOf P)`** for `P = proofParams N` (`capsW_wK`): every capacity is a summand of
  `memOf` (`memOf_eq`), and `memOf < 2^wK` (`core_mem` for `N ≥ 64`: `40000·N < 2^(16 + L)`; for
  `N < 64` a direct bound `≤ 10^6` with `L = 8`, `memOf_small`); `CapsW.mono`, `capsW_at`,
  `proom_at`. `CoreK K KH c` (proof parameters, `wK ≤ K`, `WB K`, handles `< 2^KH`) gives the
  hypotheses of the five A2 wrappers.
* **`Params`** (`PeakParams`): `partA_pk`, `partB_pk`, `partC_pk`, `paramsS_pk` along the exec facts
  `partA_ok`, `partB_ok`, `partC_ok`. The expressions' peaks come from `Expr.wdM_sound` with every
  local at width `K/2` and shifts at most `K` (`2^UG`, `2^HC`: `UG ≤ 4L`, `HC ≤ 30L + 64`). Computing
  the width with `simp` and closing with `omega` timed out (nested `max`, case splits), so the widths
  are bounded by a linear form `a·(K/2) + b` whose pair `(a, b)` is computed from the syntax alone
  (`Expr.wl`, `Expr.wlp`, `wpM_le_wlp`) and checked by `decide` (`a ≤ 2`, `b ≤ 500`). Then
  `allocSlot_pk` (`capE_maxv`, from `CapsW`), `newCore_pk` and `eagerCore_pk` (`initCore_peak`,
  `wb_fresh`).
* **The wrapper pieces** (`PeakWrapM`): `byPar_pk`, `orderC_pk`, `curDelC_pk`, `mirrorDelC_pk`,
  `curInsC_pk`, `nxtInsC_pk`, `mirrorInsC_pk`, `liveIncC_pk`, `liveDecC_pk`, with the value bounds
  `WK K KH T om`: option (B)'s `WBW T om om.nxt`, both cores of the proof parameters with `wK ≤ K`,
  `K_B < 2^K`, `T < 2^KH`. Every insertion goes through `insertAfter_peak` with its `InService`
  (as in `curInsW_ok`, `nxtInsW_ok`).
* **The rebuild** (`PeakRebuildM`): `prepC_pk`, `copyC_pk`, `endC_pk`, `spendC_pk`; the loop
  invariant `LoopB` is Level M's `LoopI` with `WK` of the state of Level F's run (carried as
  `loop_wb` carries `WBW`: `WK.prep` from `PrepM.wb`, `WK.copy` from `copy_wbw`), because `LoopI`'s
  existential forgets which Level F state the machine holds; `iterC_pk` re-runs `iterW_ok`'s case
  analysis with budgets, `loopC_pk` (`wpB_loop`, the cost from `iterW_ok`). `startC_pk`: the new
  core's capacity satisfies `N' ≤ 4N` (`MInv.nxtN`, the argument of `reach_mem`, applied to the
  state after the operation), so `wK' ≤ wK + 128` (`wK_mono4`). `rebuildC_pk`.
* **The operations** (`PeakOpsM`): `insertW_pk`, `deleteW_pk`, `orderW_pk`, along `insertW_ok`,
  `deleteW_ok`, `orderW_okM`; `WK` of each intermediate wrapper state (`T = t + 1`) from option (B)'s
  `insert_step`/`delete_step` reasoning, `mirror_wbw`, `mirrorDel_wbw`.

**The results** (`PeakTheoremW`):

```
theorem opS_pk (h : WEnc om m p) (hI : MInv om Sp) (hB : WBW t om om.nxt) (hv : op.Valid Sp)
    (hK : wKom om + 128 ≤ K) (hKB : om.KB < 2 ^ K) (hKH : t + 1 < 2 ^ KH) :
    wpB (BW K KH) (opS op) TT m

theorem theoremW_op {KB t : Nat} {om : OM} {Sp : OM.Spec.State} {m : State} {p : Nat} (h4 : 4 ≤ KB)
    (hKB : KB < 2 ^ 512) (hR : ReachW KB t om Sp) (h : WEnc om m p) {op : OM.Spec.Op} (hv : op.Valid Sp) :
    dpk (opS op) m < 2 ^ (2 * (wKom om + 128) + 5) + 2 * (t + 1)

theorem theoremW_init {m : State} {KB : Nat} (hkb : m.loc "kb" = KB) (hKB : KB < 2 ^ 512) :
    dpk initWS m < 2 ^ 1029
```

**The constants: c₀ = 5, c₁ = 2, W₀ = 1029.** `theoremW_op` takes `K = wKom om + 128`,
`KH = log₂(t + 1) + 1` (`t + 1 < 2^KH ≤ 2(t + 1)`), so the budget `2^(2K+4) + 2^KH` is below
`2^(2K+5) + 2(t+1)`. The initialization's first core has `L = 8`, `wK = 512`, and its budget
`BW 512 1 = 2^1028 + 2` is below `2^1029`; `K_B < 2^512` (stored in `wa 7`) is below it.

**What remains: A4** (about 250–400 lines). The statement of the proposal above, with `theoremW_op`
and `theoremW_init` as its two bounds. What A4 must supply: along the machine run of `theoremAB_M`,
each state before operation `i` holds (`WEnc om m p`) the wrapper state `om` with
`ReachW K_B i om Sp_i`. `step_reach` gives `Reach` (some `om` with `MInv`), and the `om'` of
`insertW_ok`, `deleteW_ok`, `orderW_okM` is Level F's `OM.apply` result (`om.insert … = .ok (_, om')`),
so `Reach` can be strengthened to `ReachW` by threading the run (a `run_reach` with `ReachW`); the
initial state comes from `initW_ok`'s `OM.init … = .ok om` (`ReachW.init`). The hypotheses of
`theoremW_op` are then `4 ≤ K_B`, `K_B < 2^512` (both in the statement), `ReachW`, `WEnc` and the
validity of the operation (from `Spec.Valid`). The cumulative corollary follows by `peak_exec`.

**Total remaining: about 250–400 lines** (A4).
