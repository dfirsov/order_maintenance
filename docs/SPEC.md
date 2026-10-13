# Order Maintenance in O(1) Worst Case — Design Specification

Status: **draft v0.2** (2026-10-13; §5.6 rewritten after prototyping). This is the pseudocode specification that the Lean
implementation and proofs will follow. The Python prototype in `prototype/` implements all of it.

---

## 0. Summary of decisions

| Topic | Decision |
|---|---|
| Interface | `insertAfter`, `insertFirst`, `delete`, `order` on element handles |
| Architecture | Dietz–Sleator style constant-height hierarchy: **elements → groups → chunks → top list** |
| Top list | Weight-balanced B-tree with immutable label tables, per-chunk stored paths and "ghost drains" into fresh siblings (§5.6). It refines Kopelowitz 2012 §3 and needs no collision protocol. Prototyped: zero fallbacks, jobs of `6H+4` steps, up to 10⁶ chunks |
| Deletion | Tombstones + incremental global rebuilding (the core is insert-only) |
| Growth | Fixed capacity N per epoch; global rebuilding into capacity ~4n |
| **Safety principle** | **Every write is guarded by an O(1) local check; any failed guard triggers a synchronous full rebuild.** Functional correctness then holds for *any* schedule of background work. Scheduling and timing only matter for the cost bound, where we prove the fallback is never reached. |
| Proof layering | Abstract `List` ⟵ *Shape* (nested labeled lists) ⟵ concrete arena (arrays + indices) |
| Cost model | Code is written in a step-counting monad from the start; the O(1) bound is proved later |

The safety principle is the key idea that makes "correctness first, bound later" possible.
In every published algorithm, the fact that labels never collide depends on intricate timing
arguments: background processes finish in time, splits never overlap badly, and so on. A
guard check on every write turns each of those arguments into a *cost* fact instead of a
*correctness* fact.

---

## 1. Literature and why we don't follow any single paper

Local copies are in `papers/`.

* **Dietz & Sleator 1987/88**, *Two algorithms for maintaining order in a list*
  (CMU-CS-88-113; `papers/dietz-sleator-1987.pdf`).
  * §2: a simple list-labeling algorithm with labels in `[0, M)`, `M > n²`, and
    O(log n) amortized relabels; it reaches O(1) amortized with sublists of size log n.
  * §3 + appendix: the **O(1) worst-case algorithm**. It uses a tree of height 4 in which
    internal nodes of height h hold ≤ logʰN leaves and are split *incrementally* into two
    "overflow" siblings. The root's children are ordered by **Willard's** dense-file
    algorithm (O(log² n) worst case; the journal version is 54 pages), which runs in the
    background with two timestamped versions of every field. A max-priority
    "reservation process" decides which depth-1 node gets new siblings next. The
    *zeroing-game theorem* (their Thm 5) bounds how full a node can get while it waits.
  * The appendix pseudocode has bugs. For example, `IncrementalSplit` updates only
    `nleaves` of `pred(x)`, not of its ancestors.
* **Bender, Cole, Demaine, Farach-Colton, Zito 2002**, *Two simplified algorithms…*
  (ESA; `papers/bender-et-al-2002.pdf`). It gives a simple amortized "tag-range
  relabeling" algorithm with an easy proof. Its worst-case O(1) algorithm is deferred to a
  "full paper" that **was never published** (confirmed by Kopelowitz 2012). Its §5
  (O(log² n) worst-case file maintenance) has proofs left "to the full version".
* **Kopelowitz 2012**, *On-line indexing for general alphabets via predecessor queries on
  subsets of an ordered list* (FOCS; arXiv:1208.3798; `papers/kopelowitz-2012.pdf`).
  * §3: list labeling with **O(log n) worst-case** cost and polynomial label space, built
    on a weight-balanced B-tree (Arge–Vitter). Each tree level owns a bit-field of the
    tag. After a node split, a background "tag-process" rewrites that field in the
    subtree. An extra epoch bit keeps queries correct while a rewrite is half done.
  * §4: O(1) worst-case order maintenance via chunks of size O(log² n).
  * Weak spot: the handling of overlapping parent/child processes (§3.3.2) is a sketch.
    The paper itself says "many believe [prior worst-case solutions'] correctness is
    questionable".
* I found no prior formal verification of order maintenance in Coq, Isabelle or Lean.

**Our synthesis:** the lower levels and scheduling come from Dietz–Sleator. They are local
and simple, and they need no in-place relabeling because a splitting node is drained into
two *fresh* siblings. Willard is replaced by a Kopelowitz-style top list. Everything sits on
the guarded-write safety principle.

---

## 2. Problem and abstract model

The abstract state is a duplicate-free list `L : List Handle` of live elements.

| Operation | Precondition | Effect | Result |
|---|---|---|---|
| `insertFirst()` | — | `L := y :: L` | fresh handle `y` |
| `insertAfter(x)` | `x ∈ L` | insert fresh `y` immediately after `x` | `y` |
| `delete(x)` | `x ∈ L` | remove `x` | — |
| `order(x, y)` | `x, y ∈ L` | — | `true` iff `x` occurs before `y` in `L` |

The structure allocates handles. A deleted handle may be reused only after the next
rebuild has purged it.

**Correctness theorem (target).** For every operation sequence that satisfies the
preconditions, the implementation's results equal the abstract model's results.

**Cost theorem (target, later).** In the cost model of §9, every operation costs at most a
constant `C` steps, independent of n and of the history.

---

## 3. Model of computation

* Word RAM with word size `w = Θ(log N)`, where `N` is the capacity of the current epoch.
  Labels and tags are `O(log N)` bits, i.e. O(1) words. Comparing or adding them counts as
  one step.
* In Lean, labels are `Nat`. The bit-width bound is a *proved invariant*, used only by the
  cost theorem.
* Within an epoch, `N` is fixed. We keep `N ≤ 8·max(n, 16)` via rebuilding, so
  `log N = O(log n)`.

---

## 4. Architecture of the core (insert-only, capacity N)

```
 top list      C1 ──── C2 ──── C3 ──── … ──── Cm        chunks, tag(C) from the top structure
               │       │
 group list    g g g   g g …                            groups, label within chunk
               │
 element list  H e e e e e e e …                        elements, label within group
```

Three global doubly linked lists (elements, groups, chunks). Every element points to its
group, and every group points to its chunk. Membership is **contiguous**: the elements of
group `g` are exactly the range `g.first … g.last` of the element list, and likewise the
groups of chunk `c`. Groups and chunks may be **empty**: newly created overflow nodes start
empty.

`H` is a sentinel element. It is always first, never deleted and never visible.
`insertFirst()` is `insertAfter(H)`.

### 4.1 Records

```
Elem  e : next, prev : Elem?    grp : Group    lab : Nat    live : Bool
Group g : next, prev : Group?   first, last : Elem?   chk : Chunk   lab : Nat
          size : Nat                               -- elements in range, incl. tombstones
          st   : Quiet | Overflow(src : Group) | Splitting(l r : Group)
Chunk c : next, prev : Chunk?   first, last : Group?  size : Nat  -- elements beneath
          st   : Quiet | Overflow(src : Chunk) | Splitting(l r : Chunk)
          topLeaf : TopNode     pq : bucket links
```

### 4.2 Keys and the order query

```
key(e)       = (tag(e.grp.chk), e.grp.lab, e.lab)     compared lexicographically
order(x, y)  = key(x) <lex key(y)                      -- 2 dereferences + ≤ 3 comparisons
```

The query uses no pointer-equality tests. It is correct as soon as keys strictly increase
along the element list (§6).

### 4.3 Parameters

`L = ⌈log₂ N⌉`. All constants below are **to be tuned experimentally** (§10, milestone M3);
only the stated relations matter for the proofs.

| Name | Meaning | Order |
|---|---|---|
| `G` | a group starts splitting when `size ≥ G` | `Θ(L)` |
| `T` | chunk capacity | `Θ(L²)` |
| `θ = ⌊2T/3⌋` | a quiet chunk with `size > θ` waits in the priority queue | |
| `B_e, B_g` | label widths for elements and groups | `Θ(L)` |
| `Δ_e = 2^(B_e−1) / (2·G_max+2)` | label step for appending at either end | |
| `K_G, K_C, K_R` | background work per operation: group moves, chunk moves, top-structure steps | `O(1)` |

Why chunks have size Θ(L²): the top structure accepts one insertion at a time, and each
takes Θ(log m) operations to finish. By the zeroing game (§8.2), the fullest waiting chunk
gains only O(log m · H_m) = O(L²) elements before it is served.

---

## 5. Algorithms

### 5.1 Labeled-range primitives (used at the element and group levels)

A *labeled range* is the member range of a parent (elements of a group, groups of a chunk)
with strictly increasing labels in `[0, 2^B)`.

```
labEmpty            = 2^(B−1)
labAfter(a)         = a.lab + Δ         guard: a.lab + Δ < 2^B        -- a is the last member
labBefore(b)        = b.lab − Δ         guard: b.lab ≥ Δ              -- b is the first member
labBetween(a, b)    = ⌊(a.lab+b.lab)/2⌋ guard: a.lab + 1 < b.lab
```

A failed guard means `FALLBACK` (§5.8). Labels are never rewritten in place at these
levels. Every member gets its label once, when it is inserted or moved into a range, and a
splitting range is drained into fresh ranges. This is why no epoch bit is needed below the
top list.

### 5.2 Insert

```
proc insertAfter(x):                         -- core version; the wrapper (§5.7) calls this
  g := x.grp ; c := g.chk
  ℓ := if x = g.last then labAfter(x) else labBetween(x, x.next)
  y := newElem(lab = ℓ, grp = g, live = true) ; link y after x ; if x = g.last then g.last := y
  g.size += 1 ; c.size += 1 ; PQ.adjust(c, +1)
  if g.st = Quiet ∧ g.size ≥ G then StartGroupSplit(g)
  Drive(g) ; Drive(c) ; Reservation.run(K_R)
  return y

proc Drive(v):                               -- v is a group or a chunk
  match v.st with
  | Splitting _    => SplitStep(v)   × K
  | Overflow(src)  => SplitStep(src) × K
  | Quiet          => skip
```

Inserts into either overflow sibling also drive the source's split, as in Dietz–Sleator.
`Drive` uses explicit `src` pointers rather than `pred`/`next`.

### 5.3 Group split (Dietz–Sleator style)

```
proc StartGroupSplit(g):                     -- c = g.chk
  gl := newGroup(chk=c, st=Overflow(g), empty)
  gr := newGroup(chk=c, st=Overflow(g), empty)
  gl.lab := if g = c.first then labBefore(g) else labBetween(g.prev, g)
  gr.lab := if g = c.last  then labAfter(g)  else labBetween(g, g.next)
  link gl before g and gr after g in the group list ; fix c.first / c.last
  g.st := Splitting(gl, gr)

proc SplitStep(g)  with g.st = Splitting(gl, gr):
  if g.size = 0 then
      unlink g ; fix g.chk.first/last ; gl.st := Quiet ; gr.st := Quiet ; free g ; return
  if gl.size ≤ gr.size then                       -- move first element left
      guard gl.next = g
      e := g.first ; ℓ := if gl.size = 0 then labEmpty else labAfter(gl.last)
      g.first := e.next (or none) ; gl.last := e (and gl.first if it was empty)
      e.grp := gl ; e.lab := ℓ ; transfer 1 from g to gl  (sizes; chunk sizes if
                                                           chunks differ; PQ.adjust ±1)
  else                                             -- move last element right (mirror image)
      guard g.next = gr ; e := g.last ; ℓ := if gr.size = 0 then labEmpty else labBefore(gr.first) …
```

The element list itself never changes during a split; only group membership and labels do.

### 5.4 Chunk split (same shape, groups as members)

```
proc StartChunkSplit(x, y, z):  x.st := Splitting(y, z) ; y.st := z.st := Overflow(x) ; PQ.remove(x)

proc SplitStep(x)  with x.st = Splitting(y, z):
  if x.size = 0 ∧ x.first = none then
      unlink x from the chunk list ; Top.remove(x) ; y.st := z.st := Quiet
      PQ.enterIfAbove(y) ; PQ.enterIfAbove(z) ; free x ; return
  if y.size ≤ z.size then
      guard y.next = x ; gg := x.first ; ℓ := if y empty then labEmpty else labAfter(y.last)
      move gg to the end of y with label ℓ ; y.size += gg.size ; x.size −= gg.size
  else  mirror image with z, x.last, labBefore
```

Moving a group costs O(1), however large the group: its elements point to the group, not to
the chunk.

### 5.5 Reservation process and priority queue

```
state Reservation : Idle | Busy(job : TopJob)

proc Reservation.run(k):
  repeat k times:
    match state with
    | Idle     => if PQ.nonempty then
                    x := PQ.popMax()                       -- fullest quiet chunk with size > θ
                    y, z := newChunk(), newChunk()
                    job := Top.beginInsertAround(x, y, z)  -- O(1); y, z get valid tags now
                    StartChunkSplit(x, y, z) ; state := Busy(job)
    | Busy(j)  => if Top.step(j) = Done then state := Idle
```

`PQ` is a bucket queue over sizes in `(θ, T_hard]`. It keeps a sorted doubly linked list of
non-empty buckets. Sizes of quiet chunks change by ±1 per step, so `adjust`, `remove` and
`popMax` are O(1).

There is one slow path: `enterIfAbove(c)`, when a chunk becomes quiet with `size > θ`. It
scans for the bucket's neighbors, which costs O(T). The cost proof must show this never
happens; Dietz–Sleator's Lemma 4 argument says freshly quiet overflow chunks hold
`< 2T/3` elements.

### 5.6 Top structure — weight-balanced tree with ghost drains (prototyped, `prototype/top_wbbt.py`)

**Interface used by the rest of the design:**

```
tag(c)                    : Nat           -- O(1) read of the stored tag
insertAround(x, y, z)     : Job           -- O(1): y before x, z after x, with valid tags
step(job)                 : Done | More   -- O(1) background work
```

Emptied chunks are never removed from the top structure. They stay in the chunk list as
`DEAD` tombstones until the next global rebuild, because unlinking one would cost O(log m).

**Safety contract.** Stored tags strictly increase along the chunk list, including
tombstones, at all times between steps. Every tag write is guarded against the chunk's two
neighbours.

**Cost contract.** Each job finishes within `J = O(log m)` steps. Tags are `O(log N)` bits.
No guard ever fails.

`top_simple.py` is the milestone-1 stand-in: correct, but not O(1).

#### Design

Weight-balanced B-tree (Arge–Vitter), branching parameter `a = 8`. Leaves are chunks, and
the root has a fixed height `H = ⌈log_a m_max⌉ + 1` for the whole epoch. A node's *weight* is
the number of chunks ever inserted beneath it. A non-root node of height `h` is drained once
its weight exceeds `2aʰ`. Nodes are of two kinds:

* **Live** nodes form the live tree. It is used for weights and for deciding where new
  nodes go.
* **Ghost** nodes are being drained. A ghost has no live children, but chunk paths may
  still pass through it.

Three ideas replace Kopelowitz's in-place relabelling and its collision protocol:

1. **Immutable label tables.** Each node `v` has a table that assigns labels in `[0, 2^β)` to
   its *entries*. Entries are child nodes, or chunks when `h = 1`. A label never changes
   once assigned. New entries get labels by averaging their neighbours.
2. **Stored paths.** Each chunk `c` stores a path `p[1..H]` (with `p[H] = root` and
   `p[0] = c`). Its tag is
   `tag(c) = Σ_j  lab_{p[j]}(p[j−1]) · 2^((j−1)β)`.
   The stored path may run through ghosts. Since tables are immutable, a tag changes only
   when its own path changes.
3. **Drain into fresh siblings (Dietz–Sleator style).** Draining `v`:
   * Create live siblings `v1` and `v2`. Insert them immediately before and after `v` in
     *every table that contains `v`*.
   * Partition `v`'s live children by weight. Never separate the two targets of a drain
     that is still running.
   * Give `v1` and `v2` fresh tables with evenly spread labels. Copy into them every entry
     of `v`'s table that is still referenced: live children, plus ghosts that still have
     chunks. Each copied entry is marked LEFT or RIGHT.
   * `v` becomes a ghost, and `v1`, `v2` become its *targets*. A target may not drain until
     its source's drain has finished.
   * The **sweep** repeatedly takes the first chunk of `v`'s range if it is LEFT and sets
     `p[h] := v1`, otherwise the last chunk (which is then RIGHT) and sets `p[h] := v2`.
     Each such rewrite changes exactly two fields of one tag:
     `F_{h+1} = lab_{p[h+1]}(·)` and `F_h = lab_{·}(p[h−1])`.
   * When `v`'s range is empty, remove `v` from every table and drop its own table.

   Every node keeps the range `first..last` of chunks whose stored path has `p[h] = v`.
   Ranges are contiguous.

**Why overlapping drains need no coordination.** A drain at height `h` rewrites only the
entry `p[h]`. It reads the current `p[h+1]` and `p[h−1]` to compute the two fields it
changes. A parent drain (`p[h+1]`) and a child drain (`p[h−1]`) can therefore interleave
freely: whichever writes last, the tag is a function of the current path. The tables they
need always exist, because of the two "every table containing" rules above.

**Job for one reservation** (`insertAround(x, y, z)`, then steps):

```
O(1) part : label y before x and z after x in every table holding x; tag(y), tag(z) from
            tag(x) by replacing field F_1; y, z join x's live parent
step 1..H : copy x's path into y, z one entry per step; extend node ranges where x was an end
then      : walk the live tree from the live parent up to the root. At each node v:
              weight(v) += 2
              if weight(v) > 2a^h, v is not the root, and v is not a target:  start draining v
              if v is the target of a draining source u:  s sweep steps of u's drain  (s = 8)
```

**Parameters and measurements** (`prototype/top_stress.py`, top level in isolation, up to
10⁶ chunks, five adversaries; `prototype/stress.py`, full system):

| | Observed |
|---|---|
| Fallbacks | 0, with `s = 8` and `β = 4a + 8 = 40` |
| Longest job | `6H + 4` steps (46, 56, 66 at m = 10⁴, 10⁵, 10⁶), i.e. about 3.4 log₂ m |
| Largest table | ≤ 28 entries (live fanout ≤ 4a, plus ghosts) |
| Label bits used | ≤ 18 of β per table, in the worst case of always inserting next to the newest chunk |
| `s ≤ 4` | fails |

Why `s ≤ 4` fails: drains fall behind, targets that may not drain keep growing, their tables
overflow, and fallbacks follow. The threshold matches the estimate `s ≥ 4(1+ε)`. A drain
moves about `2aʰ` chunks, and its targets can absorb about `aʰ` new chunks (`aʰ/2` jobs)
before they overflow.

Ghosts whose targets receive no insertions never finish draining. This is harmless: they
cost O(1) table entries each and are purged by the next rebuild. Up to 2.6% of chunks were
affected under random insertions.

#### Invariants for the cost proof (to be proved in M6)

* **(W1) Adjacency.** For a draining `u` with targets `u1, u2`, the entries `u1, u, u2` are
  consecutive in every table that contains `u`.
* **(W2) Ranges.** The chunks with `p[h] = v` form the contiguous run `v.first..v.last`.
  For a draining `u`, its LEFT chunks precede its RIGHT chunks, the run of `u1` ends right
  before `u`'s run, and the run of `u2` starts right after it.
* **(W3) Tables.** For every chunk and every `j`, `p[j−1]` is an entry of `p[j]`'s table.
* **(W4) Ghost-path order.** For consecutive chunks `x < y`, let `j` be the highest level
  where their paths differ. Then `p[j](x)` and `p[j](y)` are entries of the common table
  `p[j+1]`, in label order. This is exactly `tag(x) < tag(y)`.
* **(W5) Timing.** A drain finishes before either target exceeds `2aʰ(1+ε)`. Hence fanout
  is ≤ 4a + O(1), and a table receives ≤ 4a + O(1) insertions in its lifetime, so `β = 4a + 8`
  bits never run out.

W1–W4 say each sweep step's guard passes, and W5 says averaging never runs out of room.

### 5.7 Wrapper: deletion and global rebuilding

```
state : cur : Core, nxt : Option (Core × cursor), live : Nat

delete(x):        x.live := false (in cur, and in nxt if x was already copied) ; live −= 1
order(x, y):      cur.order(x, y)
insertAfter(x):   y := cur.insertAfter(x)
                  if nxt active ∧ x already copied then nxt.insertAfter(x′) ; mark y copied
                  RebuildStep(K_B)
RebuildStep(k):   if nxt = none ∧ (cur.inserted ≥ N/2 ∨ live < N/8) then
                      nxt := (Core.empty(capacity = 4·max(live,16)), cursor = cur.H)
                  copy up to k live elements at the cursor into nxt (append at the end)
                  if the cursor reaches the end then cur := nxt.core ; nxt := none
```

Each element record keeps its node in `cur` and its node in `nxt`. Constants are chosen so
that the copy finishes well before `cur` reaches capacity.

### 5.8 Fallback

`FALLBACK` means a synchronous rebuild: drop all background state and rebuild `cur` from
the live element sequence, with even labels at every level, all nodes `Quiet`, and a fresh
top structure. It costs O(n) and is correct by construction. The cost theorem proves it is
**unreachable**.

---

## 6. Safety invariant (functional correctness)

**Shape view.** Abstract the concrete state as nested lists:

```
Shape = List (Chunk × tag) where each chunk ↦ List (Group × lab) where each group ↦ List (Elem × lab × live)
```

**INV-S (safety invariant):**

1. **Well-formed lists.** The three linked lists are well formed: `next`/`prev` agree,
   they are acyclic, and every reachable index is allocated.
2. **Contiguous nesting.** Concatenating the groups' element ranges, in group-list order,
   gives exactly the element list; likewise for chunks and groups. Empty groups and empty
   chunks are allowed.
3. **Sorted at every level.**
   * chunk tags strictly increase along the chunk list;
   * within each chunk, group labels strictly increase;
   * within each group, element labels strictly increase.
4. **Sentinel and abstraction.** `H` is first, and `toList(state) = filter live (elements after H)`.

**Lemma (query correctness).** INV-S implies that keys strictly increase along the element
list. Hence `order(x,y)` holds iff `x` precedes `y`.

**Lemma (preservation).** Each primitive preserves INV-S if its guard holds, and is
skipped (`FALLBACK`) otherwise. This covers element insertion, `StartGroupSplit`, an
element move, group removal, the chunk-level analogues, top-structure tag writes and
chunk insertion. Each check is local: it compares only with immediate neighbors.

**Theorem (correctness).** The wrapper refines the abstract model of §2. This holds for any
interleaving of background steps; scheduling is irrelevant to correctness.

The top structure's internal state (weights, processes, epoch bits) appears **nowhere** in
INV-S. Its code only has to be total: out-of-range reads return defaults.

---

## 7. Timing invariants (for the cost theorem, later)

Here is what must hold in every reachable state for no guard to fail:

* **(T1) Groups.** `size ≤ G_hard`. Insertions over a group's lifetime are at most
  `G_max`, so the label room `B_e` is never exhausted. A splitting group is emptied before
  either overflow sibling reaches `G`, which needs `K_G` large enough (Dietz–Sleator
  Lemma 4).
* **(T2) Chunks.** Analogous to T1, with `T`, `B_g` and `K_C`. Freshly quiet chunks have
  `size ≤ θ`, so the slow path of §5.5 is never taken.
* **(T3) Reservation.** A quiet chunk never exceeds `T_hard` before it is served. This
  follows from the zeroing game (§8.2) with rounds of length `J/K_R`.
* **(T4) Top structure.** Weight-balanced B-tree bounds; every tag-process finishes before
  its node's halves can split again; no label table overflows.
* **(T5) Rebuild.** The copy finishes before `cur` reaches capacity, and `N` stays within a
  constant factor of `n`.

---

## 8. Lemmas to formalize

### 8.1 Averaging capacity

Start with gap `Δ`. Then at least `⌊log₂ Δ⌋` arbitrary `labBetween` insertions succeed
before any guard fails. Similarly, `k` pushes at one end need `k·Δ` room.

### 8.2 Zeroing game (Dietz–Sleator Thm 5)

Take reals `x₁…x_n ≥ 0`, all initially 0. Repeat: set some maximal `x_i` to 0, then add
nonnegative amounts summing to at most 1. Then always `x_i < H_{n−1} + 1`.

The proof considers `S_k`, the sum of the k largest values, and shows
`S_1 ≤ H_{k−1} + S_k/k` by induction. It is self-contained and a good first Lean target.
We need a discretized, weighted version: each round adds at most `R` in total.

### 8.3 Weight-balanced B-tree (Arge–Vitter)

Fanout stays in `[a/4, 4a]`, the height is `O(log_a m)`, and after a split each half has
weight `Ω(W)`.

### 8.4 Dietz–Sleator Lemma 4 (overflow nodes never need to split before their source is empty)

Needed for T1 and T2.

---

## 9. Lean architecture

```
OrderMaintenance/
  Spec.lean            abstract model (List Handle), operations, `order` via index
  Shape.lean           nested labeled lists, primitive ops with guards, INV-S, query lemma
  Arena.lean           arrays + Nat indices, total accessors
  LabeledRange.lean    §5.1 primitives
  Core/Group.lean      §5.3      Core/Chunk.lean  §5.4      Core/Reservation.lean §5.5
  Top/Simple.lean      milestone-1 top (averaging + full relabel)
  Top/WBBT.lean        target top (§5.6)
  Core.lean            insertAfter / order / fallback
  Wrapper.lean         §5.7
  Cost.lean            step-counting monad
  Games/Zeroing.lean   §8.2
  Test/…               executable differential tests vs Spec, stress drivers
```

* **Cost monad.** `abbrev M := StateT State (Tick)`, where `Tick α = α × Nat` counts
  steps. Every primitive charges 1. Correctness proofs project away the count, and cost
  proofs use it. Writing the code this way now avoids rewriting it later.
* **Refinement in two layers.**
  * `Arena → Shape`: pointer reasoning. Each primitive is local; prove that the abstraction
    function commutes with it.
  * `Shape → Spec`: order reasoning on plain lists. No pointers.
* **Totality.** No `partial def`. Loops run on explicit fuel, and fuel bounds come from
  sizes. Array reads use `getD`, so safety never depends on bounds invariants.
* **Executable from day one.** Lean compiles the arena implementation. A differential
  tester runs random and adversarial workloads against `Spec`. Instrumentation records:
  * the number of fallbacks, which must be 0;
  * the maximum number of steps per operation;
  * the maximum fullness of chunks and groups.

---

## 10. Milestones

| # | Deliverable | Proof content |
|---|---|---|
| M0 | Lake project, `Spec`, `Shape`, naive reference implementation, test harness | `Shape` query lemma |
| M1 | Full core and wrapper with `Top/Simple`; executable; differential tests pass | — |
| M2 | **Correctness theorem** for M1 (INV-S preservation, refinement to `Spec`) | main correctness result |
| M3 | `Top/WBBT` (§5.6) ported from the prototype, where it is already validated: no fallbacks, flat max-steps | correctness carries over automatically (safety principle) |
| M4 | Zeroing game and averaging-capacity lemmas in Lean | standalone combinatorics |
| M5 | Cost theorem for the lower levels and wrapper, assuming the top structure's cost contract | T1, T2, T3, T5 |
| M6 | Cost contract for `Top/WBBT` | T4 — the research-risk item |

---

## 11. Risks

* **The top structure (M6).** The design in §5.6 works in the prototype. What remains is
  proving W1–W5, especially the timing invariant W5. The safety principle keeps this
  risk from contaminating M2.
* **Constants.** Tags are `Hβ ≈ 40·log₈ m` bits wide. That is fine for the theory but
  slow in practice.
* **Proof scale.** Pointer reasoning in the `Arena → Shape` step is the bulk of M2. Keep
  primitives tiny and uniform across levels: groups and chunks share the labeled-range
  code, parameterized by level.
