# Order Maintenance in O(1) Worst Case — Algorithm and Proof

Status: **v0.3, complete pen-and-paper proof** (2026-10-14). Fixes applied and re-tested
(§6, `docs/TESTING.md` §8). Every cost lemma is now proved with exact constants, and the
assembly is an explicit induction over time (§4.7). The findings of this pass are listed in
§6.6. Companion to `docs/SPEC.md` (engineering specification
and Lean plan) and `docs/TESTING.md` (empirical results). This document describes the
algorithm in conventional terms and gives pen-and-paper proofs of correctness and of
the O(1) worst-case bound. It is the blueprint for the Lean proofs (milestones M2 and
M4–M6).

Writing the proofs exposed three problems that the testing campaign missed. One of them
is a real cost bug, confirmed by a new adversary. They are collected in §6 with fixes.
§2 describes the algorithm *with* the fixes, and marks each changed step with **[fix]**.
All three are now applied to the prototype and re-tested, including a *lemma checker* that
measures every quantitative bound of §4 (`docs/TESTING.md` §8).

---

## 0. Results and status

**Theorem A (correctness).** For every sequence of operations that satisfies the
preconditions, every answer equals the answer of the list model (§1). This holds for every
choice of parameters (subject to the mild conditions of §3.4) and for every schedule of
background work.

**Theorem B (cost).** With the parameters of §2.9, every operation performs O(1) steps in
the worst case on a word RAM with Θ(log N)-bit words.

| Part | Section | Status of the sketch |
|---|---|---|
| Correctness | §3 | Complete; ready to formalize |
| Groups: split timing, sizes, label room | §4.2 | Complete; needs a wider element label **[fix 2]** |
| Chunks: split timing, sizes, label room | §4.3 | Complete given *family moves* **[fix 3]**; C3 re-proved in v0.3 |
| Reservation: zeroing game | §4.4 | Complete |
| Top structure: order invariant, guards | §4.5.1 | Complete; replaces SPEC's W4 by a cleaner global-order invariant |
| Top structure: drain timing, table sizes, label room | §4.5.2–4.5.6 | Complete, with exact per-height constants (`prototype/top_bounds.py`); funding `s ≥ 9` suffices for `a = 8` |
| Wrapper: rebuild timing | §4.6 | Complete given a new sizing rule **[fix 1]** |
| Assembly and conditions I1–I10 | §4.7 | Complete: induction over time; exact conditions hold for all `L ≥ 8` (`prototype/lower_bounds.py`) |

The overall shape is the one Dietz and Sleator (1987) proposed. Two things are new. Below
the top level, every write is guarded, so correctness never depends on timing. The top level
is a weight-balanced tree with immutable label tables and "ghost drains", replacing
Willard's algorithm and Kopelowitz's in-place relabeling.

---

## 1. Problem and model

Maintain a list of distinct elements under

* `insertAfter(x)`: insert a new element immediately after `x` and return it (and `insertFirst()`);
* `delete(x)`: remove `x`;
* `order(x, y)`: does `x` precede `y`?

Preconditions: every argument `x`, `y` is a live element, i.e. returned by an insertion and not
yet deleted.

**Model.** Word RAM. Within an *epoch*, a core has a fixed capacity `N`, and `L = ⌈log₂ N⌉`.
Words have `Θ(L)` bits. All labels and tags are `O(L)` bits (O(1) words), and comparing or
adding them is O(1). A *step* is an O(1)-time unit of work.

---

## 2. The algorithm

### 2.1 Structure

The algorithm keeps three nested lists:

```
 chunk list    C1 ─── C2 ─── C3 ─── … ─── Cm         each chunk has a tag, maintained by the top structure
               │      │
 group list    g g g  g g …                           each group has a label within its chunk
               │
 element list  H e e e e e e …                        each element has a label within its group
```

* The **element list** is the user's list, plus a sentinel `H` that is always first. Deleted
  elements stay in it as *tombstones* until the next rebuild.
* Elements are partitioned into **groups**, and groups into **chunks**. Membership is
  *contiguous*: the elements of a group are a consecutive run of the element list, and
  likewise for the groups of a chunk. Groups and chunks may be empty.
* Every element stores a pointer to its group and a label. Every group stores a pointer to
  its chunk and a label. Every chunk stores a tag.

The **key** of an element `e` is the triple `(tag(chunk(e)), lab(group(e)), lab(e))`, and
```
order(x, y)  =  key(x) <lex key(y)
```
This costs two dereferences and at most three comparisons. Everything else exists to keep
keys strictly increasing along the element list, with every update costing O(1).

**Levels and sizes.** Groups hold `Θ(L)` elements and chunks hold `Θ(L²)` elements, so
there are `O(N/L²)` chunks. The top structure maintains chunk tags with `O(log m)`
worst-case work per chunk insertion. That work is spread over `Θ(L)` user operations, and
this spreading is what the chunk size pays for (§4.4).

**Splitting into fresh siblings.** No level below the top ever relabels in place. When a
group or chunk `v` is too big, two *empty* siblings `v⁻` (before `v`) and `v⁺` (after `v`) are
created. Then `v` is emptied incrementally: members move one at a time from the front of `v`
to the end of `v⁻`, or from the back of `v` to the front of `v⁺`. Each move gives the member a
fresh label in its new parent. This is the Dietz–Sleator incremental split. The three nodes
`(v⁻, v, v⁺)` form a **family** until `v` is empty and removed. `v` is *splitting* and `v⁻`,
`v⁺` are *overflow* nodes; all other nodes are *quiet*.

### 2.2 Labels

A member range (the elements of a group, or the groups of a chunk) carries labels in
`[0, 2^B)` that strictly increase. Three primitives produce new labels:

```
labEmpty           = 2^(B−1)                                  first member of an empty range
labAfter(a)        = lab(a) + Δ          guard: < 2^B          a is the last member
labBefore(b)       = lab(b) − Δ          guard: ≥ 0            b is the first member
labBetween(a, b)   = ⌊(lab(a)+lab(b))/2⌋  guard: lab(a)+1 < lab(b)
```

`Δ = 2^(B−1)/(8G'+8)`, where `G'` is the range's size parameter. Pushing at an end costs a
fixed step; averaging halves a gap. A label never changes while its member stays in the
range.

### 2.3 Inserting an element; group splits

```
insertAfter(x):                            -- in a core; the wrapper (§2.7) calls this
  g := group(x)
  ℓ := (x = last(g)) ? labAfter(x) : labBetween(x, next(x))
  link a new element y with label ℓ after x, in group g
  size(g) += 1 ; size(chunk(g)) += 1
  if g is quiet and size(g) ≥ G then StartSplit(g)
  Drive(g) ; Drive(chunk(g)) ; Reserve(K_R)
  return y

Drive(v):  if v is splitting, do K moves of v's split; if v is overflow with source u, do K moves of u's split
           (K = K_G for groups, K_C for chunks)

StartSplit(g):                             -- g in chunk c
  g⁻ := new empty group in c, label between g's predecessor in c and g (labBefore(g) if g is first in c)
  g⁺ := new empty group in c, label between g and its successor in c (labAfter(g) if g is last in c)
  link g⁻ before g and g⁺ after g ; mark the family (g⁻, g, g⁺)

SplitMove(g):                              -- one move of a splitting group
  if g is empty: unlink g; g⁻ and g⁺ become quiet; stop
  if size(g⁻) ≤ size(g⁺): move first(g) to the end of g⁻    (label labEmpty or labAfter(last(g⁻)))
  else:                   move last(g) to the front of g⁺   (label labEmpty or labBefore(first(g⁺)))
```

The element list itself never changes during a split; only group membership and labels
change. The move rule keeps the siblings balanced.

### 2.4 Chunk splits

These work the same way as group splits, with groups as members and chunk labels drawn
from `B_g` bits. One difference:

* **[fix 3] Family moves.** If the group at the end of `x` that is about to move belongs to
  a family, the whole family `(g⁻, g, g⁺)` moves in this one step (three O(1) relinks).
  This keeps every family inside a single chunk (invariant F, §4.3).

Moving a group is O(1) however large it is: elements point to their group, not to their chunk.

A chunk is not split as soon as it is big. Splitting a chunk means inserting two new leaves
into the top structure, which is a long job. The reservation process (§2.5) decides which
chunk goes next.

### 2.5 Reservation process

```
Reserve(k):  repeat k times:
  if no job is running:
     if PQ is non-empty:
        x := PQ.popMax()                     -- the largest quiet chunk with size > θ
        create empty chunks y, z; link y before x and z after x
        job := Top.insertAround(x, y, z)     -- O(1); gives y, z valid tags immediately
        start x's split into (y, x, z)
  else advance the job by one step; when it finishes, the process is idle again
```

`PQ` is a bucket queue keyed by chunk size. It holds exactly the quiet chunks with size
greater than `θ = ⌊2T/3⌋`. Sizes of quiet chunks change by +1 per step, so it supports
`adjust`, `remove` and `popMax` in O(1). Its only slow operation inserts a chunk that becomes
quiet while above `θ`. Lemma C2 shows that this never happens.

### 2.6 Top structure: a weight-balanced tree with ghost drains

The chunks are the leaves of a tree of fixed height `H` with branching parameter `a`
(a weight-balanced B-tree in the sense of Arge and Vitter). A node of height `h` has **drain
threshold** `W_h = 2aʰ`. Its **weight** `w(v)` is the number of chunks below it.

**Tables.** Each node `v` of height `h` has a *table*: a list of *entries* (nodes of height
`h−1`, or chunks when `h = 1`), each with a label in `[0, 2^β)`. Labels in a table are
**immutable**. A new entry gets the average of its neighbours' labels.

**Paths and tags.** Each chunk `c` stores a path `p₁(c), …, p_H(c)`, with `p₀(c) = c` and
`p_H(c) = root`. Its tag is the concatenation of the labels along that path:

```
tag(c) = Σ_{j=1..H}  lab_{p_j(c)}( p_{j−1}(c) ) · 2^((j−1)β)
```

A stored path may lag behind the tree. It may still pass through *ghosts*, nodes that are
being drained. Since table labels never change, a tag changes only when its own path
changes.

**Live tree and ghosts.** The live nodes form a weight-balanced tree over all chunks; it
decides weights and where new nodes go. A *ghost* `v` has no live children, two *targets*
`v⁻, v⁺`, and a *range*: the chunks `c` with `p_h(c) = v`, which are always consecutive in
the chunk list. The range may be empty: a ghost finishes only at the first sweep call that
finds its range empty.

```
StartDrain(v):                               -- v live, non-root, w(v) > W_h, v is not a target
  create live nodes v⁻, v⁺ of height h
  insert v⁻ immediately before and v⁺ immediately after v in EVERY table that contains v
  split v's live children into a left and a right part of about equal weight,
      never separating the two targets of a running drain
  give v⁻ (v⁺) a fresh table with evenly spaced labels: the referenced entries of v's table
      (live children, and ghosts that still have chunks) of the left (right) part, marked LEFT (RIGHT)
  v becomes a ghost with targets v⁻, v⁺ ; v⁻, v⁺ replace v among its parent's live children

SweepStep(v):                                -- v a ghost of height h
  if range(v) is empty:  remove v from every table and drop its table ; done
  c := first chunk of range(v)
  if p_{h−1}(c) is LEFT:  p_h(c) := v⁻       -- c leaves the front of v's range
  else  c := last chunk of range(v) ; p_h(c) := v⁺      -- it is RIGHT
  recompute fields h and h+1 of tag(c) and write the tag (guarded, §2.8)
```

A target may not itself start draining until its source's drain has finished. Ghosts are
never re-parented. Chunks that become empty are not removed from the top structure;
they stay as *dead* leaves until the next rebuild.

**One job per reservation.** `insertAround(x, y, z)` has an O(1) part, after which the
job runs one step per call:

```
O(1) part:  in every table that contains x, insert y right before x and z right after x
            p(y) := p(z) := p(x)    (logically; physically copied one level per job step)
            tag(y), tag(z) := tag(x) with field 1 replaced ; y, z join x's live parent
steps:      copy the path (H steps), then walk from x's live parent up to the root. At each node u:
              w(u) += 2
              if w(u) > W_h, u is not the root and u is not a target:  StartDrain(u)
              if u is a target of a ghost v:  s steps of SweepStep(v)
```

The job is the only top-level activity, and jobs run one at a time. So no drain step
interleaves with a path copy.

### 2.7 Wrapper: deletion and global rebuilding

The cores above are insert-only. The wrapper adds deletion and growth by global
rebuilding.

```
state: cur (a core that answers queries), optionally nxt (a core being filled) with a cursor into cur

order(x, y):      cur.order(x, y)
delete(x):        mark x dead in cur, and in nxt if x was already copied ; RebuildStep(K_B)
insertAfter(x):   y := cur.insertAfter(x)
                  if nxt exists and x was already copied:  insert y after x in nxt too
                  RebuildStep(K_B)

RebuildStep(k):
  if there is no nxt:
      if cur.count ≥ N/2  or  (N > N_MIN and live < N/8):
          N' := 4·max(live + ⌊(cur.count + H')/(K_B − 1)⌋ + 1, 16),  H' := L + 2      [fix 1]
          nxt := empty core of capacity N'      -- no step is done in this operation
  else do k steps:
      while nxt is not ready: one preparation step (its top tree is built one node per step,
          at most H' steps)
      then: one step = copy the element at the cursor to the end of nxt if it is live,
          and advance the cursor (it starts at the first element after the sentinel)
      as soon as the cursor passes the last element, nxt replaces cur (free)
```

Before preparation ends there is no cursor, nothing is copied and nothing is mirrored.
`N_MIN = 64` is the capacity of the first core.

**Handles.** The O(1) bound needs O(1) worst-case access from a user's element to its node
in `cur` and in `nxt`. Each user element has a record with two slots, one per core parity,
and an epoch stamp.
* The core of epoch `e` uses slot `e mod 2`.
* "`x` was already copied" means `stamp(x) = e + 1`; the copy step and the mirroring set it.
* The swap increments `e`, and the retired core is dropped. Both are O(1).

The prototype uses hash maps instead, which give expected O(1).

The prototype originally set `N' := 4·max(live, 16)`. §6.1 shows that this is wrong.

### 2.8 Guards and fallback

Every write that could break the order of keys is **guarded** by an O(1) comparison with
its immediate neighbours, computed before the write it protects:

* the label guards of §2.2;
* sibling adjacency at every split move: `next(v⁻) = v`, or `prev(v⁺) = v`;
* every top-level tag write compares the new tag with the tags of the chunk-list neighbours.

Two primitives change auxiliary structure before a guard:
* the reservation links `y, z` before `insertAround`'s tag guards;
* group removal re-runs a guarded `StartSplit` on its siblings.

This is harmless by Lemma 3.3.

A failed guard triggers **FALLBACK**, immediately, before any further primitive or query. It
rebuilds the current core synchronously from its element list, keeping every element record.
Groups get `⌊G/2⌋` elements each, chunks `⌊⌊T/2⌋/⌊G/2⌋⌋` groups each, all labels are evenly
spaced, and the top tree is rebuilt with evenly spaced labels. This costs O(n), and
Theorem B shows that it never happens.

### 2.9 Parameters

| Symbol | Meaning | Proof value | Prototype default |
|---|---|---|---|
| `L` | `⌈log₂ N⌉`, but at least `L₀` | `L₀ = 8` (§4.7) | `L₀ = 4` |
| `G` | group split threshold | `2L` | `2L` |
| `T` | chunk capacity | `3L²` | `L²` |
| `θ` | PQ threshold | `⌊2T/3⌋` | same |
| `B_e` | element label bits | `2G + ⌈log₂(8G+8)⌉ + 8` **[fix 2]** | `G + ⌈log₂(8G+8)⌉ + 8` |
| `B_g` | group label bits | `2g' + ⌈log₂(8g'+8)⌉ + 8`, `g' = ⌊3T/G⌋` | same |
| `K_G, K_C` | split moves per insert | `4, 4` | `4, 4` |
| `K_R` | top steps per insert | `4` | `2` |
| `a` | top branching parameter | `8` | `8` |
| `s` | sweep steps per job per draining ancestor | `11` (`≥ 9` suffices, §4.5.3) | `8` |
| `β` | label bits per top table | `6a = 48` (`≥ 34` suffices, §4.5.5) | `4a + 8 = 40` |
| `H` | top height | `⌈log_a m_max⌉ + 1`, `m_max ≥` max number of chunks | same |
| `K_B` | rebuild steps per operation | `4` | `4` |

The proof values are chosen so that the inequalities of §4 hold with room to spare. They
are larger than necessary; §5 compares them with the thresholds found empirically. The
floor `L₀ = 8` makes every inequality of §4.7 hold exactly, with no "for `L` large enough".

---

## 3. Correctness

Correctness never depends on timing. The background processes can be arbitrarily late or
interleaved, and splits can even never finish.

The facts used are the guards, plus the top structure's structural invariants (Lemma T2),
which hold under any timing. The table lookups of a sweep step rely on T2: in the prototype
they would raise an exception, rather than fail a guard, if T2 did not hold.

The proof covers the WBBT top structure (`top="wbbt"` in the prototype). The prototype's
simpler `SimpleTop`, used in some tests, is not covered.

### 3.1 The safety invariant

A core satisfies **INV-S** if:

1. **Lists.** The element, group and chunk lists are well-formed doubly linked lists, and `H`
   is the first element.
2. **Contiguous nesting.** Concatenating the element runs of the groups, in group-list
   order, gives the element list. Concatenating the group runs of the chunks, in chunk-list
   order, gives the group list.
3. **Sortedness.**
   * element labels strictly increase within each group;
   * group labels strictly increase within each chunk;
   * chunk tags strictly increase along the chunk list (dead chunks included).

INV-S says nothing about sizes, states, the priority queue or the top tree's internals.

**Lemma 3.1 (keys).** Under INV-S, keys strictly increase along the element list.
Consequently, for elements `x`, `y`, `order(x, y)` holds iff `x` precedes `y`.

*Proof.* Let `x` precede `y`.
* If they are in the same group, compare their element labels (3a).
* If they are in different groups of the same chunk, `group(x)` precedes `group(y)` in that
  chunk by contiguity (2), so the group labels are ordered by (3b).
* Otherwise `chunk(x)` precedes `chunk(y)` by contiguity, and the tags are ordered by (3c).

In every case the first differing component of the key decides, and it decides `<`. The
converse holds because `<lex` is a strict total order. ∎

### 3.2 Preservation

**Lemma 3.2 (guarded primitives).** Each primitive either succeeds and preserves INV-S, or
fails a guard and leaves the element list unchanged. The primitives are: element insertion,
`StartSplit`, a group or chunk split move (including family moves), group removal,
reservation, the O(1) part of `insertAround`, a sweep step and drain start.

*Proof sketch.* Take each primitive in turn.
* **Element insertion.** It links `y` between `x` and `next(x)` in `x`'s group. The new label
  lies strictly between the labels of `x` and its successor in the group (if any), and below
  `2^B_e`. The guard is exactly this condition.
* **`StartSplit`.** It inserts two empty groups next to `g` in `g`'s chunk. Their labels lie
  between the labels of `g`'s neighbours within the chunk. No run changes.
* **A split move.** The sibling-adjacency guard ensures that the moved member is
  contiguous with the receiving run. The new label is above (below) every label of the
  receiving run, which is again guarded. Removing an end member keeps the source sorted.
  The element (group) list itself is unchanged.
* **A family move.** It is three group moves, each of the above form.
* **Group removal.** It removes an empty run.
* **Reservation.** It links two empty chunks around `x`. Their tags are written only
  through guarded writes.
* **Top tag writes.** Each one is guarded against the two chunk-list neighbours, so (3c)
  is preserved.

* **Everything else** changes no list, label or tag, so INV-S is unaffected. This covers:
  * path-copy steps and range pointers;
  * weight updates;
  * drain start, apart from its guarded table insertions;
  * drain finish;
  * PQ updates;
  * chunk retirement;
  * tombstone marking;
  * the preparation steps of a new core.

Only element insertion mutates the element list, and it checks its guard first. ∎

**Lemma 3.3 (fallback).** FALLBACK reads only the element list, and its output satisfies
INV-S with the same element list. It keeps every element record: its identity, its
liveness and its position. After FALLBACK, the retried element insertion passes its guard.

*Proof.* FALLBACK builds evenly spaced labels at each level from a fixed list, so INV-S
holds by construction. After it, every element gap is at least `2^B_e/(⌊G/2⌋+1) ≥ 2`, and the
last element of a group has room `2^B_e/(⌊G/2⌋+1) > Δ_e`. So the retried guard holds (§3.4). ∎

Lemma 3.2 lets partial mutations of the group, chunk or top structures precede a failed
guard (§2.8). Since FALLBACK runs immediately and reads only the element list, such partial
states are discarded.

**Theorem 3.4 (core).** Every core satisfies INV-S between operations, and its element list
(live elements, after `H`) equals the abstract list of the operations applied to it.

*Proof.* By induction over primitives, using Lemmas 3.2 and 3.3. ∎

### 3.3 The wrapper

**Invariant R.** `cur` satisfies Theorem 3.4 and its live sequence is the abstract list `A`.
If `nxt` is being filled, its live sequence equals the subsequence of `A` that lies before
the cursor (in `cur`'s element list).

(Before `nxt`'s preparation ends there is no cursor and `nxt` is empty. Treat the cursor
as sitting at the first element after the sentinel.)

*Preservation.* Element records survive FALLBACK (Lemma 3.3), so the cursor and the
handles' slots stay valid.
* **Insert after a copied `x`.** The new `y` is placed directly after `x`, which is before
  the cursor, so it must be in `nxt` immediately after `x`, and it is mirrored there.
  Inserting after the sentinel counts as inserting after a copied element once preparation
  has ended. Before that, `y` lands at or after the cursor's start and is copied later.
* **Insert after an uncopied `x`.** `x` is live (§1), and the cursor passes a live element only
  by copying it. So `x` is at or after the cursor, and `y` is after it and will be copied
  later.
* **Delete.** It marks the element dead in both cores if it was copied, and only in `cur`
  otherwise.
* **Copy step.** It appends the cursor's element if it is live, then advances the cursor.

When the cursor reaches the end, `nxt`'s live sequence is `A`, so swapping preserves R. ∎

**Theorem A** follows from Invariant R and Lemma 3.1.

### 3.4 Conditions on parameters for Theorem A

Theorem A needs only that FALLBACK's layout is valid and that the retried insertion
passes. Sufficient conditions:
* `2^B_e ≥ 2(⌊G/2⌋+1)` and `Δ_e < 2^B_e/(⌊G/2⌋+1)`;
* the analogous conditions for `B_g`;
* for the top tree, `2^β > max(a, ⌈m_F/a^(H−1)⌉)`. FALLBACK's tables have at most `a`
  entries below the root, and the root gets the rest. Here
  `m_F ≤ (N + 1)/⌊G/2⌋ + 1` bounds the number of chunks FALLBACK creates.

All parameter sets in §2.9 satisfy these with a wide margin. The adversarial review showed
that the `β` condition is needed: with `β = 3`, `a = 8`, FALLBACK produced equal tags.

---

## 4. Cost

### 4.1 What has to be shown

An operation at the wrapper level performs at most `K_B + 2` core operations: its own
insertion in `cur`, possibly a mirror insertion in `nxt`, and up to `K_B` copy insertions.
Each core insertion does O(1) work plus `K_G` group moves, `K_C` chunk moves and `K_R` top
steps. So Theorem B follows from these facts:

* **(K1)** no guard ever fails (no FALLBACK);
* **(K2)** the PQ's slow path is never taken;
* **(K3)** every top step is O(1): tables have O(a) entries, an entry lies in O(1) tables, and
  each step touches O(1) tables;
* **(K4)** labels and tags have `O(L)` bits.

The proof goes bottom-up: groups, chunks, reservation, top, wrapper. Each level uses only
size bounds from the levels below.

### 4.2 Groups

Let `k_G := ⌈G/(K_G−1)⌉ + 1`.

**Lemma G1 (group split).** Let `K_G ≥ 2`, and let a group `g` start splitting at size `G`.
Then `g` is removed after at most `k_G` insertions into its family. At removal, both siblings
have sizes in `[(G−3)/2, (G + k_G + 3)/2]`.

*Proof.* Only insertions into the family drive `g`'s split. Each one adds at most one
element to `g` and then removes up to `K_G`. So after `i` insertions, `size(g) ≤ G − (K_G−1)·i`
while `g` is nonempty. `g` is therefore empty after at most `⌈G/(K_G−1)⌉` insertions and
removed by the next move, which is at most one more insertion.

For balance, let `d = size(g⁻) − size(g⁺)`. An insertion changes `d` by at most 1. Each move
goes to the smaller sibling, so it decreases `|d|` (or moves it from 0 to 1). Hence
`|d| ≤ 1` after every drive that makes at least two moves. The last drive may make fewer
moves, and the removal costs one more insertion, so `|d| ≤ 3` at removal. The siblings
together hold `G + (number of insertions) ≤ G + k_G` elements. ∎

With `K_G = 4`: `k_G ≤ G/3 + 2`, and freshly quiet siblings have size at most `2G/3 + 3 < G`.

**Corollary G2.** No group exceeds `G + 1` elements. The "immediate split of a freshly quiet
oversized sibling" in the prototype (`_remove_group`) is unreachable. This explains why the
mutation that deletes it (M20 in `docs/TESTING.md`) is equivalent.

**Lemma G3 (lifetime).** Let `g_min = ⌈(G−3)/2⌉`. A group receives at most

```
U_G := max(2k_G + G − g_min,  G − 1 + k_G)                       user insertions, and
A_G := max(⌊(G + k_G + 3)/2⌋ + G − g_min + k_G,  G + k_G)        arrivals (insertions plus moves)
```

over its lifetime. For `K_G = 4` these are at most `⌈4G/3⌉ + 6` and `⌈3G/2⌉ + 7`.

*Proof.* A sibling's life has three phases.
* As an overflow node, it receives at most `k_G` user insertions (G1).
* As a quiet node, it starts with at least `g_min` elements and splits at `G`, so it
  receives at most `G − g_min` insertions.
* While splitting, it receives at most `k_G` insertions.

The sum is `2k_G + G − g_min`, at most `7G/6 + 6` for `K_G = 4`. The sentinel's first group
starts with one element: `G − 1 + k_G`, at most `4G/3 + 1` for `K_G = 4`. FALLBACK groups do not arise (K1). For arrivals, add the
overflow phase's at most `⌊(G + k_G + 3)/2⌋` arrivals (G1) to the user insertions of the two
later phases. ∎

**Lemma G4 (element labels).** No element-level guard fails if

```
Δ_e = ⌊2^(B_e−1)/(8G+8)⌋ ≥ 2^(U_G)      and      A_G ≤ 8G + 7.
```

*Proof.*
* **Gaps.** Every gap between consecutive elements of a group is either created by a push
  (exactly `Δ_e`) or obtained from such a gap by halvings, one per `labBetween`. A gap of
  width `w` survives `k` nested halvings with width at least `⌊w/2^k⌋`. A group sees at most
  `U_G` halvings in its lifetime.
* **Pushes.** There are at most `A_G` pushes in each direction from `labEmpty = 2^(B_e−1)`,
  each of size `Δ_e`.
* **Adjacency.** The adjacency guards hold by contiguity and the family structure. ∎

The first condition needs `B_e ≥ 4G/3 + 7 + log₂(8G+8)`. The prototype's
`B_e = G + ⌈log₂(8G+8)⌉ + 8` falls short by about `G/3` bits. The adversary would have to
put all of a group's insertions, over its whole lifetime, into one gap. The campaign never
came close (at most 40 of 59–63 bits used), but the proof needs the wider label: **[fix 2]**
sets `B_e = 2G + ⌈log₂(8G+8)⌉ + 8`, which is still `Θ(L)`.

### 4.3 Chunks

**Invariant F (families stay together).** The three groups of a family lie in the same chunk.

*Preservation.* `StartSplit` creates both siblings in `g`'s chunk. A chunk move transfers a
whole family **[fix 3]**. Group removal only shrinks a family. ∎

Under F, a chunk's size changes only through user insertions into it and through chunk
split moves. Element moves between chunks never happen.

Without F (the prototype before fix 3), a chunk split can leave `g⁻` in one chunk and `g` in the
next. Group moves then transfer elements into a *quiet* chunk without a user insertion
there. Each such family transfers at most `G + k_G` elements, but the zeroing game of §4.4
charges this as a `δ = O(L)` error in *every* round. That costs a term `δ·H_m = Θ(L²)`, as
large as `T` itself. Family moves remove the issue for the price of three relinks per move.

Write `g_min := ⌈(G−3)/2⌉` for the least size of a freshly quiet group (G1),
`units(s) := ⌊s/g_min⌋ + 1`, and `u_max := G + k_G`.

**Lemma C1 (chunk split).** Let `K_C ≥ 2`, and let a chunk `x` start splitting with size `s₀`.
Then `x` is removed after at most `k_C(s₀) := ⌈units(s₀)/(K_C − 1)⌉ + 1` insertions into its
family. At removal, both siblings have size at most `⌊(s₀ + k_C + u_max + 2)/2⌋`.

*Proof.*
* **Units.** A *unit* of a chunk is a group family or a quiet group, and a chunk move
  transfers exactly one unit (fix 3).
  * A family holds at least `G` elements. Every quiet group holds at least `g_min ≥ 1`
    elements (G1), except the core's first group, which holds the sentinel.
  * So when the split starts, `x` holds at most `units(s₀)` units.
* **Emptying.** During the split, an insertion into `x` adds at most one unit to `x`.
  * The only new unit can come from the dissolution of the family that the insertion drives,
    which turns one family into two quiet groups. `StartSplit` turns one quiet group into one
    family.
  * Insertions into `x⁻` or `x⁺` add nothing to `x`.
  * Each insertion into the family then moves `K_C` units out of `x` while `x` is nonempty.
  * So after `i` insertions a nonempty `x` has at most `units(s₀) − (K_C − 1)·i` units. It is
    empty after `⌈units(s₀)/(K_C−1)⌉` insertions and removed by the next move, at most one
    insertion later.
* **Balance.** Let `d = size(x⁻) − size(x⁺)`. A move goes to the smaller sibling and transfers
  between 1 and `u_max` elements (G1).
  * If `|d| ≤ u_max + 1` before a move, then `|d| ≤ u_max` after it.
  * An insertion changes `|d|` by at most 1.
  * So `|d| ≤ u_max` after every drive that makes a move, and `|d| ≤ u_max + 2` at removal.
  * The siblings hold at most `s₀ + k_C` elements in total. ∎

**Lemma C2 (PQ slow path).** Let every chunk start splitting with size at most `T`
(Lemma R), and let

```
c_max := ⌊(T + k_C(T) + u_max + 2)/2⌋ ≤ θ        (I4).
```

Then freshly quiet chunks have size at most `c_max ≤ θ`, so `enterIfAbove` is never called
on a chunk above `θ` (K2). For the proof parameters, `c_max ≤ 1.5L² + 11L/6 + 3.5 ≤ 2L² = θ`
for `L ≥ 6`.

**Lemma C3 (group labels).** Let `I_C := T + 2k_C(T)`, and let `g' := ⌊3T/G⌋` be the group
labels' size parameter, so `Δ_g = ⌊2^(B_g−1)/(8g' + 8)⌋`. Define

```
D_C := 1 + ⌊I_C/g_min⌋,      P_C := 6·(units(T) + k_C(T)) + 1 + ⌊I_C/g_min⌋.
```

If `Δ_g ≥ 2^(D_C + 1)` and `P_C ≤ 8g' + 7` (condition I10), no group-level guard fails.

*Proof.* Fix a chunk `X`.
* **Lifetime.** `X` receives at most `I_C` user insertions in its life:
  * at most `k_C` as an overflow chunk;
  * at most `T` while quiet (Lemma R);
  * at most `k_C` while splitting.

  The structure of the argument is that of Lemma T5.
* **Label events.** Group labels in `X` change only through these events:
  * **`StartSplit(g)`.** It inserts `g⁻` and `g⁺` next to `g`, halving the two gaps around
    `g`, or pushing by `Δ_g` when `g` is at an end. Afterwards `g` is splitting and never
    splits again. `g⁻, g, g⁺` stay consecutive, because only quiet groups split.
  * **Removal of an emptied `g`.** It merges `(g⁻, g)` and `(g, g⁺)`.
  * **Chunk moves.** A group arriving at an end gets a pushed label, creating a gap of exactly
    `Δ_g`. A group leaving at an end merges an end gap with the boundary.
* **Roots and children.** Call `g^±` the *children* of `g`. The *roots* are the groups that
  arrived by moves (possibly as a whole family that was already splitting) and `X`'s first
  group.
* **Histories.** Give gaps histories as in Lemma T5, with "`StartSplit` of an endpoint" in
  place of "drain of an endpoint". A pushed gap starts with the empty history.
* **Claim 1.** Every interior gap is at least `⌊Δ_g/2^D⌋`, where `D` is the length of its
  history. The proof is as in Claim 1 of T5. A pushed gap is exactly `Δ_g`.

*Claim 2: at most `⌊I_C/g_min⌋` children start splitting in `X`'s life.*
* **Charging.** Charge each child `x` of `p` that starts splitting:
  * the insertions into `x` from the end of `p`'s split until `x` starts splitting;
  * the user insertions into `p`'s family during `p`'s split, or half of them if `x`'s
    sibling also starts splitting.

  This way no insertion is charged more than once in total. Every charged insertion is into
  `X` during its life.
* **Each charge is at least `g_min`.** When `p`'s split ends, its children hold
  `s⁻ + s⁺ = G + i` elements, where `i` is the number of family insertions, and each holds
  at most `⌊(G + i + 3)/2⌋` (G1). A child then grows only by user insertions, and starts
  splitting at exactly `G`.
  * If only `x` splits, it is charged `i + G − s_x ≥ i + G − ⌊(G+i+3)/2⌋ ≥ g_min`.
  * If both split, together they are charged `i + (G − s⁻) + (G − s⁺) = G ≥ 2g_min`.
* **Conclusion.** The total charge is at most `I_C`, which proves Claim 2.

*Claim 3: at most 2 roots start splitting within one history.* Let `Φ` be the number of
endpoints of the history's current gap that are roots and have not started splitting.
* At the start of a history, `Φ ≤ 2`.
* A halving makes the splitting endpoint stop counting, and the new endpoint is a child.
* A merge at a removed `g` replaces the endpoint `g`, which no longer counts, by `g^±`.
  * Usually `g^±` are children, and `Φ` is unchanged.
  * The exception is a family that arrived already splitting. Then `g^±` are unsplit roots.
    But `g`'s only gaps are its two push gaps, and they stay unchanged until the merge,
    because `g^±` cannot split while `g` exists. So such a history started at one of those
    push gaps with `Φ ≤ 1`, and no root split before the merge. So at most 2 roots split.

Hence a gap about to be halved has `D ≤ 1 + ⌊I_C/g_min⌋ = D_C`, and size at least
`⌊Δ_g/2^(D_C)⌋ ≥ 2`.

*Pushes.* Consider one end of `X`. Labels are pushed there by arriving groups and by
`StartSplit` of the current end group.
* **Arrivals.** The source chunk moves at most `units(T) + k_C` units in all: its units at
  the split start, plus at most one new unit per insertion. Each unit has at most 3 groups.
* **End splits by roots.** Each root splits at most once, and there are at most as many
  roots as arrivals, plus 1.
* **End splits by children.** By Claim 2 there are at most `⌊I_C/g_min⌋` of these in all.
  This covers children exposed at an end because units left `X` during its own split.
* **Conclusion.** There are at most `P_C` pushes per end. As in G4, `8g' + 7` pushes fit
  between `labEmpty` and either end of the label space. ∎

For the proof parameters (`g_min = L − 1`, `g' = ⌊9L/2⌋`):
* `D_C ≤ 1 + (3L² + 2L + 6)/(L − 1) ≤ 3L + 10`, against a budget of
  `B_g − 1 − log₂(8g'+8) ≥ 2g' + 7 ≥ 9L + 6`;
* `P_C ≤ 27L + 58 ≤ 36L + 3 ≤ 8g' + 7` for `L ≥ 7`.

The draft v0.2 sketch of C3 claimed that a fresh sibling needs at least `(G+3)/2`
insertions before it splits. That is the *upper* bound of G3. The correct lower bound is
`g_min`, and only after the family insertions are charged to the children. The first v0.3
version counted depth along lineages and missed end splits exposed during `X`'s own split.
Both were found by the adversarial review (§6.6).

### 4.4 Reservation: the zeroing game

**Theorem Z (zeroing game; Dietz–Sleator 1987, Thm 5, scaled and with decreases).** Take
variables `x₁, …, x_n ≥ 0`, initially 0. Each round, the player sets a maximal `x_i` to 0. Then
the adversary adds nonnegative amounts summing to at most `R`, and may decrease any
variables (keeping them nonnegative). Then always

```
x_i ≤ R · (H_{n−1} + 1),          H_k = 1 + 1/2 + … + 1/k.
```

*Proof.* Let `S_k` be the sum of the `k` largest values. We show by induction over rounds
that `S_k ≤ k·R·(H_{n−1} − H_{k−1} + 1)` for all `k`.
* The case `k = n` holds because the total is at most `nR`.
* For the step, zeroing a maximal value `z ≥ S_{k+1}/(k+1)` and adding `R` gives
  `S_k' ≤ S_{k+1} − z + R ≤ (k/(k+1))·S_{k+1} + R`. Substituting the bound for `S_{k+1}`
  gives the bound for `S_k`.
* Decreases never increase any `S_k`.

`k = 1` is the claim. New variables entering at value 0 are covered by taking `n` as the
maximum count. ∎

The proof also shows that zeroing a value within `δ` of the maximum gives the bound
`(R + δ)(H_{n−1} + 1)`. This is the variant that fix 3 avoids needing.

**Lemma R (chunk sizes).** Let `J` bound the length of a top job in steps (Lemma T4), and
let `R := ⌈J/K_R⌉ + 1`. Let `m` bound the number of chunks in the core. Then every quiet chunk
has size at most

```
T_hard := θ + R · (H_{m−1} + 1).
```

*Proof.* A *round* runs from one pop to the next.
* **Adds per round.** In an insertion, the user's element is linked before `Reserve` runs,
  so the pop insertion's add precedes its pop. Each insertion advances the job by `K_R`
  steps, and the next pop happens in the insertion during which the job ends. So the adds
  between two pops come from at most `⌈(J+1)/K_R⌉ ≤ R` insertions.
* **A different count.** The checker's `res_round` counts insertions from the pop insertion
  to the job's end, which is at most `⌈J/K_R⌉ + 1`. That is also `≤ R`.
* **Variables.** `x_c = max(0, size(c) − θ)` for quiet chunks `c`.
* **Zeroing.** The pop removes a chunk of maximal size, hence of maximal `x_c`, which is the
  player's zeroing. A splitting chunk leaves the game.
* **New variables.** Chunks entering the quiet state enter at `x = 0` by Lemma C2.
* **Adds.** Under invariant F, the only increases are user insertions, one element per core
  insertion, so the adds per round total at most `R`.
* **Idle periods.** If the PQ is empty when a job ends, all variables are 0. The next
  insertion that pushes a chunk above `θ` pops it in the same core operation.

Theorem Z applies. ∎

**What this requires of the parameters.** Lemma C2 and the reservation count both use
`T_hard ≤ T`, i.e. `R(H_{m−1} + 1) ≤ T/3`. With `J ≤ (s+3)H` (Lemma T4), `H ≈ L/3`, and
`H_{m−1} + 1 ≤ 0.7L + 2`, the left side is about `0.23(s+3)·L²/K_R`. The condition becomes

```
c_T · K_R  ≳  0.7 · (s + 3)        (T = c_T L²)
```

The proof parameters give `3 · 4 = 12 ≥ 9.8` for `s = 11`. `SPEC.md` §7.1 estimated
`c_T·K_R ≳ 4.2`, but used the measured job length `6H + 4` instead of the provable `(s+3)H`.

**Number of chunks.** Every reservation pops a quiet chunk of size above `θ`. That chunk
became quiet with size at most `c_max` (Lemma C2), or it is the core's first chunk, which started
with size 1. So its quiet period received at least `θ + 1 − c_max` user insertions, and
distinct reservations use distinct quiet periods. A core receives at most `N` insertions
(Lemma W), and each reservation adds 2 chunks. Hence

```
m ≤ m_max := 3 + 2·⌊N/(θ + 1 − c_max)⌋        (≈ 12N/T for the proof parameters).
```

`H` is chosen with `a^(H−1) ≥ m_max` (I8). By (F5) of §4.5.2, the root then has exactly one
child, which never drains.

### 4.5 Top structure

#### 4.5.1 Order invariant and guards

Write `A_h(c)` for the live ancestor of chunk `c` at height `h`.

* **(P) Paths.** For every chunk `c` and height `h`, `p_h(c)` is either `A_h(c)`, or a ghost
  whose target is `A_h(c)`.
* **(W1) Adjacency.** For every ghost `v`, the entries `v⁻, v, v⁺` are consecutive in every
  table that contains `v`.
* **(W3) Tables.** For every chunk `c` and every `j ≥ 1`, `p_{j−1}(c)` is an entry of
  `p_j(c)`'s table.
* **(O) Global order.** For every height `h`, there is a linear order `≺_h` on the nodes of
  height `h` (and `≺_0` is the chunk-list order) such that:
  * **(O1)** in every table at height `h`, label order agrees with `≺_{h−1}`;
  * **(O2)** along the chunk list, `p_h(c)` is non-decreasing with respect to `≺_h`;
  * **(O3)** for every ghost `v`, `v⁻` and `v⁺` are its immediate `≺_h`-predecessor and
    successor.
* **(S) Sides.** For every ghost `v`:
  * the side marking of `v`'s entries is monotone (all LEFT before all RIGHT) with respect to
    `≺_{h−1}`;
  * every entry `p_{h−1}(c)`, for `c` in `range(v)`, is in `v⁻`'s table if it is LEFT and in `v⁺`'s
    table if it is RIGHT.

`SPEC.md` stated the cost invariants W1–W4. (O) replaces W2 and W4: contiguity of ranges
follows from (O2), and W4 is now a consequence rather than an invariant.

**Lemma T1 (sorted tags).** (O1), (O2) and (W3) imply that tags strictly increase along the
chunk list.

*Proof.* Let `c` precede `d`, and let `j` be the largest level with `p_j(c) ≠ p_j(d)`. It exists
and is below `H`, since `p_H` is always the root, and `p₀(c) = c ≠ d`.
* Both `p_j(c)` and `p_j(d)` are entries of the common table `p_{j+1}` (W3).
* By (O2), `p_j(c) ≺_j p_j(d)`, so by (O1) the label of `p_j(c)` is smaller.
* Field `j+1` of `tag(c)` is therefore smaller than that of `tag(d)`, and all higher fields
  are equal. Fields are `β`-bit digits. ∎

**Lemma T2 (preservation).** Every top-level operation preserves (P), (W1), (W3), (O) and (S).

*Proof sketch.*
* **`insertAround`.** Place `y` immediately before `x` and `z` immediately after `x` in `≺_0`.
  Their labels go next to `x` in every table holding `x` (O1). Paths are copied from `x`
  (O2, W3, P). No drain step can run during the copy (§2.6).
* **`StartDrain(v)`, part 1.** Place `v⁻` and `v⁺` immediately around `v` in `≺_h` (O3). For a
  table holding `v`, the new entry sits between `v` and its table neighbour `w`, and `w ≺ v⁻`
  because `v⁻` is adjacent to `v` in `≺_h` (O1, W1).
* **`StartDrain(v)`, part 2.** The new tables copy entries in `v`'s order (O1). Sides follow
  the partition boundary in table order, and a ghost child takes the side of its targets,
  which surround it (S). Every referenced entry is copied (S, W3).
* **`SweepStep(v)`.** It changes one `p_h(c)` from `v` to `v⁻`, with `c` the first chunk of
  `range(v)`.
  * Its predecessor has `p_h ≺ v`, hence `≼ v⁻` (O3), and its successor has `p_h ≽ v`, so (O2)
    is kept. The RIGHT case is symmetric.
  * `v⁻` is in the table `p_{h+1}(c)`. That table holds `v` by (W3), hence `v⁻` by (W1).
  * `p_{h−1}(c)` is in `v⁻`'s table by (S).
  * (P) holds because `A_h(c) = v⁻`, since `v`'s left part went to `v⁻`.
  * Monotone sides plus (O2) at height `h−1` mean that `range(v)` is LEFT on a prefix and
    RIGHT on a suffix. So the step always finds a valid end, and its "sides out of order"
    guard never fires.
* **Later insertions into tables holding a ghost.** These come from `insertAround` or from a
  child drain. They go into every table holding the entry, which includes the target table
  when the entry was copied (S), and they inherit the entry's side.
* **`Finish(v)`.** When `range(v)` is empty, no path refers to `v`, so removing it from every
  table preserves everything. ∎

**Corollary.** Every top-level tag write passes its guard, by Lemma T1 applied to the state
after the write. Every table lookup in a sweep step succeeds, by (W1), (W3) and (S).

#### 4.5.2 Preliminaries for the timing proofs

This section and the next three give complete proofs of the top structure's cost
lemmas. Every constant is explicit. `prototype/top_bounds.py` computes them, and the
lemma checker compares them with measured maxima (§4.5.6).

**Hypothesis (I8).** At most `m_max ≤ a^(H−1)` chunks ever exist in a core. Chunks are
never freed, so this also bounds the dead ones.

**Weights.** `w(u)` denotes the *stored* weight, the number the algorithm reads. Write
`ŵ(u)` for the true number of chunks in `u`'s live subtree.

* **(F1) Exactness.** Weights change only in walks, and a walk goes bottom-up. When a walk
  visits `u`, `w` is exact on `u` and on its whole subtree. Between steps, `w(u) = ŵ(u)` for
  every live `u`, except that the ancestors of the running job's `y, z` that the walk has not
  yet visited have `w(u) = ŵ(u) − 2`.
* **(F2) Monotonicity.** A live node's weight changes only by `+2`, when a walk visits it. A
  new target starts with the sum of its children's weights. No weight ever decreases.
* **(F3) Serial jobs.** Jobs run one at a time. Drains start, and sweep steps run, only inside
  walks. A job's path copy is complete before its walk starts.
  * The invariants of §4.5.1 refer to *logical* paths: from its `insertAround` on, `y` and `z`
    are treated as carrying `x`'s path in full.
  * The physical copy, and the range pointers of the levels it has not yet reached, catch up
    one level per step. Nothing reads them earlier.
* **(F4) Origins.** Every node is either one of the `H` nodes of the initial chain (one per
  height), or a target created by `StartDrain`.
* **(F5) The top two levels.** A node of height `H−1` never exceeds `m_max ≤ a^(H−1) < W_{H−1}`,
  so it never drains. Hence the root has exactly one child, its table has exactly one entry,
  and drains happen only at heights `h ≤ H−2`.

**Units.** The live children of a node at height `h` group into *units*. A unit is either a
child that is not a target, or the two targets of one running drain. The two targets of a
drain are adjacent in their parent's child list: they replace their source there, and
neither can drain, nor be separated by a partition, before the drain finishes.

**Constants.** For `h ≥ 1`, with `W_h = 2aʰ`:

```
K_h = ⌊(W_h + 2)/(s − 2)⌋ + 1        funded jobs per drain                    (T3)
Π_h = W_h + 2 + 2K_h                 weight of a target pair                   (T3)
τ_1 = a + 1,   τ_h = aʰ + 1 + Π_{h−1}   heaviest fresh target                  (T0)
λ_1 = a,       λ_h = aʰ + 1 − Π_{h−1}   lightest fresh target                  (T0)
Θ_h = τ_h + 2K_h                     heaviest blocked target                   (T3)
γ_h = W_h + 1 − τ_h                  least growth of a target before it drains (T5)
```

For the proof parameters `a = 8`, `s = 11`:

| `h` | `W_h` | `K_h` | `Π_h` | `τ_h` | `λ_h` | `Θ_h` | `Θ_h/W_h` | `γ_h` |
|---|---|---|---|---|---|---|---|---|
| 1 | 16 | 3 | 24 | 9 | 8 | 15 | 0.938 | 8 |
| 2 | 128 | 15 | 160 | 89 | 41 | 119 | 0.930 | 40 |
| 3 | 1024 | 115 | 1256 | 673 | 353 | 903 | 0.882 | 352 |
| 4 | 8192 | 911 | 10016 | 5353 | 2841 | 7175 | 0.876 | 2840 |
| `h → ∞` | | `≈ W_h/9` | `≈ 1.22·W_h` | | `≈ 0.347·W_h` | | `→ 7/8` | |

**Lemma T0 (partition).** Let `StartDrain(v)` run at height `h` with `S = w(v)`, and let
`U` be the largest weight of a unit among `v`'s children.
1. It gives up only if `v` has one child, or two children that form a unit.
2. Otherwise both parts weigh at least `⌈S/2⌉ − U` and at most `⌊S/2⌋ + U`.
3. At `h = 1` (unit weights, no pairs) the parts weigh exactly `⌊S/2⌋` and `⌈S/2⌉`.

*Proof.* Let `w₀, …, w_{n−1}` be the children's stored weights and `σ_k` their prefix sums.
The code partitions by `σ_n`, which equals `S = w(v)` by (F1). The code
picks the largest `k ≤ n−1` with `σ_k ≤ ⌊S/2⌋`, then sets `k := max(k, 1)`. At `h ≥ 2`, if
children `k−1, k` form a pair, it moves `k` one place right. If that reaches `n`, it sets
`k := n−1` and moves left while `k−1, k` form a pair. It gives up if `k = 0`. The left part is
`σ_k`, the right part `S − σ_k`.
* **Greedy cut.** The left part is `σ_k ≤ ⌊S/2⌋`. If `k < n−1`, then `σ_{k+1} ≥ ⌊S/2⌋ + 1`, so
  the right part is `S − σ_{k+1} + w_k ≤ ⌈S/2⌉ − 1 + U ≤ ⌊S/2⌋ + U`. If `k = n−1`, the right part
  is one child, at most `U`.
* **`k := max(k, 1)`.** This changes `k` only if `w₀ > ⌊S/2⌋`. Then the left part is `w₀ ≤ U`
  and the right part is below `S/2`.
* **Pair shift right.** The new left part is `σ_{k−1} + (w_{k−1} + w_k)`. Here
  `σ_{k−1} ≤ ⌊S/2⌋`, because `k−1` is at or before the greedy cut (`σ₀ = 0` in the forced
  case), and the pair is one unit. So the left part is at most `⌊S/2⌋ + U`. The right part
  only shrinks.
* **Pair shift back.** This happens only when the last two children form a pair. Pairs are
  disjoint, so the loop takes one step, to `k = n−2`. It reaches `0` only if `n = 2`, which
  is case 1. Otherwise the right part is that pair, at most `U`, and the left part is
  `σ_{n−2} ≤ σ_{n−1}`. Here `σ_{n−1} ≤ ⌊S/2⌋`, because the cut before the right shift sat at
  `n−1`, either greedily or as the forced `k = 1` with `n = 2`.

In every case both parts are at most `⌊S/2⌋ + U`. So each is at least `S − ⌊S/2⌋ − U`, which
proves 2. If `n = 1`, the code gives up. That proves 1. At `h = 1` every weight is 1 and
`⌊S/2⌋ ≤ n − 1`, so the greedy cut is exactly `k = ⌊S/2⌋`, which proves 3. ∎

#### 4.5.3 Drain timing

**Lemma T3 (drain timing).** Assume `Θ_h ≤ W_h` for all `1 ≤ h ≤ H−2` and `Π_{h−1} ≤ W_h`
for all `2 ≤ h ≤ H−2` (condition I6). Then at every moment between steps, except that (c)
is claimed only between jobs:

* **(a)** every live node of height `h ≤ H−1` that is neither the root nor a target has
  `w ≤ W_h`;
* **(b)** every drain, of some `v` at height `h`, started with
  `|range(v)| = w(v) = S_v ∈ [W_h + 1, W_h + 2]`, and `StartDrain` never gives up;
* **(c)** if, between jobs, a drain of `v` at height `h` is unfinished after `f` funding jobs,
  then `|range(v)| ≤ S_v − (s−2)f`. So it finishes during its `K_h`-th funding job at the
  latest. (While a funding job runs, the range can exceed this bound by 2, because the job's
  path copy runs before its sweeps.);
* **(d)** if a drain of `v` at height `h` is running and has been funded by `f` jobs so far,
  then `w(v⁻) + w(v⁺) = S_v + 2f ≤ Π_h`. Moreover each target `t` satisfies
  `λ_h ≤ w₀(t) ≤ τ_h` and `w(t) ≤ w₀(t) + 2f ≤ Θ_h`, where `w₀(t)` is its weight at creation.

Here a *funding job* of `v` is a job whose walk visits a target of `v` while `v` is unfinished.
Such a walk performs up to `s` sweep steps of `v`.

*Proof.* By induction over steps, for all heights at once. Initially there are only the
chain nodes, of weight 1, and no drains. Path-copy steps change no weight and start no
drain. Their effect on ranges is accounted for in case 2 below. So consider a walk step
visiting `u` at height `h`. The root and heights `≥ H−1` are covered by (F5). Every other
node keeps its weight, except as described.

*Case 1: `u` is not a target.* Before the step, `w(u) ≤ W_h` by (a), so after `w(u) += 2` it is
at most `W_h + 2`. If it is at most `W_h`, (a) is kept. Otherwise `StartDrain(u)` runs with
`S = w(u) ∈ [W_h + 1, W_h + 2]`, exact by (F1).
* **Range.** By (P), a chunk `c` below `u` has `p_h(c) = u`, or `p_h(c)` is a ghost with target
  `u`. The second is impossible, since `u` is not a target. So `range(u)` is exactly the
  `S` chunks below `u`. This gives (b) apart from giving up.
* **Units.** Let `h ≥ 2`. A child of `u` that is not a target weighs at most `W_{h−1}`. If it lay
  on this walk, its own step has already ended, and (a) held afterwards. If it started
  draining during this walk, it has been replaced by a pair with `f = 0`. A pair weighs at
  most `Π_{h−1}` by (d). So `U ≤ Π_{h−1}`, since `W_{h−1} < Π_{h−1}`. At `h = 1`, `U = 1`.
* **No giving up.** A single child would weigh at most `W_{h−1} < W_h < S`. A single pair would
  weigh at most `Π_{h−1} ≤ W_h < S`. Both contradict the total `S`. So by T0.1, `StartDrain`
  does not give up.
* **Fresh targets.** By T0, each target weighs at most `⌊(W_h+2)/2⌋ + Π_{h−1} = τ_h` and at
  least `⌈(W_h+1)/2⌉ − Π_{h−1} = λ_h`. At `h = 1`, T0.3 gives `a` and `a + 1`. With `f = 0`
  this is (d).

The new targets are not subject to (a). The ghost `u` has left the live tree.

*Case 2: `u` is a target of a ghost `v`.* This job is `v`'s `(f+1)`-th funding job.
* **Count.** `v` is unfinished after `f` completed funding jobs, so by (c),
  `0 ≤ S_v − (s−2)f`. Hence `f ≤ (W_h + 2)/(s−2)` and `f + 1 ≤ K_h`.
* **Weights.** `w(u)` grows by 2, and `u` is the only target of `v` that the walk visits. So
  (d) continues with `f + 1 ≤ K_h`. That gives `w(u) ≤ τ_h + 2K_h = Θ_h` and
  `w(v⁻) + w(v⁺) ≤ W_h + 2 + 2K_h = Π_h`.
* **Range.** Only two things change `range(v)`:
  * a sweep step of `v`, which removes one chunk;
  * a path copy that gives `y, z` the entry `p_h(x) = v`, which adds two.

  Other ghosts move chunks only to live targets, and other heights' sweeps change other
  fields. In the second case `A_h(x) ∈ {v⁻, v⁺}` by (P). Between the path copy and the walk
  reaching height `h`, only heights below `h` can drain, and that leaves `A_h(y) = A_h(x)`
  unchanged. So the job that adds the two chunks is itself a funding job of `v`, namely
  this one.
* **(c).** If `v` is still unfinished after this job, every one of its `s` sweep calls moved
  a chunk: a call on an empty range would have finished `v`. So `|range(v)|` dropped by at
  least `s − 2` during this job, which proves (c) for `f + 1`. Hence an unfinished drain has
  had at most `⌊S_v/(s−2)⌋` funding jobs, and it finishes during the next one at the latest.
  That job need not finish it on its first call, since its own path copy may have added 2
  chunks.
* **Release.** If `v` finishes in this step, both targets stop being targets. Each weighs at
  most `Θ_h ≤ W_h` by (d), so (a) holds for them from now on. ∎

**Consequences.**
1. **Drain start.** A node starts draining with weight at most `W_h + 2`.
2. **Funding.** A drain needs at most `K_h ≈ (W_h + 2)/(s−2)` funding jobs.
3. **Blocked targets.** A target never needs to drain while blocked, since it stays at or
   below `W_h`.
4. **Give-up branches.** `StartDrain`'s give-up branches are unreachable.

The bounds are attained at `h = 1`: drain start weight 18, blocked targets 15, pairs 24,
3 funding jobs (§4.5.6). Ghosts whose targets receive no further insertions never finish.
They are harmless: they cost table space, which Lemma T4 counts.

**Checking I6 for all heights.** Expand `K_j ≤ (W_j+2)/(s−2) + 1` in the definitions. For
`h ≥ 2` this gives

```
Θ_h ≤ q·W_h + c_q,     q = 1/2 + s/(a(s−2)) + 2/(s−2),     c_q = 7 + 8/(s−2).
```

So I6 holds if `q < 1`, `Θ_1 = a + 3 + 2⌊(2a+2)/(s−2)⌋ ≤ 2a`, and `Θ_h ≤ W_h` for the finitely
many `h` with `W_h < c_q/(1−q)`. The second inequality, `Π_{h−1} ≤ W_h`, holds whenever
`a ≥ 3` and `s ≥ 4`, since then `(a − s/(s−2))·W_{h−1} ≥ 2a ≥ 4 + 4/(s−2)`.

| `a` | `s` | `q` | Holds for | Fails at |
|---|---|---|---|---|
| 8 | 11 (proof value) | 7/8 | `h ≥ 2` by the closed form; `h = 1`: `15 ≤ 16` | — |
| 8 | 9 | 53/56 | `h ≥ 3` by the closed form; `h = 1, 2`: `15 ≤ 16`, `127 ≤ 128` | — |
| 8 | 8 (prototype default) | 1 | — | `h = 1`: `Θ_1 = 17 > 16`; asymptotically `q = 1` |
| 16 | 8 | 11/12 | all `h` | — |

So `s ≥ 9` suffices for `a = 8`. The draft v0.2 sketch needed `s ≥ 11`, because it bounded a
unit by `2W_{h−1}` instead of `Π_{h−1} ≈ 1.22·W_{h−1}` and did not use the exact partition at
height 1. The proof parameters keep `s = 11` for margin. For `s = 8` the failure is real.
The adversaries drive blocked targets at height 1 to 18 > 16 and drain starts to 20 (§4.5.6),
exactly as the recursion predicts once a released target may exceed `W_1`. That run still
had no fallback, because overweight nodes cost only a few more table entries.

#### 4.5.4 Sizes, tables and step cost

Define `par(e)` for an entry `e` of height `h−1`:
* if `e` is a live node or a chunk, `par(e)` is its live parent;
* if `e` is a ghost, `par(e)` is the live parent of its targets.

For a live node `p`, write `src(p)` for the ghost whose target `p` is, if any.

**Invariant (Q).** Every table that contains `e` is the table of `par(e)` or of `src(par(e))`.

*Proof that every operation preserves (Q).*
* **`insertAround(x, y, z)`.** `y` and `z` enter exactly the tables of `x`, and
  `par(y) = par(z) = par(x)`.
* **`StartDrain(v)`, with `v` live and not a target, and `P = par(v)`.**
  * **The tables holding `v`.** By (Q) they are `P`'s and possibly `src(P)`'s. `v⁻` and `v⁺`
    enter exactly these, and `par(v^±) = P`. For the ghost `v` itself, `par(v)` is still `P`.
  * **Live children `e` of `v`.** They were only in `v`'s table, because `v` has no source. Each
    now also enters the table of its new parent `v^±`, and `src(v^±) = v`.
  * **Ghost entries `g` of `v`'s table.** Since `v` is live, (Q) gives `par(g) = v`. If `g` still
    has chunks, it is copied into the table of the target that receives `g`'s targets
    (`side[g] = side[g⁻]`), which becomes `par(g)`. Otherwise it stays only in `v`'s table, and
    `v = src(par(g))`.
  * **Everything else** keeps its tables, `par` and `src`.
* **`Finish(v)`.** `v` leaves every table, and its own table is dropped. Afterwards `v^±`
  have no source, and nothing remains in `v`'s table. ∎

**Lemma T4 (sizes and cost).** Assume I6 and I8. Define

```
C_1 = W_1 + 2,      C_h = 1 + ⌊(W_h + 1)/λ_{h−1}⌋               (h ≥ 2)
C'_1 = Π_1 + 2,     C'_h = 1 + ⌊(Π_h + 1)/λ_{h−1}⌋              (h ≥ 2)
E_h = C_h + ⌊C_h/2⌋,  E'_h = C'_h + ⌊C'_h/2⌋   for h ≥ 2;   E_1 = C_1, E'_1 = C'_1
```

(Under I6, `λ_h ≥ 2 + 2K_h` and `γ_h = λ_h − 1 ≥ 1` for `2 ≤ h ≤ H−2`, since
`Θ_h = aʰ + 1 + Π_{h−1} + 2K_h ≤ 2aʰ`; also `λ_1 = γ_1 = a`. So all divisions below are
well defined.)

1. A live non-root node of height `h` has at most `C_h` live children. The root has one.
2. The table of a live node of height `h` has at most `E_h` entries. The table of a ghost has
   at most `E'_h`.
3. Every node or chunk is an entry of at most 2 tables.
4. A job has at most `J := (s+3)·H` steps.
5. A step does `O(max_h E'_h)` work.

*Proof.*
1. **Children.** By T3(a) and (d), a live non-root node `u` has `w(u) ≤ W_h` between steps,
   and `w(u) ≤ W_h + 2` in the step where it drains. By (F1), `ŵ(u) ≤ W_h + 2`.
   * **Height 1.** The children are `ŵ(u)` chunks.
   * **Height `h ≥ 2`.** By (F4) and T3(d), every child is either a target created with
     weight `≥ λ_{h−1}` (never decreasing, by (F2)) or the one chain node of height `h−1`
     (weight `≥ 1`). So `(C − 1)·λ_{h−1} + 1 ≤ W_h + 2`.
   * **Root.** (F5).
2. **Tables.**
   * **Live owner.** Let `u` be live. A source is a ghost, so `u ≠ src(·)`. By (Q), every live
     entry of `u`'s table has `par = u`: it is one of `u`'s live children.
   * **Ghost entries.** By (W1), each ghost entry `g` is flanked by its two targets, which are
     live entries of the same table. Distinct ghosts have distinct targets. So there are at
     most `⌊C/2⌋` ghost entries.
   * **Height 1.** Every entry is a chunk, so there are no ghost entries.
   * **Ghost owner.** Let `u` be a ghost. By (Q), its live entries are children of `u⁻` or
     `u⁺`. These two weigh `ŵ ≤ Π_h + 2` together, by T3(d) plus the lag of (F1), and the
     same counting applies with `Π_h + 2` in place of `W_h + 2`.
3. **Tables per entry.** Immediate from (Q).
4. **Job length.** The path copy takes `H` steps. At each of the `H` walk levels there is at
   most one step for `StartDrain`, `s` sweep steps and one step to move up.
5. **Step cost.**
   * `StartDrain` copies at most one table, of `≤ E_h` entries, and inserts into at most 2
     tables (3).
   * A sweep step does O(1) table lookups and one guarded tag write.
   * `Finish` touches the at most `E'_h` entries of its table and at most 2 tables. ∎

For `a = 8`, `s = 11`:

| `h` | `C_h` | `E_h` | `C'_h` | `E'_h` |
|---|---|---|---|---|
| 1 | 18 | 18 | 26 | 26 |
| 2 | 17 | 25 | 21 | 31 |
| 3 | 26 | 39 | 31 | 46 |
| `≥ 4` | 24 | 36 | 29 | 43 |

So every table has at most 46 entries, and every node at most 26 children. The draft v0.2
claimed `4a + 1 = 33` and `6a + 2 = 50`. The row `≥ 4` follows from the closed forms of
§4.5.5.

#### 4.5.5 Label room in tables

**Lemma T5 (label room).** Assume I6 and I8, and for each height `h ≤ H−1` let

```
n₀_1 = a + 1;   n₀_h = c + ⌊c/2⌋ with c = 1 + ⌊(τ_h − 1)/λ_{h−1}⌋     (h ≥ 2)
D_1  = ⌊(W_1 + 2 − λ_1)/2⌋ + K_1 − 1,     D^c_1 = ⌊(W_1 + 1)/2⌋ + K_1 − 1
D_h  = 1 + ⌊Θ_h/γ_{h−1}⌋,                 D^c_h = 1 + ⌊(W_h + 1 + 2K_h)/γ_{h−1}⌋   (h ≥ 2)
```

If `⌊2^β/(n₀_h + 1)⌋ ≥ 2^(D_h + 1)` and `β ≥ D^c_h + 2` for every `h` (condition I7), then no
table insertion fails.

*Set-up.*
* **Gaps.** A table's labels lie in `[0, 2^β)`. Put sentinels at `−1` and `2^β`. A *gap* is the
  difference between two consecutive labels.
* **Insertion.** Inserting next to an entry takes `⌊(lo+hi)/2⌋` of the surrounding gap. It
  succeeds iff `hi − lo ≥ 2`, and both new gaps are at least `⌊(hi − lo)/2⌋`.
* **Removal.** Removing an entry merges two gaps into one at least as large as either.
* **Initial gaps.** A table created by `StartDrain` with `n₀` entries has all gaps at least
  `g₀ = ⌊2^β/(n₀ + 1)⌋`. A chain table has one entry at `2^(β−1)`, so `g₀ = 2^(β−1)`.
* **Initial entries.** A fresh target's table holds the live children of its part, at most
  `1 + ⌊(τ_h − 1)/λ_{h−1}⌋` by the counting of T4.1, plus at most half as many ghosts. So
  `n₀ ≤ n₀_h`. At height 1 a fresh target has at most `τ_1 = a + 1` chunks.
* **Growth `G_X`.** For a table `X` at height `h`, let `G_X` be the number of chunks inserted
  below `X`'s entries during `X`'s lifetime. By (Q), these entries lie below `X` while `X`
  is live, and below `X⁻, X⁺` while `X` is a ghost.
  * **While `X` is live,** its weight grows from `w₀(X)` to at most `W_h + 2`. By (F5) this
    also holds at height `H−1`, where `X` never drains.
  * **While `X` is a ghost,** every insertion below `X^±` comes from a funding job of `X`.
    There are at most `K_h` of these, by T3(c), adding 2 chunks each.
  * **Total.** `G_X ≤ W_h + 2 − w₀(X) + 2K_h`. A fresh target has `w₀ ≥ λ_h`, so for `h ≥ 2`,
    `G_X ≤ Θ_h`. The chain node has `w₀ = 1`, so `G_X ≤ W_h + 1 + 2K_h`.

*Proof for height `h ≥ 2`.*
* **Where insertions happen.** Entries are inserted only by `StartDrain(e)`, for a live entry
  `e`. It puts `e⁻` immediately before and `e⁺` immediately after `e`, and halves the two gaps
  next to `e`. Afterwards `e` is a ghost and is never again a place of insertion.
* **Histories.** Give every gap a *history*, a list of drains.
  * The gaps of a new table have the empty history.
  * When the drain of an endpoint `y` halves a gap, both resulting gaps get the old gap's
    history followed by `y`'s drain.
  * When the removal of a ghost merges two gaps (by (W1), `(g⁻, g)` and `(g, g⁺)`), the merged
    gap takes the shorter of the two histories.

  Write `D(gap)` for the length of a gap's history.

*Claim 1: every gap has size `≥ ⌊g₀ / 2^D⌋`.* By induction over events.
* **Halving.** Each new gap has at least half the old size, rounded down, and `D` grows by 1.
* **Merge.** The merged gap is at least as large as either part, and it takes the smaller `D`.
* **Other events.** Nothing else changes a gap.

*Claim 2: `D ≤ 2 + ⌊G_X/γ_{h−1}⌋` for every gap.*
* **Distinct nodes.** A node drains at most once, so the drains in one history are of
  distinct nodes.
* **Non-initial entries: at most `⌊G_X/γ_{h−1}⌋` drain in all of `X`'s life.**
  * A non-initial entry `x` was created as a target with weight `≤ τ_{h−1}` (T3(d)), and
    drains with weight `≥ W_{h−1} + 1`. So while `x` is live, at least `γ_{h−1}` chunks are
    inserted below it, all during `X`'s lifetime and below entries of `X`.
  * Each insertion lies below at most one such node, since at any moment distinct live nodes
    of the same height have disjoint subtrees.
* **Initial entries: at most 2 per history.** Let `Φ` be the number of endpoints of the
  history's current gap that are initial entries and have not drained during `X`'s
  lifetime. This includes nodes that were already ghosts when `X` was created.
  * At the start, `Φ ≤ 2`.
  * A halving by the drain of endpoint `y` makes `y` stop counting, and the new endpoint
    `y^±` is not initial.
  * A merge at a ghost `g` replaces the endpoint `g` by `g^±`. If `g` drained during `X`'s
    lifetime, it did not count, and `g^±` (created by that drain) is not initial. If `g` was
    already a ghost when `X` was created, then `g` counted, and so does `g^±`: it is an initial
    entry, and as a target of a running drain it cannot have drained.
  * So `Φ` never increases, and each drain of an initial entry in the history decreases it.

*Conclusion for `h ≥ 2`.* After the drain of `y` halves a gap, the resulting gaps have
`D ≤ 2 + ⌊G_X/γ_{h−1}⌋` by Claim 2. So the halved gap had `D ≤ 1 + ⌊G_X/γ_{h−1}⌋`, which
is `D_h`, or `D^c_h` for the chain table. By Claim 1 that gap was at least `⌊g₀/2^D⌋ ≥ 2`
under I7, so the insertion succeeds.

The draft v0.3 first counted `D` along the *lineages* of a gap's two endpoints. That
undercounts the inner gaps `(y⁻, y)` left by a drain, and the adversarial review found
violations of that version of Claim 1 (§6.6). The bound itself is unchanged.

*Proof for height 1.* Entries are chunks, inserted by `insertAround(x, y, z)`. That halves
the two gaps around `x`, which may be halved again later.
* **Depth.** The halvings in one gap's history come from distinct jobs, and each adds 2
  chunks below `X`'s entries.
* **Counting jobs.** While `X` is live, its weight grows from `w₀ ≥ λ_1` (or 1 for the chain
  node) to at most `W_1 + 2`. While it is a ghost, there are at most `K_1` funding jobs.
* **Conclusion.** Histories are as above (no entry is ever removed at height 1). A gap about
  to be halved has a history of at most `D_1` (or `D^c_1`) jobs, and Claim 1 applies. ∎

For `a = 8`, `s = 11`:

| `h` | `n₀_h` | `D_h` | `D^c_h` | Bits needed |
|---|---|---|---|---|
| 1 | 9 | 7 | 10 | 12 |
| 2 | 18 | 15 | 20 | 22 |
| 3 | 25 | 23 | 32 | 34 |
| `≥ 4` | 24 | 21 | 29 | 31 |

So `β ≥ 34` suffices. The proof value `β = 48` and the prototype's `β = 40` both satisfy I7,
with room to spare. The draft v0.2 bound was `β ≥ 40`. At height 1 the depth bound `D_1 = 7`
is attained in testing (§4.5.6).

**Closed forms for all heights.** Use `K_j ≤ (W_j+2)/(s−2) + 1` and `r = s/(s−2)`. For `h ≥ 2`:
* `Π_{h−1} ≤ r·W_{h−1} + 4 + 4/(s−2)`;
* `λ_h ≥ μ·W_h − ν`, with `μ = 1/2 − r/a` and `ν = 3 + 4/(s−2)`;
* `γ_h = λ_h − 1`.

For `h ≥ 3`, each of `C_h, C'_h, n₀_h, D_h, D^c_h` is therefore bounded by an expression of
the form `(αW + c)/(μW − d)` with `W = W_{h−1}` and `c, d ≥ 0`. Such an expression does not
increase with `W` once `μW > d`. Its value at `h = 4` therefore bounds every `h ≥ 4`. This
gives the rows `≥ 4` above. `top_bounds.py` computes both the exact values for small `h` and
the closed-form values.

Tags take `Hβ` bits. With `H ≤ L/3 + 2` this is `O(L)` (K4).

#### 4.5.6 Measured against the exact bounds

`top_wbbt.py` records the per-height maximum of every quantity bounded above, and
`check()` verifies (Q). Results are in `docs/TESTING.md` §9.
* At `s = 11` no bound is exceeded.
* Several bounds are attained exactly at height 1: drain start weight `W_1 + 2 = 18`,
  `K_1 = 3`, `Θ_1 = 15`, `Π_1 = 24`, `τ_1 = 9`, `λ_1 = 8`, `C_1 = E_1 = 18`, `n₀_1 = 9`,
  `D_1 = 7`, and tables per entry `= 2`.
* At `s = 8` (I6 false), the measured values exceed `Θ_1`, `Π_1`, `τ_1` and `W_1 + 2`, as
  predicted.

### 4.6 Wrapper

**Lemma W (rebuild timing; with [fix 1]).** Let `K_B ≥ 4` and `H' := L + 2`. Then, for a
core `cur` of capacity `N`:

1. `cur.count ≤ N/2 + ⌊(N/2 + H')/(K_B − 1)⌋ + 1 < N` at all times (about `2N/3` for `K_B = 4`);
2. `nxt` never holds more than `N'/4 + 1` elements (sentinel included) before it replaces `cur`;
3. `N' ≤ 4N`. So `L' ≤ L + 2`, and `nxt`'s preparation takes at most `H'` steps (its top tree
   has height at most `L'`).

*Proof.* By induction over rebuilds. Let a rebuild be triggered with `c₀` elements in
`cur` (tombstones included) and `live₀` live elements.
* **`c₀ ≤ N/2`.** `cur` was installed holding at most `N/4 + 1` elements, by (2) for the
  previous rebuild (or it is the first core). `count` grows by one per insertion, and the
  trigger fires at `count = N/2` at the latest.
* **(3).** We have `live₀ ≤ c₀ ≤ N/2` and `K_B ≥ 4`. So
  `N' ≤ 4·max(N/2 + (N/2 + H')/3 + 1, 16) ≤ 4N`, since `H' + 3 ≤ N`.
* **Length.** The trigger operation does no step. Every later operation does `K_B` steps
  until the rebuild ends, after at most `H'` preparation steps and a scan of at most `c₀ + I`
  elements, where `I` is the number of insertions during the rebuild. So the rebuild spans
  `⌈(H' + c₀ + I)/K_B⌉` operations at most, and `I` is at most that. This gives
  `I ≤ ⌊(c₀ + H')/(K_B − 1)⌋ + 1`.
* **(2).** Every element of `nxt` is a copy of an element that was live at the trigger, or was
  inserted during the rebuild (copied or mirrored, never both). So `nxt` holds at most
  `live₀ + I`, plus the sentinel, and `N' ≥ 4(live₀ + I)`.
* **(1).** `count ≤ c₀ + I`. ∎

The prototype implements exactly these steps (`wrapper.py`, `_rebuild_step`), and testing
attains the bounds with excess exactly 0 for `K_B` from 4 to 32. An earlier version wasted
up to two steps per rebuild, and its own Lemma W checks overshot by 1 for `K_B ≥ 12`
(adversarial review, §6.6).

**Space and word size.** `N' ≤ 4·live₀ + 2N/3 + O(log N)`. So `N` follows the live count
within a constant factor, apart from a geometrically decaying memory of the recent maximum.
`log N' ≤ log N + 2`, so the word size grows by at most a constant number of bits per epoch.

Each core needs its arrays allocated without an O(N) initialization step: allocate them
incrementally during the rebuild, or use constant-time-initializable arrays. `SPEC.md` §7.2
already records this requirement for the Lean model.

### 4.7 Assembling Theorem B

**The order of the argument.** The lemmas depend on each other in a cycle:
* C1 needs Lemma R's size bound;
* R needs C2, the job length (T4.4) and the chunk count;
* C2 and the chunk count need C1;
* T3–T5 need the chunk count (I8).

Time breaks the cycle. Suppose some claim of §4.2–4.6 fails, and let `t` be the first step
at which one does. Every claim holds at all earlier steps. Check each claim at `t`:
* **G1–G4.** They use only `G`, `K_G` and the absence of FALLBACK before `t`.
* **C1, at the end of a chunk split that started at `t₀ < t`.** It uses `s₀ ≤ T`, which is
  R at `t₀`, and G1 at `t`, which depends only on the absence of FALLBACK before `t`.
* **C2 at `t`.** It uses C1 for a split that ends at `t`.
* **R at `t`.**
  * The job length bound `(s+3)H` is structural: the proof of T4.4 uses neither I6 nor I8.
  * The adds per round use F.
  * New variables are at most `θ` by C2 at `t`.
  * The game history before `t` satisfies Theorem Z.
  * The count uses `m ≤ m_max`.
* **Chunk count at `t`.** It uses C1 and C2 for quiet periods that ended at pops at or
  before `t`, and Lemma W.
* **T3–T5 at `t`.** They are inductions over steps of their own. They use only I8 (the chunk
  count at `t`) and I6/I7.
* **C3 at `t`.** It uses R and C1 for the lifetime of the chunk, up to `t`.
* **W at `t`.** It is a count.
* **(K1) for guards.** No guard fails at `t`:
  * element labels: G4;
  * group labels: C3;
  * table labels: T5;
  * tag writes: T1 and T2;
  * adjacency guards: Lemma 3.2 together with F;
  * the slow path of the PQ is not taken (K2): Lemma C2.

So no claim fails at `t`, a contradiction. Hence no FALLBACK ever happens, and all bounds
hold forever.

**The step count.** By T4, a top step costs `c_top = O(max_h E'_h)`. The wrapper keeps
every core within capacity (W). Each wrapper operation therefore performs at most

```
(K_B + 2) · ( c_ins + K_G·c_move + K_C·c_move + K_R·c_top ) + c_wrap      steps,
```

These are constants independent of `n` and of the history. ∎

**Conditions.** `prototype/lower_bounds.py` evaluates every condition exactly for each `L`
(using `top_bounds.py` for I6 and I7). For the proof parameters:

| # | Condition (exact) | Used in | Holds for |
|---|---|---|---|
| I1 | `K_G ≥ 2`, `⌊(G + k_G + 3)/2⌋ < G`, `g_min ≥ 1` | G1, G2 | `L ≥ 4` |
| I2 | `⌊2^(B_e−1)/(8G+8)⌋ ≥ 2^(U_G)` and `A_G ≤ 8G + 7`, with the exact `U_G`, `A_G` of G3 | G4 | all `L` |
| I3 | `K_C ≥ 2` | C1 | — |
| I4 | `c_max ≤ θ` | C2 | `L ≥ 5` |
| I5 | `θ + R·(H_{m_max−1} + 1) ≤ T`, with `R = ⌈(s+3)H/K_R⌉ + 1` | R | `L ≥ 8` |
| I6 | `Θ_h ≤ W_h` for all `h`, and `Π_{h−1} ≤ W_h` for `h ≥ 2` (§4.5.3) | T3–T5 | all `L` (`a = 8, s = 11`) |
| I7 | `⌊2^β/(n₀_h+1)⌋ ≥ 2^(D_h+1)` and `β ≥ D^c_h + 2` for all `h` (§4.5.5) | T5 | `β ≥ 34` |
| I8 | `a^(H−1) ≥ m_max` | T3–T5, R | by the choice of `H` |
| I9 | `K_B ≥ 4` and the sizing rule of §2.7 | W | — |
| I10 | `Δ_g ≥ 2^(D_C+1)` and `P_C ≤ 8g' + 7` | C3 | `L ≥ 6` |

All of them hold for every `8 ≤ L ≤ 200`. I5 is the binding one: it fails at `L = 7`.

**All `L ≥ 56` in closed form.** For `T = 3L²`, `G = 2L`, `K_* = 4`, `a = 8`, `s = 11`:
* the bounds above give `c_max ≤ 1.5L² + 11L/6 + 3.5`;
* hence `θ + 1 − c_max ≥ 0.4L²` for `L ≥ 20`;
* hence `m_max ≤ 2^(L+3)/L² ≤ 2^(L−8)` for `L ≥ 56`;
* hence `H ≤ L/3`, `R ≤ 7L/6 + 2` and `H_{m_max−1} + 1 ≤ 0.6932·L`.

So `R·(H_{m_max−1}+1) ≤ 0.81L² + 1.4L ≤ L² = T − θ`, which is I5. I1, I2, I4 and I10 were
shown in closed form above, and I6–I9 do not depend on `L`. Together with the exact check
for `8 ≤ L ≤ 64`, every condition holds for all `L ≥ L₀ = 8`.

With `L₀ = 4` the proof parameters fail I5 for `L ≤ 7` and I10 at `L = 5`. The draft v0.2
had hidden this in an unspecified constant `c₁`. The prototype's proof preset now uses
`L₀ = 8` (`Params.proof`). The default preset is not covered by the proof (§5).

---

## 5. Provable constants versus measured thresholds

| Quantity | Empirical threshold (`docs/TESTING.md`) | Provable here | Why the gap |
|---|---|---|---|
| `K_G` | `≥ 2` | `≥ 2` (sizes); `4` (comfortable label count) | none for sizes |
| Top funding `s` | `≥ 6` (no fallback) | `≥ 9` (`a = 8`) | at `s = 8` Lemma T3's bound really fails at height 1 (measured 18 > 16), but a slightly overweight node costs only table space; a proof for `s < 9` would have to tolerate that |
| `β` | ≤ 20 bits used of 40 | `≥ 34` (with `s = 11`) | Claim 2 of T5 lets one gap's history absorb every drain in its table; at height 1 the bound is attained |
| `c_T·K_R` | defaults (`1·2`) never failed | `≳ 0.7(s+3)` | provable job length `(s+3)H` versus measured `6H + 4` |
| `B_e` | ≤ 40 of 59–63 bits used | `≥ 4G/3 + log₂(8G+8) + 7` | a group's insertions would all have to land in one gap |
| `L₀` (smallest `L`) | 4 never failed | 8 (I5 binds) | Lemma R's harmonic bound is crude when `H_m` and `R` are large relative to `T = 3L²` |

None of these gaps is a correctness issue. Each only says how large the constants must be
for the cost theorem. Tightening them is optional work for after the Lean proof.

---

## 6. Problems found while writing the proofs

### 6.1 Rebuild sizing (real cost bug; confirmed)

The prototype sizes a new core by the live count, `N' = 4·max(live, 16)`. But the rebuild's
length is proportional to `cur.count`, tombstones included, and the user may insert
throughout it.

The adversary:
1. Fill `cur` to `N/2` elements, with `live` just above `N/8`.
2. Delete every live element during the copy.
3. When the empty copy is installed, the next rebuild starts with `live = 0`, so its core has
   capacity 64.
4. Insert at the front: every insertion is mirrored into the 64-capacity core while the
   cursor crawls over about `N/8` tombstones.

Results (`python3 prototype/rebuild_attack.py`):

| `N` of the large core | Elements forced into a capacity-64 core | Fallbacks | Max steps/op |
|---|---|---|---|
| 3·10⁴ | 1,209 | 0 | 101 |
| 1.2·10⁵ | 4,809 | 0 | 91 |
| 4.9·10⁵ | 19,209 | 0 | 104 |
| 2·10⁶ | 76,809 | 4 ("top: table full") | **4,115** |

The overloaded core's top tree has a fixed height of 3. Its effective root's table grows
without bound (84 entries) until labels run out. The testing campaign missed this because
no workload deleted nearly everything during a rebuild and then inserted heavily.

**Fix 1.** `N' := 4·max(live + ⌈(cur.count + H')/(K_B − 1)⌉, 16)` (§2.7, Lemma W).

### 6.2 Element label width (proof gap; not observed)

Lemma G3 allows up to `4G/3 + 6` insertions into one gap of a group, but
`B_e = G + ⌈log₂(8G+8)⌉ + 8` only guarantees about `G + 6` halvings. The count is
probably not tight. **Fix 2** (`B_e = 2G + …`) costs `G` more bits per element label.

### 6.3 Families split across chunks (proof gap; not observed)

A chunk split can separate a splitting group from one of its siblings. Elements then flow
into a quiet chunk without a user insertion there. That breaks the per-round accounting of
the zeroing game, and repairing it inside the game costs `Θ(L²)` (§4.3). **Fix 3** moves
whole families in one chunk-split step.

Alternatives:
* key the PQ on "insertions since becoming quiet" instead of on size;
* accept the `δ` term and choose `c_T` about 3 times larger.

### 6.4 Smaller observations

* The prototype's `m_max = 6N/θ + 16 = 9N/T + 16` underestimates the chunk count bound
  (`12N/T`). The default preset still uses it. Since v0.3 the proof preset uses the exact
  `m_max` of §4.4 (`Params.proof` sets `P.m_max`), and so should the Lean port.
* The prototype's reservation links `y`, `z` before computing their tags. This is correct
  (Lemma 3.2: FALLBACK reads only the element list), but the Lean port should compute
  first and link afterwards, so that every primitive is atomic.
* SPEC's invariant W4 is replaced by the global-order invariant (O), which is simpler to
  state and to preserve.
* Lemma T2 shows that the prototype's guards "drain sides out of order" and "missing
  table entry" are unreachable. Lemma G2 shows the same for `_remove_group`'s immediate
  re-split.

### 6.5 After the fixes (2026-10-14)

All three fixes are applied to the prototype. Details and numbers are in `docs/TESTING.md`
§8.

* **Fix 1.** `rebuild_attack.py` now runs with 0 fallbacks and about 100 steps per op at
  n = 2²⁰ (previously 4,115). Reverting the fix (mutant M21) is caught by the lemma checker
  through Lemma W.
* **Fix 2.** Not observable at testable sizes, as predicted. Reverting it (M25) survives
  the battery and is classified "proof-only".
* **Fix 3.** Invariant F is checked by `Core.check()`. Reverting the fix (M22), or applying
  it at one end only (M23), is caught immediately.
* **A consequence of fix 3.** A quiet chunk's size now only grows. So the priority queue's
  decrement path and the group-removal code that fixes a chunk's `first`/`last` are
  unreachable. Mutation M19 ("queue not told about shrinkage") became equivalent. The Lean
  port can drop these paths.
* **Rounds in Lemma R.** The lemma checker found jobs spanning `⌈J/K_R⌉ + 1` insertions,
  from the pop insertion to the job's end. The game itself needs the adds between consecutive
  pops, at most `⌈(J+1)/K_R⌉`, as the first draft had (pointed out by the adversarial review).
  Both are at most `R = ⌈J/K_R⌉ + 1`, so Lemma R stands as stated (§4.4).
* **Coverage.** The suites execute every line of the algorithm except 38 (`linecov.py`).
  Each of those lines is one of:
  * a guard that the proof says never fires (tag, adjacency, sweep-side and table-entry
    guards: Lemmas T1, T2, 3.2);
  * a path that the proof says is unreachable (`StartDrain`'s give-up branches: §4.5.3; the
    cross-chunk move and the queue decrement: invariant F; drain steps on a finished node);
  * dead code (the chunk free list, since removed: chunks are never freed).

### 6.6 Found while completing the proof (v0.3)

* **C3 had a wrong step.** The v0.2 sketch said a fresh sibling group needs at least
  `(G+3)/2` insertions before it splits. That is G3's *upper* bound on a quiet group's
  insertions. A sibling can leave its family with up to `(G + k_G + 3)/2` elements, so it
  needs only about `G/3`. The corrected proof (§4.3) charges the family insertions to the
  children. A history argument like T5's then gives depth `≤ 3L + 10` against a budget of
  `9L + 6`. Not observed in testing: at most 16 nested halvings were measured.
* **Small `L` was not covered.** v0.2 relied on an unspecified constant `c₁` in `T`. With the
  exact constants, the proof parameters fail I5 for `L ≤ 7` (and I10 at `L = 5`). The proof
  now fixes `L ≥ L₀ = 8` instead. `Params.proof` uses `L_min = 8`. The cost is constant:
  cores smaller than 256 elements use the `L = 8` sizes.
* **T3 is sharper than sketched.** Bounding a unit by the pair weight `Π_{h−1}` instead of
  `2W_{h−1}`, and using the exact partition at height 1, lowers the funding requirement from
  `s ≥ 11` to `s ≥ 9` (`a = 8`). At `s = 8` the bound really fails, at height 1 only, and
  testing shows exactly the predicted overshoot.
* **T4 and T5 are sharper too.** Tables have at most 46 entries (v0.2 claimed 50), nodes at
  most 26 children (v0.2: 33), and 34 label bits suffice (v0.2: 40). Several bounds are
  attained exactly at height 1 (§4.5.6).
* **New invariant (Q).** It describes which tables can hold an entry. It replaces the informal
  argument for "at most 2 tables per entry", and is now checked by `WBBTTop.check()`.
* **C1 tightened.** Units are counted with the exact lower bound `g_min`, and the split ends
  after `⌈units/(K_C−1)⌉ + 1` insertions (v0.2: `K_C − 2` in the denominator). The
  instrumentation now checks the tighter bound, and testing comes within 2–5 insertions of it.

### 6.7 Adversarial review of v0.3 (2026-10-14)

Three independent reviewers, each with no prior context, checked one part of the proof
against the prototype and tried to break it. One covered the top structure, one the lower
levels and the assembly, one correctness and the wrapper. None found a false final
conclusion. Their findings, all verified and fixed:

* **T5 Claim 1 and C3 Claim 1 (gap depth): false as written.** Found by two reviewers
  independently, with counterexamples on the real code.
  * Counting depth along the *lineages* of a gap's endpoints undercounts the inner gaps
    `(y⁻, y)` that a drain or split leaves behind.
  * Fixed by counting along each gap's own halving history (§4.5.5, §4.3). The bounds `D_h`
    and `D_C` are unchanged.
* **C3, pushes: a missing case.** A child exposed at a chunk end while the chunk itself splits
  can split there. Fixed by counting child splits globally, charging each sibling half of
  its family's insertions (Claim 2 of C3).
* **T3(c) holds only between jobs.** A funding job's path copy adds 2 to the range before its
  sweeps. The proof only ever used (c) between jobs. The statement now says so.
* **Lemma W: constants off by 1–2.**
  * The inequality needs a floor plus 1, not a real division.
  * The prototype wasted up to two steps per rebuild. Its own Lemma W checks overshot by 1
    for `K_B ≥ 12`.
  * Fixed in both the doc and `wrapper.py`. `H' := L + 2` is now explicit, with `N' ≤ 4N`
    proved.
* **§3.4: the `β` condition for FALLBACK was missing.** With `β = 3`, the rebuilt top tree
  had equal tags. Now stated explicitly.
* **Unstated assumptions, now stated:**
  * the arguments of an operation are live elements (§1);
  * FALLBACK runs immediately and keeps element records (§2.8, Lemma 3.3);
  * correctness also uses Lemma T2;
  * the wrapper needs O(1) handle slots per core parity (§2.7);
  * the cursor is undefined while `nxt` is being prepared.
* **Smaller corrections:**
  * Lemma 3.2's case list is complete.
  * Rounds in Lemma R are defined as the intervals between pops.
  * The facts (C1)–(C4) are renamed (K1)–(K4), so they no longer clash with Lemmas C1–C3.
  * G3 states its constants for general `K_G`.
  * `B_g` in §2.9 matches the code.
  * Positivity of `λ_h` and `γ_h` is stated.
  * The prototype now computes `H` with integers rather than a floating-point log.

---

## 7. Next steps

1. ~~Apply the fixes to the prototype and re-run the battery.~~ Done (§6.5).
2. ~~Complete the pen-and-paper proof.~~ Done in v0.3:
   * T3–T5 written out in full (§4.5.2–4.5.6);
   * C3 corrected (§4.3);
   * an explicit induction over time and exact conditions for all `L ≥ 8` (§4.7).

   The exact bounds are checked by `lemmas.py` and `top_stress.py` (`docs/TESTING.md` §9).
3. **Optionally tighten the constants of §5.** For example, T3 for `s < 9`.
4. **Lean.** Theorem A (§3) can start immediately (M0–M2). It needs none of §4. Theorem Z
   (§4.4) is a self-contained first target for M4.
