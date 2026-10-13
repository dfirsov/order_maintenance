# Order Maintenance in O(1) Worst Case — Algorithm and Proof Sketch

Status: **draft v0.1** (2026-10-14). Companion to `docs/SPEC.md` (engineering specification
and Lean plan) and `docs/TESTING.md` (empirical results). This document describes the
algorithm in conventional terms and sketches pen-and-paper proofs of correctness and of
the O(1) worst-case bound. It is the blueprint for the Lean proofs (milestones M2 and
M4–M6).

Writing the proofs exposed three problems that the testing campaign missed. One of them
is a real cost bug, confirmed by a new adversary. They are collected in §6 with fixes.
The prototype has **not** been changed yet; §2 describes the algorithm *with* the fixes,
and marks each changed step with **[fix]**.

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
| Chunks: split timing, sizes, label room | §4.3 | Complete given *family moves* **[fix 3]** |
| Reservation: zeroing game | §4.4 | Complete |
| Top structure: order invariant, guards | §4.5.1 | Complete; replaces SPEC's W4 by a cleaner global-order invariant |
| Top structure: drain timing, table sizes, label room | §4.5.2–4.5.4 | Sketch with explicit constants; provable funding `s ≥ 11` (empirically `s ≥ 6` suffices) |
| Wrapper: rebuild timing | §4.6 | Complete given a new sizing rule **[fix 1]** |

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
`v⁻, v⁺`, and a nonempty *range*: the chunks `c` with `p_h(c) = v`, which are always
consecutive in the chunk list.

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
  if there is no nxt and (cur.count ≥ N/2 or live < N/8):
      N' := 4·max(live + ⌈(cur.count + H')/(K_B − 1)⌉, 16)          [fix 1]
      nxt := empty core of capacity N' (its top tree built one node per step, H' steps)
  else do k steps: first finish building nxt, then advance the cursor over cur, appending
      each live element it passes to the end of nxt ; at the end of cur, nxt replaces cur
```

The prototype sets `N' := 4·max(live, 16)`. §6.1 shows that this is wrong.

### 2.8 Guards and fallback

Every write that could break the order of keys is **guarded** by an O(1) comparison with
its immediate neighbours, computed before anything is mutated:

* the label guards of §2.2;
* sibling adjacency at every split move: `next(v⁻) = v`, or `prev(v⁺) = v`;
* every top-level tag write compares the new tag with the tags of the chunk-list neighbours.

A failed guard triggers **FALLBACK**: rebuild the current core synchronously from its
element list. Groups get `⌊G/2⌋` elements each and chunks `⌊T/2⌋` elements each, all
labels are evenly spaced, and the top tree is rebuilt with evenly spaced labels. This costs
O(n), and Theorem B shows that it never happens.

### 2.9 Parameters

| Symbol | Meaning | Proof value | Prototype default |
|---|---|---|---|
| `L` | `⌈log₂ N⌉` (at least 4) | | |
| `G` | group split threshold | `2L` | `2L` |
| `T` | chunk capacity | `3L² + c₁L` | `L²` |
| `θ` | PQ threshold | `⌊2T/3⌋` | same |
| `B_e` | element label bits | `2G + ⌈log₂(8G+8)⌉ + 8` **[fix 2]** | `G + ⌈log₂(8G+8)⌉ + 8` |
| `B_g` | group label bits | `6T/G + ⌈log₂(24T/G+8)⌉ + 8` | same |
| `K_G, K_C` | split moves per insert | `4, 4` | `4, 4` |
| `K_R` | top steps per insert | `4` | `2` |
| `a` | top branching parameter | `8` | `8` |
| `s` | sweep steps per job per draining ancestor | `11` | `8` |
| `β` | label bits per top table | `6a = 48` | `4a + 8 = 40` |
| `H` | top height | `⌈log_a m_max⌉ + 1`, `m_max ≥` max number of chunks | same |
| `K_B` | rebuild steps per operation | `4` | `4` |

The proof values are chosen so that the inequalities of §4 hold with room to spare. They
are larger than necessary; §5 compares them with the thresholds found empirically. `c₁`
absorbs lower-order terms for small `L` (§4.3).

---

## 3. Correctness

Correctness never depends on timing. The background processes can be arbitrarily late or
interleaved, and splits can even never finish. The only facts used are the guards.

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

Only element insertion mutates the element list, and it checks its guard first. ∎

**Lemma 3.3 (fallback).** FALLBACK reads only the element list, and its output satisfies
INV-S with the same element list. After FALLBACK, the retried element insertion passes its
guard.

*Proof.* FALLBACK builds evenly spaced labels at each level from a fixed list, so INV-S
holds by construction. After it, every element gap is at least `2^B_e/(⌊G/2⌋+1) ≥ 2`, and the
last element of a group has room `2^B_e/(⌊G/2⌋+1) > Δ_e`. So the retried guard holds (§3.4). ∎

Lemma 3.2 lets partial mutations of the group, chunk or top structures precede a failed
guard (the prototype's reservation links `y` and `z` before computing their tags). Since
FALLBACK reads only the element list, such partial states are discarded.

**Theorem 3.4 (core).** Every core satisfies INV-S between operations, and its element list
(live elements, after `H`) equals the abstract list of the operations applied to it.

*Proof.* By induction over primitives, using Lemmas 3.2 and 3.3. ∎

### 3.3 The wrapper

**Invariant R.** `cur` satisfies Theorem 3.4 and its live sequence is the abstract list `A`.
If `nxt` is being filled, its live sequence equals the subsequence of `A` that lies before
the cursor (in `cur`'s element list).

*Preservation.*
* **Insert after a copied `x`.** The new `y` is placed directly after `x`, which is before
  the cursor, so it must be in `nxt` immediately after `x`, and it is mirrored there.
  Inserting after the sentinel counts as inserting after a copied element.
* **Insert after an uncopied `x`.** `x` is at or after the cursor, so `y` is after it and will be
  copied later.
* **Delete.** It marks the element dead in both cores if it was copied, and only in `cur`
  otherwise.
* **Copy step.** It appends the cursor's element if it is live, then advances the cursor.

When the cursor reaches the end, `nxt`'s live sequence is `A`, so swapping preserves R. ∎

**Theorem A** follows from Invariant R and Lemma 3.1.

### 3.4 Conditions on parameters for Theorem A

Theorem A needs only that FALLBACK's layout is valid and that the retried insertion
passes. Sufficient conditions: `2^B_e ≥ 2(⌊G/2⌋+1)`, `Δ_e < 2^B_e/(⌊G/2⌋+1)`, and the analogous
conditions for `B_g` and `β`. All parameter sets in §2.9 satisfy them.

---

## 4. Cost

### 4.1 What has to be shown

An operation at the wrapper level performs at most `K_B + 2` core operations: its own
insertion in `cur`, possibly a mirror insertion in `nxt`, and up to `K_B` copy insertions.
Each core insertion does O(1) work plus `K_G` group moves, `K_C` chunk moves and `K_R` top
steps. So Theorem B follows from these facts:

* **(C1)** no guard ever fails (no FALLBACK);
* **(C2)** the PQ's slow path is never taken;
* **(C3)** every top step is O(1): tables have O(a) entries, an entry lies in O(1) tables, and
  each step touches O(1) tables;
* **(C4)** labels and tags have `O(L)` bits.

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

**Lemma G3 (lifetime).** A group receives at most `U_G := ⌈4G/3⌉ + 6` user insertions and at
most `A_G := ⌈3G/2⌉ + 7` arrivals in total (insertions plus moves) over its lifetime.

*Proof.* A sibling's life has three phases.
* As an overflow node, it receives at most `k_G` user insertions (G1).
* As a quiet node, it starts with at least `(G−3)/2` elements and splits at `G`, so it
  receives at most `(G+3)/2` insertions.
* While splitting, it receives at most `k_G` insertions.

The sum is at most `7G/6 + 6`. The sentinel's first group starts with one element:
`G − 1 + k_G ≤ 4G/3 + 1`. FALLBACK groups do not arise (C1). For arrivals, add the
overflow phase's at most `2G/3 + 3` arrivals (G1) to the user insertions of the two later
phases. ∎

**Lemma G4 (element labels).** No element-level guard fails if

```
Δ_e = 2^(B_e−1)/(8G+8) ≥ 2^(U_G)      and      A_G ≤ 8G + 8.
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

Without F (the current prototype), a chunk split can leave `g⁻` in one chunk and `g` in the
next. Group moves then transfer elements into a *quiet* chunk without a user insertion
there. Each such family transfers at most `G + k_G` elements, but the zeroing game of §4.4
charges this as a `δ = O(L)` error in *every* round. That costs a term `δ·H_m = Θ(L²)`, as
large as `T` itself. Family moves remove the issue for the price of three relinks per move.

**Lemma C1 (chunk split).** Let a chunk `x` start splitting with size `s₀ ≤ T` (Lemma R
supplies this bound). Then `x` is removed after at most `k_C := ⌈(5s₀/G + 3)/(K_C − 2)⌉ + 1`
insertions into its family. At removal, both siblings have size at most
`(s₀ + k_C)/2 + 2(⌈4G/3⌉ + 3)`.

*Proof.* Units are families (at least `G` elements together), quiet groups (at least
`(G−3)/2` elements, by G1) and the sentinel's group. So `x` holds at most `5s₀/G + 3` units.
Each insertion creates at most two new groups (one `StartSplit`, i.e. one new unit) and
drives `K_C` unit moves. Hence `x` is empty after `k_C` insertions. Balance is as in G1, except
that a move transfers up to one unit, at most `⌈4G/3⌉ + 3` elements, so `|d|` stays below two
units. ∎

With `T = Θ(L²)` and `G = Θ(L)`, `k_C = O(L)`. So a freshly quiet chunk has size at most
`s₀/2 + c₂L` for a constant `c₂` (about 8 with the proof parameters).

**Lemma C2 (PQ slow path).** If every quiet chunk stays at most `T` (Lemma R), freshly quiet
chunks have size at most `T/2 + c₂L ≤ θ − T/6 + c₂L`, which is below `θ` once `T/6 > c₂L`.
So `enterIfAbove` is never called on a chunk above `θ` (C2).

The constant `c₁` in `T = 3L² + c₁L` makes `T/6 > c₂L` hold for every `L ≥ 4`, not only
for large `L`.

**Lemma C3 (group labels).** No group-level guard fails with the `B_g` of §2.9.

*Proof sketch, as in G4.*
* **Halvings.** A gap between consecutive groups of a chunk is halved only when one of
  its two adjacent groups splits. After the first such split, the adjacent group is a fresh
  sibling, which must receive at least `(G+3)/2` insertions before it splits. So a gap sees at
  most `2 + (user insertions into the chunk)/((G+3)/2)` halvings. That is at most
  `2 + 8T/(3G) + O(1)`, since a chunk receives at most `4T/3 + O(L)` insertions in its life
  (overflow phase, quiet phase up to `T`, and `k_C` while splitting).
* **Pushes.** Pushes at each end number at most the units moved in plus the end splits,
  which is at most `5T/G + O(1)`, within the `8·(3T/G) + 8` budget.
* **Budget.** `B_g` provides `6T/G + 6` halvings. ∎

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

**Lemma R (chunk sizes).** Let `J` bound the length of a top job (Lemma T4), and let
`R := ⌈(J + 1)/K_R⌉`. Let `m` bound the number of chunks in the core. Then every quiet chunk
has size at most

```
T_hard := θ + R · (H_{m−1} + 1).
```

*Proof.* A *round* is the lifetime of one reservation job, from popping a chunk to the job's
end. It lasts at most `R` core insertions, since each insertion advances the job by `K_R`
steps. The game's variables are `x_c = max(0, size(c) − θ)` for quiet chunks `c`.
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

**Number of chunks.** Each reservation needs a chunk that grew from at most `T/2 + c₂L`
(freshly quiet) to above `θ`, which takes at least `T/6 − c₂L` insertions. So
`m ≤ 2N/(T/6 − c₂L) + O(1)`. The choice `m_max = 12N/T + O(1)` and `2a^(H−1) ≥ 2m_max`
also make the root's only child (height `H−1`) never drain. So the root has fanout 1, and
the node below it is the effective root.

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

#### 4.5.2 Drain timing

Let `q := 1/2 + 2/a + 2/(s−2)`.

**Lemma T3 (drains finish in time).** Suppose `q < 1`. Then for every height `h`:

1. a drain of `v` starts with `|range(v)| ≤ w(v) ≤ W_h + 2`;
2. it finishes within `(W_h + 2)/(s−2) + 1` jobs that pass through its targets;
3. until it finishes, each target has weight at most `q·W_h + O(1) < W_h`. So a target is
   never over threshold while it is blocked.

*Proof sketch (induction on height and time).*
* **Start.** By (P), `range(v)` is contained in `v`'s subtree, so `|range(v)| ≤ w(v)`. A
  non-target node starts draining at the first walk that finds it over threshold, so
  `w(v) ≤ W_h + 2` by (3) for its own source, if any.
* **Partition.** A unit of the partition is a child, or a pair of targets of a running drain.
  By (3) at height `h−1`, a unit weighs at most `2·W_{h−1} = 2W_h/a`. So each part weighs at
  most `w(v)/2 + 2W_h/a`.
* **Progress.** A job affects `range(v)` only if it inserts next to a chunk of `v⁻`'s or `v⁺`'s
  subtree (P). Such a job adds at most 2 chunks to the range, and its walk passes the target
  and funds `s` sweep steps of `v`. So after `k` such jobs, `|range(v)| ≤ W_h + 2 − (s−2)k`,
  which proves (2).
* **Growth.** During those jobs a target gains at most `2k ≤ 2(W_h + 2)/(s−2) + 2` chunks.
  Its final weight is at most `W_h/2 + 2W_h/a + 2W_h/(s−2) + O(1) = q·W_h + O(1)`, which
  proves (3). ∎

The branches of `StartDrain` that give up ("fewer than two children" and "all children are
one target pair") are unreachable: those children weigh at most `2W_{h−1} < W_h`.

**The constant.** For `a = 8`, `q < 1` needs `s > 10`, so the proof uses `s = 11`, giving
`q ≈ 0.97`. Empirically, `s ≥ 6` already never failed. The bound is not tight, because it lets
the adversary realize every worst case at once, in every generation:
* a target pair at the partition boundary;
* all growth on one side;
* every insertion landing in the unswept part.

For `s` between 6 and 10, a sharper argument might work, for example amortizing over
generations, but none is attempted here. Increasing `a` also helps: `a = 16` allows `s = 8`.

Ghosts whose targets receive no further insertions never finish. They are harmless:
(W1) charges each one to two live entries of the same table (Lemma T4).

#### 4.5.3 Sizes and step cost

**Lemma T4 (O(1) steps).**

1. A live node has at most `4a + 1` live children.
2. A table has at most `1.5·(non-ghost entries)` entries, so at most `6a + 2`.
3. Every node or chunk is an entry of at most 2 tables.
4. A job has at most `J := (s+3)·H` steps.
5. Each step touches O(1) tables, so it costs `O(a)`.

*Proof sketch.*
1. Fresh children weigh at least `W_{h−1}·(1/2 − 2/a)` (the partition bound). The only light
   child is the one descending from the initial single-chunk chain. A live node weighs at
   most `W_h + 2`. With `a = 8` this gives at most `W_h/(W_{h−1}/4) + 1 = 4a + 1` children.
2. Every ghost entry has two non-ghost entries of its own around it (W1), and distinct ghosts
   have distinct targets.
3. The tables holding an entry are those of its live parent `P` and, while `P` is the target
   of a running drain, of `P`'s source. A target cannot start draining while its source
   drains, so there are no longer chains. The measured maximum is 2.
4. The path copy takes `H` steps, and each walk level takes at most `s + 2` steps.
5. Each step does table operations on O(1) tables of `O(a)` entries. ∎

#### 4.5.4 Label room in tables

**Lemma T5.** No table runs out of labels if `β ≥ 4qa + 3 + log₂(6a + 3)`.

*Proof sketch.*
* **Initial gaps.** A table starts with at most `6a + 2` evenly spaced entries.
* **What halves a gap.** A gap is halved only by insertions next to one of its two
  endpoints: a drain of that entry, or, at height 1, a chunk inserted next to it.
* **Nested halvings at height `h ≥ 2`.** After the first drain at a position, the adjacent
  entry is a fresh target. It must gain at least `W_{h−1}/4` (at `a = 8`) before it drains.
  The subtree gains at most `q·W_h + O(1)` over the table's life: from creation, through its
  own drain, until the table is dropped (T3). So there are at most `2 + 4qa` nested halvings.
* **Height 1.** Each job halves at most one gap, and the node gains 2 chunks per job, so
  there are at most `q·a + O(1)` halvings.

Each halving costs one bit of the initial gap. ∎

With `a = 8` and `s = 11` (`q ≈ 0.97`), this needs `β ≥ 40`. The prototype's `β = 4a + 8 = 40`
just meets the bound, and used at most 20 bits in testing. The proof parameters use `β = 48`
for margin.
Tags take `Hβ ≈ 16L` bits, i.e. `O(L)` (C4).

### 4.6 Wrapper

**Lemma W (rebuild timing; with [fix 1]).** Let `K_B ≥ 4`. Then:

1. `cur.count ≤ N/2 + (N/2 + H')/(K_B − 1) < N` at all times (at most about `2N/3` for `K_B = 4`);
2. `nxt` never holds more than `N'/4 + 1` elements before it replaces `cur`.

*Proof.*
* **Rebuild length.** Let a rebuild start with `c₀` elements in `cur` (tombstones included)
  and `live₀` live elements. It ends after the `H'` preparation steps and a scan of at most
  `c₀ + I` elements, where `I` is the number of insertions during the rebuild. At `K_B` steps
  per operation, `I ≤ (H' + c₀ + I)/K_B`, so `I ≤ (c₀ + H')/(K_B − 1)`.
* **`nxt` stays small.** `nxt` receives `live₀` copies plus at most `I` mirrored insertions, and
  `N' = 4·(live₀ + ⌈(c₀ + H')/(K_B−1)⌉)` covers this four times over. This gives (2).
* **`cur` stays small.** A newly installed core therefore starts below a quarter of its
  capacity. It triggers a rebuild no later than `count = N/2`, so `c₀ ≤ N/2`, and (1) follows
  from the bound on `I`. ∎

**Space and word size.** `N' ≤ 4·live₀ + 2N/3 + O(1)`, so `N` follows the live count within
a constant factor, apart from a geometrically decaying memory of the recent maximum.
`log N' ≤ log N + 2`, so the word size grows by at most a constant number of bits per epoch.

Each core needs its arrays allocated without an O(N) initialization step: allocate them
incrementally during the rebuild, or use constant-time-initializable arrays. `SPEC.md` §7.2
already records this requirement for the Lean model.

### 4.7 Assembling Theorem B

For every core operation, in order:
* C1 for the top level (T1, T2, T5);
* C1 for groups (G4) and chunks (C3);
* C2 (C2, with sizes from Lemma R);
* C3 (T4);
* C4 (§2.9).

The wrapper keeps every core within capacity (W). Each wrapper operation therefore
performs at most

```
(K_B + 2) · ( c_ins + K_G·c_move + K_C·c_move + K_R·c_top ) + c_wrap      steps,
```

with `c_top = O(a)`. All of these are constants independent of `n` and of the history. ∎

**Inequalities used** (all hold for the proof values of §2.9):

| # | Condition | Used in | Proof values |
|---|---|---|---|
| I1 | `K_G ≥ 2` and `(G + k_G + 3)/2 < G` | G1, G2 | `K_G = 4` |
| I2 | `B_e − 1 − log₂(8G+8) ≥ 4G/3 + 6` | G4 | `B_e = 2G + …` |
| I3 | `K_C ≥ 3` | C1 | `4` |
| I4 | `T/6 > c₂L` | C2 | via `c₁` |
| I5 | `R·(H_{m−1}+1) ≤ T/3` | R, C2 | `c_T·K_R = 12` |
| I6 | `q = 1/2 + 2/a + 2/(s−2) < 1` | T3 | `a = 8, s = 11` |
| I7 | `β ≥ 4qa + 3 + log₂(6a+3)` | T5 | `β = 48` |
| I8 | `2a^(H−1) ≥ 2m_max`, `m_max ≥ 12N/T + O(1)` | T4, R | `H` as defined |
| I9 | `K_B ≥ 4` and the sizing rule of §2.7 | W | `K_B = 4` |

---

## 5. Provable constants versus measured thresholds

| Quantity | Empirical threshold (`docs/TESTING.md`) | Provable here | Why the gap |
|---|---|---|---|
| `K_G` | `≥ 2` | `≥ 2` (sizes); `4` (comfortable label count) | none for sizes |
| Top funding `s` | `≥ 6` | `≥ 11` (`a = 8`) | T3 combines worst cases that the adversaries do not produce together |
| `β` | ≤ 20 bits used of 40 | `≥ 40` (with `s = 11`) | the nested-halving count is crude |
| `c_T·K_R` | defaults (`1·2`) never failed | `≳ 0.7(s+3)` | provable job length `(s+3)H` versus measured `6H + 4` |
| `B_e` | ≤ 40 of 59–63 bits used | `≥ 4G/3 + log₂(8G+8) + 7` | a group's insertions would all have to land in one gap |

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
  (`12N/T`). It is still safe, because the effective root's threshold is `2a^(H−1) ≥ 2m_max`.
  The Lean port should use the cleaner `m_max`.
* The prototype's reservation links `y`, `z` before computing their tags. This is correct
  (Lemma 3.2: FALLBACK reads only the element list), but the Lean port should compute
  first and link afterwards, so that every primitive is atomic.
* SPEC's invariant W4 is replaced by the global-order invariant (O), which is simpler to
  state and to preserve.
* Lemma T2 shows that the prototype's guards "drain sides out of order" and "missing
  table entry" are unreachable. Lemma G2 shows the same for `_remove_group`'s immediate
  re-split.

---

## 7. Next steps

1. **Apply the fixes to the prototype and re-run the battery.** Add the rebuild-sizing
   adversary of §6.1 to `stress.py`, and add a test that checks invariant F.
2. **Check the remaining sketch-level arguments in more detail.** Lemma T3 (drain timing) and
   T5 (table label room) are the most delicate. They should be written out in full on paper
   before M6. The other lemmas are routine to formalize.
3. **Optionally tighten the constants of §5.** In particular, a proof of T3 with `s` close to
   the empirical threshold 6.
4. **Lean.** Theorem A (§3) can start immediately (M0–M2). It needs none of §4. Theorem Z
   (§4.4) is a self-contained first target for M4.
