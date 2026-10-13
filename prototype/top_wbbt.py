"""Top-level list labeling over chunks with O(log m) worst-case work per insertion.

Weight-balanced B-tree (Arge–Vitter) in the style of Kopelowitz 2012 §3, but
with Dietz–Sleator-style splitting and immutable label tables:

* Every tree node has a label table assigning labels (β bits) to its entries.
  A label, once assigned, never changes.
* Every chunk stores a *path* p[1..H] (p[H] = root) and its tag is the
  concatenation of the labels  F_j = lab_{p[j]}(p[j-1])  (p[0] = the chunk),
  with F_H most significant.
* A node v that grows too heavy is *drained*, not relabelled: two fresh live
  siblings v1 (before v) and v2 (after v) are created, v's live children are
  partitioned between them with fresh evenly spread labels, and v becomes a
  ghost. A background sweep then rewrites, chunk by chunk, the path entry
  p[h] = v to v1 (left part, swept left to right) or v2 (right part, swept
  right to left). Each rewrite changes exactly two fields of one tag.
* A ghost keeps its table and its entries in its parents' tables until no
  chunk path refers to it any more.

Tables containing a node: when v is drained, v1/v2 are inserted next to v in
every table that contains v; when a node starts draining, every referenced
entry of its table is copied into v1's or v2's table. So any path that can
arise has labels in the tables it needs.

Work is done by jobs (generators). One job per reservation inserts the two
new chunks, then walks the live tree upward: increments weights, starts
drains, and grants `s` sweep steps to the drain feeding each ancestor.

Every tag write is guarded against the chunk-list neighbours (safety
principle, docs/SPEC.md); a failed guard raises GuardFailure.
"""
from __future__ import annotations

import math
from dataclasses import dataclass, field

from guards import GuardFailure

NIL = -1
LEFT, RIGHT = 0, 1


@dataclass(slots=True)
class Node:
    height: int
    live_parent: int = NIL
    children: list = field(default_factory=list)   # live children, in order
    weight: int = 0
    lab: dict = field(default_factory=dict)        # entry -> label (immutable)
    order: list = field(default_factory=list)      # entries in label order
    in_tables: list = field(default_factory=list)  # nodes whose table holds this node
    first: int = NIL                               # range of chunks with p[height] = self
    last: int = NIL
    draining: bool = False
    t1: int = NIL                                  # drain targets
    t2: int = NIL
    side: dict = field(default_factory=dict)       # entry -> LEFT/RIGHT while draining
    overflow_of: int = NIL                         # source node while it drains into us
    alive: bool = True


class WBBTTop:
    def __init__(self, core, *, a: int = 8, s: int = 8, beta: int | None = None) -> None:
        self.core = core
        self.a = a
        self.s = s
        self.beta = beta if beta is not None else 4 * a + 8   # ~1 bit per table insertion
        self.top_steps = 0
        self.relabels = 0          # full rebuilds (fallbacks)
        self.max_table = 0
        self.max_lab = 0
        self.min_gap = 1 << (self.beta + 1)   # smallest label gap ever split by averaging
        self.drains = 0
        self.max_job = 0           # longest job, in steps
        self.max_ghosts = 0        # most ghosts alive at once
        P = core.P
        m_max = 6 * P.N // max(P.theta, 1) + 16
        self.H = max(2, math.ceil(math.log(m_max, a)) + 1)
        self._reset()

    # ----------------------------------------------------------- utilities
    def _reset(self) -> None:
        self.nodes: list[Node] = []
        self.path: dict[int, list[int]] = {}    # chunk -> [NIL, p1, ..., pH]
        self.cin: dict[int, list[int]] = {}     # chunk -> nodes whose table holds it
        self.lpar: dict[int, int] = {}          # chunk -> live height-1 parent

    def _new_node(self, h: int) -> int:
        self.nodes.append(Node(height=h))
        return len(self.nodes) - 1

    def _in_tables(self, e: int, h: int) -> list[int]:
        """Tables containing entry e, which lives at height h (0 = chunk)."""
        return self.cin[e] if h == 0 else self.nodes[e].in_tables

    def _tag_of(self, c: int) -> int:
        p = self.path[c]
        t = 0
        below = c
        for j in range(1, self.H + 1):
            t |= self.nodes[p[j]].lab[below] << ((j - 1) * self.beta)
            below = p[j]
        return t

    def _guard_tag(self, c: int, t: int) -> None:
        C = self.core.C
        pr, nx = C[c].prev, C[c].next
        if pr != NIL and not C[pr].tag < t:
            raise GuardFailure("top: tag not above predecessor")
        if nx != NIL and not t < C[nx].tag:
            raise GuardFailure("top: tag not below successor")

    def _room_next_to(self, T: Node, e: int, before: bool) -> int:
        """A label for a new entry right before/after e in table T (averaging)."""
        i = T.order.index(e)
        if before:
            lo = T.lab[T.order[i - 1]] if i > 0 else -1
            hi = T.lab[e]
        else:
            lo = T.lab[e]
            hi = T.lab[T.order[i + 1]] if i + 1 < len(T.order) else 1 << self.beta
        if lo + 1 >= hi:
            raise GuardFailure("top: table full")
        self.min_gap = min(self.min_gap, hi - lo)
        return (lo + hi) // 2

    def _table_insert(self, T: Node, e: int, new: int, before: bool, lab: int) -> None:
        i = T.order.index(e)
        T.order.insert(i if before else i + 1, new)
        T.lab[new] = lab
        if T.draining:
            T.side[new] = T.side[e]
        self.max_table = max(self.max_table, len(T.order))
        self.max_lab = max(self.max_lab, lab)

    # ------------------------------------------------------------ build
    def init_first(self, c: int) -> None:
        self._build([c])

    def relabel_all(self) -> None:
        """Fallback: rebuild the whole tree from the chunk list, all paths clean."""
        self.relabels += 1
        core = self.core
        chunks = []
        c = core.first_chunk
        while c != NIL:
            chunks.append(c)
            c = core.C[c].next
        self._build(chunks)
        self.top_steps += len(chunks)

    def _build(self, chunks: list[int]) -> None:
        self._reset()
        a, H = self.a, self.H
        level = list(chunks)            # entries at the current height
        for h in range(1, H + 1):
            groups = [level[i:i + a] for i in range(0, len(level), a)] if h < H else [level]
            nxt = []
            for grp in groups:
                v = self._new_node(h)
                V = self.nodes[v]
                V.children = list(grp)
                V.order = list(grp)
                gap = (1 << self.beta) // (len(grp) + 1)
                for i, e in enumerate(grp):
                    V.lab[e] = (i + 1) * gap
                    if h == 1:
                        self.cin[e] = [v]
                        self.lpar[e] = v
                        V.weight += 1
                    else:
                        E = self.nodes[e]
                        E.in_tables = [v]
                        E.live_parent = v
                        V.weight += E.weight
                self.max_table = max(self.max_table, len(grp))
                nxt.append(v)
            level = nxt
        # paths, ranges, tags
        for c in chunks:
            p = [NIL] * (H + 1)
            v = self.lpar[c]
            for j in range(1, H + 1):
                p[j] = v
                V = self.nodes[v]
                if V.first == NIL:
                    V.first = c
                V.last = c
                v = V.live_parent
            self.path[c] = p
        for c in chunks:
            self.core.C[c].tag = self._tag_of(c)

    # ------------------------------------------------------------ insertion
    def insert_around(self, x: int, y: int, z: int):
        """y, z are linked before/after x in the chunk list. O(1) part:
        give them labels next to x, copy x's path, set tags. Returns the job."""
        H = self.H
        px = self.path[x]
        tabs = self.cin[x]
        # compute all labels first (guards), then mutate
        ly = {T: self._room_next_to(self.nodes[T], x, True) for T in tabs}
        lz = {T: self._room_next_to(self.nodes[T], x, False) for T in tabs}
        p1 = self.nodes[px[1]]
        f1x = p1.lab[x]
        ty = self.core.C[x].tag - f1x + ly[px[1]]
        tz = self.core.C[x].tag - f1x + lz[px[1]]
        self._guard_tag(y, ty)
        self._guard_tag(z, tz)
        for T in tabs:
            self._table_insert(self.nodes[T], x, y, True, ly[T])
            self._table_insert(self.nodes[T], x, z, False, lz[T])
        for c in (y, z):
            # the path is copied one entry per job step (O(H) work must not
            # happen inside a single core operation); nothing reads it earlier
            self.path[c] = [NIL] * (H + 1)
            self.cin[c] = list(tabs)
            self.lpar[c] = self.lpar[x]
        lp = self.nodes[self.lpar[x]]
        i = lp.children.index(x)
        lp.children[i:i + 1] = [y, x, z]
        self.core.C[y].tag = ty
        self.core.C[z].tag = tz
        self.top_steps += 1
        return self._job(x, y, z)

    def step(self, job) -> bool:
        self.top_steps += 1
        try:
            next(job)
            return True
        except StopIteration:
            return False

    def run_job(self, job) -> int:
        """Run a job to completion; return its length in steps."""
        n = 0
        while self.step(job):
            n += 1
        self.max_job = max(self.max_job, n)
        return n

    def _job(self, x: int, y: int, z: int):
        H = self.H
        # 1. copy x's path into y, z and extend ranges where x was an end
        for j in range(1, H + 1):
            v = self.path[x][j]
            self.path[y][j] = self.path[z][j] = v
            V = self.nodes[v]
            if V.first == x:
                V.first = y
            if V.last == x:
                V.last = z
            yield
        # 2. weights, drains, sweep funding along the live tree
        v = self.lpar[y]
        while v != NIL:
            V = self.nodes[v]
            up = V.live_parent
            V.weight += 2
            if (up != NIL and not V.draining and V.overflow_of == NIL
                    and V.weight > 2 * self.a ** V.height):
                self._start_drain(v)
                yield
            src = V.overflow_of
            if src != NIL:
                for _ in range(self.s):
                    if not self._drain_step(src):
                        break
                    yield
            yield
            v = up

    # ------------------------------------------------------------ drains
    def _start_drain(self, v: int) -> None:
        V = self.nodes[v]
        h = V.height
        kids = V.children
        if len(kids) < 2:
            return              # nothing to split (e.g. a chain node above a heavy child)
        # partition live children by weight; never separate the two targets of
        # a still-active drain (they sit around their ghost in the table)
        wt = (lambda e: 1) if h == 1 else (lambda e: self.nodes[e].weight)
        total = sum(wt(e) for e in kids)
        acc, k = 0, 0
        while k < len(kids) - 1 and acc + wt(kids[k]) <= total // 2:
            acc += wt(kids[k])
            k += 1
        k = max(k, 1)
        if h > 1:
            while 0 < k < len(kids) and self._same_drain(kids[k - 1], kids[k]):
                k += 1
            if k >= len(kids):
                k = len(kids) - 1
                while k > 0 and self._same_drain(kids[k - 1], kids[k]):
                    k -= 1
            if k == 0:
                return          # cannot split now; retry on a later insertion
        boundary = kids[k]      # first child of the right part
        # entries of v's table that still matter: live children + ghosts with chunks
        entries = [e for e in V.order
                   if h == 1 or e in kids or self.nodes[e].first != NIL]
        side = {}
        s_ = LEFT
        for e in V.order:
            if e == boundary:
                s_ = RIGHT
            side[e] = s_
        # ghost entries take the side of their targets
        if h > 1:
            for e in entries:
                E = self.nodes[e]
                if E.draining:
                    side[e] = side[E.t1]
        left = [e for e in entries if side[e] == LEFT]
        right = [e for e in entries if side[e] == RIGHT]
        # labels for v1 / v2 in every table holding v (guards first)
        l1 = {T: self._room_next_to(self.nodes[T], v, True) for T in V.in_tables}
        l2 = {T: self._room_next_to(self.nodes[T], v, False) for T in V.in_tables}
        # -- mutate
        self.drains += 1
        v1, v2 = self._new_node(h), self._new_node(h)
        V = self.nodes[v]
        V1, V2 = self.nodes[v1], self.nodes[v2]
        for T in V.in_tables:
            self._table_insert(self.nodes[T], v, v1, True, l1[T])
            self._table_insert(self.nodes[T], v, v2, False, l2[T])
        V1.in_tables = list(V.in_tables)
        V2.in_tables = list(V.in_tables)
        for W, part in ((V1, left), (V2, right)):
            gap = (1 << self.beta) // (len(part) + 1)
            W.order = list(part)
            for i, e in enumerate(part):
                W.lab[e] = (i + 1) * gap
            self.max_table = max(self.max_table, len(part))
        for e in left:
            self._in_tables(e, h - 1).append(v1)
        for e in right:
            self._in_tables(e, h - 1).append(v2)
        V1.children = [e for e in kids if side[e] == LEFT]
        V2.children = [e for e in kids if side[e] == RIGHT]
        for W, w in ((V1, v1), (V2, v2)):
            for e in W.children:
                if h == 1:
                    self.lpar[e] = w
                else:
                    self.nodes[e].live_parent = w
            W.weight = sum(wt(e) for e in W.children)
            W.live_parent = V.live_parent
            W.overflow_of = v
        par = self.nodes[V.live_parent]
        i = par.children.index(v)
        par.children[i:i + 1] = [v1, v2]
        V.draining, V.t1, V.t2, V.side = True, v1, v2, side
        self.ghosts = getattr(self, "ghosts", 0) + 1
        self.max_ghosts = max(self.max_ghosts, self.ghosts)
        V.live_parent = NIL
        V.children = []
        self.top_steps += len(V.order) + len(V.in_tables)

    def _same_drain(self, a_: int, b_: int) -> bool:
        A, B = self.nodes[a_], self.nodes[b_]
        return A.overflow_of != NIL and A.overflow_of == B.overflow_of

    def _drain_step(self, v: int) -> bool:
        """Move one chunk off ghost v. Returns False when v is fully drained."""
        V = self.nodes[v]
        if not V.alive:
            return False
        h = V.height
        if V.first == NIL:
            self._finish_drain(v)
            return False
        y = V.first
        below = y if h == 1 else self.path[y][h - 1]
        if V.side[below] == LEFT:
            t, left = V.t1, True
        else:
            y = V.last
            below = y if h == 1 else self.path[y][h - 1]
            if V.side[below] != RIGHT:
                raise GuardFailure("top: drain sides out of order")
            t, left = V.t2, False
        T = self.nodes[t]
        p = self.path[y]
        par = self.nodes[p[h + 1]]
        b = self.beta
        if t not in par.lab or below not in T.lab:
            raise GuardFailure("top: missing table entry")
        old = (par.lab[v] << (h * b)) | (V.lab[below] << ((h - 1) * b))
        new = (par.lab[t] << (h * b)) | (T.lab[below] << ((h - 1) * b))
        tag = self.core.C[y].tag - old + new
        self._guard_tag(y, tag)
        # -- mutate
        self.core.C[y].tag = tag
        p[h] = t
        C = self.core.C
        if V.first == V.last:
            V.first = V.last = NIL
        elif left:
            V.first = C[y].next
        else:
            V.last = C[y].prev
        if left:
            if T.first == NIL:
                T.first = y
            T.last = y
        else:
            if T.last == NIL:
                T.last = y
            T.first = y
        return True

    def _finish_drain(self, v: int) -> None:
        V = self.nodes[v]
        h = V.height
        for e in V.order:
            tabs = self._in_tables(e, h - 1)
            if v in tabs:
                tabs.remove(v)
        for T in V.in_tables:
            Tn = self.nodes[T]
            Tn.order.remove(v)
            del Tn.lab[v]
            Tn.side.pop(v, None)
        for t in (V.t1, V.t2):
            if self.nodes[t].overflow_of == v:
                self.nodes[t].overflow_of = NIL
        V.alive = False
        V.in_tables = []
        self.ghosts -= 1
        self.top_steps += len(V.order)

    # ------------------------------------------------------------ checks
    def check(self) -> None:
        """Structural sanity of the top structure (not needed for safety)."""
        core = self.core
        c = core.first_chunk
        while c != NIL:
            if NIL in self.path[c][1:]:     # path still being copied by its job
                c = core.C[c].next
                continue
            assert core.C[c].tag == self._tag_of(c), "cached tag != path tag"
            for j in range(1, self.H + 1):
                assert self.nodes[self.path[c][j]].alive
            c = core.C[c].next
