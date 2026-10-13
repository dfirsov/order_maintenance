"""Insert-only order-maintenance core with fixed capacity N (docs/SPEC.md §4-5).

Representation mirrors the planned Lean arena: records live in Python lists and
refer to each other by integer index (NIL = -1).

Three global doubly linked lists -- elements, groups, chunks -- with contiguous
membership: the elements of a group form the range first..last of the element
list, and likewise for the groups of a chunk.

Safety principle: every primitive computes all guarded values *before* mutating
anything and raises GuardFailure if a guard fails, leaving the state untouched.
The caller then falls back to a synchronous rebuild (`_fallback`).
"""
from __future__ import annotations

import math
from dataclasses import dataclass, field

from guards import GuardFailure
from pq import BucketPQ
from top_simple import SimpleTop
from top_wbbt import WBBTTop

NIL = -1
QUIET, OVERFLOW, SPLITTING, DEAD = 0, 1, 2, 3   # DEAD: emptied chunk kept as tombstone


@dataclass(slots=True)
class Elem:
    next: int = NIL
    prev: int = NIL
    grp: int = NIL
    lab: int = 0
    live: bool = True
    h: int = -1               # user handle (-1 for the sentinel)


@dataclass(slots=True)
class Group:
    next: int = NIL
    prev: int = NIL
    first: int = NIL          # element range, NIL if empty
    last: int = NIL
    chk: int = NIL
    lab: int = 0
    size: int = 0             # elements in range, tombstones included
    st: int = QUIET
    src: int = NIL            # OVERFLOW: the group being split
    l: int = NIL              # SPLITTING: overflow siblings
    r: int = NIL
    alive: bool = True


@dataclass(slots=True)
class Chunk:
    next: int = NIL
    prev: int = NIL
    first: int = NIL          # group range, NIL if no groups
    last: int = NIL
    size: int = 0             # elements beneath
    st: int = QUIET
    src: int = NIL
    l: int = NIL
    r: int = NIL
    tag: int = 0              # written only by the top structure
    alive: bool = True


@dataclass
class Params:
    N: int                    # capacity (elements ever inserted, incl. sentinel)
    L: int                    # ceil(log2 N)
    G: int                    # group split threshold
    T: int                    # chunk capacity
    theta: int                # chunks with size > theta wait in the PQ
    B_e: int                  # element label bits
    B_g: int                  # group label bits
    B_t: int                  # top tag bits (simple top)
    D_e: int                  # push step for element labels
    D_g: int                  # push step for group labels
    K_G: int                  # group-split moves per drive
    K_C: int                  # chunk-split moves per drive
    K_R: int                  # reservation/top steps per operation
    J: int                    # simulated length of one top insertion job (simple top)
    top: str = "simple"       # "simple" or "wbbt"
    top_a: int = 8            # WBBT branching parameter
    top_s: int = 8            # WBBT sweep steps per insertion per drain
    top_beta: int | None = None   # WBBT label bits per level (None: 4a + 8)

    @staticmethod
    def for_capacity(N: int, *, c_G: int = 2, c_T: int = 1, K_G: int = 4,
                     K_C: int = 4, K_R: int = 2, c_J: int = 1,
                     top: str = "simple") -> "Params":
        L = max(4, math.ceil(math.log2(max(N, 2))))
        G = c_G * L
        T = c_T * L * L
        theta = (2 * T) // 3
        # A group receives O(G) insertions in its lifetime; averaging can halve a
        # gap once per insertion, so B_e must exceed G plus the push budget.
        B_e = G + math.ceil(math.log2(8 * G + 8)) + 8
        groups_per_chunk = max(1, (3 * T) // G)
        B_g = 2 * groups_per_chunk + math.ceil(math.log2(8 * groups_per_chunk + 8)) + 8
        B_t = 3 * L + 8
        D_e = (1 << (B_e - 1)) // (8 * G + 8)
        D_g = (1 << (B_g - 1)) // (8 * groups_per_chunk + 8)
        return Params(N=N, L=L, G=G, T=T, theta=theta, B_e=B_e, B_g=B_g, B_t=B_t,
                      D_e=D_e, D_g=D_g, K_G=K_G, K_C=K_C, K_R=K_R, J=c_J * L, top=top)


@dataclass
class Stats:
    steps: int = 0            # O(1)-work units outside the top structure
    fallbacks: int = 0
    fallback_reasons: dict = field(default_factory=dict)
    pq_scan: int = 0          # slow-path PQ scan steps (should stay 0)
    max_group: int = 0
    max_chunk: int = 0
    max_lab_e: int = 0
    max_lab_g: int = 0
    min_lab_e: int = 1 << 4096   # "infinity" (labels are far narrower)
    min_lab_g: int = 1 << 4096
    min_gap_e: int = 1 << 4096    # smallest gap ever split by averaging
    min_gap_g: int = 1 << 4096
    max_pq: int = 0           # max number of chunks waiting in the PQ
    reservations: int = 0


class Core:
    def __init__(self, P: Params, lazy: bool = False) -> None:
        """lazy=True defers building the top structure: call prepare_step()
        until it returns True before using the core (O(1) work per call)."""
        self.P = P
        self.E: list[Elem] = []
        self.Gs: list[Group] = []
        self.C: list[Chunk] = []
        self.free_g: list[int] = []
        self.free_c: list[int] = []
        self.stats = Stats()
        self.count = 0
        self.pq = BucketPQ(self)
        self.top = (WBBTTop(self, a=P.top_a, s=P.top_s, beta=P.top_beta)
                    if P.top == "wbbt" else SimpleTop(self))
        self.res_job = None       # None = reservation idle
        # sentinel H = element 0, alone in group 0, in chunk 0
        c = self._new_chunk()
        g = self._new_group(c)
        if lazy:
            self._prep = self.top.init_steps(c)
            self.ready = False
        else:
            self.top.init_first(c)
            self.ready = True
        self.Gs[g].lab = 1 << (P.B_g - 1)
        self.C[c].first = self.C[c].last = g
        self.HEAD = self._new_elem(g, 1 << (P.B_e - 1), -1)
        self.E[self.HEAD].live = False
        self.Gs[g].first = self.Gs[g].last = self.HEAD
        self.Gs[g].size = 1
        self.C[c].size = 1
        self.first_group = g
        self.first_chunk = c
        self.tail = self.HEAD
        self.count = 1

    def prepare_step(self) -> bool:
        """One step of deferred initialization; True once the core is ready."""
        if not self.ready:
            self.stats.steps += 1
            try:
                next(self._prep)
            except StopIteration:
                self.ready = True
        return self.ready

    # ------------------------------------------------------------------ alloc
    def _new_elem(self, g: int, lab: int, h: int) -> int:
        self.E.append(Elem(grp=g, lab=lab, h=h))
        return len(self.E) - 1

    def _new_group(self, c: int) -> int:
        if self.free_g:
            i = self.free_g.pop()
            self.Gs[i] = Group(chk=c)
        else:
            self.Gs.append(Group(chk=c))
            i = len(self.Gs) - 1
        return i

    def _new_chunk(self) -> int:
        if self.free_c:
            i = self.free_c.pop()
            self.C[i] = Chunk()
        else:
            self.C.append(Chunk())
            i = len(self.C) - 1
        return i

    # ------------------------------------------------------- label primitives
    def _between(self, a: int, b: int, why: str) -> int:
        if a + 1 >= b:
            raise GuardFailure(why)
        st = self.stats
        if why[0] == "e":
            st.min_gap_e = min(st.min_gap_e, b - a)
        else:
            st.min_gap_g = min(st.min_gap_g, b - a)
        return (a + b) // 2

    @staticmethod
    def _after(a: int, D: int, B: int, why: str) -> int:
        v = a + D
        if v >= (1 << B) or v <= a:
            raise GuardFailure(why)
        return v

    @staticmethod
    def _before(b: int, D: int, why: str) -> int:
        if b < D or D <= 0:
            raise GuardFailure(why)
        return b - D

    # ----------------------------------------------------------------- query
    def key(self, e: int) -> tuple[int, int, int]:
        x = self.E[e]
        g = self.Gs[x.grp]
        return (self.C[g.chk].tag, g.lab, x.lab)

    def order(self, x: int, y: int) -> bool:
        return self.key(x) < self.key(y)

    # ---------------------------------------------------------------- insert
    def insert_after(self, x: int, h: int) -> int:
        try:
            y = self._insert_elem(x, h)
        except GuardFailure as ex:
            self._fallback(str(ex))
            y = self._insert_elem(x, h)
        try:
            self._background(y)
        except GuardFailure as ex:
            self._fallback(str(ex))
        return y

    def mark_dead(self, x: int) -> None:
        self.E[x].live = False

    def _insert_elem(self, x: int, h: int) -> int:
        P = self.P
        ex = self.E[x]
        g = ex.grp
        G = self.Gs[g]
        if x == G.last:
            lab = self._after(ex.lab, P.D_e, P.B_e, "elem: no room after last")
        else:
            lab = self._between(ex.lab, self.E[ex.next].lab, "elem: no room between")
        # -- mutate
        self.stats.steps += 1
        y = self._new_elem(g, lab, h)
        ey = self.E[y]
        ey.prev = x
        ey.next = ex.next
        if ex.next != NIL:
            self.E[ex.next].prev = y
        ex.next = y
        if self.tail == x:
            self.tail = y
        if G.last == x:
            G.last = y
        G.size += 1
        self.count += 1
        self._chunk_size(G.chk, +1)
        self.stats.max_group = max(self.stats.max_group, G.size)
        self.stats.max_lab_e = max(self.stats.max_lab_e, lab)
        self.stats.min_lab_e = min(self.stats.min_lab_e, lab)
        return y

    def _background(self, y: int) -> None:
        P = self.P
        g = self.E[y].grp
        if self.Gs[g].st == QUIET and self.Gs[g].size >= P.G:
            self._start_group_split(g)
        self._drive_group(self.E[y].grp)
        self._drive_chunk(self.Gs[self.E[y].grp].chk)
        self._reservation(P.K_R)

    # ----------------------------------------------------------- chunk sizes
    def _chunk_size(self, c: int, d: int) -> None:
        C = self.C[c]
        old = C.size
        C.size += d
        if C.st == QUIET:
            self.pq.adjust(c, old, C.size)
        self.stats.max_chunk = max(self.stats.max_chunk, C.size)

    # ---------------------------------------------------------- group split
    def _start_group_split(self, g: int) -> None:
        P = self.P
        G = self.Gs[g]
        c = G.chk
        C = self.C[c]
        if g == C.first:
            lab_l = self._before(G.lab, P.D_g, "group: no room before first")
        else:
            lab_l = self._between(self.Gs[G.prev].lab, G.lab, "group: no room left")
        if g == C.last:
            lab_r = self._after(G.lab, P.D_g, P.B_g, "group: no room after last")
        else:
            lab_r = self._between(G.lab, self.Gs[G.next].lab, "group: no room right")
        # -- mutate
        self.stats.steps += 1
        gl = self._new_group(c)
        gr = self._new_group(c)
        G = self.Gs[g]          # list may have been reallocated? (no: objects stable)
        L_, R_ = self.Gs[gl], self.Gs[gr]
        L_.lab, L_.st, L_.src = lab_l, OVERFLOW, g
        R_.lab, R_.st, R_.src = lab_r, OVERFLOW, g
        # link gl before g
        L_.prev, L_.next = G.prev, g
        if G.prev != NIL:
            self.Gs[G.prev].next = gl
        else:
            self.first_group = gl
        G.prev = gl
        # link gr after g
        R_.prev, R_.next = g, G.next
        if G.next != NIL:
            self.Gs[G.next].prev = gr
        G.next = gr
        if C.first == g:
            C.first = gl
        if C.last == g:
            C.last = gr
        G.st, G.l, G.r = SPLITTING, gl, gr
        self.stats.max_lab_g = max(self.stats.max_lab_g, lab_r)
        self.stats.min_lab_g = min(self.stats.min_lab_g, lab_l)

    def _drive_group(self, g: int) -> None:
        G = self.Gs[g]
        if G.st == SPLITTING:
            s = g
        elif G.st == OVERFLOW:
            s = G.src
        else:
            return
        for _ in range(self.P.K_G):
            if not self._group_split_step(s):
                return

    def _group_split_step(self, g: int) -> bool:
        """One move of a splitting group. Returns False once g is gone."""
        P = self.P
        G = self.Gs[g]
        if G.size == 0:
            self._remove_group(g)
            return False
        gl, gr = G.l, G.r
        L_, R_ = self.Gs[gl], self.Gs[gr]
        center = 1 << (P.B_e - 1)
        if L_.size <= R_.size:
            if L_.next != g:
                raise GuardFailure("group split: left sibling not adjacent")
            e = G.first
            lab = center if L_.size == 0 else \
                self._after(self.E[L_.last].lab, P.D_e, P.B_e, "elem: push-back room")
            # -- mutate
            self.stats.steps += 1
            if G.size == 1:
                G.first = G.last = NIL
            else:
                G.first = self.E[e].next
            if L_.size == 0:
                L_.first = e
            L_.last = e
            dst = gl
        else:
            if R_.prev != g:
                raise GuardFailure("group split: right sibling not adjacent")
            e = G.last
            lab = center if R_.size == 0 else \
                self._before(self.E[R_.first].lab, P.D_e, "elem: push-front room")
            self.stats.steps += 1
            if G.size == 1:
                G.first = G.last = NIL
            else:
                G.last = self.E[e].prev
            if R_.size == 0:
                R_.last = e
            R_.first = e
            dst = gr
        D = self.Gs[dst]
        self.E[e].grp = dst
        self.E[e].lab = lab
        G.size -= 1
        D.size += 1
        if D.chk != G.chk:
            self._chunk_size(D.chk, +1)
            self._chunk_size(G.chk, -1)
        self.stats.max_group = max(self.stats.max_group, D.size)
        self.stats.max_lab_e = max(self.stats.max_lab_e, lab)
        self.stats.min_lab_e = min(self.stats.min_lab_e, lab)
        return True

    def _remove_group(self, g: int) -> None:
        self.stats.steps += 1
        G = self.Gs[g]
        C = self.C[G.chk]
        if G.prev != NIL:
            self.Gs[G.prev].next = G.next
        else:
            self.first_group = G.next
        if G.next != NIL:
            self.Gs[G.next].prev = G.prev
        if C.first == g and C.last == g:
            C.first = C.last = NIL
        elif C.first == g:
            C.first = G.next
        elif C.last == g:
            C.last = G.prev
        quiet = []
        for s in (G.l, G.r):
            S = self.Gs[s]
            if S.st == OVERFLOW and S.src == g:
                S.st, S.src = QUIET, NIL
                quiet.append(s)
        G.alive = False
        G.next = G.prev = NIL
        self.free_g.append(g)
        for s in quiet:
            if self.Gs[s].size >= self.P.G:
                self._start_group_split(s)

    # ---------------------------------------------------------- chunk split
    def _drive_chunk(self, c: int) -> None:
        C = self.C[c]
        if C.st == SPLITTING:
            s = c
        elif C.st == OVERFLOW:
            s = C.src
        else:
            return
        for _ in range(self.P.K_C):
            if not self._chunk_split_step(s):
                return

    def _chunk_split_step(self, x: int) -> bool:
        P = self.P
        X = self.C[x]
        if X.first == NIL:
            self._remove_chunk(x)
            return False
        y, z = X.l, X.r
        Y, Z = self.C[y], self.C[z]
        center = 1 << (P.B_g - 1)
        if Y.size <= Z.size:
            if Y.next != x:
                raise GuardFailure("chunk split: left sibling not adjacent")
            gg = X.first
            lab = center if Y.first == NIL else \
                self._after(self.Gs[Y.last].lab, P.D_g, P.B_g, "group: push-back room")
            self.stats.steps += 1
            if X.last == gg:
                X.first = X.last = NIL
            else:
                X.first = self.Gs[gg].next
            if Y.first == NIL:
                Y.first = gg
            Y.last = gg
            dst = y
        else:
            if Z.prev != x:
                raise GuardFailure("chunk split: right sibling not adjacent")
            gg = X.last
            lab = center if Z.first == NIL else \
                self._before(self.Gs[Z.first].lab, P.D_g, "group: push-front room")
            self.stats.steps += 1
            if X.first == gg:
                X.first = X.last = NIL
            else:
                X.last = self.Gs[gg].prev
            if Z.first == NIL:
                Z.last = gg
            Z.first = gg
            dst = z
        Gg = self.Gs[gg]
        Gg.chk = dst
        Gg.lab = lab
        s = Gg.size
        X.size -= s            # x is SPLITTING, dst is OVERFLOW: neither is in the PQ
        self.C[dst].size += s
        self.stats.max_chunk = max(self.stats.max_chunk, self.C[dst].size)
        self.stats.max_lab_g = max(self.stats.max_lab_g, lab)
        self.stats.min_lab_g = min(self.stats.min_lab_g, lab)
        return True

    def _remove_chunk(self, x: int) -> None:
        """x is empty. It stays in the chunk list as a DEAD tombstone: unlinking
        it from the top structure would cost O(log m). Tombstones are purged by
        the next global rebuild."""
        self.stats.steps += 1
        X = self.C[x]
        X.st = DEAD
        for s in (X.l, X.r):
            S = self.C[s]
            if S.st == OVERFLOW and S.src == x:
                S.st, S.src = QUIET, NIL
                self.pq.enter_if_above(s)

    # ----------------------------------------------------------- reservation
    def _reservation(self, k: int) -> None:
        for _ in range(k):
            self.stats.steps += 1
            if self.res_job is None:
                if self.pq.empty():
                    return
                self.stats.max_pq = max(self.stats.max_pq, len(self.pq.where))
                self.stats.reservations += 1
                x = self.pq.pop_max()
                y = self._new_chunk()
                z = self._new_chunk()
                X, Y, Z = self.C[x], self.C[y], self.C[z]
                Y.prev, Y.next = X.prev, x
                if X.prev != NIL:
                    self.C[X.prev].next = y
                else:
                    self.first_chunk = y
                X.prev = y
                Z.prev, Z.next = x, X.next
                if X.next != NIL:
                    self.C[X.next].prev = z
                X.next = z
                job = self.top.insert_around(x, y, z)
                X.st, X.l, X.r = SPLITTING, y, z
                Y.st, Y.src = OVERFLOW, x
                Z.st, Z.src = OVERFLOW, x
                self.res_job = job
            elif not self.top.step(self.res_job):
                self.res_job = None

    # -------------------------------------------------------------- fallback
    def _fallback(self, reason: str) -> None:
        """Synchronous rebuild of groups, chunks and tags from the element list."""
        P = self.P
        self.stats.fallbacks += 1
        self.stats.fallback_reasons[reason] = self.stats.fallback_reasons.get(reason, 0) + 1
        seq = []
        e = self.HEAD
        while e != NIL:
            seq.append(e)
            e = self.E[e].next
        self.Gs, self.C, self.free_g, self.free_c = [], [], [], []
        self.pq = BucketPQ(self)
        self.res_job = None
        gs = max(1, P.G // 2)
        gpc = max(1, (P.T // 2) // gs)
        groups = [seq[i:i + gs] for i in range(0, len(seq), gs)]
        chunks = [groups[i:i + gpc] for i in range(0, len(groups), gpc)]
        prev_c = NIL
        prev_g = NIL
        for cgroups in chunks:
            c = self._new_chunk()
            C = self.C[c]
            C.prev = prev_c
            if prev_c != NIL:
                self.C[prev_c].next = c
            step_g = (1 << P.B_g) // (len(cgroups) + 1)
            for j, elems in enumerate(cgroups):
                g = self._new_group(c)
                G = self.Gs[g]
                G.lab = (j + 1) * step_g
                G.prev = prev_g
                if prev_g != NIL:
                    self.Gs[prev_g].next = g
                step_e = (1 << P.B_e) // (len(elems) + 1)
                for k, el in enumerate(elems):
                    self.E[el].grp = g
                    self.E[el].lab = (k + 1) * step_e
                G.first, G.last, G.size = elems[0], elems[-1], len(elems)
                if j == 0:
                    C.first = g
                C.last = g
                C.size += len(elems)
                prev_g = g
            prev_c = c
        self.first_chunk = 0
        self.first_group = 0
        self.top.relabel_all()

    # ------------------------------------------------------------ inspection
    def elements(self) -> list[int]:
        out = []
        e = self.HEAD
        while e != NIL:
            out.append(e)
            e = self.E[e].next
        return out

    def check(self) -> None:
        """Full O(n) check of INV-S (docs/SPEC.md §6) plus bookkeeping."""
        P = self.P
        # element list
        elems = self.elements()
        assert elems[0] == self.HEAD and self.E[self.HEAD].prev == NIL
        assert len(elems) == len(self.E) == self.count, "lost elements"
        for a, b in zip(elems, elems[1:]):
            assert self.E[b].prev == a
        assert self.tail == elems[-1]
        # group list
        groups = []
        g = self.first_group
        assert self.Gs[g].prev == NIL
        while g != NIL:
            assert self.Gs[g].alive
            groups.append(g)
            if self.Gs[g].next != NIL:
                assert self.Gs[self.Gs[g].next].prev == g
            g = self.Gs[g].next
        assert len(groups) == sum(1 for G in self.Gs if G.alive)
        # chunk list
        chunks = []
        c = self.first_chunk
        assert self.C[c].prev == NIL
        while c != NIL:
            assert self.C[c].alive
            chunks.append(c)
            if self.C[c].next != NIL:
                assert self.C[self.C[c].next].prev == c
            c = self.C[c].next
        assert len(chunks) == sum(1 for C in self.C if C.alive)
        # contiguous nesting: elements in groups
        flat = []
        for g in groups:
            G = self.Gs[g]
            rng = []
            if G.first != NIL:
                e = G.first
                while True:
                    rng.append(e)
                    if e == G.last:
                        break
                    e = self.E[e].next
                    assert e != NIL, "group range runs off the list"
            else:
                assert G.last == NIL
            assert len(rng) == G.size, f"group size {G.size} != {len(rng)}"
            for e in rng:
                assert self.E[e].grp == g
            labs = [self.E[e].lab for e in rng]
            assert all(a < b for a, b in zip(labs, labs[1:])), "elem labels unsorted"
            assert all(0 <= v < (1 << P.B_e) for v in labs)
            flat.extend(rng)
        assert flat == elems, "groups do not tile the element list"
        # contiguous nesting: groups in chunks
        flat = []
        for c in chunks:
            C = self.C[c]
            rng = []
            if C.first != NIL:
                g = C.first
                while True:
                    rng.append(g)
                    if g == C.last:
                        break
                    g = self.Gs[g].next
                    assert g != NIL
            else:
                assert C.last == NIL
            for g in rng:
                assert self.Gs[g].chk == c
            assert C.size == sum(self.Gs[g].size for g in rng), "chunk size"
            labs = [self.Gs[g].lab for g in rng]
            assert all(a < b for a, b in zip(labs, labs[1:])), "group labels unsorted"
            assert all(0 <= v < (1 << P.B_g) for v in labs)
            flat.extend(rng)
        assert flat == groups, "chunks do not tile the group list"
        tags = [self.C[c].tag for c in chunks]
        assert all(a < b for a, b in zip(tags, tags[1:])), "chunk tags unsorted"
        # derived: keys strictly increase
        keys = [self.key(e) for e in elems]
        assert all(a < b for a, b in zip(keys, keys[1:])), "keys unsorted"
        # split-state consistency
        for g in groups:
            G = self.Gs[g]
            if G.st == SPLITTING:
                for s in (G.l, G.r):
                    assert self.Gs[s].alive and self.Gs[s].st == OVERFLOW and self.Gs[s].src == g
                assert self.Gs[G.l].next == g and self.Gs[G.r].prev == g, "group siblings"
            elif G.st == OVERFLOW:
                assert self.Gs[G.src].st == SPLITTING
        for c in chunks:
            C = self.C[c]
            if C.st == SPLITTING:
                for s in (C.l, C.r):
                    assert self.C[s].alive and self.C[s].st == OVERFLOW and self.C[s].src == c
                assert self.C[C.l].next == c and self.C[C.r].prev == c, "chunk siblings"
            elif C.st == OVERFLOW:
                assert self.C[C.src].st == SPLITTING
            elif C.st == DEAD:
                assert C.first == NIL and C.size == 0
        # priority queue holds exactly the quiet chunks above theta
        want = {c for c in chunks if self.C[c].st == QUIET and self.C[c].size > P.theta}
        self.pq.check(want)
        if hasattr(self.top, "check"):
            self.top.check(quiescent=self.res_job is None)
