"""Full order-maintenance structure: deletion and growth via incremental
global rebuilding on top of the insert-only Core (docs/SPEC.md §5.7).

`cur` answers all queries. When `cur` reaches half its capacity, or when too
few of its elements are live, a fresh Core `nxt` sized for the live count is
filled in the background by appending live elements in list order, K_B per
update. Inserts after an already-copied element are mirrored into `nxt`.
"""
from __future__ import annotations

from core import NIL, Core, Params

N_MIN = 64


class OrderMaintenance:
    def __init__(self, *, K_B: int = 4, params=Params.for_capacity) -> None:
        self.params = params
        self.K_B = K_B
        self.cur = Core(params(N_MIN))
        self.cur_idx: dict[int, int] = {}
        self.nxt: Core | None = None
        self.nxt_idx: dict[int, int] = {}
        self.cursor = NIL
        self.cursor_set = False   # copying starts only once nxt is fully initialized
        self.live = 0
        self.next_handle = 0
        self.rebuilds = 0
        self.retired: list[Core] = []      # finished cores, kept only for statistics
        self.max_fill = 0.0                # max over time of cur.count / cur.P.N

    # ------------------------------------------------------------- interface
    def insert_first(self) -> int:
        return self._insert(None)

    def insert_after(self, x: int) -> int:
        return self._insert(x)

    def delete(self, x: int) -> None:
        self.cur.mark_dead(self.cur_idx.pop(x))
        if self.nxt is not None and x in self.nxt_idx:   # only copied elements
            self.nxt.mark_dead(self.nxt_idx.pop(x))
        self.live -= 1
        self._rebuild_step()

    def order(self, x: int, y: int) -> bool:
        return self.cur.order(self.cur_idx[x], self.cur_idx[y])

    # -------------------------------------------------------------- internals
    def _insert(self, hx: int | None) -> int:
        hy = self.next_handle
        self.next_handle += 1
        xi = self.cur.HEAD if hx is None else self.cur_idx[hx]
        self.cur_idx[hy] = self.cur.insert_after(xi, hy)
        if self.nxt is not None and self.cursor_set and (hx is None or hx in self.nxt_idx):
            xn = self.nxt.HEAD if hx is None else self.nxt_idx[hx]
            self.nxt_idx[hy] = self.nxt.insert_after(xn, hy)
        self.live += 1
        self.max_fill = max(self.max_fill, self.cur.count / self.cur.P.N)
        self._rebuild_step()
        return hy

    def _rebuild_step(self) -> None:
        if self.nxt is None:
            N = self.cur.P.N
            if self.cur.count >= N // 2 or (N > N_MIN and self.live < N // 8):
                self.nxt = Core(self.params(4 * max(self.live, 16)), lazy=True)
                self.nxt_idx = {}
                self.cursor_set = False
                self.rebuilds += 1
            return
        if not self.cursor_set:
            # build nxt's initial top structure incrementally, then start copying
            for _ in range(self.K_B):
                if self.nxt.prepare_step():
                    self.cursor = self.cur.E[self.cur.HEAD].next
                    self.cursor_set = True
                    break
            return
        for _ in range(self.K_B):
            if self.cursor == NIL:
                self.retired.append(self.cur)
                self.cur, self.cur_idx = self.nxt, self.nxt_idx
                self.nxt, self.nxt_idx = None, {}
                return
            e = self.cur.E[self.cursor]
            if e.live:
                assert e.h not in self.nxt_idx, "cursor met an already-copied element"
                self.nxt_idx[e.h] = self.nxt.insert_after(self.nxt.tail, e.h)
            self.cursor = e.next

    # ------------------------------------------------------------ inspection
    def cores(self) -> list[Core]:
        return self.retired + [self.cur] + ([self.nxt] if self.nxt else [])

    def total_steps(self) -> int:
        """Core steps plus top-structure work, over all cores."""
        return sum(c.stats.steps + c.top.top_steps for c in self.cores())

    def check(self) -> list[int]:
        """Check both cores; return the live handles of `cur` in order."""
        self.cur.check()
        live = [self.cur.E[e].h for e in self.cur.elements() if self.cur.E[e].live]
        assert len(live) == self.live == len(self.cur_idx)
        if self.nxt is not None and self.cursor_set:
            self.nxt.check()
            copied = [self.nxt.E[e].h for e in self.nxt.elements() if self.nxt.E[e].live]
            assert copied == live[:len(copied)], "nxt is not a prefix of cur"
        return live
