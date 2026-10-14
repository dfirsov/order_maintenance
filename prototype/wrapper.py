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
        assert K_B >= 2, "the rebuild must outpace insertions (Lemma W)"
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
        self.max_install_fill = 0.0        # max nxt.count / nxt.P.N when nxt replaces cur
        self.max_fill_excess = -(1 << 60)  # max cur.count - Lemma W(1) bound (lemmas.py)
        self.max_install_excess = -(1 << 60)   # max nxt.count - (N'/4 + 1) at install

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
    def next_capacity(self) -> int:
        """Capacity of the next core (docs/PROOF.md §2.7, Lemma W).

        The rebuild takes H' preparation steps plus one step per element of cur
        it scans (tombstones included), K_B steps per operation, and every
        insertion meanwhile may end up in nxt. So nxt receives at most
        live + floor((count + H')/(K_B - 1)) + 1 elements; size it four times that.
        H' <= L + 2 because the new capacity is at most 4N (K_B >= 4).
        Sizing by `live` alone is wrong: see rebuild_attack.py.
        """
        prep = self.cur.P.L + 2
        mirrored = (self.cur.count + prep) // (self.K_B - 1) + 1
        return 4 * max(self.live + mirrored, 16)

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
        P = self.cur.P
        bound = P.N // 2 + (P.N // 2 + P.L + 2) // (self.K_B - 1) + 1
        self.max_fill_excess = max(self.max_fill_excess, self.cur.count - bound)
        self._rebuild_step()
        return hy

    def _rebuild_step(self) -> None:
        if self.nxt is None:
            N = self.cur.P.N
            if self.cur.count >= N // 2 or (N > N_MIN and self.live < N // 8):
                self.nxt = Core(self.params(self.next_capacity()), lazy=True)
                self.nxt_idx = {}
                self.cursor_set = False
                self.rebuilds += 1
            return
        # exactly K_B steps (docs/PROOF.md §2.7, Lemma W): first H' preparation steps
        # (the call that finds the preparation finished does no work and costs
        # nothing), then one step per scanned element; the swap is free and happens
        # as soon as the cursor passes the last element
        budget = self.K_B
        while budget > 0:
            if not self.cursor_set:
                if self.nxt.prepare_step():
                    self.cursor = self.cur.E[self.cur.HEAD].next
                    self.cursor_set = True
                else:
                    budget -= 1
                continue
            if self.cursor != NIL:
                e = self.cur.E[self.cursor]
                if e.live:
                    assert e.h not in self.nxt_idx, "cursor met an already-copied element"
                    self.nxt_idx[e.h] = self.nxt.insert_after(self.nxt.tail, e.h)
                self.cursor = e.next
                budget -= 1
            if self.cursor == NIL:
                self.max_install_fill = max(self.max_install_fill, self.nxt.count / self.nxt.P.N)
                self.max_install_excess = max(self.max_install_excess,
                                              self.nxt.count - (self.nxt.P.N // 4 + 1))
                self.retired.append(self.cur)
                self.cur, self.cur_idx = self.nxt, self.nxt_idx
                self.nxt, self.nxt_idx = None, {}
                return

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
