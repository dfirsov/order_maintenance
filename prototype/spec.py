"""Abstract model of the order-maintenance problem (docs/SPEC.md §2).

A plain Python list of handles. O(n) operations; used only as the reference
in differential tests.
"""
from __future__ import annotations


class SpecOM:
    def __init__(self) -> None:
        self.items: list[int] = []
        self.next_handle = 0

    def _fresh(self) -> int:
        h = self.next_handle
        self.next_handle += 1
        return h

    def insert_first(self) -> int:
        h = self._fresh()
        self.items.insert(0, h)
        return h

    def insert_after(self, x: int) -> int:
        h = self._fresh()
        self.items.insert(self.items.index(x) + 1, h)
        return h

    def delete(self, x: int) -> None:
        self.items.remove(x)

    def order(self, x: int, y: int) -> bool:
        return self.items.index(x) < self.items.index(y)
