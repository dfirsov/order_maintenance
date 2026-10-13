"""Shared exception for guarded writes (docs/SPEC.md, safety principle)."""


class GuardFailure(Exception):
    """A guarded write found no label room or broken adjacency.

    Raised before any mutation; the caller falls back to a synchronous rebuild.
    """
