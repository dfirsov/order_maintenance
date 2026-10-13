# Python prototype

Executable model of `docs/SPEC.md`, written as arrays plus integer indices so the
Lean port is mechanical.

| File | Contents |
|---|---|
| `spec.py` | abstract model (plain list) |
| `core.py` | insert-only core: elements → groups → chunks, guarded writes, fallback, reservation process, `check()` for the safety invariant (SPEC §6) |
| `pq.py` | O(1) bucket priority queue of chunks waiting for the top level |
| `top_simple.py` | milestone-1 top level: averaging plus full relabel (correct, not O(1)); simulates a job length of Θ(log m) |
| `top_wbbt.py` | real top level (SPEC §5.6): weight-balanced tree, immutable label tables, stored paths, ghost drains; O(log m) per job |
| `guards.py` | `GuardFailure`, shared by the core and the top level |
| `wrapper.py` | deletion (tombstones) and growth via incremental global rebuilding |
| `test_om.py` | differential tests against `spec.py`, including forced fallbacks |
| `stress.py` | adversarial workloads with instrumentation (`TOP=wbbt` selects the real top level) |
| `top_stress.py` | the top level in isolation, up to 10⁶ chunks |

```
python3 -m unittest test_om              # differential tests, both top levels
TOP=wbbt python3 stress.py 200000        # all workloads, full system
TOP=wbbt python3 stress.py 200000 harmonic
python3 top_stress.py 1000000            # top level alone
```

Targets for `stress.py`:
- `fallbacks=0` and `pq_scan=0`;
- `max_steps/op` flat in n;
- `big_core_chunk/T` below the label-width budget.

`max_steps/op` includes top-level work. With `top_simple.py` that includes its O(m)
full relabels, which is why the real top level exists.
