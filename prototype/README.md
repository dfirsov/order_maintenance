# Python prototype

Executable model of `docs/SPEC.md`, written as arrays plus integer indices so the
Lean port is mechanical.

| File | Contents |
|---|---|
| `spec.py` | abstract model (plain list) |
| `core.py` | insert-only core: elements → groups → chunks, guarded writes, fallback, reservation process, `check()` for the safety invariant (SPEC §6) |
| `pq.py` | O(1) bucket priority queue of chunks waiting for the top level (deterministic: LIFO within a bucket) |
| `top_simple.py` | milestone-1 top level: averaging plus full relabel (correct, not O(1)); simulates a job length of Θ(log m) |
| `top_wbbt.py` | real top level (SPEC §5.6): weight-balanced tree, immutable label tables, stored paths, ghost drains; O(log m) per job |
| `guards.py` | `GuardFailure`, shared by the core and the top level |
| `wrapper.py` | deletion (tombstones) and growth via incremental global rebuilding |
| `test_om.py` | differential tests against `spec.py`, including forced fallbacks |
| `stress.py` | adversarial workloads with instrumentation (`TOP=wbbt` selects the real top level) |
| `top_stress.py` | the top level in isolation, up to 10⁶ chunks |
| `fuzz.py` | random-parameter fuzzing with every invariant checked after every operation |
| `battery.py`, `mutate.py` | quick pass/fail battery; mutation testing (are injected bugs caught?) |
| `measure.py` | executed lines per operation (`sys.monitoring`), per-decade and per-function maxima |
| `callprofile.py` | max lines per call × max calls per operation, giving a structural bound per operation |
| `scaling.py`, `summarize_scaling.py` | headroom metrics vs n, up to 3·10⁶ |
| `sweep.py`, `search.py` | parameter sensitivity; automated adversary search |
| `rebuild_attack.py` | adversary for the rebuild sizing rule (`docs/PROOF.md` §6.1); broke the O(1) bound at n = 2²⁰ before fix 1 |
| `lemmas.py` | lemma checker: measures every quantitative bound of `docs/PROOF.md` §4 per core (presets `default`, `proof`), including the exact per-height top bounds |
| `top_bounds.py` | exact constants of Lemmas T3–T5 per height, plus closed forms for all heights (`docs/PROOF.md` §4.5) |
| `lower_bounds.py` | exact constants and conditions I1–I10 of the lower levels and the assembly, per `L` (`docs/PROOF.md` §4.7) |
| `trace.py`, `trace_campaign.py` | export operation traces with answers, keys, counters and state digests; the Lean model (`lean/OM/Test/Replay.lean`) must replay them exactly |
| `linecov.py` | line coverage of the algorithm under all suites; every uncovered line should be a provably unreachable path |
| `results/` | raw outputs of the campaign (see `docs/TESTING.md`) |

```
python3 -m unittest test_om              # differential tests, both top levels
TOP=wbbt python3 stress.py 200000        # all workloads, full system
TOP=wbbt python3 stress.py 200000 harmonic
python3 top_stress.py 1000000            # top level alone
```

The full testing campaign and its results are in `docs/TESTING.md` (reproduction commands
in §7 there).

Targets for `stress.py`:
- `fallbacks=0` and `pq_scan=0`;
- `max_steps/op` flat in n;
- `big_core_chunk/T` below the label-width budget.

`max_steps/op` includes top-level work. With `top_simple.py` that includes its O(m)
full relabels, which is why the real top level exists.
