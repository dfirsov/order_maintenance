# Testing and measurement report

Status: 2026-10-13. Prototype code: `prototype/`. Raw results: `prototype/results/`.
Design: `docs/SPEC.md`.

## Summary

| Question | Answer |
|---|---|
| Is the prototype correct? | No wrong answer and no invariant violation in any run. That covers the differential tests, 5,000+ random-parameter fuzz trials with every invariant checked after every operation, and all stress runs. |
| Does the test suite have teeth? | Yes. 20 of 20 injected bugs are caught. 3 control edits (guard removals) and 1 harmless edit survive, as expected. |
| Is the cost per operation bounded? | Yes, empirically. Up to 10⁶ operations on 16 workloads, the worst operation costs ≤ 3,034 executed lines, and 99.9% of operations stay under 1,900. Every function's cost per call is flat, and its number of calls per operation is capped by the code's structure. |
| Did the safety-net rebuild ever fire with default parameters? | Never: zero fallbacks in every scaling, line-count and search run (10³ to 3·10⁶ operations; top level alone up to 10⁶ chunks). It fired only in deliberate fault runs: tiny label widths, fuzzed parameters, and sweep settings below the thresholds in §6. |
| What did the campaign find? | One real O(log n) step, now fixed. One guard hardened. Two test-suite blind spots, now closed. One redundant code path. Numeric thresholds for the cost proof (§6). The default chunk capacity is safe in practice but **not provably** so: the proof needs `c_T·K_R ≳ 4.2` (§4). |

## 1. Correctness

### Differential tests
`test_om.py`: 16 tests, 8 per top level. Every answer is compared with a plain-list model.
The full invariant check runs after every operation in small runs:
* core INV-S (SPEC §6);
* priority-queue consistency;
* top-level invariants W1–W4 (SPEC §5.6), checked directly.

Workloads: random, insert-heavy, delete-heavy, hammering one gap, sequential, front-only,
tiny labels (fallbacks forced), and slow reservations (chunks over-fill).

### Random-parameter fuzzing
`fuzz.py`: 5,300 trials, plus 40 more in every battery run. **Zero failures.** The fallback
rebuild fired in 3,943 of the 5,000 large-campaign trials, so the safety net was heavily
exercised under full checking.

Each trial draws, deliberately near the feasible minimum:

| Parameter | Range |
|---|---|
| group size G | 2–10 |
| chunk size T | G to 8G |
| per-operation budgets K_G, K_C, K_R | 1–5 |
| simulated job length | 1–12 |
| label widths | minimum + 0–6 bits |
| top-level branching a | 5–10 |
| drain funding s | 1–10 |
| top-level label width | minimum + 0–12 bits |

It also draws a random operation mix (delete rate up to 45%) and a random anchor policy
(uniform, hammer, sequential, mixed), and picks a top level. The run is 200–1,500 operations,
all invariants are checked after every operation, and answers are compared with the list model.

## 2. Testing the tests (`mutate.py`, `battery.py`)

Each mutant is one textual edit to an algorithm file. The battery runs differential tests on
both top levels, 40 fuzz trials, stress on 5 workloads (requiring zero fallbacks and bounded
headroom) and the top level alone.

| | Result |
|---|---|
| M01–M19 (bugs in labels, splits, PQ, scheduling, rebuild, top-level drains, ranges, weights) | all **killed** |
| M20 (oversized newly-quiet groups don't start splitting at once) | survives: **equivalent**. They start on their next insert anyway; candidate simplification for the Lean port |
| C01–C03 (remove the drain-step tag guard / group-split adjacency guard / chunk-split adjacency guard) | survive, as intended. With a correct algorithm these guards never trip |

Two blind spots were found and closed:
* **M07** (serve the emptiest waiting chunk instead of the fullest) was invisible to all
  workloads. The harmonic adversary spreads inserts evenly, so the serving order doesn't
  matter to it. A new **starvation adversary** now catches it (chunk/T reaches 1.40).
* **M19** (queue not told when a chunk shrinks) needs a rare path: a group split moving an
  element across a chunk boundary while the chunk is queued. Fuzzing with skewed parameters
  now reaches it.

## 3. Cost per operation

### Method
`measure.py` counts **every executed line** in the algorithm's files, per operation, using
Python 3.12 `sys.monitoring`. Adversary code is excluded. This catches any loop that
hand-placed counters would miss.

Work inside C calls is bounded separately by recording:
* the largest list a C-level list operation touches;
* the tag width in bits.

### Results at 10⁶ operations (`results/lines_1e6.txt`)

| Workload | max lines/op | p99.9 | mean |
|---|---|---|---|
| group_end | 3034 | 1756 | 303 |
| zigzag | 2999 | 1792 | 331 |
| spread1k | 2998 | 1789 | 327 |
| harmonic / starve / chunk_end / hammer | 2987–2988 | 1785–1876 | 313–327 |
| insert_random / front / random | 2833–2867 | 1671–1856 | 265–327 |
| spread64 / narrow_gap / harmonic_half | 2722–2790 | 1772–1827 | 319–335 |
| append / churn / delete_burst | 2309–2447 | 1382–1716 | 158–338 |

All 16 workloads had zero fallbacks. Bounds on C-level work:

| Quantity | Max observed |
|---|---|
| top-level table size | 26 |
| live-children list | 18 |
| tables containing one entry | 2 |
| tag width | 280 bits = 13 words of log₂N = 22 bits |

### Why the maximum still drifts upward, and why that's fine
The per-decade maximum rises slowly, for example 2,132 → 2,639 → 2,987.

`callprofile.py` splits this into two numbers per function:

| Function | max lines per call (flat in n) | max calls per op (structural cap) |
|---|---|---|
| top-level drain start | 351–354 (table size ≤ 26) | observed 3, cap 12 |
| group-split move | 30 | observed 24 = cap (6 inserts × K_G) |
| chunk-split move | 28 | observed 16, cap 24 |
| drain step | 31 | observed 11, cap 12 |
| drain finish | 117 | observed 2, cap 12 |

* **Cost per call is flat in n:** it is bounded by table sizes.
* **Calls per operation are capped** by fixed loop counts. An operation makes at most 6 core
  inserts: 1 live, 1 mirrored, and K_B = 4 rebuild copies. Each insert makes at most K_G
  group moves, K_C chunk moves and K_R top-level steps. Each top-level step does at most one
  of: a drain start, a drain step (plus a possible finish), a weight-walk level, or a
  path-copy level.

The observed totals approach the product of these caps as rare coincidences accumulate. The
`churn` workload keeps the structure tiny (log₂N = 13), yet shows the same drift
(1,590 → 2,006 → 2,447). So the drift depends on the number of operations, not on n.

Hard cap at default parameters: about 10⁴ lines per operation, provided top-level tables
stay ≤ about 26 entries. That condition is exactly timing invariant W5.

### Real O(log n) step found and fixed
At the start of a background rebuild, the new core's initial top-level tree (a chain of H
nodes) was built inside one operation: 96 → 124 → 152 lines, growing with log n. It is now
built one node per background step before copying starts, and inserts are mirrored into
the new core only once it is ready.

### Model assumptions (not visible to line counting)
* **Array growth.** Python lists grow by amortized doubling. A worst-case model needs arrays
  sized in advance, with the O(N) allocation spread over the rebuild's background steps (or
  constant-time-initializable arrays). The Lean port must pick one.
* **Word-RAM arithmetic.** Tags are `H·β` bits ≈ 13 words of log₂N bits; comparisons and
  additions count as O(1).
* **Hash maps.** Python dicts stand in for arrays indexed by handle.

## 4. Scaling and headroom (`scaling.py`, `results/scaling_summary.txt`)

Full system, default parameters, untraced. Each cell is max steps/op (the hand-placed
counter, including top-level work) / peak chunk fullness relative to T. Zero fallbacks and
zero slow queue scans in every cell.

| workload | 10³ | 10⁴ | 10⁵ | 10⁶ | 3·10⁶ |
|---|---|---|---|---|---|
| append | 68/0.72 | 77/0.72 | 93/0.72 | 93/0.72 | 93/0.72 |
| chunk_end | 67/0.72 | 83/0.72 | 100/0.72 | 116/0.72 | 116/0.72 |
| churn | 49/0.72 | 55/0.72 | 73/0.72 | 95/0.72 | 101/0.72 |
| delete_burst | 66/0.72 | 83/0.72 | 86/0.72 | 100/0.72 | 103/0.73 |
| front | 77/0.72 | 86/0.72 | 101/0.72 | 115/0.72 | 116/0.72 |
| group_end | 82/0.72 | 83/0.72 | 109/0.72 | 120/0.72 | 120/0.72 |
| hammer | 74/0.72 | 84/0.72 | 107/0.72 | 116/0.72 | 116/0.72 |
| harmonic | 66/0.72 | 88/0.78 | 101/0.78 | 116/0.83 | not run* |
| harmonic_half | 66/0.72 | 84/0.78 | 102/0.79 | 110/0.80 | not run* |
| insert_random | 66/0.72 | 98/0.72 | 98/0.72 | 113/0.72 | 113/0.72 |
| narrow_gap | 74/0.72 | 84/0.72 | 96/0.72 | 112/0.72 | 112/0.72 |
| random | 71/0.72 | 76/0.72 | 109/0.72 | 115/0.72 | 115/0.72 |
| spread1k | 66/0.72 | 84/0.72 | 97/0.72 | 117/0.72 | 117/0.72 |
| spread64 | 67/0.72 | 81/0.72 | 107/0.72 | 110/0.72 | 110/0.72 |
| starve | 66/0.72 | 91/0.79 | 106/0.79 | 116/0.79 | not run* |
| zigzag | 66/0.72 | 81/0.72 | 104/0.72 | 117/0.72 | 117/0.72 |

\* The queue adversaries re-scan the whole list every round, so at 3·10⁶ they ran for hours
and were stopped. The slowness is in the adversary, not the algorithm. Queue attacks are
covered at 10⁶ in two configurations (below).

* **Steps per operation level off.** The maximum is identical at 10⁶ and 3·10⁶ for every
  workload that finished both.
* **Label headroom grows with n.** Label widths grow with log N.

  | Level | At 3·10⁶, worst case |
  |---|---|
  | element labels | ≤ 39 of 63 bits used |
  | group labels | ≤ 15 of 85 |
  | top-level labels | ≤ 20 of 40 |
  | group-label push range | ≤ 4% used |
  | element-label push range | ≤ 12% used |
* **Other headroom.** The old core's fill during a rebuild stays ≤ 0.69 (the trigger is 0.5,
  the capacity 1.0). Top-level tables have ≤ 26 entries.
* **Top level alone** (`top_stress.py`, five adversaries):
  * zero fallbacks;
  * longest job 46 / 56 / 66 steps at m = 10⁴ / 10⁵ / 10⁶, i.e. 6H + 4;
  * tables ≤ 28 entries;
  * with the final width β = 40, tested to m = 3·10⁵ with ≥ 22 bits free. The 10⁶ runs used
    the earlier β = 80 and consumed at most 18 bits.

### Finding: chunk capacity versus the zeroing game

Under the queue attacks, peak chunk fullness creeps up slowly with n (harmonic: 0.78 → 0.83
from 10⁵ to 10⁶). That is predicted:

1. One top-level job takes about `6H` steps, with `H = log₈ m`. At `K_R` steps per operation
   a reservation round lasts `R ≈ 2·log₂m / K_R` operations.
2. The zeroing game bounds the overshoot above θ by `R·(H_m + 1) ≈ (1.4/K_R)·(log₂ m)²`.
3. Chunk capacity is `T = c_T·L²`, and the slack above θ is `T/3`.

So the bound stays below the slack for every n iff `c_T·K_R ≳ 4.2`. The defaults
(`c_T = 1`, `K_R = 2`) satisfy this only empirically: measured overshoots are about 60% of the
bound, comfortably safe at any practical n, but not provably safe. **For the cost proof use
`K_R = 4`, `c_T = 2`**, which gives the bound a 2× margin.

Check at n = 10⁶ (`proof_params.py`, `results/proof_params.txt`):

| Workload | defaults (K_R=2, c_T=1) | proof parameters (K_R=4, c_T=2) |
|---|---|---|
| harmonic | chunk 0.83·T, 179 queued, 116 steps/op | chunk 0.69·T, 21 queued, 139 steps/op |
| starve | 0.79·T, 20 queued, 116 | 0.69·T, 20 queued, 139 |
| hammer | 0.72·T, 116 | 0.68·T, 132 |
| random | 0.72·T, 115 | 0.68·T, 128 |

Zero fallbacks in every run. The proof parameters remove almost all queue pressure (peak
barely above θ = 0.67·T) for about 20% more work per operation.

## 5. Adversaries

### Hand-written (`stress.py`)
* **Basic:** random, insert-only random, front, append, hammer (one gap), spread (64/1k
  anchors), churn.
* **Queue attacks:**
  * harmonic: the zeroing-game adversary;
  * harmonic on half the chunks;
  * starvation: hammer the smallest waiting chunk.
* **Label attacks:**
  * insert right after a group's or chunk's last element (the push-label path);
  * narrowest gap among 16 sampled elements;
  * zigzag between front and back.
* **Rebuild attack (delete_burst):** grow, delete 90%, then hammer both sides of the copy
  cursor.

The strongest are the queue attacks: chunk fullness reaches 0.78–0.81·T, against 0.72
otherwise.

### Automated search (`search.py`)
A mixed adversary: weights over 11 attack moves, number of hot spots, reshuffle period,
fraction of chunks attacked round-robin. It was optimised by random sampling plus hill
climbing over about 480 candidates in two campaigns.

**No fallbacks.** The best "danger" score was 0.76, the worst normalised headroom ratio. The
hand-written queue attacks score about 0.80. Automated search found nothing the targeted
attacks missed.

## 6. Parameter sensitivity: thresholds for the cost proof (`sweep.py`)

One constant varied at a time; 6 workloads; n = 100k.

| Constant (default) | Safe | Fails | Mechanism |
|---|---|---|---|
| top-level drain funding s (8) | ≥ 6 | ≤ 5 | Drains fall behind. Targets may not drain, so their tables overflow and fallbacks fire. Theory: s ≥ 4(1+ε). |
| top-level steps per operation K_R (2) | ≥ 2 | 1 | Reservations take twice as long, and chunks over-fill (1.06·T) under queue attacks. Zeroing game: fullness ∝ job length / K_R. |
| group-split moves per insert K_G (4) | ≥ 2 | 1 | Moves don't outpace inserts. Splitting groups never empty, so groups grow to 8·G and fallbacks fire. This is the Dietz–Sleator "k large enough" condition. |
| chunk-split moves K_C (4) | ≥ 1 | — | One move carries a whole group |
| rebuild copy speed K_B (4) | ≥ 3 comfortable | 2 is tight | Fill of the old core reaches 0.89 at K_B = 2 (still below 1) |
| branching a (8) | 5–16 | — | Top label use grows with a (β = 4a+8 grows with it) |
| group factor c_G (2) | 1–3 | — | |
| chunk factor c_T (1) | 1–2 | — | |

These are the concrete numeric hypotheses the Lean cost proof (SPEC M5/M6) must
establish: K_G ≥ 2, s ≥ 4(1+ε), K_R chosen against T via the zeroing game, and K_B against
the rebuild trigger.

## 7. Reproducing

```
cd prototype
python3 -m unittest test_om                      # differential tests
python3 battery.py                               # quick pass/fail battery
python3 mutate.py -j 12                          # mutation testing
python3 fuzz.py 5000 -j 12                       # random-parameter fuzzing
python3 measure.py 1000000 -j 16                 # executed-lines per op, all workloads
python3 callprofile.py 200000 hammer harmonic    # per-call / per-op structural bound
python3 scaling.py -j 8                          # headroom vs n, up to 3e6
python3 sweep.py 100000 -j 8                     # parameter sensitivity
python3 search.py 320 -j 8                       # adversary search
```
