# Testing and measurement report

Status: 2026-10-14 (§8 added after the proof-driven fixes). Prototype code: `prototype/`. Raw results: `prototype/results/`.
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
python3 rebuild_attack.py                        # §8: rebuild-sizing adversary
python3 lemmas.py 1000000 -j 23                  # §8: every bound of docs/PROOF.md §4
python3 lemmas.py 300000 --seeds 4 -j 23
python3 fuzz.py 20000 -j 23; python3 fuzz.py 2000 --long -j 23
python3 linecov.py 300                           # §8: lines the suites never execute
```

## 8. Re-test after the proof-driven fixes (2026-10-14)

Writing the pen-and-paper proof sketch (`docs/PROOF.md`) found one real cost bug and two
proof gaps that the campaign above had missed (`docs/PROOF.md` §6). All three are fixed:

| Fix | Change | Evidence |
|---|---|---|
| 1. Rebuild sizing | the next core is sized `4·max(live + ⌈(count + L + 2)/(K_B − 1)⌉, 16)` instead of `4·max(live, 16)` | `rebuild_attack.py` at n = 2²⁰: before, 4 fallbacks, 4,115 steps/op, a capacity-64 core holding 76,809 elements; after, 0 fallbacks, ≈ 100 steps/op |
| 2. Element label width | `B_e = 2G + …` instead of `G + …` | not observable at testable n (as predicted) |
| 3. Family moves | a chunk-split step moves a whole family `(g⁻, g, g⁺)`, keeping invariant F | F checked in `Core.check()`; zero element moves across chunks in every run |

### The lemma checker (`lemmas.py`)

The campaign above measured *outcomes* (no fallbacks, flat cost). The lemma checker
measures the *intermediate quantities* that the proof sketch bounds. For every core of
every run, it compares each instrumented maximum with the bound claimed in `docs/PROOF.md`
§4, evaluated for that core's own parameters:
* group-split length and sibling balance (G1);
* group sizes (G2);
* lifetime insertions and arrivals per group (G3);
* nested halvings per label gap (G4, C3);
* chunk-split length and fresh sibling size (C1);
* freshly quiet chunk size (C2);
* invariant F;
* chunk overshoot above `θ` against the zeroing-game bound, with both the provable and the
  measured job length (R);
* insertions per reservation round (R);
* weights at drain start, blocked target weights and drain funding (T3);
* fanout, table size, tables per entry and job length (T4);
* label bits per table (T5);
* fill of `cur` and of `nxt` at installation (W).

A claim is *judged* only when its hypotheses hold for the preset. For example, Lemma T3
assumes `q = 1/2 + 2/a + 2/(s−2) < 1`, which holds for the proof preset (`s = 11`) but not
for the default `s = 8`.

Two presets: `default` (`Params.for_capacity`) and `proof` (`Params.proof`: `c_T = 3`,
`K_R = 4`, `s = 11`, `β = 48`).

| Run | Result |
|---|---|
| 23 workloads × 2 presets, 10⁶ ops (`results/lemmas_1e6.txt`) | **0 violations**; max 137 steps/op (proof preset), 117 (default) |
| 23 workloads × 2 presets × 4 seeds, 3·10⁵ ops (`results/lemmas_3e5_seeds.txt`) | **0 violations** in 184 runs |
| top level alone, 5 adversaries × `s ∈ {8, 11}`, 3·10⁴ and 3·10⁵ chunks (`results/top_lemmas.txt`) | 0 fallbacks; with `s = 11` every T3/T4/T5 claim holds; tables per entry ≤ 2, ≤ 19 of 40 label bits used |

Worst ratios measured/bound at 10⁶ ops, proof preset (1 = the bound is attained):

| Claim | Worst ratio | Note |
|---|---|---|
| G1 split length − k_G | ≤ 0 (−2) | |
| G2 group size ≤ G + 1 | 0.98 | groups reach `G` exactly |
| G3 lifetime arrivals | 0.82 | |
| G4 nested halvings of an element gap | 0.61 | 28 halvings, bound 46; budget of the *new* `B_e`: 74 |
| C2 freshly quiet chunk ≤ θ | 0.58 | the PQ slow path is never taken |
| R overshoot above θ (provable J) | 0.14 | 24 elements, bound 171 |
| R insertions per round ≤ ⌈J/K_R⌉ + 1 | **1.00** | attained: this found the off-by-one in the first draft of Lemma R |
| T3 drain start weight ≤ W_h + 2 | **1.00** | attained at height 1 |
| T3 blocked target weight / W_h | 0.94 | with `s = 8` (hypothesis false): **1.06**, i.e. targets do exceed the threshold, as the theory predicts |
| T3 funding jobs per drain | **1.00** | attained |
| T4 tables per entry ≤ 2 | **1.00** | attained |
| T4 job length ≤ (s+3)H | 0.63 | |
| T5 table label bits | 0.45 | 18 of 48 bits |
| W1, W2 core fill | ≤ 0 | `nxt` reaches `N'/4 − 3` at installation |

The attained bounds (ratio exactly 1) are a good sign: they show that the lemmas are tight
where the proof says they are, rather than loose bounds that the tests never approach.

### New corner-case adversaries (`stress.py`)

| Workload | Corner case | Aimed at |
|---|---|---|
| `rebuild_cycle` | §6.1's attack repeated, with target capacity growing 1k → 1M | Lemma W, fix 1 |
| `yoyo` | grow to k ∈ {1, 3, 10, …, 30000}, delete everything, repeat: the list is empty again and again | shrink/grow rebuilds back to back |
| `fifo` | queue: append at tail, delete at head; `live` constant, `count` grows | rebuilds copying mostly tombstones |
| `cursor_chase` | during a rebuild, insert right after the last copied element and delete the element under the cursor | Invariant R at its edge (mirroring boundary) |
| `shrink_only` | grow, then delete everything without inserting | `live < N/8` cascades down to the minimum capacity |
| `flicker` | insert and immediately delete: `live` ∈ {0, 1}, `count` grows | ~1000 rebuilds per 60k ops |
| `family_edge` | insert into the end groups of the next chunk to be split | fix 3 (family moves at both ends) |
| `t3` (`top_stress.py`) | find a draining node, insert at the far edge of its unswept LEFT part | Lemma T3's worst case |

All run with 0 fallbacks and 0 slow PQ scans, under both presets, with full invariant
checks. Executed lines per operation at 2·10⁵ ops (`results/lines_new_2e5.txt`): at most
2,934, within the campaign's previous maximum (3,034), and flat across decades.

With `s = 8`, the `t3` adversary pushes blocked targets to 1.125 × `W_h` and drain starts to
1.25 × `W_h` already at 3·10⁴ chunks. The other workloads stay at 1.06 there, and only
`random` also reaches 1.125, at 3·10⁵ chunks. With `s = 11` the worst over all 10 runs is
0.94 at both sizes, so Lemma T3 holds. Jobs stay within `(s+3)H` (71 ≤ 112 at 3·10⁵ chunks).

### Fuzzing and mutation testing after the fixes

* **Fuzzing.** `fuzz.py` now also draws `K_B ∈ {2, 3, 4, 6}` and a phase schedule: steady,
  "wipe" (grow, then delete everything) or alternating bursts.
  * 6,000 + 20,000 short trials: **0 failures**, with fallbacks in 79%.
  * 2,000 long trials (5k–30k ops, full check every 97 ops): **0 failures**.
* **Mutation testing** (`results/mutation.txt`).
  * The four new mutants for the fixes behave as expected. Reverting fix 1 (M21) is caught by
    the lemma checker's Lemma W. Reverting fix 3 fully (M22) or at one end (M23), or
    mislabeling a family moved right (M24), is caught by invariant F or label order.
    Reverting fix 2 (M25) survives, as expected for a proof-only margin.
  * M19 ("queue not told about chunk shrinkage") now survives. It is **equivalent** since fix 3:
    under invariant F, quiet chunks never shrink.

### Coverage (`linecov.py`)

`linecov.py` records which lines of the algorithm files the suites execute: unit tests,
fuzzing (short and long), every stress workload under three presets, and the top level
alone.
* All but 38 executable lines are covered.
* Every uncovered line is one of three kinds:
  * a guard that `docs/PROOF.md` says never fires: tag guards, adjacency guards, and the
    sweep's side and table-entry guards;
  * a path the proof says is unreachable: `StartDrain`'s give-up branches, the cross-chunk
    element move, the queue's decrement path, the chunk-boundary fix-ups in group removal
    (all unreachable under invariant F), and drain steps on a finished node;
  * dead code: the chunk free list, which has been removed.

So no reachable corner of the algorithm is left untested.


## 9. Exact bounds and the adversarial review (2026-10-14, PROOF.md v0.3)

PROOF.md v0.3 replaces the asymptotic bounds of the top structure and the lower levels with
exact integer constants. The checks are:
* `prototype/top_bounds.py` computes the per-height constants of Lemmas T3–T5;
* `prototype/lower_bounds.py` computes the constants and conditions I1–I10 for each `L`;
* `top_wbbt.py` records the per-height maximum of every bounded quantity, and `check()` now
  also verifies the new invariant (Q).

The lemma checker and `top_stress.py` compare the measured maxima with the exact bounds.
They judge a bound only when the lemma's hypotheses hold for the parameters.

### Exact bounds

| Run | Result |
|---|---|
| `lemmas.py 300000 --preset both --seeds 2` (23 workloads, 92 runs; `results/lemmas_exact_3e5.txt`) | **0 violations**, at most 117 steps per operation |
| top structure alone, 6 adversaries × `s ∈ {9, 11}`, 3·10⁴ chunks (`results/top_exact_3e4.txt`) | 0 fallbacks, **0 violations** of the exact bounds, for `s = 9` too |
| top structure alone, 6 adversaries × `s ∈ {9, 11}`, 3·10⁵ chunks (`results/top_exact_3e5.txt`) | 0 fallbacks, **0 violations** of the exact bounds (12 runs); job length ≤ 71 steps (s = 11), ≤ 26 children/table entries, ≤ 19 gap bits used; drain start weight W_h + 1 reached at heights 4 and 5 (bound W_h + 2) |

**Attained exactly** (proof preset, `a = 8`, `s = 11`, height 1):

| Bound | Value |
|---|---|
| drain start weight | `W_1 + 2 = 18` |
| funded jobs per drain | `K_1 = 3` |
| blocked target weight | `Θ_1 = 15` |
| weight of a target pair | `Π_1 = 24` |
| fresh target weight | `τ_1 = 9` and `λ_1 = 8` |
| live children and live table entries | `C_1 = E_1 = 18` |
| entries of a new table | `n₀_1 = 9` |
| halving depth | `D_1 = 7` (target-owned table) and `D^c_1 = 10` (chain table) |
| tables per entry | 2 |
| Lemma W bounds (`K_B` from 4 to 32, after the wrapper fix) | excess 0 |

The chunk bounds come close but are not attained: C1's insertion count is within 2–5 of its
bound. C3's group-label depth is far from tight: at most 16 halvings measured against a bound
of 64.

**Default preset (`s = 8`, I6 false).** The checker reports the bounds there without judging
them. At height 1 they are exceeded exactly as §4.5.3 predicts:
* blocked targets reach `Θ_1 = 17` for `s = 8`;
* fresh targets reach 10 > 9, drain starts 19–20 > 18, and children and table entries
  19–20 > 18.

This happens once a released target may exceed `W_1`. No fallback occurs.

### Adversarial review

Three independent reviewers, each covering one part of the proof, read PROOF.md v0.3 and
tried to break it against the code. Each wrote its own scripts, kept outside the repository.
The findings are in PROOF.md §6.7. Those that concern testing:

* **T5 and C3 gap depth.** The original Claim 1 failed on concrete runs: thousands of gaps
  violated it, and some were later halved. The exact gap bound that the instrumentation
  checks (`gap ≥ g₀ >> D`) was never violated. The corrected proofs bound that quantity.
* **Lemma W.** The old `wrapper.py` lost up to two steps per rebuild, and its own Lemma W
  checks overshot by 1 for `K_B ≥ 12`. After the fix, `wrapper.py` performs exactly the steps
  of §2.7, and the bounds hold with excess exactly 0 for `K_B` from 4 to 32.
  `rebuild_attack.py` still runs with 0 fallbacks, at 86–112 steps per operation.
* **`β = 3`.** FALLBACK produced equal tags (`Core.check`: "chunk tags unsorted"), which is why
  §3.4 now states the condition on `β`. All presets use `β ≥ 40`.
* **No correctness counterexample.** Differential fuzzing aimed at the rebuild cursor found
  no mismatch:
  * presets default with both top structures, proof, and tiny labels;
  * `K_B ∈ {2, 3, 4, 7}`;
  * inserts just before, at and after the cursor;
  * FALLBACK in the middle of a rebuild.

### Mutation testing after the fixes

After the wrapper fix, M07 ("reservation serves the emptiest chunk") survived the battery.
The rebuild timing had shifted, and the 20,000-operation `starve` run no longer pushed
chunks past `0.95·T`; it still does at 10⁵ operations. Rather than lengthen the run, the
core now counts reservations that pop a chunk smaller than the PQ's maximum
(`stats.pop_not_max`). The lemma checker requires this count to be 0, because it is exactly
the property Lemma R needs. M07 is now killed by that claim. The full suite is **ALL AS
EXPECTED** (`results/mutation.txt`).

### Reproducing (prototype/)

```
python3 top_bounds.py 8 11 48          # per-height constants of T3-T5 and the closed forms
python3 lower_bounds.py 8 200          # conditions I1-I10 for every L (all hold from L = 8)
python3 lemmas.py 300000 -j 8 --preset both --seeds 2
python3 -c "import top_stress as t; print(t.run('t3', 30000, check_every=1500, s=11)['exact_violations'])"
python3 mutate.py -j 6
```
