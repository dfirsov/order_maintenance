# Experiment: a linear `startDrain` (2026-10-20, not verified)

The slowest operations spend most of their steps in drain starts of the top structure, and 75% of
those in list searches (profile of the slowest operation at 10⁶ elements, random insertion,
190,189 steps: `find` 143k, `lookup` 6k, `assocSet` 7k, `startDrain` itself 22k). `startDrainS`
(`lean/OM/Impl/StartDrain.lean`) does, per entry of the ghost's table (up to 160), a search of
the children and of the side list, in four passes, and builds the side list with `assocSet`:
quadratic in the table size. The cost bound `sdBound = 8,977,738` is dominated by these terms
(`T·115T` for the side list, `2·T·40S` for the tables, with T = S = 160).

`LinSD.lean` replaces the side-list and table stages by linear ones (append; side read at the
entry's index; child test by the live-parent pointer) and splices the result into the extracted
machine program in place of every call of `startDrain` (20 call sites, 10 per core). Nothing in
the repository's program or proofs changes. `run.sh` reproduces everything below.

**Same behaviour.** `dig.rs` runs `check`'s random operation mixes (insertions, deletions, order
queries; 300,000 operations each) and prints a hash of the whole machine memory (`digest.rs`)
every 1,000 operations. Original and variant agree at all 1,204 checkpoints
(`results/digest_check.txt`):

| mode | max steps: original | max steps: linear | mean: original | mean: linear |
|---|---|---|---|---|
| grow | 127,818 | 50,797 | 860 | 839 |
| churn | 68,237 | 29,426 | 521 | 521 |
| mix | 127,121 | 47,187 | 517 | 505 |
| hot (always after the first) | 132,175 | 57,297 | 1,065 | 1,022 |

**Slowest operation** (`compare`, four workloads, three runs, performance cores;
`results/lin_*.csv` against `rust/results/compare/om_*.csv`):

| elements | max steps: original → linear | slowest: original → linear | mean |
|---|---|---|---|
| 10⁵ | 127–128k → 49–57k | 137–150 → 81–102 µs | unchanged |
| 10⁶ | 190–192k → 68–88k | 229–235 → 123–138 µs | unchanged |
| 10⁷ | 248–251k → 82–85k | 305–312 → 159–168 µs | unchanged |

Three times fewer steps at 10⁷; growth per decade drops from about 60k to about 17k steps on random
insertion and is flat from 10⁶ to 10⁷ on clustered ones. Time improves 1.9 times (what remains does
more memory traffic per step). Mean time is unchanged: drain starts are rare.

**What dominates now.** In the slowest operation at 10⁶ (67,930 steps), 61% are still searches,
now mostly in drain steps (`drainStep`: per chunk moved, a lookup in the ghost's side list and
four label lookups in tables, about 1,500 steps each, 22 drain steps).

**Proof work if adopted.** New core-language code for the side-list and table stages, their
`_ok` proofs and cost terms, and three facts from the invariants: table entries are distinct, the
side list is in table order, and a live child's live-parent pointer is its parent. Level F and
the top-structure proofs are unchanged. The quadratic terms of `sdBound` become linear except the
per-ghost and per-child side lookups.
