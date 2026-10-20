# Experiments: what lowers the worst case further (2026-10-20, not verified)

Three independent levers, each measured by splicing changes into the extracted program or the
runtime; the repository's program, proofs and runtime are unchanged. `run.sh` reproduces
`results/`. Per-operation times are minima over three in-process runs, performance cores only,
as in `rust/results/compare`.

## 1. Fewer top-job steps per operation: the profile K_R = 1

The slowest operations happen during a rebuild: an operation performs up to six core
insertions, and each runs `K_R = 8` top-job steps (91% of the slowest operation's steps at 10⁶
after the linear `startDrain`, `../linear-drain-start`). The pen-and-paper conditions of the
proof also hold for `K_R = 1` with `a = 5`, `s = 16`, `T = 12L²`, `θ = 2T/3`, `H = L/2 + 1`
(`prototype/lower_bounds.py` and `top_bounds.py`, every L from 8 to 40, with this H). The program
reads `K_R`, `a`, `s`, `θ` and `H` from its parameter array, so `Splice.lean` rewrites only the
parameter computation (and `T`, `θ`, `H` and the node capacity where the program computes them).

The variant answers like the specification on `check`'s grow, churn and mix runs (300,000
operations each), and no guard fails (a failed guard aborts the run: its handler subtracts below
0). Peak memory at 10⁷ elements is 8% higher (2.80 against 2.59 GB, with the runtime patch below).

## 2. A linear `startDrain`

As in `../linear-drain-start` (identical memory to the verified program at 1,204 checkpoints).

## 3. A runtime that never makes one operation pay for fresh memory (`runtime.patch`)

Once steps are few, the slowest operations are those that touch fresh memory: a page fault costs
about 2.3 µs, and single operations took up to 510 of them. `runtime.patch` (against `rust/src`):
* the block pool faults in its memory ahead of use, at most 4 pages per update, keeping 2,048
  pages in reserve (slabs of 8 MB, the next one mapped in advance), and maps slabs with `mmap`
  (glibc's `calloc` reused heap memory and zeroed all 2 MB in one operation, 0.8 ms);
* a freed block is zeroed incrementally (2 pages per update) instead of all at once when reused;
* the per-array lists (blocks in use, large values) are radix trees of pool blocks instead of
  vectors reserved at full capacity on first use (a rebuild start reserved up to 343 MB in about
  70 allocations, each a system call and a fault);
* the small-object allocator maps its chunks directly and faults the next one in ahead of use.

The patched runtime gives the same memory digest as the repository's on the same program, and
answers like the specification. A further change, block tables as radix trees of pool blocks
(no `mmap` per array), was slower at 10⁷ (`results/kr1_lin_rt_radix_*.csv`): the extra level is
one more dependent memory access per array access, and it shows in the cold operations below.

## Results: slowest operation per decade (four workloads; K_R = 1 alone: random and hammer)

| | steps at 10⁵ / 10⁶ / 10⁷ | slowest time at 10⁵ / 10⁶ / 10⁷ |
|---|---|---|
| verified program | 127–128k / 190–192k / 248–251k | 137–150 / 229–235 / 305–312 µs |
| linear `startDrain` | 49–57k / 68–88k / 82–85k | 81–102 / 123–138 / 159–168 µs |
| K_R = 1 | 46–47k / 68–69k / 69k | 65 / 109–112 / 121–126 µs |
| K_R = 1 + linear | 22–23k / 24–33k / 26–33k | 64–79 / 87–89 / 107–137 µs |
| K_R = 1 + linear + runtime | same | 39–54 / 64–69 / 79–171 µs |

Mean time per insertion changes little (random insertion at 10⁷: 4.58 µs verified, 4.55 with
K_R = 1 + linear, 4.32 with the runtime patch).

**Steps fall 7.5–9.5 times at 10⁷; time falls 2–4 times.** With the levers combined, the slowest
operation in time is no longer the one with the most steps (26–33k), and is at most 20 page
faults. What remains are cold operations right after a core swap: their few thousand steps go to
the new core's memory, written during the rebuild and no longer cached (about 27 ns per step
instead of 2). This is a floor of the memory system rather than of the algorithm; the lever for
it is fewer cache lines per step (the machine's arrays are separate, so one step touches one
line per field), not fewer steps.

## Proof work if adopted

* K_R = 1: the ten or so lemmas proved for the exact parameter formulas (`CostSetup`, among them
  the zeroing-game inequality), the machine code computing the parameters and its agreement
  proof; the algorithm proofs are generic in the parameters. The bound's K_R-proportional part
  (the job steps of each core insertion) shrinks about eightfold.
* Linear `startDrain`: see `../linear-drain-start`.
* Runtime: none (trusted), but it must keep realizing the model's constant-time memory.
