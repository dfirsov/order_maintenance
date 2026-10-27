# Tag-range relabeling (Bender et al. 2002, Sec. 3). Measures, for each relabeling of a range of
# size 2^i, the insertions into that range since it was last made uniform (by a relabeling of it
# or of an enclosing range), and compares with the paper's (2 - T/2)(2/T)^i and with
# (T-1)/2 * (2/T)^i.
import sys, bisect, random
k = int(sys.argv[4]) if len(sys.argv) > 4 else 40; u = 1 << k; T = float(sys.argv[1]) if len(sys.argv) > 1 else 1.5
mode = sys.argv[2] if len(sys.argv) > 2 else "front"
tags = []                      # sorted occupied tags
since = [dict() for _ in range(k + 1)]  # (i, j) -> insertions into range since it was last made uniform
def thr(i): return T ** (-i)
def count(lo, hi): return bisect.bisect_left(tags, hi) - bisect.bisect_left(tags, lo)
worst = {}
def insert_at(pos):            # insert a new element at list position pos (0 = front)
    lo_t = tags[pos - 1] if pos > 0 else -1
    hi_t = tags[pos] if pos < len(tags) else u
    ref = lo_t if lo_t >= 0 else 0
    for i in range(k + 1):     # record the insertion in every enclosing range
        since[i][ref >> i] = since[i].get(ref >> i, 0) + 1
    if hi_t - lo_t > 1:
        tags.insert(pos, (lo_t + hi_t) // 2); return
    for i in range(1, k + 1):  # smallest enclosing range of ref that is not overflowing with the new element
        lo = (ref >> i) << i; hi = lo + (1 << i)
        c = count(lo, hi) + 1
        if c <= (1 << i) * thr(i):
            break
    else:
        raise SystemExit("root overflow")
    a = bisect.bisect_left(tags, lo); b = bisect.bisect_left(tags, hi)
    tags.insert(pos, None)     # placeholder; relabel evenly
    b += 1
    step = (1 << i) / c
    for t in range(c):
        tags[a + t] = lo + int(t * step)
    n_ins = since[i].get(ref >> i, 0)
    key = i
    worst[key] = min(worst.get(key, 1e18), n_ins)
    for ii in range(i + 1):    # the range and everything below it are uniform now
        a0, b0 = lo >> ii, hi >> ii
        if b0 - a0 <= len(since[ii]):
            for jj in range(a0, b0): since[ii].pop(jj, None)
        else:
            for jj in [x for x in since[ii] if a0 <= x < b0]: del since[ii][jj]
random.seed(1)
n = int(sys.argv[3]) if len(sys.argv) > 3 else 20000
for s in range(n):
    insert_at(0 if mode == "front" else random.randint(0, len(tags)))
print(f"T={T} mode={mode} n={len(tags)}")
print(" i   min ins between relabels   paper (2-T/2)(2/T)^i   (T-1)/2*(2/T)^i")
for i in sorted(worst):
    if i < 4: continue
    print(f"{i:2d}  {worst[i]:10d}  {(2 - T/2) * (2/T)**i:22.1f}  {(T-1)/2 * (2/T)**i:18.1f}")
