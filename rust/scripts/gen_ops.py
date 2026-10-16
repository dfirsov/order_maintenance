"""Random valid operation files for the cross-check (lake exe xrun / xrun): python3 gen_ops.py N SEED [mix|churn]."""
import random, sys
n, seed = int(sys.argv[1]), int(sys.argv[2])
mode = sys.argv[3] if len(sys.argv) > 3 else 'mix'
rng = random.Random(seed)
lst, fresh, out = [], 0, []
for _ in range(n):
    r = rng.random()
    if not lst or r < 0.1:
        out.append("f"); lst.insert(0, fresh); fresh += 1
    elif r < (0.6 if mode == 'mix' else 0.45 if (_ // 300) % 2 == 0 else 0.15):
        i = rng.randrange(len(lst)); out.append(f"a {lst[i]}"); lst.insert(i + 1, fresh); fresh += 1
    elif r < (0.8 if mode == 'mix' else 0.9):
        i = rng.randrange(len(lst)); out.append(f"d {lst[i]}"); lst.pop(i)
    else:
        out.append(f"o {rng.choice(lst)} {rng.choice(lst)}")
print("\n".join(out))
