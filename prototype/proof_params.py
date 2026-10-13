"""Check the "provable margin" parameter choice (K_R=4, c_T=2) against the queue attacks."""
import concurrent.futures as cf
import sys

import stress
from core import Params


def one(args):
    wl, n, K_R, c_T = args
    r = stress.run(wl, n, params=lambda N: Params.for_capacity(N, top="wbbt", K_R=K_R, c_T=c_T))
    return wl, n, K_R, c_T, {k: r[k] for k in ("fallbacks", "max_steps/op", "max_chunk/T",
                                                "max_pq", "g_bits_used", "B_g_last", "max_fill")}


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000
    tasks = [(wl, n, K_R, c_T) for wl in ("harmonic", "starve", "hammer", "random")
             for K_R, c_T in ((2, 1), (4, 2))]
    with cf.ProcessPoolExecutor(8) as ex:
        for wl, n, K_R, c_T, r in ex.map(one, tasks):
            print(f"{wl:9s} n={n} K_R={K_R} c_T={c_T}: {r}", flush=True)
