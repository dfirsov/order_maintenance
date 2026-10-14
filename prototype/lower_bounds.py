"""Exact constants of the lower-level lemmas and the assembly (docs/PROOF.md §4.2-4.4, §4.7).

    python3 lower_bounds.py [L0] [Lmax]

For the proof parameters (Params.proof) at each word-size parameter L, computes
the constants that the proofs of Lemmas G1-G4, C1-C3, R, W and the chunk count
derive, evaluates the inequalities I1-I9 of §4.7, and reports the smallest L0
from which all of them hold up to Lmax. The top-structure conditions come from
top_bounds.py.

All quantities are exact integers (no O(1) terms), so that the proof's
"for L large enough" becomes a concrete threshold.
"""
from __future__ import annotations

import math
import sys
from fractions import Fraction

import top_bounds


def harmonic(k: int) -> Fraction:
    return sum((Fraction(1, i) for i in range(1, k + 1)), Fraction(0))


def harmonic_upper(k: int) -> float:
    """H_k <= ln k + 1 (exact sum for small k)."""
    return float(harmonic(k)) if k <= 2000 else math.log(k) + 0.5773 + 1 / (2 * k)


def lower(L: int, *, c_G: int = 2, c_T: int = 3, c1: int = 0, K_G: int = 4, K_C: int = 4,
          K_R: int = 4, a: int = 8, s: int = 11, beta: int = 48, K_B: int = 4,
          B_e: int | None = None, B_g: int | None = None, N: int | None = None) -> dict:
    """Constants for a core whose capacity N satisfies L = ceil(log2 N), N <= 2^L
    (N defaults to 2^L, the worst case)."""
    N = (1 << L) if N is None else N
    G = c_G * L
    T = c_T * L * L + c1 * L
    theta = (2 * T) // 3
    # ---- groups (G1-G4)
    k_G = -(-G // (K_G - 1)) + 1                     # insertions until the split ends (G1)
    gmin = -(-(G - 3) // 2)                          # freshly quiet group, lower bound (G1)
    gmax = (G + k_G + 3) // 2                        # freshly quiet group, upper bound (G1)
    U_G = max(2 * k_G + (G - gmin), G - 1 + k_G)     # lifetime insertions (G3)
    A_G = max(gmax + (G - gmin) + k_G, G + k_G)      # lifetime arrivals (G3)
    if B_e is None:
        B_e = 2 * G + math.ceil(math.log2(8 * G + 8)) + 8
    D_e = (1 << (B_e - 1)) // (8 * G + 8)
    # ---- chunks (C1-C3)
    units = lambda size: size // gmin + 1             # units in a chunk of this size (C1)
    k_C = -(-units(T) // (K_C - 1)) + 1              # insertions until a chunk split ends (C1)
    u_max = G + k_G                                  # largest unit (a family)
    cmax = (T + k_C + u_max + 2) // 2                # freshly quiet chunk, upper bound (C1)
    I_C = T + 2 * k_C                                # lifetime insertions of a chunk (C3)
    gp = max(1, (3 * T) // G)                        # groups_per_chunk of Params
    if B_g is None:
        B_g = 2 * gp + math.ceil(math.log2(8 * gp + 8)) + 8
    D_g = (1 << (B_g - 1)) // (8 * gp + 8)
    depth_g = 1 + I_C // gmin                        # halvings of a group gap before a halving (C3)
    moved = 3 * (units(T) + k_C)                     # groups pushed by moves at one end (C3)
    pushes_g = 2 * moved + 1 + I_C // gmin           # pushes at one end of a chunk (C3)
    # ---- reservation (R) and the number of chunks
    growth = theta + 1 - cmax                        # least growth of a quiet chunk before its pop
    m_max = 3 + 2 * (N // growth) if growth > 0 else None
    H = max(2, math.ceil(math.log(m_max, a) - 1e-12) + 1) if m_max else None
    while H is not None and a ** (H - 1) < m_max:
        H += 1
    J = (s + 3) * H if H else None
    R = -(-J // K_R) + 1 if J else None
    T_hard = theta + R * (harmonic_upper(m_max - 1) + 1) if R else None
    # ---- wrapper (W)
    H_new = L + 2                                    # bound on the next core's preparation steps
    cur_max = N // 2 + (N // 2 + H_new) // (K_B - 1) + 1
    tb = top_bounds.summary(a, s, H) if H else None
    cond = {
        "I1 groups: K_G >= 2, fresh sibling < G, >= 1": K_G >= 2 and gmax < G and gmin >= 1,
        "I2 element labels: D_e >= 2^U_G, A_G <= 8G+7": D_e >= (1 << U_G) and A_G <= 8 * G + 7,
        "I3 chunks: K_C >= 2": K_C >= 2,
        "I4 fresh chunk <= theta (C2)": cmax <= theta,
        "C3 group labels: D_g >= 2^(depth+1), pushes <= 8g'+7":
            D_g >= (1 << (depth_g + 1)) and pushes_g <= 8 * gp + 7,
        "I5 T_hard <= T (R)": T_hard is not None and T_hard <= T,
        "I6 top drain timing (T3)": tb is not None and tb["ok"],
        "I7 top label room (T5)": tb is not None and tb["beta_min"] <= beta,
        "I8 a^(H-1) >= m_max": m_max is not None and a ** (H - 1) >= m_max,
        "I9 wrapper: K_B >= 4, cur.count < N": K_B >= 4 and cur_max < N,
    }
    return dict(L=L, N=N, G=G, T=T, theta=theta, k_G=k_G, gmin=gmin, gmax=gmax, U_G=U_G, A_G=A_G,
                B_e=B_e, k_C=k_C, units_T=units(T), u_max=u_max, cmax=cmax, I_C=I_C, gp=gp,
                B_g=B_g, depth_g=depth_g, pushes_g=pushes_g, growth=growth, m_max=m_max, H=H,
                J=J, R=R, T_hard=T_hard, cond=cond, ok=all(cond.values()))


def main() -> None:
    args = [int(x) for x in sys.argv[1:]]
    L0 = args[0] if args else 4
    Lmax = args[1] if len(args) > 1 else 64
    cols = ["G", "T", "theta", "k_G", "U_G", "A_G", "k_C", "cmax", "depth_g", "pushes_g",
            "m_max", "H", "R", "T_hard"]
    print("  L " + "".join(f"{c:>9s}" for c in cols) + "  failing")
    first_ok = None
    for L in range(L0, Lmax + 1):
        d = lower(L)
        bad = [k.split()[0] for k, v in d["cond"].items() if not v]
        if not bad and first_ok is None:
            first_ok = L
        if bad:
            first_ok = None
        if L <= 24 or L % 8 == 0 or bad:
            vals = "".join(f"{(int(d[c]) if d[c] is not None else -1):9d}" for c in cols)
            print(f"{L:3d} {vals}  {' '.join(bad)}")
    print(f"all conditions hold for {first_ok} <= L <= {Lmax}" if first_ok else "conditions fail at Lmax")


if __name__ == "__main__":
    main()
