"""Exact constants of the top-structure lemmas T3-T5 (docs/PROOF.md §4.5.2-4.5.4).

    python3 top_bounds.py [a] [s] [beta] [H]

Computes, for every height h, the bounds that the pen-and-paper proof derives,
and checks the conditions the proof needs. lemmas.py and top_stress.py compare
the instrumented maxima of top_wbbt.py against these numbers.

Notation (all quantities are chunk counts, i.e. weights):
  W_h      drain threshold 2a^h
  K_h      max funded jobs of one drain                  (T3.2)
  Pi_h     max total weight of the two targets of a drain (T3.3)
  tau_h    max weight of a fresh target                   (partition bound)
  Theta_h  max weight of a target while blocked           (T3.3; need Theta_h <= W_h)
  lam_h    min weight of a fresh target                   (T4.1)
  gam_h    min gain of a target between creation and its own drain (T5)
  C_h      max live children of a live non-root node      (T4.1)
  Cg_h     max live children of the two targets of a ghost (T4.2)
  E_h      max entries of a live table; Eg_h of a ghost table (T4.2)
  n0_h     max entries of a table when it is created      (T5)
  Dt_h     max halving depth of a gap before it is halved, target-owned table (T5)
  Dc_h     same for the table of the initial chain node   (T5)
  bits_h   label bits needed at height h                  (T5)
"""
from __future__ import annotations

import sys


def bounds(a: int = 8, s: int = 11, H: int = 12) -> dict:
    """Per-height constants for h = 1..H-1 (the root never drains)."""
    assert a >= 2 and s >= 3
    W = {h: 2 * a ** h for h in range(0, H + 1)}
    K, Pi, tau, Th, lam, gam = {}, {}, {}, {}, {}, {}
    C, Cg, E, Eg, n0, Dt, Dc, bits = {}, {}, {}, {}, {}, {}, {}, {}
    for h in range(1, H):
        K[h] = (W[h] + 2) // (s - 2) + 1
        Pi[h] = W[h] + 2 + 2 * K[h]
        if h == 1:
            tau[h] = a + 1                       # unit weights: parts floor/ceil(S/2), S <= 2a+2
            lam[h] = a                           # S >= 2a+1
        else:
            tau[h] = a ** h + 1 + Pi[h - 1]      # floor(S/2) + largest unit, S <= W_h + 2
            lam[h] = a ** h + 1 - Pi[h - 1]      # ceil(S/2) - largest unit, S >= W_h + 1
        gam[h] = W[h] + 1 - tau[h]
        Th[h] = tau[h] + 2 * K[h]
        if h == 1:
            C[h] = W[1] + 2                      # chunks; +2 for the job in progress
            Cg[h] = Pi[1] + 2
            E[h], Eg[h] = C[h], Cg[h]            # entries are chunks: no ghosts
            n0[h] = tau[1]
            jobs_t = (W[1] + 2 - lam[1]) // 2 + K[1]
            jobs_c = (W[1] + 1) // 2 + K[1]
            Dt[h], Dc[h] = jobs_t - 1, jobs_c - 1
        else:
            if lam[h - 1] <= 0 or gam[h - 1] <= 0:
                raise ValueError(f"lambda_{h-1} or gamma_{h-1} <= 0: a too small for s")
            C[h] = 1 + (W[h] + 1) // lam[h - 1]
            Cg[h] = 1 + (Pi[h] + 1) // lam[h - 1]
            E[h], Eg[h] = C[h] + C[h] // 2, Cg[h] + Cg[h] // 2
            c0 = 1 + (tau[h] - 1) // lam[h - 1]
            n0[h] = c0 + c0 // 2
            G_t = W[h] + 2 - lam[h] + 2 * K[h]   # = Theta_h
            G_c = W[h] + 1 + 2 * K[h]
            Dt[h] = 1 + G_t // gam[h - 1]
            Dc[h] = 1 + G_c // gam[h - 1]
        # floor(2^beta / (n0+1)) >= 2^(Dt+1)  and  2^(beta-1) >= 2^(Dc+1)
        bt = Dt[h] + 1
        while (1 << bt) < (1 << (Dt[h] + 1)) * (n0[h] + 1):
            bt += 1
        bits[h] = max(bt, Dc[h] + 2)
    return dict(a=a, s=s, H=H, W=W, K=K, Pi=Pi, tau=tau, Theta=Th, lam=lam, gam=gam,
                C=C, Cg=Cg, E=E, Eg=Eg, n0=n0, Dt=Dt, Dc=Dc, bits=bits)


def conditions(b: dict) -> list[tuple[str, bool]]:
    hs = sorted(b["K"])
    return [
        ("T3: Theta_h <= W_h for all h", all(b["Theta"][h] <= b["W"][h] for h in hs)),
        ("T3: Pi_{h-1} < W_h (StartDrain never gives up)",
         all(b["Pi"][h - 1] <= b["W"][h] for h in hs if h >= 2)),
        ("T4: lam_h > 0, gam_h > 0", all(b["lam"][h] > 0 and b["gam"][h] > 0 for h in hs)),
    ]


def closed_form(a: int = 8, s: int = 11, h0: int = 4) -> dict:
    """Upper bounds valid for every height h >= h0 (h0 >= 3), from the closed forms of
    PROOF.md §4.5.5. Each is (alpha*W + c)/(mu*W - d) with W = W_{h-1}, non-increasing
    in W, so its value at h = h0 bounds all larger heights."""
    assert h0 >= 3
    r = s / (s - 2)
    q = 0.5 + r / a + 2 / (s - 2)                  # Theta_h <= q W_h + cq
    cq = 7 + 8 / (s - 2)
    mu = 0.5 - r / a                               # lam_h >= mu W_h - nu   (h >= 2)
    nu = 3 + 4 / (s - 2)
    W = 2 * a ** (h0 - 1)                          # W_{h-1} at h = h0
    den = mu * W - nu                              # lower bound on lam_{h-1}
    assert den > 1, "mu W - nu must be positive"
    Pi_h = r * a * W + 4 + 4 / (s - 2)
    tau_h = a * W / 2 + 1 + r * W + 4 + 4 / (s - 2)
    C = 1 + int((a * W + 1) // den)
    Cg = 1 + int((Pi_h + 1) // den)
    c0 = 1 + int((tau_h - 1) // den)
    n0 = c0 + c0 // 2
    Dt = 1 + int((q * a * W + cq) // (den - 1))
    Dc = 1 + int((r * a * W + 3 + 4 / (s - 2)) // (den - 1))
    bt = Dt + 1
    while (1 << bt) < (1 << (Dt + 1)) * (n0 + 1):
        bt += 1
    return dict(q=q, cq=cq, mu=mu, nu=nu, Theta_ok=(1 - q) * a * W >= cq and q < 1,
                C=C, E=C + C // 2, Cg=Cg, Eg=Cg + Cg // 2, n0=n0, Dt=Dt, Dc=Dc, bits=max(bt, Dc + 2))


def summary(a: int = 8, s: int = 11, H: int = 12) -> dict:
    b = bounds(a, s, H)
    hs = sorted(b["K"])
    return dict(b, max_children=max(b["C"][h] for h in hs),
                max_table=max(max(b["E"][h], b["Eg"][h]) for h in hs),
                beta_min=max(b["bits"][h] for h in hs), ok=all(ok for _, ok in conditions(b)))


def check_top(top) -> list[tuple[str, int, int, int]]:
    """Compare the per-height maxima recorded by a WBBTTop with these bounds.

    Returns [(claim, h, measured, bound)]; a claim holds iff measured <= bound.
    The bounds assume the hypotheses of T3 (conditions() all ok)."""
    b = top.bounds
    if b is None:
        return []
    W, H = b["W"], top.H
    spec = {
        "start": ("T3.1 drain start weight <= W_h + 2", lambda h: W[h] + 2),
        "funded": ("T3.2 funded jobs per drain <= K_h", lambda h: b["K"][h]),
        "target": ("T3.3 blocked target weight <= Theta_h", lambda h: b["Theta"][h]),
        "pair": ("T3.3 weight of a target pair <= Pi_h", lambda h: b["Pi"][h]),
        "fresh_max": ("T3 fresh target weight <= tau_h", lambda h: b["tau"][h]),
        "fresh_min_neg": ("T4.1 fresh target weight >= lam_h", lambda h: -b["lam"][h]),
        "children": ("T4.1 live children <= C_h", lambda h: b["C"][h] if h < H else 1),
        "table_live": ("T4.2 live table entries <= E_h", lambda h: b["E"][h]),
        "table_ghost": ("T4.2 ghost table entries <= Eg_h", lambda h: b["Eg"][h]),
        "n0": ("T5 entries of a new table <= n0_h", lambda h: b["n0"][h]),
        "depth_drain": ("T5 halving depth, target-owned table <= Dt_h", lambda h: b["Dt"][h]),
        "depth_chain": ("T5 halving depth, chain table <= Dc_h", lambda h: b["Dc"][h]),
    }
    out = []
    for (name, h), val in sorted(top.hmax.items()):
        if name in spec:
            claim, f = spec[name]
            out.append((claim, h, val, f(h)))
    out.append(("T5 label gaps below g0 >> D (count)", 0, top.depth_viol, 0))
    out.append(("T4.3 tables per entry <= 2", 0, top.max_in_tables, 2))
    out.append(("T4.4 job length <= (s+3)H", 0, top.max_job, (top.s + 3) * H))
    return out


def main() -> None:
    args = [int(x) for x in sys.argv[1:]]
    a, s = (args + [8, 11])[:2]
    beta = args[2] if len(args) > 2 else None
    H = args[3] if len(args) > 3 else 6
    b = summary(a, s, H)
    cols = ["W", "K", "Pi", "tau", "Theta", "lam", "gam", "C", "Cg", "E", "Eg", "n0", "Dt", "Dc", "bits"]
    print(f"a = {a}, s = {s}")
    print("  h " + "".join(f"{c:>9s}" for c in cols) + "   Theta/W")
    for h in sorted(b["K"]):
        print(f"{h:3d} " + "".join(f"{b[c][h]:9d}" for c in cols) + f"   {b['Theta'][h] / b['W'][h]:.3f}")
    for name, ok in conditions(b):
        print(f"  {'ok  ' if ok else 'FAIL'} {name}")
    cf = closed_form(a, s, 4)
    print(f"  closed form for all h >= 4: q = {cf['q']:.4f}, Theta ok = {cf['Theta_ok']}, "
          f"C <= {cf['C']}, E <= {cf['E']}, Eg <= {cf['Eg']}, n0 <= {cf['n0']}, "
          f"Dt <= {cf['Dt']}, Dc <= {cf['Dc']}, bits <= {cf['bits']}")
    print(f"  max live children {b['max_children']}, max table {b['max_table']}, "
          f"label bits needed {b['beta_min']}" + ("" if beta is None else
          f" ({'ok' if b['beta_min'] <= beta else 'FAIL'} for beta = {beta})"))


if __name__ == "__main__":
    main()
