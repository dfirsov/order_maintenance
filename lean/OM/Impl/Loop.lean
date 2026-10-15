import OM.Impl.ArrayLemmas

/-!
# M6: reasoning about loops of the core language

`evalF_loop`: a loop runs to completion when each iteration succeeds and keeps an invariant,
with cost at most `1 + cost(bound) + N · (1 + body)`.
-/

namespace OM.Impl

open OM.Model
open OM.Machine (Reg)

theorem runForF_inv {κ : Caps} (b : Stm) (x : Reg) (N : Nat) (I : Nat → Core → Loc → Prop) (cb : Nat)
    (hb : ∀ k < N, ∀ s L, I k s L →
      ∃ s' L' c, evalF κ b s (OM.Machine.State.upd L x k) = .ok s' L' c ∧ c ≤ cb ∧ I (k + 1) s' L') :
    ∀ n k s L, k + n = N → I k s L →
      ∃ s' L' c, runForF (evalF κ b) x k n s L = .ok s' L' c ∧ c ≤ n * (1 + cb) ∧ I N s' L'
  | 0, k, s, L, hk, hI => ⟨s, L, 0, rfl, by simp, by rw [← hk]; simpa using hI⟩
  | n + 1, k, s, L, hk, hI => by
    obtain ⟨s1, L1, c1, he, hc, hI1⟩ := hb k (by omega) s L hI
    obtain ⟨s2, L2, c2, he2, hc2, hI2⟩ := runForF_inv b x N I cb hb n (k + 1) s1 L1 (by omega) hI1
    refine ⟨s2, L2, (1 + c1) + c2, ?_, ?_, hI2⟩
    · simp only [runForF, he, Res.addCost, Res.bind, he2]
    · rw [Nat.succ_mul]; nlinarith

theorem evalF_assign_ok {κ : Caps} {x : Reg} {e : Exp} {s : Core} {L : Loc} {v : Nat}
    (h : e.ev κ s L = some v) : evalF κ (.assign x e) s L = .ok s (OM.Machine.State.upd L x v) (1 + e.cost) := by
  simp [evalF, h]

/-- **The loop rule.** -/
theorem evalF_loop {κ : Caps} {x : Reg} {n : Exp} {b : Stm} {s : Core} {L : Loc} {N : Nat}
    (hn : n.ev κ s L = some N) (I : Nat → Core → Loc → Prop) (cb : Nat) (h0 : I 0 s L)
    (hb : ∀ k < N, ∀ s L, I k s L →
      ∃ s' L' c, evalF κ b s (OM.Machine.State.upd L x k) = .ok s' L' c ∧ c ≤ cb ∧ I (k + 1) s' L') :
    ∃ s' L' c, evalF κ (.loop x n b) s L = .ok s' L' c ∧ c ≤ 1 + n.cost + N * (1 + cb) ∧ I N s' L' := by
  obtain ⟨s', L', c, he, hc, hI⟩ := runForF_inv b x N I cb hb N 0 s L (by omega) h0
  refine ⟨s', L', 1 + n.cost + c, ?_, by omega, hI⟩
  simp only [evalF, hn, he, Res.addCost]

end OM.Impl
