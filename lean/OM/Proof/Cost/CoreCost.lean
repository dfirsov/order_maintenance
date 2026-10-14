import OM.Proof.Cost.Background

/-!
# The cost invariant of a core, and insertion without FALLBACK

`CostInv` collects the invariants of M4 between operations: INV-S, Lemmas G1–G4, C1–C3, the
queue, the chunk count, the top structure's invariant (through its contract) and the zeroing game
with its round accounting. From it, an insertion never takes FALLBACK: it runs exactly
`insertElem` and `background`, and `CostInv` holds again.
-/

namespace OM.Proof

open OM.Model OM.Zeroing

set_option linter.deprecated false

/-- **The cost invariant** of a core. -/
structure CostInv (TI : Core → Prop) (μ : Job → Nat) (J n R : Nat) (L : List Nat) (s : Core) :
    Prop where
  low : LowInv s L
  ti : TI s
  game : ∃ y i a ip js, GameInv n R s y i a ip ∧ RoundOK s.P.K_R J μ s ip js

theorem run_onGuard_ok {α : Type} {act handler : CM α} {s s' : Core} {a : α}
    (h : act.run s = .ok a s') : (onGuard act handler).run s = .ok a s' := by
  rw [run_onGuard, h]

/-- **Insertion without FALLBACK** (Lemma K1 for insertions). From the cost invariant, inserting
after a listed element runs exactly the element link and the background work, never FALLBACK, and
restores the cost invariant. -/
theorem insertAfter_cost {TI : Core → Prop} {μ : Job → Nat} {J cap n R : Nat} {L : List Nat}
    {s : Core} {x : Nat} (hTC : TopContract TI μ J cap) (hC : CostInv TI μ J n R L s)
    (hx : x ∈ L) (hk : 1 ≤ s.P.K_R) (hR : J / s.P.K_R + 1 ≤ R) (hn : 1 ≤ n)
    (hsize : 2 + 2 * ((s.count + 1) / (s.P.theta + 1 - cmax s.P)) ≤ n + 1)
    (hcap : 2 + 2 * ((s.count + 1) / (s.P.theta + 1 - cmax s.P)) ≤ cap)
    (hI5 : (s.P.theta : ℝ) + R * (Hn (n - 1) + 1) ≤ s.P.T) (hh : Nat) :
    ∃ s', (insertAfter x hh).run s = .ok s.E.size s' ∧
      (do let y ← insertElem x hh; background y; pure y).run s = .ok s.E.size s' ∧
      CostInv TI μ J n R (OM.Spec.insertAfterL x s.E.size L) s' ∧ s'.count = s.count + 1 ∧
      s'.P = s.P := by
  obtain ⟨y, i, a, ip, js, hG, hRO⟩ := hC.game
  have hdiv : s.count / (s.P.theta + 1 - cmax s.P) ≤ (s.count + 1) / (s.P.theta + 1 - cmax s.P) :=
    Nat.div_le_div_right (Nat.le_succ s.count)
  have hcnt0 : 2 + 2 * (s.count / (s.P.theta + 1 - cmax s.P)) ≤ n + 1 := by omega
  obtain ⟨s1, s2, hrun1, hrun2, hPost, heG, hgC, hE12, hP1⟩ := insert_step hTC hC.low hC.ti hG hRO hx
    hk hR hn hcnt0 hI5 hh
  have hyL : s.E.size ∈ OM.Spec.insertAfterL x s.E.size L :=
    (OM.Spec.mem_insertAfterL hx).mpr (Or.inl rfl)
  rw [heG, hgC] at hrun2
  obtain ⟨s', hbg, hL', hTI', hc', hP', hgame'⟩ := background_ok hTC hPost hyL heG hgC hrun2 hE12
    hP1 rfl hn (by rw [hPost.count]; exact hsize) (by rw [hPost.count]; exact hcap) hI5
  refine ⟨s', ?_, ?_, ⟨hL', hTI', by rw [hP']; exact hgame'⟩, hc'.trans hPost.count, hP'⟩
  · unfold insertAfter
    rw [run_bind, run_onGuard_ok hrun1]
    dsimp only
    rw [run_bind, run_onGuard_ok hbg]
    rfl
  · rw [run_bind, hrun1]
    dsimp only
    rw [run_bind, hbg]
    rfl

end OM.Proof
