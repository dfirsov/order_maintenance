import OM.Proof.Cost.Pop

/-!
# The reservation, one iteration at a time

The lower invariants (`LowInv`: INV-S, Lemmas G and C1–C3, the queue, the chunk count) survive the
top structure's steps, which change only top-structure fields and chunk tags.
-/

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-- The invariants below the top structure, with no undriven insertion. -/
structure LowInv (s : Core) (L : List Nat) : Prop where
  inv : ∃ A, INV s A ∧ A.elist = L
  ginv : ∃ gh, GInv s L gh (fun _ => 0)
  cinv : ∃ s₀, CInv s L (fun _ => 0) (fun _ => 0) s₀ ∧ LX s₀ (fun _ => 0) (fun _ => 0) s
  pq : PQC s
  cnt : ∃ e pops, CountInv s e pops
  cp : CParams s.P

theorem TopRel.gsame {s s' : Core} (h : TopRel s s') : GSame s s' := by
  have hG : ∀ g, s'.Gs.getX g = s.Gs.getX g := fun g => by rw [h.Gs]
  have hE : ∀ e, s'.E.getX e = s.E.getX e := fun e => by rw [h.E]
  refine ⟨by rw [h.Gs], fun g => ?_, fun g => ?_, fun g => ?_, fun g => ?_, fun g => ?_,
    fun g => ?_, fun g => ?_, fun g => ?_, fun e => ?_, fun e => ?_, h.rest.2.2.1, h.rest.1⟩ <;>
    simp only [gSz, gSt, gSrc, gLl, gRr, gN, gC, gA, eG, eL, hG, hE]

theorem TopRel.csame {s s' : Core} (h : TopRel s s') : CSame s s' := by
  refine ⟨h.Csize, fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_,
    h.rest.1⟩ <;> simp only [cSz, cSt, cSrc, cLl, cRr, cN] <;> rw [h.C c]

theorem TopRel.qsame {s s' : Core} (h : TopRel s s') : QSame s s' := by
  refine ⟨h.Csize, h.rest.1, fun c _ => ?_, fun c _ _ => ?_⟩
  · simp only [cSt]; rw [h.C c]
  · simp only [cSz]; rw [h.C c]

theorem TopRel.pqsame {s s' : Core} (h : TopRel s s') : PQSame s s' := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, -⟩ := h.pq
  exact ⟨p4, p2, p3, p1, p5, p6, p8, p7, by rw [h.rest.1]⟩

/-- **The lower invariants across a top-structure step.** -/
theorem LowInv.top {s s' : Core} {L : List Nat} (h : LowInv s L) (hT : TopRel s s')
    (hI : ∃ A, INV s' A ∧ A.elist = L) : LowInv s' L := by
  obtain ⟨gh, hG⟩ := h.ginv
  obtain ⟨s₀, hC, ⟨lg, hL⟩, hLP, hP⟩ := h.cinv
  obtain ⟨e, pops, hN⟩ := h.cnt
  obtain ⟨A, hIA, hel⟩ := h.inv
  have hPe := hT.rest.1
  refine ⟨hI, ⟨gh, hG.of_gsame hT.gsame⟩, ⟨s₀, ?_, ⟨lg, hL.transfer hT.lsame⟩, by rw [hPe]; exact hLP,
    by rw [hPe]; exact hP⟩, h.pq.qsame hT.pqsame hT.qsame, ⟨e, pops, hN.frame hT.qsame hT.rest.2.1⟩,
    by rw [hPe]; exact h.cp⟩
  have hGS := hT.gsame
  refine hC.transfer hT.csame (fun c => ?_) (fun c => ?_) hC.δu (fun g hg => ?_)
  · unfold celts; congr 1; funext x; rw [hGS.chk, hGS.eG]
  · rw [units_of_Gs hT.Gs]
  · have hg' : LiveG s g := (liveG_of_Gs hT.Gs g).mp hg
    rw [hGS.chk]; exact hC.gchk g hg'

/-- With an empty queue, every game value is 0. -/
theorem gval_zero_of_empty {s : Core} (h : PQC s) (h0 : s.pqHi = 0) (c : Nat) : gval s c = 0 := by
  obtain ⟨bl, nb, hQ⟩ := h
  have := (hQ.empty_iff.mp h0) c
  unfold inQC at this; unfold gval
  simp only [decide_eq_false_iff_not, not_and, not_lt] at this
  split
  · next hc => have := this hc.1 hc.2; omega
  · rfl

end OM.Proof
