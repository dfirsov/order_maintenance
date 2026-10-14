import OM.Proof.Cost.Budget

/-!
# The insertion step

The element link (`insertElem`) and the chunk-size update (`chunkSize`): every guard passes, and
the invariants hold with one undriven insertion in the group and in the chunk.
-/

namespace OM.Proof

open OM.Model OM.Zeroing

set_option linter.deprecated false

/-- **The element link succeeds**, keeping INV-S and Lemma G4's invariant. -/
theorem ins_elem_ok {s : Core} {A : Abs} {gh : GGh} (hI : INV s A)
    (hG : GInv s A.elist gh (fun _ => 0)) (hP : GParams s.P) {x : Nat} (hx : x ∈ A.elist)
    (hh : Nat) :
    ∃ lab, (insertElem x hh).run s = .ok s.E.size (linkElem s x s.E.size lab hh) ∧
      (∃ A', INV (linkElem s x s.E.size lab hh) A' ∧
        A'.elist = OM.Spec.insertAfterL x s.E.size A.elist) ∧
      ∃ gh', GInv (linkElem s x s.E.size lab hh) (OM.Spec.insertAfterL x s.E.size A.elist) gh'
        (fun b => if b = eG s x then 1 else 0) := by
  obtain ⟨lab, hrun, hG'⟩ := ginv_insertElem hI hG hP hx hh
  refine ⟨lab, hrun, ?_, hG'⟩
  rcases insertElem_run s x hh with ⟨lab', h1, h2, hr⟩ | ⟨msg, hr⟩
  · rw [hrun] at hr
    have he : linkElem s x s.E.size lab hh = linkElem s x s.E.size lab' hh := by
      injection hr
    rw [he]
    exact ⟨_, inv_linkElem hI hx h1 h2⟩
  · rw [hrun] at hr; cases hr

end OM.Proof

namespace OM.Proof

open OM.Model OM.Zeroing

set_option linter.deprecated false

/-- **The chunk-size update succeeds and keeps the queue invariant** (Lemma K2: no scan). -/
theorem chunkSize_ok {s : Core} {x lab hh : Nat} (hpq : PQC s) (hcL : LiveC s (gC s (eG s x))) :
    ∃ s2, (chunkSize (gC s (eG s x)) true).run (linkElem s x s.E.size lab hh) = .ok () s2 ∧
      PQOnly (sizeState (linkElem s x s.E.size lab hh) (gC s (eG s x))) s2 ∧ PQC s2 := by
  generalize hc : gC s (eG s x) = c at hcL ⊢
  generalize hs1 : linkElem s x s.E.size lab hh = s1
  have hC1 : s1.C = s.C := by rw [← hs1]; rfl
  have hP1 : s1.P = s.P := by rw [← hs1]; rfl
  have hst : ∀ d, cSt (sizeState s1 c) d = cSt s d := by
    intro d; simp only [cSt, sizeState, Array.getX_modify, hC1]; split <;> simp_all
  have hsz : ∀ d, cSz (sizeState s1 c) d = cSz s d + if d = c then 1 else 0 := by
    intro d; simp only [cSz, sizeState, Array.getX_modify, hC1]
    by_cases h : d = c
    · subst h; simp [hcL.2]
    · simp [h, Ne.symm h]
  have hLC : ∀ d, LiveC (sizeState s1 c) d ↔ LiveC s d := by
    intro d; simp only [LiveC, sizeState, Array.size_modify', hC1]
  have hPS : PQSame s (sizeState s1 c) := by
    rw [← hs1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hPs : (sizeState s1 c).P = s.P := by rw [← hP1]; rfl
  obtain ⟨bl, nb, hQ⟩ := hpq
  by_cases hq : cSt s c = .quiet
  · have hq1 : cSt s1 c = .quiet := by simp only [cSt, hC1]; exact hq
    rw [chunkSize_run_q hq1]
    have hsz1 : cSz s1 c = cSz s c := by simp only [cSz, hC1]
    rw [hsz1]
    have hss : sizeState s1 c = { s1 with C := s1.C.modify c fun C => { C with size := (s1.C.getX c).size + 1 } } := rfl
    have hQ' : QRep (sizeState s1 c) (cSz s) (inQC s) bl nb := hQ.congr hPS (fun _ => rfl) (fun _ _ => rfl)
    have hin : inQC s c = decide ((sizeState s1 c).P.theta < cSz s c) := by
      unfold inQC; rw [hPs]; simp [hcL, hq]
    obtain ⟨st', hrun, hO, hQI⟩ := pqAdjust_inc hQ' (by have := hcL.1; omega) hin
      (fun _ => rfl)
    refine ⟨st', hrun, hO, ?_⟩
    have hsz' : ∀ d, cSz st' d = cSz s d + if d = c then 1 else 0 := by
      intro d; rw [← hsz d]; simp only [cSz, hO.C]
    refine QInv.congr (k' := cSz st') (inQ' := inQC st') hQI (PQSame.refl _) (fun d => ?_)
      (fun d hd => ?_)
    · unfold inQC
      have hL' : LiveC st' d ↔ LiveC s d := by simp only [LiveC, hO.C]; exact hLC d
      have hst' : cSt st' d = cSt s d := by rw [← hst d]; simp only [cSt, hO.C]
      rw [hsz', hst', hO.P, hPs]
      by_cases hdc : d = c
      · subst hdc; rw [Function.update_self]; simp [hL', hcL, hq]
      · rw [Function.update_of_ne hdc]; simp [hL', hdc]
    · rw [hsz']
      by_cases hdc : d = c
      · subst hdc; rw [Function.update_self]; simp
      · rw [Function.update_of_ne hdc]; simp [hdc]
  · have hq1 : cSt s1 c ≠ .quiet := by simp only [cSt, hC1]; exact hq
    rw [chunkSize_run_nq hq1]
    refine ⟨_, rfl, PQOnly.refl _, ⟨bl, nb, hQ.congr hPS (fun d => ?_) (fun d hd => ?_)⟩⟩
    · unfold inQC
      rw [hst, hsz, hPs]
      by_cases hdc : d = c
      · subst hdc; simp [hq]
      · simp only [if_neg hdc, Nat.add_zero, hLC]
    · rw [hsz]
      have : d ≠ c := by
        rintro rfl; unfold inQC at hd; simp only [decide_eq_true_eq] at hd; exact hq hd.2.1
      simp [this]

end OM.Proof
