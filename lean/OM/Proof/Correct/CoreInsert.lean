import OM.Proof.Correct.Fallback

/-!
# The core's insertion (`Core.insertAfter`)

`insertAfter x h` inserts a new element after `x`. If the label guard fails, FALLBACK rebuilds
and the retried insertion succeeds (`RoomP`); if the background work fails a guard, FALLBACK
rebuilds. Either way the result satisfies INV-S, and the element list is `x`'s list with the
new element `y = |E|` right after `x`.
-/

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-- The parameter conditions for the core (`docs/PROOF.md` §3.4). -/
def CoreP (P : Params) : Prop := FbOK P ∧ RoomP P

theorem run_onGuard {α : Type} (act handler : CM α) (s : Core) :
    (onGuard act handler).run s =
      match act.run s with
      | .ok a s' => .ok a s'
      | .error (.guard _) s' => handler.run s'
      | .error e s' => .error e s' := by
  show EStateM.tryCatch act _ s = _
  simp only [EStateM.tryCatch, EStateM.run]
  rcases act s with ⟨a, s'⟩ | ⟨e, s'⟩
  · rfl
  · rcases e <;> rfl

/-- With room after `x`, the insertion succeeds. -/
theorem insertElem_ok {s : Core} {A : Abs} (hR : Room s A) {x : Nat} (hx : x ∈ A.elist) (hh : Nat) :
    ∃ lab, eL s x < lab ∧ (x ≠ gLs s (eG s x) → lab < eL s (eN s x)) ∧
        (insertElem x hh).run s = .ok s.E.size (linkElem s x s.E.size lab hh) := by
  obtain ⟨hD, hr⟩ := hR
  obtain ⟨hlast, hmid⟩ := hr x hx
  rcases insertElem_run s x hh with h | ⟨msg, h⟩
  · exact h
  · exfalso
    revert h
    unfold insertElem
    simp only [run_getP_bind, run_getE_bind, run_getG_bind]
    by_cases hl : x = (s.Gs.getX (s.E.getX x).grp).last
    · rw [if_pos (beq_iff_eq.mpr hl), run_bind, run_after]
      have := hlast hl
      simp only [eL] at this
      rw [if_neg (by omega)]
      simp only [run_get_bind, run_modify_bind, run_pure]
      exact fun h => by cases h
    · rw [if_neg (fun h => hl (beq_iff_eq.mp h))]
      simp only [run_getE_bind]
      rw [run_bind, run_between]
      have := hmid hl
      simp only [eL, eN] at this
      rw [if_neg (by omega)]
      simp only [run_get_bind, run_modify_bind, run_pure]
      exact fun h => by cases h

/-- The element records after an insertion of `y` with handle `hh`. -/
structure InsFrame (s s' : Core) (y hh : Nat) : Prop where
  hy : y = s.E.size
  size : s'.E.size = s.E.size + 1
  live : ∀ e, (s'.E.getX e).live = if e = y then true else (s.E.getX e).live
  h : ∀ e, (s'.E.getX e).h = if e = y then hh else (s.E.getX e).h
  P : s'.P = s.P

theorem InsFrame.linkElem (s : Core) (x lab hh : Nat) :
    InsFrame s (linkElem s x s.E.size lab hh) s.E.size hh :=
  ⟨rfl, linkElem_Esize s x lab hh, linkElem_live s x lab hh, linkElem_h s x lab hh, rfl⟩

theorem InsFrame.eframe {s t u : Core} {y hh : Nat} (h1 : InsFrame s t y hh) (h2 : EFrame t u) :
    InsFrame s u y hh :=
  ⟨h1.hy, h2.size.trans h1.size, fun e => (h2.live e).trans (h1.live e),
   fun e => (h2.h e).trans (h1.h e), h2.P.trans h1.P⟩

theorem EFrame.insFrame {s t u : Core} {y hh : Nat} (h1 : EFrame s t) (h2 : InsFrame t u y hh) :
    InsFrame s u y hh :=
  ⟨h2.hy.trans h1.size, h2.size.trans (by rw [h1.size]),
   fun e => by rw [h2.live, h1.live], fun e => by rw [h2.h, h1.h], h2.P.trans h1.P⟩

/-- The first phase: the insertion itself, with FALLBACK and a retry on a failed guard. -/
theorem insertPhase {s : Core} {A : Abs} (hI : INV s A) {x : Nat} (hx : x ∈ A.elist)
    (hP : CoreP s.P) (hh : Nat) :
    ∃ s' A', (onGuard (insertElem x hh) (do fallback; insertElem x hh)).run s = .ok s.E.size s' ∧
      INV s' A' ∧ A'.elist = OM.Spec.insertAfterL x s.E.size A.elist ∧ InsFrame s s' s.E.size hh := by
  rw [run_onGuard]
  rcases insertElem_run s x hh with ⟨lab, h1, h2, hr⟩ | ⟨msg, hr⟩
  · rw [hr]
    obtain ⟨I', e'⟩ := inv_linkElem hI hx h1 h2 (h := hh)
    exact ⟨_, _, rfl, I', e', InsFrame.linkElem s x lab hh⟩
  · rw [hr]
    simp only
    rw [run_bind]
    have hne : A.elist ≠ [] := List.ne_nil_of_mem hx
    obtain ⟨s2, hf, hE2, A2, I2, hel2, hR2⟩ := fallback_run_room (hI.elemOK hne) hP.1 hP.2
    rw [hf]
    simp only
    have hx2 : x ∈ A2.elist := hel2 ▸ hx
    obtain ⟨lab, h1, h2, hr2⟩ := insertElem_ok hR2 hx2 hh
    obtain ⟨I', e'⟩ := inv_linkElem I2 hx2 h1 h2 (h := hh)
    have hF := hE2.insFrame (InsFrame.linkElem s2 x lab hh)
    rw [hE2.size] at hr2 I' e' hF
    rw [hr2]
    exact ⟨_, _, rfl, I', by rw [e', hel2], hF⟩

/-- **The core's insertion.** From INV-S, `insertAfter x h` with `x` in the element list returns
`y = |E|`, and the result satisfies INV-S with element list `insertAfterL x y`. -/
theorem insertAfter_run {s : Core} {A : Abs} (hI : INV s A) {x : Nat} (hx : x ∈ A.elist)
    (hP : CoreP s.P) (hh : Nat) :
    ∃ s' A', (insertAfter x hh).run s = .ok s.E.size s' ∧
      INV s' A' ∧ A'.elist = OM.Spec.insertAfterL x s.E.size A.elist ∧ InsFrame s s' s.E.size hh := by
  unfold insertAfter
  rw [run_bind]
  obtain ⟨s1, A1, h1, I1, e1, f1⟩ := insertPhase hI hx hP hh
  rw [h1]
  simp only
  rw [run_bind, run_onGuard]
  have hP1 : CoreP s1.P := f1.P ▸ hP
  have hb := good_background s.E.size s1 A1 I1
  revert hb
  rcases (background s.E.size).run s1 with ⟨⟨⟩, s2⟩ | ⟨e, s2⟩
  · rintro ⟨hE2, A2, I2, e2⟩
    exact ⟨s2, A2, rfl, I2, e2.trans e1, f1.eframe hE2⟩
  · rcases e with msg | msg
    · intro hE2
      have hne : A1.elist ≠ [] := by
        rw [e1]; exact List.ne_nil_of_mem ((OM.Spec.mem_insertAfterL hx).mpr (Or.inl rfl))
      obtain ⟨s3, hf, hE3, A3, I3, hel3⟩ :=
        fallback_run ((I1.elemOK hne).of_eframe hE2) (hE2.P ▸ hP1.1)
      simp only
      rw [hf]
      exact ⟨s3, A3, rfl, I3, hel3.trans e1, f1.eframe (hE2.trans hE3)⟩
    · exact fun h => h.elim

end OM.Proof
