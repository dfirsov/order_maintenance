import OM.Proof.Cost.InsStep

/-!
# Parts of the background work

Closing Lemma C3's undriven counts; the inserted element stays in its chunk through the group
phase; the chunk count through the chunk drive.
-/

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-- Undriven insertions can always be forgotten in Lemma C3 (they only gave slack). -/
theorem LInv.close {s : Core} {lg : LGh} {s₀ δ δu : Nat → Nat} (hL : LInv s lg s₀ δ δu)
    (hδu : ∀ c, δu c ≤ δ c) : LInv s lg s₀ (fun _ => 0) (fun _ => 0) := by
  refine { hL with arrS := fun x hx hxs => ?_ }
  have h := hL.arrS x hx hxs
  have := hδu x
  simp only [Nat.add_zero, Nat.mul_zero]
  omega

theorem LX.close {s : Core} {s₀ δ δu : Nat → Nat} (h : LX s₀ δ δu s) (hδu : ∀ c, δu c ≤ δ c) :
    LX s₀ (fun _ => 0) (fun _ => 0) s := by
  obtain ⟨⟨lg, hL⟩, h2, h3⟩ := h; exact ⟨⟨lg, hL.close hδu⟩, h2, h3⟩

/-- **The inserted element stays in its chunk** through the group phase. -/
theorem xgroup_track {L : List Nat} {c' : Nat} (y c : Nat) (hy : y ∈ L) :
    XGroup (fun t => gC t (eG t y) = c) (fun t => gC t (eG t y) = c) L c' := by
  refine ⟨fun δ p => ⟨?_, ?_, ?_⟩, ?_⟩
  · intro t A gh hI hel hG hok hst hX
    subst hel
    have hp' := hI.mem_glist_iff.mpr hok.live
    have hl' : gLl t p ∈ A.glist := hI.mem_of_gN hok.adj hok.live.1
    have hlp : gLl t p ≠ p := by
      intro e; have := hok.adj; rw [e, hI.gList.next p hp'] at this
      exact succOf_ne_self hI.gList.nodup p hok.live.1 this
    obtain ⟨rest, hrun⟩ := hI.run_head hp' hok.ne
    have hm := mem_runOf.mp (hrun ▸ (by simp : gF t p ∈ gF t p :: rest))
    have M := moveLState_spec hlp hok.live.2.1 (hI.gAlloc _ hl') ((hI.eAlloc _).mp hm.1).2
    rw [M.eG, M.links.chk]
    split
    · next he => rw [hok.chk, ← hX, he, hm.2]
    · exact hX
  · intro t A gh hI hel hG hok hst hX
    subst hel
    have hp' := hI.mem_glist_iff.mpr hok.live
    have hr' : gRr t p ∈ A.glist := hI.mem_of_gP hok.adj hok.live.1
    have hrp : gRr t p ≠ p := by
      intro e; have := hok.adj; rw [e, hI.gList.prev p hp'] at this
      exact predOf_ne_self hI.gList.nodup p hok.live.1 this
    obtain ⟨front, hrun⟩ := hI.run_last hp' hok.ne
    have hm := mem_runOf.mp (hrun ▸ (by simp : gLs t p ∈ front ++ [gLs t p]))
    have M := moveRState_spec hrp hok.live.2.1 (hI.gAlloc _ hr') ((hI.eAlloc _).mp hm.1).2
    rw [M.eG, M.links.chk]
    split
    · next he => rw [hok.chk, ← hX, he, hm.2]
    · exact hX
  · intro t A gh hI hel hG hp hs he hl hr hl' hr' hc hX
    subst hel
    have Fp := hG.fam p hp hs
    have hpp : gP t p ≠ p := by
      rw [hI.gList.prev p (hI.mem_glist_iff.mpr hp)]; exact predOf_ne_self hI.gList.nodup p hp.1
    have hgPl : gP t p = gLl t p := by
      have := hI.gP_gN (hI.mem_glist_iff.mpr Fp.lLive) (by rw [Fp.lAdj]; exact hp.1)
      rw [Fp.lAdj] at this; exact this
    have R := removeState_spec hp.2.1 Fp.lLive.2.1 Fp.rLive.2.1 hpp
      (fun _ => by rw [hgPl]; exact Fp.lLive.2.1)
    have : eG (removeState t p) y = eG t y := by simp only [eG, R.E]
    rw [this, R.chk]; exact hX
  · intro s A gh g labL labR hI hel hG hg hq hsz hL hR hX
    subst hel
    have S := splitSpec hI (hI.mem_glist_iff.mpr hg) labL labR
    have hyl : LiveG s (eG s y) := hI.mem_glist_iff.mp (hI.eG_mem hy)
    have : eG (splitState s g labL labR) y = eG s y := by simp only [eG, S.E]
    rw [this, S.chk, if_neg]
    · exact hX
    · rintro (h | h)
      · exact S.glOut (h ▸ hyl)
      · exact S.grOut (h ▸ hyl)

end OM.Proof

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

theorem cmoveL_qsame {s : Core} {x : Nat} {u labs : List Nat} (hxy : x ≠ cLl s x)
    (hx : x < s.C.size) (hy : cLl s x < s.C.size) (hxs : cSt s x = .splitting)
    (hys : cSt s (cLl s x) = .overflow) : QSame s (cmoveLState s x u labs) := by
  have hCs : (moveGroupsLeft s x (cLl s x) u labs).C.size = s.C.size := by simp [moveGroupsLeft]
  have hC := fun c => cmoveSizes_C (t := moveGroupsLeft s x (cLl s x) u labs) (u := u) hxy
    (by rw [hCs]; exact hx) (by rw [hCs]; exact hy) c
  have hCm := fun c => moveGroupsLeft_C (s := s) (u := u) (labs := labs) hxy hx hy c
  have fld : ∀ c, cSt (cmoveLState s x u labs) c = cSt s c ∧
      (c ≠ x → c ≠ cLl s x → cSz (cmoveLState s x u labs) c = cSz s c) := by
    intro c
    simp only [cSt, cSz, cmoveLState]
    rw [hC c, hCm c]
    by_cases h1 : c = x
    · subst h1; simp only [if_true, if_neg hxy]; split <;> simp
    · by_cases h2 : c = cLl s x
      · subst h2; simp [h1]
      · simp [h1, h2]
  refine ⟨by simp [cmoveLState, cmoveSizes, hCs], rfl, fun c _ => by rw [(fld c).1],
    fun c _ hq => (fld c).2 ?_ ?_⟩
  · rintro rfl; rw [hxs] at hq; cases hq
  · rintro rfl; rw [hys] at hq; cases hq

theorem cmoveR_qsame {s : Core} {x : Nat} {u labs : List Nat} (hxz : x ≠ cRr s x)
    (hx : x < s.C.size) (hz : cRr s x < s.C.size) (hxs : cSt s x = .splitting)
    (hzs : cSt s (cRr s x) = .overflow) : QSame s (cmoveRState s x u labs) := by
  have hCs : (moveGroupsRight s x (cRr s x) u labs).C.size = s.C.size := by simp [moveGroupsRight]
  have hC := fun c => cmoveSizes_C (t := moveGroupsRight s x (cRr s x) u labs) (u := u) hxz
    (by rw [hCs]; exact hx) (by rw [hCs]; exact hz) c
  have hCm := fun c => moveGroupsRight_C (s := s) (u := u) (labs := labs) hxz hx hz c
  have fld : ∀ c, cSt (cmoveRState s x u labs) c = cSt s c ∧
      (c ≠ x → c ≠ cRr s x → cSz (cmoveRState s x u labs) c = cSz s c) := by
    intro c
    simp only [cSt, cSz, cmoveRState]
    rw [hC c, hCm c]
    by_cases h1 : c = x
    · subst h1; simp only [if_true, if_neg hxz]; split <;> simp
    · by_cases h2 : c = cRr s x
      · subst h2; simp [h1]
      · simp [h1, h2]
  refine ⟨by simp [cmoveRState, cmoveSizes, hCs], rfl, fun c _ => by rw [(fld c).1],
    fun c _ hq => (fld c).2 ?_ ?_⟩
  · rintro rfl; rw [hxs] at hq; cases hq
  · rintro rfl; rw [hzs] at hq; cases hq

/-- **The chunk count through the chunk drive.** -/
theorem cxsteps_count {X Y : Core → Prop} {L : List Nat} {δ δu s₀ : Nat → Nat} {x : Nat}
    (h : CXSteps X Y L δ δu s₀ x) :
    CXSteps (fun t => X t ∧ ∃ e pops, CountInv t e pops)
      (fun t => Y t ∧ ∃ e pops, CountInv t e pops) L δ δu s₀ x := by
  refine h.and ?_ ?_ ?_
  · intro t A gh labs hI hel hG hC hxL hst hX
    subst hel
    obtain ⟨e, pops, hN⟩ := hX
    have Fx := hC.cfam x hxL hst
    exact ⟨e, pops, hN.frame (cmoveL_qsame (Ne.symm (Fx.lx hI hxL)) hxL.2 Fx.lLive.2 hst Fx.lSt) rfl⟩
  · intro t A gh labs hI hel hG hC hxL hst hX
    subst hel
    obtain ⟨e, pops, hN⟩ := hX
    have Fx := hC.cfam x hxL hst
    exact ⟨e, pops, hN.frame (cmoveR_qsame (Ne.symm (Fx.rx hI hxL)) hxL.2 Fx.rLive.2 hst Fx.rSt) rfl⟩
  · intro t A gh hI hel hG hC hxL hst hl hr hX
    subst hel
    obtain ⟨e, pops, hN⟩ := hX
    have Fx := hC.cfam x hxL hst
    exact ⟨_, pops, hN.remove hxL.2 Fx.lLive.2 Fx.rLive.2 (Fx.lx hI hxL) (Fx.rx hI hxL) hst Fx.lSt
      Fx.rSt hl hr⟩

end OM.Proof
