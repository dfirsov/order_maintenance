import OM.Proof.Cost.Wrap

/-!
# The wrapper: what the machine code needs along Level F's run

The machine code of an operation calls core procedures; each call needs the core's cost
invariant and some facts about its arguments. Level F's cost proof establishes them along the
run, at intermediate states it does not expose. This file replays the proof of the rebuild loop
(`rebuildLoop_cost`) and records them (`RLSafeF`).
-/

namespace OM.Proof

open OM.Model OM.Zeroing

set_option linter.deprecated false

variable {mk : Nat → Params} {TI PI : Core → Prop} {μ : Core → Nat} {ν : Core → Nat}
  {PP : Params → Prop}
  {Jf capf nf Rf : Params → Nat}

/-- **What the iterations of the rebuild loop need**, along Level F's run: a preparation step needs
a core of positive capacity and keeps its count; a copy step reads an element of `cur`, and if the
element is live, `nxt` is in service with room, the anchor `tail` is in its list, and the handle is
below the counter. -/
def RLSafeF (mk : Nat → Params) (TI : Core → Prop) (μ : Core → Nat) (Jf nf Rf : Params → Nat)
    (om : OM) (n : Core) : Nat → Nat → Prop
  | 0, _ => True
  | f + 1, b => b ≠ 0 →
    (om.cursorSet = false → 1 ≤ n.P.N ∧ om.cur.head < om.cur.E.size ∧
      ∀ r n', prepareStep.run n = .ok r n' → n'.count = n.count ∧
        (r = true → RLSafeF mk TI μ Jf nf Rf
          { om with cursor := (om.cur.E.getX om.cur.head).next, cursorSet := true } n' f b) ∧
        (r = false → RLSafeF mk TI μ Jf nf Rf om n' f (b - 1))) ∧
    (om.cursorSet = true → om.cursor ≠ NIL → om.cursor < om.cur.E.size ∧
      ((om.cur.E.getX om.cursor).live = true → ∃ L, CoreOK mk TI μ Jf nf Rf n L ∧ n.count + 1 ≤ n.P.N ∧
        n.tail ∈ L ∧ (om.cur.E.getX om.cursor).h < om.nextHandle) ∧
      ∀ om' n', copyAtCursor om n = .ok (om', n') → om'.cursor ≠ NIL →
        RLSafeF mk TI μ Jf nf Rf om' n' f (b - 1))

theorem elist_lt {c : Core} {A : Abs} (hR : CoreR c A) {e : Nat} (he : e ∈ A.elist) : e < c.E.size :=
  ((hR.inv.eAlloc e).mp he).2

/-- **The rebuild loop is safe**: under `rebuildLoop_cost`'s hypotheses, its iterations get what
they need. -/
theorem rebuildLoop_safe (S : CostSetup mk TI PI μ ν PP Jf capf nf Rf) {Sp : OM.Spec.State}
    (hS : OM.Spec.Inv Sp) {Φe live₀ I D N' : Nat} :
    ∀ fuel budget (om : OM) (n : Core) (A : Abs), CoreR om.cur A →
      liveH om.cur A.elist = Sp.list → IdxOK om.cur A om.curIdx Sp.list → NxtR' om.cur A om n →
      om.nextHandle = Sp.fresh → om.live = Sp.list.length →
      LoopC mk TI PI μ ν Jf nf Rf om n A budget Φe live₀ I D N' →
      RLSafeF mk TI μ Jf nf Rf om n fuel budget := by
  intro fuel
  induction fuel with
  | zero => intro budget om n A _ _ _ _ _ _ _; trivial
  | succ fuel ih =>
    intro budget om n A hR hL hI hN hf hlv hC hb
    have hnd : (liveH om.cur A.elist).Nodup := hL ▸ hS.1
    refine ⟨fun hf' => ?_, fun hset hc => ?_⟩
    · obtain ⟨hprep, hφ⟩ := hC.prep hf'
      obtain ⟨ready, n', hr, hN1, hN2⟩ := prepare_ok hN hR hf'
      obtain ⟨b, n2, hr2, hcnt2, hP2, hI2, hT2, hF2⟩ := hprep.step S
      rw [hr] at hr2
      injection hr2 with hr2
      injection hr2 with h1 h2
      subst h1; subst h2
      refine ⟨by rw [hC.nP, S.PN]; have := hC.room; omega, elist_lt hR hR.head, fun r n3 hr3 => ?_⟩
      have hr3' : runCore n prepareStep = .ok (r, n3) := runCore_ok hr3
      rw [hr] at hr3'
      injection hr3' with hr3'
      injection hr3' with h1 h2
      subst h1; subst h2
      refine ⟨hcnt2, fun hrd => ?_, fun hrd => ?_⟩
      · subst hrd
        have hok := hT2 rfl
        set om1 : OM := { om with cursor := (om.cur.E.getX om.cur.head).next, cursorSet := true }
          with hom1
        have hcnt : om.cur.count = A.elist.length := by
          have := hC.curok.cnt; exact this
        have hpost1 : (postOf A.elist om1.cursor).length + 1 = A.elist.length := by
          show (postOf A.elist (eN om.cur om.cur.head)).length + 1 = _
          rw [hR.inv.eList.next _ hR.head, hR.inv.eList.head,
            postOf_succOf hR.inv.eList.nodup hR.inv.eList.nonil
              (by rw [← hR.inv.eList.head]; exact hR.head), postOf_headD hR.ne, List.length_tail]
          have := List.length_pos_of_ne_nil hR.ne; omega
        have hC1 : LoopC mk TI PI μ ν Jf nf Rf om1 n' A budget Φe live₀ I D N' := by
          refine ⟨hC.curok, by rw [hP2]; exact hC.nP, fun h => by simp [hom1] at h, fun _ =>
            ⟨fun B' hB' => ?_, ?_⟩, hC.room, hC.live, hC.bud⟩
          · rw [INV.elist_unique hB' hI2]
            refine ⟨hok, ?_⟩
            rw [hcnt2, hprep.cnt]; omega
          · show (postOf A.elist om1.cursor).length + (om.KB - budget) ≤ Φe
            omega
        exact ih budget om1 n' A hR hL hI (hN2 rfl) hf hlv hC1
      · subst hrd
        obtain ⟨hprep', hν⟩ := hF2 rfl
        have hC1 : LoopC mk TI PI μ ν Jf nf Rf om n' A (budget - 1) Φe live₀ I D N' := by
          refine ⟨hC.curok, by rw [hP2]; exact hC.nP, fun _ => ⟨hprep', ?_⟩,
            fun h => absurd h (by simp [hf']), hC.room, hC.live, by have := hC.bud; omega⟩
          have := hC.bud; omega
        exact ih (budget - 1) om n' A hR hL hI hN1 hf hlv hC1
    · obtain ⟨hserve, hpost⟩ := hC.serve hset
      have hN0 := hN
      obtain ⟨B, hRB, hIB, hzB, hcs⟩ := hN0
      rw [if_pos hset] at hcs
      obtain ⟨pre, post, hsplit, hcpost, hpre, hLB⟩ := hcs
      have hfill := (hserve B hRB.inv).2
      have hcurA : om.cursor ∈ A.elist := by
        rw [hsplit, hcpost]
        cases post with
        | nil => exact absurd hcpost hc
        | cons a t => simp
      have hlB := nxtR'_live_le hN hL hset hRB.inv
      have hlive := hC.live
      have hroom : n.count + 1 ≤ n.P.N := by
        rw [hC.nP, S.PN]; have := hC.room; omega
      refine ⟨elist_lt hR hcurA, fun hl => ?_, fun om3 n3 hcp3 hc3 => ?_⟩
      · refine ⟨B.elist, (hserve B hRB.inv).1, hroom, ?_, ?_⟩
        · rw [hRB.inv.tail]
          obtain ⟨b, bt, hb⟩ := List.exists_cons_of_ne_nil hRB.ne
          rw [hb]; exact getLastD_cons_mem _ _ _
        · have hmem : hdl om.cur om.cursor ∈ Sp.list := by
            rw [← hL]; exact FM_mem_of _ _ hcurA hl
          have := hS.2 _ hmem
          rw [hf]; exact this
      · obtain ⟨om', n', hcp, e1, e2, e3, e4, e5, e6, e7, hN'⟩ := copy_ok hN hR hnd hset hc
        obtain ⟨om2, n2, B2, hcp2, hcur2, hRB2, hok2, hfill2, hP2⟩ :=
          copy_cost S hR hRB hset hc hcurA (hserve B hRB.inv).1 hfill hroom
        rw [hcp] at hcp2
        injection hcp2 with hcp2
        injection hcp2 with h1 h2
        subst h1; subst h2
        rw [hcp] at hcp3
        injection hcp3 with hcp3
        injection hcp3 with h1 h2
        subst h1; subst h2
        have hC' : LoopC mk TI PI μ ν Jf nf Rf om' n' A (budget - 1) Φe live₀ I D N' := by
          refine ⟨by rw [e1]; exact hC.curok, by rw [hP2]; exact hC.nP, fun h => absurd (e4 ▸ h)
            (by simp [hset]), fun _ => ⟨fun B' hB' => ?_, ?_⟩, hC.room, by rw [e6]; exact hC.live,
            by rw [e7]; have := hC.bud; omega⟩
          · rw [INV.elist_unique hB' hRB2.inv]; exact ⟨hok2, hfill2⟩
          · have hpo : postOf A.elist om.cursor = post := by
              rw [hsplit]
              exact (split_unique (hsplit ▸ hR.inv.eList.nodup) (hsplit ▸ hR.inv.eList.nonil) hcpost).2
            have hpne : post ≠ [] := by intro h; rw [h] at hcpost; exact hc hcpost
            have hpost' : (postOf A.elist om'.cursor).length + 1 = (postOf A.elist om.cursor).length := by
              rw [hcur2, hR.inv.eList.next _ hcurA, postOf_succOf hR.inv.eList.nodup hR.inv.eList.nonil hcurA,
                hpo, List.length_tail]
              have := List.length_pos_of_ne_nil hpne; omega
            rw [e7]; have := hC.bud; omega
        exact ih (budget - 1) om' n' A (e1 ▸ hR) (e1 ▸ hL) (e1 ▸ e2 ▸ hI) (e1 ▸ hN') (e5 ▸ hf)
          (by rw [e6]; exact hlv) hC'

end OM.Proof
