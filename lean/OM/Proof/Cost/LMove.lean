import OM.Proof.Cost.Labels

/-!
# Lemma C3 across chunk-split moves

A chunk-split move carries a unit (a quiet group, or a whole family) from one end of the splitting
chunk `x` to the adjacent end of a sibling `dst`. The moved groups get fresh labels pushed at that
end and stop being children; the sibling's arrivals and pushes grow by the unit's length.

`linv_cmove_core` handles every field but the gaps and the label range, which depend on the
direction and are proved separately.
-/

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-- **The group-label invariant across a chunk-split move**, given the gaps and ranges after it. -/
theorem linv_cmove_core {s s' : Core} {A : Abs} {L : List Nat} {gh : GGh} {δg s₀ δ δu : Nat → Nat}
    {ex : Nat} {lg lg' : LGh} {x dst : Nat} {u labs : List Nat} (hI : INV s A)
    (hG : GInvE s L gh δg ex) (hC : CInvE s A.elist δ δu s₀ x) (hL : LInv s lg s₀ δ δu)
    (M : CMoveSpec s s' x dst u labs) (hxL : LiveC s x) (hst : cSt s x = .splitting)
    (hdst : dst = cLl s x ∨ dst = cRr s x) (hu : ∀ g ∈ u, LiveG s g ∧ gC s g = x)
    (hk : u.length ≤ 3) (hunits : units s' x + 1 = units s x)
    (hm : (u.map fun g => gSz s g).sum ≤ cSz s x) (hcl : FamClosed s u)
    (hchild : ∀ g, lg'.child g = if g ∈ u then false else lg.child g)
    (hhv : lg'.hv = lg.hv) (hcs : lg'.cs = lg.cs) (hrs : lg'.rs = lg.rs) (hins : lg'.ins = lg.ins)
    (he0 : lg'.e0 = lg.e0)
    (hpb : ∀ c, lg'.pb c ≤ lg'.arB c + lg'.rs c + lg'.cs c)
    (hpf : ∀ c, lg'.pf c ≤ lg'.arF c + lg'.rs c + lg'.cs c)
    (harr : ∀ c, lg'.arB c + lg'.arF c = lg.arB c + lg.arF c + if c = dst then u.length else 0)
    (hgaps : ∀ g, LiveG s' g → g ≠ cLs s' (gC s' g) →
      gL s' g + s'.P.D_g / 2 ^ lg'.hv (gC s' g) ≤ gL s' (gN s' g))
    (hrange : ∀ g, LiveG s' g →
      cG s'.P ≤ gL s' g + lg'.pf (gC s' g) * s'.P.D_g ∧
        gL s' g ≤ cG s'.P + lg'.pb (gC s' g) * s'.P.D_g) :
    LInv s' lg' s₀ δ δu := by
  have F := M.gfields
  have Fx := hC.cfam x hxL hst
  have hxy := Fx.lx hI hxL
  have hxz := Fx.rx hI hxL
  have hyz := Fx.lr hI hxL
  have hxd : x ≠ dst := by rcases hdst with rfl | rfl; exact Ne.symm hxy; exact Ne.symm hxz
  have hdov : cSt s dst = .overflow := by rcases hdst with rfl | rfl; exact Fx.lSt; exact Fx.rSt
  have hLC : ∀ c, LiveC s' c ↔ LiveC s c := by intro c; simp only [LiveC, M.Csize]
  have hLv : ∀ z, LiveG s' z ↔ LiveG s z := M.liveG
  -- the family of a splitting chunk keeps its size
  have hfam : ∀ x', LiveC s x' → cSt s x' = .splitting → famC s' x' = famC s x' := by
    intro x' hx' hs'
    unfold famC
    rw [M.cl, M.cr, M.csz, M.csz, M.csz]
    by_cases hxx : x' = x
    · subst hxx
      rw [if_neg hxy, if_pos rfl, if_neg hxz]
      rcases hdst with rfl | rfl
      · rw [if_pos rfl, if_neg hyz.symm]; omega
      · rw [if_neg hyz, if_pos rfl]; omega
    · obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ :=
        Fx.disjoint (hC.cfam x' hx' hs') (Ne.symm hxx) hst hs'
      have hnd1 : cLl s x' ≠ dst := by rcases hdst with rfl | rfl; exact d5; exact d6
      have hnd2 : x' ≠ dst := by rcases hdst with rfl | rfl; exact d1; exact d2
      have hnd3 : cRr s x' ≠ dst := by rcases hdst with rfl | rfl; exact d7; exact d8
      rw [if_neg d3, if_neg hnd1, if_neg hxx, if_neg hnd2, if_neg d4, if_neg hnd3]
  have hcszq : ∀ d, d ≠ x → d ≠ dst → cSz s' d = cSz s d := by
    intro d h1 h2; rw [M.csz, if_neg h1, if_neg h2]
  -- groups by chunk
  have hgrp : ∀ c z, z ∈ GrpsC s' c ↔ LiveG s z ∧ (if z ∈ u then dst else gC s z) = c := by
    intro c z; rw [mem_GrpsC, hLv, (F z).2.2.2.2.2.2.2.2.2.2]
  -- charge terms
  have hterm : ∀ z, LiveG s z → chTerm s' lg' z ≤ if z ∉ u then chTerm s lg z else 0 := by
    intro z hz
    have hft : famT s' z = famT s z := by
      unfold famT; rw [(F z).2.2.2.1, (F z).2.2.2.2.1, (F _).1, (F z).1, (F _).1]
    unfold chTerm
    rw [(F z).2.1, (F z).2.2.2.1, (F z).1, hft, M.P, hchild, hchild]
    by_cases hzu : z ∈ u
    · rw [if_neg (not_not.mpr hzu), if_pos hzu]
      by_cases hs : gSt s z = .splitting
      · have hl : gLl s z ∈ u := ((hcl z hz hs).1).mpr hzu
        rw [if_pos hl]; simp [hs]
      · simp [hs]
    · rw [if_pos hzu, if_neg hzu]
      by_cases hs : gSt s z = .splitting
      · have hl : gLl s z ∉ u := fun h => hzu (((hcl z hz hs).1).mp h)
        rw [if_neg hl]
      · simp only [hs, false_and, if_false]; exact le_rfl
  have hcharge : ∀ c, charge s' lg' c ≤ charge s lg c := by
    intro c
    rw [charge_eq, charge_eq]
    calc ∑ z ∈ GrpsC s' c, chTerm s' lg' z
        ≤ ∑ z ∈ GrpsC s' c, (if z ∉ u then chTerm s lg z else 0) :=
          Finset.sum_le_sum fun z hz => hterm z ((hgrp c z).mp hz).1
      _ = ∑ z ∈ (GrpsC s' c).filter (· ∉ u), chTerm s lg z := (Finset.sum_filter _ _).symm
      _ ≤ ∑ z ∈ GrpsC s c, chTerm s lg z := by
          apply Finset.sum_le_sum_of_subset
          intro z hz
          rw [Finset.mem_filter, hgrp] at hz
          rw [if_neg hz.2] at hz
          exact mem_GrpsC.mpr hz.1
  -- pending roots
  have hpend : ∀ c, pending s' lg' c ≤ pending s lg c + if c = dst then u.length else 0 := by
    intro c
    unfold pending
    have hsub : (GrpsC s' c).filter (fun g => lg'.child g = false ∧ gSt s' g ≠ .splitting) ⊆
        (GrpsC s c).filter (fun g => lg.child g = false ∧ gSt s g ≠ .splitting) ∪
          (if c = dst then u.toFinset else ∅) := by
      intro z hz
      rw [Finset.mem_filter, hgrp, hchild, (F z).2.1] at hz
      rw [Finset.mem_union, Finset.mem_filter, mem_GrpsC]
      by_cases hzu : z ∈ u
      · right; rw [if_pos hzu] at hz; rw [if_pos hz.1.2.symm]; exact List.mem_toFinset.mpr hzu
      · left; rw [if_neg hzu] at hz; rw [if_neg hzu] at hz; exact ⟨hz.1, hz.2⟩
    refine le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_union_le _ _) ?_)
    split
    · exact Nat.add_le_add_left (List.toFinset_card_le u) _
    · simp
  have hunits' : ∀ x', LiveC s x' → cSt s x' = .splitting → x' ≠ x → units s' x' = units s x' := by
    intro x' _ hs' hxx
    have hdx : dst ≠ x' := by intro e; rw [e, hs'] at hdov; cases hdov
    apply units_congr; intro z
    unfold UnitG
    rw [hLv, (F z).2.2.2.2.2.2.2.2.2.2, (F z).2.1]
    by_cases hzu : z ∈ u
    · rw [if_pos hzu]
      have := (hu z hzu).2
      constructor
      · rintro ⟨-, h, -⟩; exact absurd h hdx
      · rintro ⟨-, h, -⟩; exact absurd (this.symm.trans h) (Ne.symm hxx)
    · rw [if_neg hzu]
  refine
    { gaps := hgaps, range := hrange, hv := ?_, pb := hpb, pf := hpf, roots := ?_, claim2 := ?_,
      insQ := ?_, insO := ?_, insS := ?_, arrS := ?_, arrN := ?_, e0 := ?_, famChild := ?_ }
  · intro c; rw [hhv, hcs, hrs]; exact hL.hv c
  · intro d hd; rw [hLC] at hd
    have h1 := hL.roots d hd
    have h2 := hpend d
    have h3 := harr d
    rw [hrs]
    split at h2 <;> split at h3 <;> omega
  · intro d hd; rw [hLC] at hd
    have h1 := hL.claim2 d hd
    have h2 := hcharge d
    rw [hcs, hins, M.P]; omega
  · intro d hd hds; rw [hLC] at hd; rw [M.cst] at hds
    have h1 : d ≠ x := by intro e; rw [e, hst] at hds; cases hds
    have h2 : d ≠ dst := by intro e; rw [e, hdov] at hds; cases hds
    rw [hins, he0, hcszq d h1 h2, M.P]; exact hL.insQ d hd hds
  · intro d hd hds; rw [hLC] at hd; rw [M.cst] at hds
    obtain ⟨hsL, hss, -⟩ := hC.covf d hd hds
    rw [hins, M.csrc, hfam _ hsL hss]; exact hL.insO d hd hds
  · intro d hd hds; rw [hLC] at hd; rw [M.cst] at hds
    rw [hins, hfam d hd hds, M.P]; exact hL.insS d hd hds
  · intro x' hx' hxs'; rw [hLC] at hx'; rw [M.cst] at hxs'
    have h1 := hL.arrS x' hx' hxs'
    rw [M.cl, M.cr, hfam x' hx' hxs', M.P]
    by_cases hxx : x' = x
    · subst hxx
      have e1 := harr (cLl s x')
      have e2 := harr (cRr s x')
      rcases hdst with rfl | rfl
      · rw [if_pos rfl] at e1; rw [if_neg hyz.symm] at e2; omega
      · rw [if_neg hyz] at e1; rw [if_pos rfl] at e2; omega
    · obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ :=
        Fx.disjoint (hC.cfam x' hx' hxs') (Ne.symm hxx) hst hxs'
      have hnd1 : cLl s x' ≠ dst := by rcases hdst with rfl | rfl; exact d5; exact d6
      have hnd3 : cRr s x' ≠ dst := by rcases hdst with rfl | rfl; exact d7; exact d8
      have e1 := harr (cLl s x'); rw [if_neg hnd1] at e1
      have e2 := harr (cRr s x'); rw [if_neg hnd3] at e2
      rw [hunits' x' hx' hxs' hxx]; omega
  · intro d hd hds; rw [hLC] at hd; rw [M.cst] at hds
    have h2 : d ≠ dst := by intro e; rw [e, hdov] at hds; exact hds rfl
    have e1 := harr d; rw [if_neg h2] at e1
    have := hL.arrN d hd hds
    rw [M.P]; omega
  · intro d hd hds; rw [hLC] at hd; rw [M.cst] at hds
    have h1 : d ≠ x := by intro e; rw [e, hst] at hds; cases hds
    have h2 : d ≠ dst := by intro e; rw [e, hdov] at hds; cases hds
    rw [he0, hcszq d h1 h2]; exact hL.e0 d hd hds
  · intro p hp hps
    rw [hLv] at hp; rw [(F p).2.1] at hps
    rw [(F p).2.2.2.1, (F p).2.2.2.2.1, hchild, hchild]
    have hc := hcl p hp hps
    by_cases hpu : p ∈ u
    · rw [if_pos (hc.1.mpr hpu), if_pos (hc.2.mpr hpu)]
    · rw [if_neg (fun h => hpu (hc.1.mp h)), if_neg (fun h => hpu (hc.2.mp h))]
      exact hL.famChild p hp hps

end OM.Proof
