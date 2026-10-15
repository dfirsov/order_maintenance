import OM.Impl.GlueTop
import OM.Impl.Background

/-!
# M6: the glue for the core's parts

Level F's cost proofs establish the hypotheses of the core's run lemmas inside their proofs (the
group drive, the chunk drive, the split starts). Here those places get Level M agreements: each
proof is followed, and its run lemma is paired with the Level M lemma for the same branch.
-/

namespace OM.Impl

open OM.Model OM.Proof

set_option linter.deprecated false

/-- **The capacities a group drive needs**, at state `s`. -/
structure GCaps (κ : Caps) (s : Core) : Prop where
  G : s.Gs.size ≤ κ.tbl .G
  E : s.E.size ≤ κ.tbl .E
  C : s.C.size ≤ κ.tbl .C
  fl : κ.tbl .G ≤ κ.lcap .freeG
  f0 : 0 < κ.lrec .freeG

theorem _root_.OM.Proof.INV.gN_lt {s : Core} {A : Abs} (hI : INV s A) {g : Nat} (hg : g ∈ A.glist) : gN s g < s.Gs.size := by
  rw [hI.gList.next g hg]
  rcases succOf_mem_or (l := A.glist) (x := g) with h | h
  · exact hI.gAlloc _ h
  · rw [h]; have := hI.gPos; unfold NIL; omega

theorem _root_.OM.Proof.INV.gP_lt {s : Core} {A : Abs} (hI : INV s A) {g : Nat} (hg : g ∈ A.glist) : gP s g < s.Gs.size := by
  rw [hI.gList.prev g hg]
  rcases predOf_mem_or (l := A.glist) (x := g) with h | h
  · exact hI.gAlloc _ h
  · rw [h]; have := hI.gPos; unfold NIL; omega

theorem _root_.OM.Proof.INV.gF_lt {s : Core} {A : Abs} (hI : INV s A) {g : Nat} (hg : g ∈ A.glist) :
    gF s g = NIL ∨ gF s g < s.E.size := by
  by_cases h : gF s g = NIL
  · exact Or.inl h
  · obtain ⟨rest, hr⟩ := hI.run_head hg h
    have : gF s g ∈ A.elist := (mem_runOf.mp (hr ▸ (by simp : gF s g ∈ gF s g :: rest))).1
    exact Or.inr ((hI.eAlloc _).mp this).2

theorem _root_.OM.Proof.INV.gLs_lt {s : Core} {A : Abs} (hI : INV s A) {g : Nat} (hg : g ∈ A.glist) :
    gLs s g = NIL ∨ gLs s g < s.E.size := by
  by_cases h : gF s g = NIL
  · left
    have hE := hI.gEnds g hg
    rw [hI.elts_eq hg] at hE
    have := (hI.first_nil_iff hg).mp h
    rw [this] at hE; exact hE.2
  · obtain ⟨front, hr⟩ := hI.run_last hg h
    have : gLs s g ∈ A.elist := (mem_runOf.mp (hr ▸ (by simp : gLs s g ∈ front ++ [gLs s g]))).1
    exact Or.inr ((hI.eAlloc _).mp this).2

/-- The free groups are distinct groups below `Gs.size`, other than `NIL`. -/
theorem _root_.OM.Proof.INV.freeG_len {s : Core} {A : Abs} (hI : INV s A) : s.freeG.length + 1 ≤ s.Gs.size := by
  have hs : s.freeG.toFinset ⊆ Finset.Ico 1 s.Gs.size := fun g hg => by
    obtain ⟨a, b, -⟩ := hI.free g (List.mem_toFinset.mp hg); simp [Finset.mem_Ico]; omega
  have := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup hI.freeNodup, Nat.card_Ico] at this
  have := hI.gPos; omega

theorem moveLState_sizes {t : Core} {p : Nat} :
    (moveLState t p).Gs.size = t.Gs.size ∧ (moveLState t p).C.size = t.C.size := by
  simp [moveLState, sizeAdj, moveFirstLeft]

theorem moveRState_sizes {t : Core} {p : Nat} :
    (moveRState t p).Gs.size = t.Gs.size ∧ (moveRState t p).C.size = t.C.size := by
  simp [moveRState, sizeAdj, moveLastRight]

theorem removeState_sizes {t : Core} {p : Nat} :
    (removeState t p).Gs.size = t.Gs.size ∧ (removeState t p).C.size = t.C.size := by
  simp only [removeState, unlinkGroup, Array.size_modify]
  constructor
  · split_ifs <;> simp
  · split_ifs <;> simp

/-- **A group split step of a drive agrees** (the cases of `DriveInv.step`). -/
theorem _root_.OM.Proof.DriveInv.stepAgree {X Y : Core → Prop} {s : Core} {L : List Nat} {δ : Nat → Nat}
    {p l r a b c j : Nat} {t : Core} (hXs : XSteps X Y L δ p (gC s p))
    (hP : GParams s.P) (hδ : ∀ z, z ≠ l → z ≠ p → z ≠ r → δ z = 0)
    (hTlo : s.P.G ≤ a + b + c) (hThi : a + b + c ≤ s.P.G + s.P.G / (s.P.K_G - 1) + 1)
    (hbal0 : a ≤ c + 2 ∧ c ≤ a + 2)
    (hD : DriveInv X s L δ p l r a b c j t) {κ : Caps} (hcg : ∀ g, LiveG t g → gC t g < t.C.size)
    (K : GCaps κ t) :
    ∃ b t', (groupSplitStep p).run t = .ok b t' ∧ StepAgree κ p t t' b ∧ t'.Gs.size = t.Gs.size ∧
      t'.C.size = t.C.size := by
  obtain ⟨A', hI', hel⟩ := hD.inv
  obtain ⟨gh, hG⟩ := hD.ginv
  subst hel
  have hp := hD.live
  have hs := hD.st
  have Fp := hG.fam p hp hs
  have hp' := hI'.mem_glist_iff.mpr hp
  have hPt := hD.P
  rw [← hPt] at hP hTlo hThi
  have hlL : LiveG t l := hD.ll ▸ Fp.lLive
  have hrL : LiveG t r := hD.rr ▸ Fp.rLive
  have hl' := hI'.mem_glist_iff.mpr hlL
  have hr' := hI'.mem_glist_iff.mpr hrL
  have hlp : l ≠ p := hD.ll ▸ Fp.lp hI' hp
  have hrp : r ≠ p := hD.rr ▸ Fp.rp hI' hp
  have hlr : l ≠ r := hD.ll ▸ hD.rr ▸ Fp.lr hI' hp
  have hsum := hD.sum
  have hcnt := hD.cnt
  have hbal := hD.bal
  have hK2 := hP.K2
  have hI1 := hP.I1
  generalize hq : t.P.G / (t.P.K_G - 1) = q at hThi hI1
  have hkG : kG t.P = q + 1 := by unfold kG; rw [hq]
  have hcE := hP.push
  rw [hkG] at hcE
  have hD0 := hP.De
  by_cases hz : gSz t p = 0
  · -- removal
    have he : gF t p = NIL := by
      rw [hI'.first_nil_iff hp', ← List.length_eq_zero_iff, ← hG.sz p hp]; exact hz
    have hszl : gSz t l < t.P.G := by rcases hbal with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
    have hszr : gSz t r < t.P.G := by rcases hbal with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
    have hgl : gmin t.P ≤ gSz t l := by
      unfold gmin; rcases hbal with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
    have hgr : gmin t.P ≤ gSz t r := by
      unfold gmin; rcases hbal with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
    have hfam : famT t p ≤ t.P.G + kG t.P := by
      unfold famT; rw [hD.ll, hD.rr, hkG]; omega
    have hg1 : 1 ≤ gmin t.P := by unfold gmin; have := hP.G4; omega
    have hrun := groupSplitStep_remove hp he (by rw [hD.ll, hD.rr]; exact hlr)
      ⟨by rw [hD.ll]; exact Fp.lSt ▸ hD.ll ▸ rfl, by rw [hD.ll]; exact hD.ll ▸ Fp.lSrc⟩
      ⟨by rw [hD.rr]; exact hD.rr ▸ Fp.rSt, by rw [hD.rr]; exact hD.rr ▸ Fp.rSrc⟩
      (by rw [hD.ll]; exact hszl) (by rw [hD.rr]; exact hszr)
    refine ⟨false, _, hrun, fun Lc hLc => ?_, removeState_sizes.1, removeState_sizes.2⟩
    obtain ⟨L', n, e, hok, hn⟩ := groupSplitStepS_remove κ t Lc hLc hp he (by rw [hD.ll, hD.rr]; exact hlr)
      ⟨by rw [hD.ll]; exact Fp.lSt ▸ hD.ll ▸ rfl, by rw [hD.ll]; exact hD.ll ▸ Fp.lSrc⟩
      ⟨by rw [hD.rr]; exact hD.rr ▸ Fp.rSt, by rw [hD.rr]; exact hD.rr ▸ Fp.rSrc⟩
      (by rw [hD.ll]; exact hszl) (by rw [hD.rr]; exact hszr) (by rw [hD.ll]; exact hlL.2.1)
      (by rw [hD.rr]; exact hrL.2.1) (hI'.gP_lt hp') (hI'.gN_lt hp') (hcg p hp) (by have := K.G; omega)
      (by have := K.C; omega) (by have := hI'.freeG_len; have := K.G; have := K.fl; omega) K.f0
    exact ⟨L', n, e, by rw [hok]; rfl, hn⟩
  · have hne : gF t p ≠ NIL := by
      intro h; apply hz
      rw [hG.sz p hp]; exact List.length_eq_zero_iff.mpr ((hI'.first_nil_iff hp').mp h)
    obtain ⟨rest, hrun⟩ := hI'.run_head hp' hne
    have he : gF t p ∈ A'.elist := (mem_runOf.mp (hrun ▸ (by simp : gF t p ∈ gF t p :: rest))).1
    have heS : gF t p < t.E.size := ((hI'.eAlloc _).mp he).2
    obtain ⟨front, hrunL⟩ := hI'.run_last hp' hne
    have heL : gLs t p ∈ A'.elist :=
      (mem_runOf.mp (hrunL ▸ (by simp : gLs t p ∈ front ++ [gLs t p]))).1
    have heLS : gLs t p < t.E.size := ((hI'.eAlloc _).mp heL).2
    by_cases hdir : gSz t l ≤ gSz t r
    · -- move to the left sibling
      have hlst : gSt t l = .overflow := hD.ll ▸ Fp.lSt
      obtain ⟨-, hpush⟩ := hG.ghO l hlL hlst
      have hlsz : gSz t l + 1 ≤ t.P.G + q + 1 := by omega
      have hroom : gF t l ≠ NIL → eL t (gLs t l) + t.P.D_e < 1 <<< t.P.B_e := by
        intro hfl
        obtain ⟨fr, hfr⟩ := hI'.run_last hl' hfl
        obtain ⟨-, h2⟩ := hG.range l hlL (gLs t l) (by rw [hfr]; simp)
        rw [cE_two _ hP.Be]
        have : (gh.pb l + 1) * t.P.D_e ≤ (t.P.G + (q + 1)) * t.P.D_e :=
          Nat.mul_le_mul_right _ (by omega)
        have : (gh.pb l + 1) * t.P.D_e = gh.pb l * t.P.D_e + t.P.D_e := by ring
        omega
      have hok : MoveLOK t p := ⟨hp, hne, by rw [hD.ll, hD.rr]; exact hdir,
        Fp.lAdj, by rw [hD.ll]; exact hroom, by omega, Fp.lC⟩
      have hrun2 := groupSplitStep_left hok
      refine ⟨true, _, hrun2, fun Lc hLc => ?_, moveLState_sizes.1, moveLState_sizes.2⟩
      obtain ⟨L', n, e, hok', -, hn⟩ := groupSplitStepS_left κ t Lc hLc hok (by rw [hD.ll]; exact hlL.2.1)
        (by rw [hD.rr]; exact hrL.2.1) heS (by
          rcases hI'.gLs_lt (hD.ll ▸ hl') with h | h
          · rw [h]; have := K.E; unfold NIL; omega
          · have := K.E; omega) (by have := K.G; omega) (by have := K.E; omega)
      exact ⟨L', n, e, by rw [hok']; rfl, by omega⟩
    · -- move to the right sibling
      have hrst : gSt t r = .overflow := hD.rr ▸ Fp.rSt
      obtain ⟨-, hpush⟩ := hG.ghO r hrL hrst
      have hrsz : gSz t r + 1 ≤ t.P.G + q + 1 := by omega
      have hroom : gF t r ≠ NIL → t.P.D_e ≤ eL t (gF t r) := by
        intro hfr
        obtain ⟨rs, hrs⟩ := hI'.run_head hr' hfr
        obtain ⟨h1, -⟩ := hG.range r hrL (gF t r) (by rw [hrs]; simp)
        have : (gh.pf r + 1) * t.P.D_e ≤ (t.P.G + (q + 1)) * t.P.D_e :=
          Nat.mul_le_mul_right _ (by omega)
        have : (gh.pf r + 1) * t.P.D_e = gh.pf r * t.P.D_e + t.P.D_e := by ring
        omega
      have hadjR : gP t (gRr t p) = p := by
        rw [← Fp.rAdj]; exact hI'.gP_gN hp' (by rw [Fp.rAdj, hD.rr]; exact hrL.1)
      have hok : MoveROK t p := ⟨hp, hne, by rw [hD.ll, hD.rr]; omega, hadjR,
        by rw [hD.rr]; exact hroom, by omega, Fp.rC⟩
      have hrun2 := groupSplitStep_right hok
      refine ⟨true, _, hrun2, fun Lc hLc => ?_, moveRState_sizes.1, moveRState_sizes.2⟩
      obtain ⟨L', n, e, hok', -, hn⟩ := groupSplitStepS_right κ t Lc hLc hok (by rw [hD.ll]; exact hlL.2.1)
        (by rw [hD.rr]; exact hrL.2.1) heLS (by
          rcases hI'.gF_lt (hD.rr ▸ hr') with h | h
          · rw [h]; have := K.E; unfold NIL; omega
          · have := K.E; omega) (by have := K.G; omega) (by have := K.E; omega)
      exact ⟨L', n, e, by rw [hok']; rfl, by omega⟩
/-- **The drive of a splitting group agrees** (the context of `ginv_drive`). -/
theorem ginv_driveAgree {X Y : Core → Prop} {s : Core} {A : Abs} {gh : GGh} {δ : Nat → Nat} {p : Nat}
    (hI : INV s A) (hXs : XSteps X Y A.elist δ p (gC s p)) (hX : X s)
    (hG : GInvE s A.elist gh δ p) (hP : GParams s.P) (hp : LiveG s p) (hs : gSt s p = .splitting)
    (hG1 : G1 s δ p)
    (hδ : ∀ z, z ≠ gLl s p → z ≠ p → z ≠ gRr s p → δ z = 0)
    (hδs : δ (gLl s p) + δ p + δ (gRr s p) ≤ 1)
    (hδle : δ (gLl s p) ≤ gSz s (gLl s p) ∧ δ p ≤ gSz s p ∧ δ (gRr s p) ≤ gSz s (gRr s p))
    {κ : Caps} (hXc : ∀ t, X t → ∀ g, LiveG t g → gC t g < t.C.size) (K : GCaps κ s) :
    ∃ s', DriveAgree κ p s s' := by
  generalize hl : gLl s p = l at *
  generalize hr : gRr s p = r at *
  generalize ha : gSz s l = a at *
  generalize hb : gSz s p = b at *
  generalize hc : gSz s r = c at *
  have hK2 := hP.K2
  have hI1 := hP.I1
  unfold G1 at hG1
  rw [hl, hr, ha, hb, hc] at hG1
  obtain ⟨g1, g2, g3, g4⟩ := hG1
  generalize hm : s.P.K_G - 1 = m at g2 hI1
  have hm1 : 1 ≤ m := by omega
  generalize hq : s.P.G / m = q at hI1
  -- the size before the undriven insertions exceeds `G` by at most `q`
  have hXq : (a - δ l) + (b - δ p) + (c - δ r) - s.P.G ≤ q := by
    rw [← hq, Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]
    have := Nat.le_add_left (m * ((a - δ l) + (b - δ p) + (c - δ r) - s.P.G)) (b - δ p)
    omega
  have hTlo : s.P.G ≤ a + b + c := by omega
  have hThi : a + b + c ≤ s.P.G + s.P.G / (s.P.K_G - 1) + 1 := by rw [hm, hq]; omega
  have hbal0 : a ≤ c + 2 ∧ c ≤ a + 2 := by omega
  refine driveGroupFromS_agree' κ s (fun j t => DriveInv X s A.elist δ p l r a b c j t ∧
    t.Gs.size = s.Gs.size ∧ t.C.size = s.C.size)
    ⟨⟨hX, rfl, EFrame.refl s, ⟨A, hI, rfl⟩, ⟨gh, hG⟩, hp, hs, hl, hr, by omega, by omega,
      Or.inl ⟨rfl, ha, hc⟩, rfl⟩, rfl, rfl⟩ ?_
  intro j t ⟨hD, hGs, hCs⟩ _
  have K' : GCaps κ t := ⟨by rw [hGs]; exact K.G, by rw [hD.ef.size]; exact K.E, by rw [hCs]; exact K.C, K.fl, K.f0⟩
  obtain ⟨bb, t', hrun, hA, hG', hC'⟩ := hD.stepAgree hXs hP (by intro z h1 h2 h3; exact hδ z h1 h2 h3) hTlo hThi hbal0
    (hXc t hD.x) K'
  refine ⟨bb, t', hrun, fun hb => ?_, hA⟩
  subst hb
  obtain ⟨t1, h1 | h1⟩ := hD.step hXs hP (by intro z h1 h2 h3; exact hδ z h1 h2 h3) hTlo hThi hbal0
  · rw [h1.1] at hrun; injection hrun with _ e; subst e
    exact ⟨h1.2, hG'.trans hGs, hC'.trans hCs⟩
  · rw [h1.1] at hrun; injection hrun with e; cases e

theorem allocGroup_size (s : Core) (c : Nat) : (allocGroup s c).2.Gs.size ≤ s.Gs.size + 1 := by
  unfold allocGroup; split <;> simp

theorem linkGroupPair_size (s : Core) (g gl gr labL labR : Nat) :
    (linkGroupPair s g gl gr labL labR).Gs.size = s.Gs.size := by
  unfold linkGroupPair; dsimp only; split_ifs <;> simp

theorem splitState_size (s : Core) (g labL labR : Nat) : (splitState s g labL labR).Gs.size ≤ s.Gs.size + 2 := by
  unfold splitState; rw [linkGroupPair_size]
  have := allocGroup_size (allocGroup s (gC s g)).2 (gC s g)
  have := allocGroup_size s (gC s g)
  omega

/-- A drive that agrees, read off a `DriveAgree` for the run Level F made. -/
theorem DriveAgree.of_run {κ : Caps} {q : Nat} {s s' s'' : Core} (hA : DriveAgree κ q s s'')
    (h : (driveGroupFrom q).run s = .ok () s') : DriveAgree κ q s s' := by
  rw [hA.1] at h; injection h with _ e; subst e; exact hA

/-- **The group phase agrees** (the context of `groupPhase_ok`): the split start, when it runs, and
the drive. -/
theorem groupPhaseAgree {X Y : Core → Prop} {s : Core} {A : Abs} {gh : GGh} {g : Nat} (hI : INV s A)
    (hXg : XGroup X Y A.elist (gC s g)) (hX : X s)
    (hG : GInv s A.elist gh (fun b => if b = g then 1 else 0)) (hP : GParams s.P)
    (hg : LiveG s g) (hpos : 1 ≤ gSz s g)
    (hroom : gSt s g = .quiet → s.P.G ≤ gSz s g → SplitRoom s g)
    {κ : Caps} (hXc : ∀ t, X t → ∀ g, LiveG t g → gC t g < t.C.size) (K : GCaps κ s)
    (hG2 : s.Gs.size + 2 ≤ κ.tbl .G) (hF0 : 0 < κ.lrec .freeG) (hF : s.freeG.length ≤ κ.lcap .freeG)
    {s1 s' : Core}
    (h1 : (if ((s.Gs.getX g).st == St.quiet && decide ((s.Gs.getX g).size ≥ s.P.G)) = true then
      startGroupSplit g else pure ()).run s = .ok () s1)
    (h2 : (driveGroup g).run s1 = .ok () s') :
    (((s.Gs.getX g).st == St.quiet && decide ((s.Gs.getX g).size ≥ s.P.G)) = true →
      ∃ L' n, evalF κ startGroupSplitS s (OM.Machine.State.setLocs (fun _ => 0) ["g"] [g]) = .ok s1 L' n ∧
        n ≤ 600) ∧
    ∃ L' n, evalF κ driveGroupS s1 (OM.Machine.State.setLocs (fun _ => 0) ["g"] [g]) = .ok s' L' n ∧
      n ≤ 30 + s1.P.K_G * 401 := by
  have hgl := hI.mem_glist_iff.mpr hg
  have hgT : g < κ.tbl .G := by have := hg.2.1; have := K.G; omega
  have hLg : OM.Machine.State.setLocs (fun _ => 0) ["g"] [g] "g" = g := by
    simp [OM.Machine.State.setLocs, OM.Machine.State.upd]
  have hδle : ∀ p, (fun b => if b = g then 1 else 0) p ≤ gSz s p := by
    intro p; by_cases h : p = g
    · subst h; simp [hpos]
    · simp [h]
  refine ⟨fun hc => ?_, ?_⟩
  · rw [if_pos hc] at h1
    exact startGroupSplitS_agree κ s _ hLg (by omega) K.C (hI.gP_lt hgl) (hI.gN_lt hgl) (hXc s hX g hg)
      (fun x hx => (hI.free x hx).2.1) hF0 hF h1
  · refine driveGroupS_agree κ s1 _ hLg hgT h2 (fun q hq => ?_)
    cases hst : gSt s g with
    | quiet =>
      by_cases hsz : s.P.G ≤ gSz s g
      · obtain ⟨labL, labR, hL, hR⟩ := hroom hst hsz
        have hc : ((s.Gs.getX g).st == St.quiet && decide ((s.Gs.getX g).size ≥ s.P.G)) = true := by
          simp only [gSt, gSz] at hst hsz; simp [hst, hsz]
        rw [if_pos hc, startGroupSplit_ok hg hL hR] at h1
        injection h1 with _ e; subst e
        have hgG : gSz s g = s.P.G := by
          have := (hG.quiet g hg hst).1; simp at this; omega
        obtain ⟨hef1, A1, hI1, hel1⟩ := Good.ok_inv (good_startGroupSplit g) hI
          (startGroupSplit_ok hg hL hR)
        have hG1 := ginv_splitStart hI hG hg hst hsz labL labR
        have hX1 := hXg.split s A gh g labL labR hI rfl hG hg hst hgG hL hR hX
        have S := splitSpec hI hgl labL labR
        have hsz2 := splitState_size s g labL labR
        generalize splitState s g labL labR = s1 at hef1 hI1 hG1 hX1 S hq h2 hsz2 ⊢
        generalize gh.reset (splitL s g) (splitR s g) = gh1 at hG1
        have hg1 : LiveG s1 g := (S.live g).mpr (Or.inr (Or.inr hg))
        have hs1 : gSt s1 g = .splitting := by rw [S.st, if_pos rfl]
        rw [← hel1] at hG1
        have hP1 : GParams s1.P := by rw [S.P]; exact hP
        have hXd : XSteps X Y A1.elist (fun _ => 0) g (gC s1 g) := by
          rw [hel1, S.chk, if_neg (not_or.mpr ⟨S.ggl, S.ggr⟩)]; exact hXg.drive _ g
        have K1 : GCaps κ s1 := ⟨by omega, by rw [S.E]; exact K.E, by rw [S.Csize]; exact K.C, K.fl, K.f0⟩
        obtain ⟨s2, hA⟩ := ginv_driveAgree hI1 hXd hX1 (hG1.weaken g) hP1 hg1 hs1
          (hG1.split g hg1 hs1 hg1.1) (fun _ _ _ _ => rfl) (by simp) (by simp) hXc K1
        have hs1' : (s1.Gs.getX g).st = .splitting := hs1
        rcases hq with ⟨-, rfl⟩ | ⟨h, -⟩
        · rw [driveGroup_split hs1'] at h2; exact hA.of_run h2
        · rw [hs1'] at h; cases h
      · have hc : ¬ ((s.Gs.getX g).st == St.quiet && decide ((s.Gs.getX g).size ≥ s.P.G)) = true := by
          simp only [gSt, gSz] at hst hsz; simp [hst]; omega
        rw [if_neg hc] at h1
        injection h1 with _ e; subst e
        simp only [gSt] at hst
        rcases hq with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [hst] at h <;> cases h
    | overflow =>
      have hc : ¬ ((s.Gs.getX g).st == St.quiet && decide ((s.Gs.getX g).size ≥ s.P.G)) = true := by
        simp only [gSt] at hst; simp [hst]
      rw [if_neg hc] at h1
      injection h1 with _ e; subst e
      obtain ⟨hp, hps, hlr⟩ := hG.ovf g hg hst
      have Fp := hG.fam _ hp hps
      have hgp : gSrc s g ≠ g := by intro e; rw [e, hst] at hps; cases hps
      have hlr0 : gLl s (gSrc s g) ≠ gRr s (gSrc s g) := Fp.lr hI hp
      have hδs : (fun b => if b = g then 1 else 0) (gLl s (gSrc s g)) +
          (fun b => if b = g then 1 else 0) (gSrc s g) +
          (fun b => if b = g then 1 else 0) (gRr s (gSrc s g)) ≤ 1 := by
        rcases hlr with e | e
        · have : gRr s (gSrc s g) ≠ g := fun h => hlr0 (e.trans h.symm)
          simp [e, hgp, this]
        · have : gLl s (gSrc s g) ≠ g := fun h => hlr0 (h.trans e.symm)
          simp [e, hgp, this]
      have hXd : XSteps X Y A.elist (fun b => if b = g then 1 else 0) (gSrc s g) (gC s (gSrc s g)) := by
        rcases hlr with e | e
        · rw [← Fp.lC, e]; exact hXg.drive _ _
        · rw [← Fp.rC, e]; exact hXg.drive _ _
      obtain ⟨s2, hA⟩ := ginv_driveAgree hI hXd hX (hG.weaken (gSrc s g)) hP hp hps
        (hG.split _ hp hps hp.1)
        (by intro z h1 h2 h3; have : z ≠ g := by
              rintro rfl; rcases hlr with e | e <;> [exact h1 e.symm; exact h3 e.symm]
            simp [this])
        hδs ⟨hδle _, hδle _, hδle _⟩ hXc K
      have hst' : (s.Gs.getX g).st = .overflow := hst
      rcases hq with ⟨h, -⟩ | ⟨-, rfl⟩
      · rw [hst'] at h; cases h
      · rw [driveGroup_ovf hst'] at h2; exact hA.of_run h2
    | splitting =>
      have hc : ¬ ((s.Gs.getX g).st == St.quiet && decide ((s.Gs.getX g).size ≥ s.P.G)) = true := by
        simp only [gSt] at hst; simp [hst]
      rw [if_neg hc] at h1
      injection h1 with _ e; subst e
      have Fp := hG.fam g hg hst
      have hl0 : gLl s g ≠ g := Fp.lp hI hg
      have hr0 : gRr s g ≠ g := Fp.rp hI hg
      obtain ⟨s2, hA⟩ := ginv_driveAgree hI (hXg.drive _ _) hX (hG.weaken g) hP hg hst
        (hG.split g hg hst hg.1) (by intro z _ h2 _; simp [h2]) (by simp [hl0, hr0])
        ⟨hδle _, hδle _, hδle _⟩ hXc K
      have hst' : (s.Gs.getX g).st = .splitting := hst
      rcases hq with ⟨-, rfl⟩ | ⟨h, -⟩
      · rw [driveGroup_split hst'] at h2; exact hA.of_run h2
      · rw [hst'] at h; cases h
    | dead => exact absurd hst (hG.notDead g hg)

end OM.Impl
