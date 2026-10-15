import OM.Impl.GlueTop
import OM.Impl.Background

/-!
# M6: the glue for the core's parts

Level F's cost proofs establish the hypotheses of the core's run lemmas inside their proofs (the
group drive, the chunk drive, the split starts). Here those places get Level M agreements: each
proof is followed, and its run lemma is paired with the Level M lemma for the same branch.
-/

namespace OM.Proof

open OM.Model OM.Zeroing

set_option linter.deprecated false

/-- The iteration step of `reservation_cost` (its proof, as a lemma). -/
theorem resInv_step {TI : Core → Prop} {μ : Core → Nat} {J k n R : Nat} {cap : Params → Nat} {L : List Nat}
    {s : Core} (hTC : TopContract TI μ J cap) (hn : 1 ≤ n)
    (hsize : 2 + 2 * (s.count / (s.P.theta + 1 - cmax s.P)) ≤ n + 1)
    (hcap : 2 + 2 * (s.count / (s.P.theta + 1 - cmax s.P)) ≤ cap s.P)
    (hI5 : (s.P.theta : ℝ) + R * (Hn (n - 1) + 1) ≤ s.P.T) :
    ∀ j t, ResInv TI k J n R μ L s j t → j < k →
      (t.resJob = none → (t.pqHi = 0 ∧ (LowInv t L ∧ TI t ∧ t.count = s.count ∧ t.P = s.P ∧
          t.resJob = none ∧ ∀ c, gval t c = 0)) ∨
        (t.pqHi ≠ 0 ∧ ∃ c t1 t2, pqPopMax.run t = .ok c t1 ∧ (splitChunkStart c).run t1 = .ok () t2 ∧
          ResInv TI k J n R μ L s (j + 1) t2)) ∧
      (∀ job, t.resJob = some job → ∃ r t1, (jobStep job).run t = .ok r t1 ∧
        ResInv TI k J n R μ L s (j + 1) { t1 with resJob := r }) := by
    intro j t hI hj
    obtain ⟨hL, hT, hc, hP, y, i, a, ip, js, hG, hR⟩ := hI
    refine ⟨fun hnone => ?_, fun job hjob => ?_⟩
    · by_cases hq0 : t.pqHi = 0
      · exact Or.inl ⟨hq0, hL, hT, hc, hP, hnone, gval_zero_of_empty hL.pq hq0⟩
      · right
        refine ⟨hq0, ?_⟩
        obtain ⟨bl, nb, hQ⟩ := hL.pq
        obtain ⟨c, hpop, hcin, hmax⟩ := pqPopMax_ok hQ hq0
        have hcq := hcin
        unfold inQC at hcq; simp only [decide_eq_true_eq] at hcq
        obtain ⟨hcL, hcQ, hθ⟩ := hcq
        obtain ⟨A, hIA, hel⟩ := hL.inv
        obtain ⟨e, pops, hN⟩ := hL.cnt
        have hI4 := hL.cp.I4
        have hd : 1 ≤ t.P.theta + 1 - cmax t.P := by omega
        -- the chunks fit
        have hpops : pops + 1 ≤ t.count / (t.P.theta + 1 - cmax t.P) := by
          rw [Nat.le_div_iff_mul_le hd]
          have hb := hN.bound
          have hcQs : c ∈ quietSet t := mem_quietSet.mpr ⟨hcL, hcQ⟩
          have hterm : cSz t c - e c ≤ ∑ d ∈ quietSet t, (cSz t d - e d) :=
            Finset.single_le_sum (f := fun d => cSz t d - e d) (fun _ _ => Nat.zero_le _) hcQs
          have he := hN.e_le c hcL hcQ
          rw [Nat.add_mul, Nat.one_mul]; omega
        have hsz := hN.size
        rw [hc, hP] at hpops
        have hcn : c - 1 < n := by have := hcL.2; omega
        have hT5 := cSz_le_T hG (by rw [hP]; exact hI5) hcL.1 hcn ⟨hcL, hcQ⟩
        -- start the split of `c`
        have hD := delSt_only t c
        have hI1 : INV (delSt t c) A := hIA.of_sameLinks hD.sameLinks (fun d => by simp only [cT, hD.C])
        have hTI1 : TI (delSt t c) := hTC.frame _ _ hD.topSame hT
        have hsz1 : (delSt t c).C.size = t.C.size := by rw [hD.C]
        have hQS := hD.lowSame.qsame
        have hcL1 : LiveC (delSt t c) c := by simp only [LiveC, hsz1]; exact hcL
        have hcq1 : cSt (delSt t c) c = .quiet := (hQS.q c hcL).mpr hcQ
        have hnone1 : (delSt t c).resJob = none := by rw [hD.rest.2.2.2.2.2.2.2.2.1]; exact hnone
        obtain ⟨job, s2, hj, hμ1, hμJ, hTI2⟩ :=
          hTC.start (delSt t c) A c hI1 hTI1 hnone1 hcL1 hcq1 (by rw [hsz1, hD.P, hP]; omega)
        have hrun := splitChunkStart_ok (by unfold NIL; have := hcL.1; omega) hcL1.2 hj
        have hs2 : TopRel (linkChunkPair (push2 (delSt t c)) c (delSt t c).C.size
            ((delSt t c).C.size + 1)) s2 := by
          have := top_insertAround c (delSt t c).C.size ((delSt t c).C.size + 1)
            (linkChunkPair (push2 (delSt t c)) c (delSt t c).C.size ((delSt t c).C.size + 1))
          rw [hj] at this; exact this
        refine ⟨c, delSt t c, _, hpop, hrun, ?_⟩
        have hGP : GParams t.P := hL.cinv.choose_spec.2.2.2
        have hL2 := lowinv_pop hL hGP hcin hT5 hs2 hrun
        have hcA : c ∈ A.chunks := (hI1.cAlloc c).mpr hcL1
        have RS := resSpec_run (job := job) hI1 hcA hs2
        obtain ⟨rE, rcnt, rhead, rP⟩ := split_rest (job := job) hs2
        have hjm : (⟨c - 1, hcn⟩ : Fin n).val + 1 = c := by simp only; have := hcL.1; omega
        refine ⟨hL2, hTI2, rcnt.trans (hD.rest.2.1.trans hc), rP.trans (hD.P.trans hP),
          gvec n t, ⟨c - 1, hcn⟩, fun _ => 0, 0, 0, hG.pop ⟨c - 1, hcn⟩ (fun jj => ?_) (fun jj => ?_),
          ?_⟩
        · unfold gvec; rw [hjm]; exact_mod_cast gval_max hcin hmax _
        · unfold gvec
          have hp := gval_pop RS (jj.val + 1)
          by_cases hjj : jj = ⟨c - 1, hcn⟩
          · rw [if_pos hjj]; rw [if_pos (by rw [hjj, hjm])] at hp; exact_mod_cast hp
          · rw [if_neg hjj]
            have hne : jj.val + 1 ≠ c := by
              intro e; apply hjj; ext; simp only; omega
            rw [if_neg hne] at hp
            exact_mod_cast hp
        · show RoundAt k J (μ (markState s2 c (delSt t c).C.size ((delSt t c).C.size + 1) job)) (some job) 0 0 (j + 1)
          exact ⟨by simp, by omega, hμ1⟩
    · obtain ⟨A, hIA, hel⟩ := hL.inv
      obtain ⟨r, t1, hj1, hTI1, hμ⟩ := hTC.step t A job hIA hT hjob
      have hTR : TopRel t t1 := by have := top_jobStep job t; rw [hj1] at this; exact this
      have hSafe : Safe t t1 := by have := pres_jobStep job t; rw [hj1] at this; exact this
      have hI1 := hSafe.2 A hIA
      have hTR' : TopRel t { t1 with resJob := r } :=
        hTR.trans ⟨rfl, rfl, rfl, fun _ => rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
      have hI1' : INV { t1 with resJob := r } A :=
        hI1.of_sameLinks (by constructor <;> intros <;> rfl) (fun _ => rfl)
      refine ⟨r, t1, hj1, hL.top hTR' ⟨A, hI1', hel⟩, hTI1, hTR'.rest.2.1.trans hc,
        hTR'.rest.1.trans hP, y, i, a, ip, js + 1,
        hG.mono (fun jj => le_of_eq (by rw [hTR'.qsame.gvec])), ?_⟩
      unfold RoundAt at hR
      rw [hjob] at hR
      obtain ⟨h1, h2, h3⟩ := hR
      show RoundAt k J (μ { t1 with resJob := r }) r ip (js + 1) (j + 1)
      cases r with
      | none => show ip * k ≤ J + (k - (j + 1)); omega
      | some j' =>
        obtain ⟨hm1, hm2⟩ := hμ j' rfl
        exact ⟨by omega, by omega, hm1⟩

end OM.Proof

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
    (moveLState t p).Gs.size = t.Gs.size ∧ (moveLState t p).C.size = t.C.size ∧ (moveLState t p).E.size = t.E.size := by
  simp [moveLState, sizeAdj, moveFirstLeft]

theorem moveRState_sizes {t : Core} {p : Nat} :
    (moveRState t p).Gs.size = t.Gs.size ∧ (moveRState t p).C.size = t.C.size ∧ (moveRState t p).E.size = t.E.size := by
  simp [moveRState, sizeAdj, moveLastRight]

theorem removeState_sizes {t : Core} {p : Nat} :
    (removeState t p).Gs.size = t.Gs.size ∧ (removeState t p).C.size = t.C.size ∧
      (removeState t p).E.size = t.E.size := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [removeState, unlinkGroup, Array.size_modify] <;> split_ifs <;> simp

/-- **A group split step of a drive agrees** (the cases of `DriveInv.step`). -/
theorem _root_.OM.Proof.DriveInv.stepAgree {X Y : Core → Prop} {s : Core} {L : List Nat} {δ : Nat → Nat}
    {p l r a b c j : Nat} {t : Core} (hXs : XSteps X Y L δ p (gC s p))
    (hP : GParams s.P) (hδ : ∀ z, z ≠ l → z ≠ p → z ≠ r → δ z = 0)
    (hTlo : s.P.G ≤ a + b + c) (hThi : a + b + c ≤ s.P.G + s.P.G / (s.P.K_G - 1) + 1)
    (hbal0 : a ≤ c + 2 ∧ c ≤ a + 2)
    (hD : DriveInv X s L δ p l r a b c j t) {κ : Caps} (hcg : ∀ g, LiveG t g → gC t g < t.C.size)
    (K : GCaps κ t) :
    ∃ b t', (groupSplitStep p).run t = .ok b t' ∧ StepAgree κ p t t' b ∧ t'.Gs.size = t.Gs.size ∧
      t'.C.size = t.C.size ∧ t'.E.size = t.E.size := by
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
    refine ⟨false, _, hrun, fun Lc hLc => ?_, removeState_sizes⟩
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
      refine ⟨true, _, hrun2, fun Lc hLc => ?_, moveLState_sizes⟩
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
      refine ⟨true, _, hrun2, fun Lc hLc => ?_, moveRState_sizes⟩
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
    ∃ s', DriveAgree κ p s s' ∧ s'.Gs.size = s.Gs.size ∧ s'.C.size = s.C.size ∧ s'.E.size = s.E.size := by
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
  let I' := fun j t => DriveInv X s A.elist δ p l r a b c j t ∧ t.Gs.size = s.Gs.size ∧ t.C.size = s.C.size
  have h0 : I' 0 s := ⟨⟨hX, rfl, EFrame.refl s, ⟨A, hI, rfl⟩, ⟨gh, hG⟩, hp, hs, hl, hr, by omega, by omega,
      Or.inl ⟨rfl, ha, hc⟩, rfl⟩, rfl, rfl⟩
  have hstepM : ∀ j t, I' j t → ∃ bb t', (groupSplitStep p).run t = .ok bb t' ∧ (bb = true → I' (j + 1) t') ∧
      StepAgree κ p t t' bb ∧ t'.Gs.size = s.Gs.size ∧ t'.C.size = s.C.size ∧ t'.E.size = s.E.size := by
    intro j t ⟨hD, hGs, hCs⟩
    have K' : GCaps κ t := ⟨by rw [hGs]; exact K.G, by rw [hD.ef.size]; exact K.E, by rw [hCs]; exact K.C, K.fl, K.f0⟩
    obtain ⟨bb, t', hrun, hA, hG', hC', hE'⟩ := hD.stepAgree hXs hP (by intro z h1 h2 h3; exact hδ z h1 h2 h3) hTlo
      hThi hbal0 (hXc t hD.x) K'
    refine ⟨bb, t', hrun, fun hb => ?_, hA, hG'.trans hGs, hC'.trans hCs, hE'.trans hD.ef.size⟩
    subst hb
    obtain ⟨t1, h1 | h1⟩ := hD.step hXs hP (by intro z h1 h2 h3; exact hδ z h1 h2 h3) hTlo hThi hbal0
    · rw [h1.1] at hrun; injection hrun with _ e; subst e
      exact ⟨h1.2, hG'.trans hGs, hC'.trans hCs⟩
    · rw [h1.1] at hrun; injection hrun with e; cases e
  obtain ⟨s', hA⟩ := driveGroupFromS_agree' κ s I' h0 (fun j t h _ => by
    obtain ⟨bb, t', a1, a2, a3, -⟩ := hstepM j t h; exact ⟨bb, t', a1, a2, a3⟩)
  obtain ⟨t, hrun, hres⟩ := driveGroupFrom_ok (s := s) (p := p) I'
    (fun t => t.Gs.size = s.Gs.size ∧ t.C.size = s.C.size ∧ t.E.size = s.E.size) h0 (fun j t h _ => by
      obtain ⟨bb, t', a1, a2, -, a4, a5, a6⟩ := hstepM j t h
      cases bb
      · exact ⟨t', Or.inr ⟨a1, a4, a5, a6⟩⟩
      · exact ⟨t', Or.inl ⟨a1, a2 rfl⟩⟩)
  rw [hA.1] at hrun; injection hrun with _ e; subst e
  refine ⟨s', hA, ?_⟩
  rcases hres with ⟨hD, hGs, hCs⟩ | h
  · exact ⟨hGs, hCs, hD.ef.size⟩
  · exact h

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

theorem DriveAgree.eq_of_run {κ : Caps} {q : Nat} {s s' s'' : Core} (hA : DriveAgree κ q s s'')
    (h : (driveGroupFrom q).run s = .ok () s') : s'' = s' := by
  rw [hA.1] at h; injection h

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
    (∃ L' n, evalF κ driveGroupS s1 (OM.Machine.State.setLocs (fun _ => 0) ["g"] [g]) = .ok s' L' n ∧
      n ≤ 30 + s1.P.K_G * 401) ∧
    s'.Gs.size ≤ s.Gs.size + 2 ∧ s'.C.size = s.C.size ∧ s'.E.size = s.E.size := by
  have hgl := hI.mem_glist_iff.mpr hg
  have hgT : g < κ.tbl .G := by have := hg.2.1; have := K.G; omega
  have hLg : OM.Machine.State.setLocs (fun _ => 0) ["g"] [g] "g" = g := by
    simp [OM.Machine.State.setLocs, OM.Machine.State.upd]
  have hδle : ∀ p, (fun b => if b = g then 1 else 0) p ≤ gSz s p := by
    intro p; by_cases h : p = g
    · subst h; simp [hpos]
    · simp [h]
  suffices hD : (∀ q, ((s1.Gs.getX g).st = .splitting ∧ q = g ∨
      (s1.Gs.getX g).st = .overflow ∧ q = (s1.Gs.getX g).src) → DriveAgree κ q s1 s') ∧
      s'.Gs.size ≤ s.Gs.size + 2 ∧ s'.C.size = s.C.size ∧ s'.E.size = s.E.size by
    refine ⟨fun hc => ?_, driveGroupS_agree κ s1 _ hLg hgT h2 hD.1, hD.2⟩
    rw [if_pos hc] at h1
    exact startGroupSplitS_agree κ s _ hLg (by omega) K.C (hI.gP_lt hgl) (hI.gN_lt hgl) (hXc s hX g hg)
      (fun x hx => (hI.free x hx).2.1) hF0 hF h1
  · cases hst : gSt s g with
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
        generalize splitState s g labL labR = s1 at hef1 hI1 hG1 hX1 S h2 hsz2 ⊢
        generalize gh.reset (splitL s g) (splitR s g) = gh1 at hG1
        have hg1 : LiveG s1 g := (S.live g).mpr (Or.inr (Or.inr hg))
        have hs1 : gSt s1 g = .splitting := by rw [S.st, if_pos rfl]
        rw [← hel1] at hG1
        have hP1 : GParams s1.P := by rw [S.P]; exact hP
        have hXd : XSteps X Y A1.elist (fun _ => 0) g (gC s1 g) := by
          rw [hel1, S.chk, if_neg (not_or.mpr ⟨S.ggl, S.ggr⟩)]; exact hXg.drive _ g
        have K1 : GCaps κ s1 := ⟨by omega, by rw [S.E]; exact K.E, by rw [S.Csize]; exact K.C, K.fl, K.f0⟩
        obtain ⟨s2, hA, hsz⟩ := ginv_driveAgree hI1 hXd hX1 (hG1.weaken g) hP1 hg1 hs1
          (hG1.split g hg1 hs1 hg1.1) (fun _ _ _ _ => rfl) (by simp) (by simp) hXc K1
        have hs1' : (s1.Gs.getX g).st = .splitting := hs1
        rw [driveGroup_split hs1'] at h2
        have e := hA.eq_of_run h2; subst e
        refine ⟨fun q hq => ?_, by omega, by rw [hsz.2.1, S.Csize], by rw [hsz.2.2, S.E]⟩
        rcases hq with ⟨-, rfl⟩ | ⟨h, -⟩
        · exact hA
        · rw [hs1'] at h; cases h
      · have hc : ¬ ((s.Gs.getX g).st == St.quiet && decide ((s.Gs.getX g).size ≥ s.P.G)) = true := by
          simp only [gSt, gSz] at hst hsz; simp [hst]; omega
        rw [if_neg hc] at h1
        injection h1 with _ e; subst e
        simp only [gSt] at hst
        rw [driveGroup_quiet hst] at h2; injection h2 with _ e; subst e
        refine ⟨fun q hq => ?_, by omega, rfl, rfl⟩
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
      obtain ⟨s2, hA, hsz⟩ := ginv_driveAgree hI hXd hX (hG.weaken (gSrc s g)) hP hp hps
        (hG.split _ hp hps hp.1)
        (by intro z h1 h2 h3; have : z ≠ g := by
              rintro rfl; rcases hlr with e | e <;> [exact h1 e.symm; exact h3 e.symm]
            simp [this])
        hδs ⟨hδle _, hδle _, hδle _⟩ hXc K
      have hst' : (s.Gs.getX g).st = .overflow := hst
      rw [driveGroup_ovf hst'] at h2
      have e := hA.eq_of_run h2; subst e
      refine ⟨fun q hq => ?_, by omega, hsz.2.1, hsz.2.2⟩
      rcases hq with ⟨h, -⟩ | ⟨-, rfl⟩
      · rw [hst'] at h; cases h
      · exact hA
    | splitting =>
      have hc : ¬ ((s.Gs.getX g).st == St.quiet && decide ((s.Gs.getX g).size ≥ s.P.G)) = true := by
        simp only [gSt] at hst; simp [hst]
      rw [if_neg hc] at h1
      injection h1 with _ e; subst e
      have Fp := hG.fam g hg hst
      have hl0 : gLl s g ≠ g := Fp.lp hI hg
      have hr0 : gRr s g ≠ g := Fp.rp hI hg
      obtain ⟨s2, hA, hsz⟩ := ginv_driveAgree hI (hXg.drive _ _) hX (hG.weaken g) hP hg hst
        (hG.split g hg hst hg.1) (by intro z _ h2 _; simp [h2]) (by simp [hl0, hr0])
        ⟨hδle _, hδle _, hδle _⟩ hXc K
      have hst' : (s.Gs.getX g).st = .splitting := hst
      rw [driveGroup_split hst'] at h2
      have e := hA.eq_of_run h2; subst e
      refine ⟨fun q hq => ?_, by omega, hsz.2.1, hsz.2.2⟩
      rcases hq with ⟨-, rfl⟩ | ⟨h, -⟩
      · exact hA
      · rw [hst'] at h; cases h
    | dead => exact absurd hst (hG.notDead g hg)

theorem cremoveState_sizes {t : Core} {x : Nat} :
    (cremoveState t x).Gs.size = t.Gs.size ∧ (cremoveState t x).C.size = t.C.size ∧
      (cremoveState t x).E.size = t.E.size := by
  simp [cremoveState]

theorem _root_.OM.Proof.INV.mem_chunks {s : Core} {A : Abs} (hI : INV s A) {c : Nat} (hc : LiveC s c) :
    c ∈ A.chunks := (hI.cAlloc c).mpr hc

theorem _root_.OM.Proof.INV.cF_lt {s : Core} {A : Abs} (hI : INV s A) {c : Nat} (hc : c ∈ A.chunks) :
    cF s c = NIL ∨ cF s c < s.Gs.size := by
  have hE := (hI.cEnds c hc).1
  rcases h : A.grps c with _ | ⟨g, gs⟩
  · rw [h] at hE; exact Or.inl hE
  · rw [h] at hE; simp only [List.headD_cons] at hE
    exact Or.inr (by rw [hE]; exact hI.gAlloc _ (A.grps_sub_glist hc (by rw [h]; simp)))

theorem _root_.OM.Proof.INV.cLs_lt {s : Core} {A : Abs} (hI : INV s A) {c : Nat} (hc : c ∈ A.chunks) :
    cLs s c = NIL ∨ cLs s c < s.Gs.size := by
  have hE := (hI.cEnds c hc).2
  rcases (A.grps c).eq_nil_or_concat with h | ⟨l, g, h⟩
  · rw [h] at hE; exact Or.inl hE
  · rw [h] at hE; simp at hE
    exact Or.inr (by rw [hE]; exact hI.gAlloc _ (A.grps_sub_glist hc (by rw [h]; simp)))

/-- **A chunk split step of a drive agrees** (the cases of `CDriveInv.step`). -/
theorem _root_.OM.Proof.CDriveInv.stepAgree {X Y : Core → Prop} {s : Core} {L : List Nat} {δ δu s₀ : Nat → Nat}
    {x y z a b c u₀ j : Nat} {t : Core} (hXs : CXSteps X Y L δ δu s₀ x) (hP : GParams s.P)
    (hCP : CParams s.P) (hδ : ∀ c', c' ≠ y → c' ≠ x → c' ≠ z → δ c' = 0)
    (hThi : a + b + c ≤ s.P.T + kC s.P s.P.T)
    (hbal0 : a ≤ c + umax s.P + 1 ∧ c ≤ a + umax s.P + 1)
    (hfam0 : a + b + c ≤ δ y + δ x + δ z + s₀ x + unitsOf s.P (s₀ x) / (s.P.K_C - 1))
    (hδs : δ y + δ x + δ z ≤ 1) (hs0T : s₀ x ≤ s.P.T)
    (hD : CDriveInv X s L δ δu s₀ x y z a b c u₀ j t) {κ : Caps} (K : GCaps κ t) :
    ∃ bb t', (chunkSplitStep x).run t = .ok bb t' ∧ CStepAgree κ x t t' bb ∧ t'.Gs.size = t.Gs.size ∧
      t'.C.size = t.C.size ∧ t'.E.size = t.E.size := by
  obtain ⟨A', hI', hel⟩ := hD.inv
  obtain ⟨gh, hG⟩ := hD.ginv
  subst hel
  have hPt := hD.P
  rw [← hPt] at hP hCP hThi hbal0 hfam0 hs0T
  have hC := hD.cinv
  have Fx := hC.cfam x hD.live hD.st
  have hxy : cLl t x ≠ x := Fx.lx hI' hD.live
  have hxz : cRr t x ≠ x := Fx.rx hI' hD.live
  have hyz : cLl t x ≠ cRr t x := Fx.lr hI' hD.live
  have hsum := hD.sum
  have hcnt := hD.cnt
  have hbal := hD.bal
  rw [← hD.ll, ← hD.rr] at hsum hbal hδ hfam0 hδs
  rw [← hPt] at hbal
  have hFB : FamBound t δ s₀ x := ⟨by omega, hδs, hs0T⟩
  have hI4 := hCP.I4
  unfold cmax at hI4
  by_cases he : cF t x = NIL
  · -- removal
    have hcx : cSz t x = 0 := by rw [hC.csz x hD.live, hI'.celts_empty hD.live he]; rfl
    have hszy' : cSz t (cLl t x) ≤ cmax t.P := by
      unfold cmax; rcases hbal with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
    have hszz' : cSz t (cRr t x) ≤ cmax t.P := by
      unfold cmax; rcases hbal with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
    have hszy : cSz t (cLl t x) ≤ t.P.theta := by
      rcases hbal with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
    have hszz : cSz t (cRr t x) ≤ t.P.theta := by
      rcases hbal with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
    have hrun := chunkSplitStep_remove he hyz hxy hxz hD.live.2 ⟨Fx.lSt, Fx.lSrc⟩ ⟨Fx.rSt, Fx.rSrc⟩
      hszy hszz
    refine ⟨false, _, hrun, fun Lc hLc => ?_, cremoveState_sizes⟩
    obtain ⟨L', n, e, hok, hn⟩ := chunkSplitStepS_remove κ t Lc hLc he hyz hxy hxz hD.live.2 ⟨Fx.lSt, Fx.lSrc⟩
      ⟨Fx.rSt, Fx.rSrc⟩ hszy hszz Fx.lLive.2 Fx.rLive.2 K.C
    exact ⟨L', n, e, by rw [hok]; rfl, by omega⟩
  · -- a move
    obtain ⟨hxc, t0, ht0⟩ := hI'.run_ne_nil he
    have hg0 : cF t x ∈ A'.glist := A'.grps_sub_glist hxc (by rw [ht0]; simp)
    have hg0L := hI'.mem_glist_iff.mp hg0
    have hg0x : gC t (cF t x) = x := hI'.chk x hxc _ (by rw [ht0]; simp)
    by_cases hdir : cSz t (cLl t x) ≤ cSz t (cRr t x)
    · have lu := left_unit hI' hG he
      have hu : (unitCand t x true).length = 1 ∨ unitOK t x (unitCand t x true) = true := by
        rcases lu with ⟨-, h⟩ | ⟨p, -, -, -, -, h⟩
        · left; rw [h]; rfl
        · right; exact h
      obtain ⟨labs, hlabs, hX'⟩ := hXs.moveL t A' gh hI' rfl hG hC hD.live hD.st he hdir hFB hD.xx
      have hrun := chunkSplitStep_left he hdir hu Fx.lAdj hlabs
      have hlen : labs.length = (unitCand t x true).length := pushBackLabs_len hlabs
      have UF := unit_facts (u := unitCand t x true) (x := x) hI' hG hP (by
        rcases lu with ⟨hq, h⟩ | ⟨p, hp, hps, hl, h, hok⟩
        · left; rw [h]; exact ⟨hq, rfl, hg0L, hg0x⟩
        · right
          refine ⟨p, hp, hps, by rw [h, hl], ?_⟩
          rw [h] at hok; exact (unitOK_three hok).2.2.2.2.1)
      obtain ⟨-, hnd, hmem, hone, hcl, hm1, hm2⟩ := UF
      have M := cmoveL_spec (s := t) (x := x) (u := unitCand t x true) (labs := labs)
        (Ne.symm hxy) hD.live.2 Fx.lLive.2 hnd hlen (fun g hg => (hmem g hg).1.2.1)
      refine ⟨true, _, hrun, fun Lc hLc => ?_, M.Gsize, M.Csize, by rw [M.E]⟩
      obtain ⟨L', n, e, hok, -, hn⟩ := chunkSplitStepS_left κ t Lc hLc he hdir hlabs hD.live.2 Fx.lLive.2 Fx.rLive.2
        (Ne.symm hxy) K.C K.G (fun g hg => (hmem g hg).1.2.1) (by have := hg0L.2.1; have := K.G; omega)
        (fun hov => by have h2 : gSrc t (cF t x) < t.Gs.size := (hG.ovf _ hg0L hov).1.2.1; have := K.G; exact lt_of_lt_of_le h2 (by omega))
        (by rcases hI'.cLs_lt (hI'.mem_chunks Fx.lLive) with h | h
            · rw [h]; have := hg0L.2.1; have := K.G; unfold NIL; omega
            · have := K.G; omega)
      exact ⟨L', n, e, by rw [hok]; rfl, by omega⟩
    · have ru := right_unit hI' hG he
      have hu : (unitCand t x false).length = 1 ∨ unitOK t x (unitCand t x false) = true := by
        rcases ru with ⟨-, h⟩ | ⟨p, -, -, -, -, h⟩
        · left; rw [h]; rfl
        · right; exact h
      have hdir' : cSz t (cRr t x) < cSz t (cLl t x) := by omega
      obtain ⟨labs, hlabs, hX'⟩ := hXs.moveR t A' gh hI' rfl hG hC hD.live hD.st he hdir' hFB hD.xx
      have hrun := chunkSplitStep_right he hdir' hu (Fx.radj hI' hD.live) hlabs
      have hlen : labs.length = (unitCand t x false).length := pushFrontLabs_len hlabs
      obtain ⟨hxc', tl, htl⟩ := hI'.run_ne_nil he
      have hE := hI'.cEnds x hxc'
      have hlm : cLs t x ∈ A'.grps x := by rw [hE.2, htl]; exact getLastD_cons_mem _ _ _
      have hgl : cLs t x ∈ A'.glist := A'.grps_sub_glist hxc' hlm
      have UF := unit_facts (u := unitCand t x false) (x := x) hI' hG hP (by
        rcases ru with ⟨hq, h⟩ | ⟨p, hp, hps, hr, h, hok⟩
        · left; rw [h]
          exact ⟨hq, rfl, hI'.mem_glist_iff.mp hgl, hI'.chk x hxc' _ hlm⟩
        · right
          refine ⟨p, hp, hps, by rw [h, hr], ?_⟩
          rw [h] at hok; exact (unitOK_three hok).2.2.2.2.1)
      obtain ⟨-, hnd, hmem, hone, hcl, hm1, hm2⟩ := UF
      have M := cmoveR_spec (s := t) (x := x) (u := unitCand t x false) (labs := labs)
        (Ne.symm hxz) hD.live.2 Fx.rLive.2 hnd hlen (fun g hg => (hmem g hg).1.2.1)
      have hglL := hI'.mem_glist_iff.mp hgl
      refine ⟨true, _, hrun, fun Lc hLc => ?_, M.Gsize, M.Csize, by rw [M.E]⟩
      obtain ⟨L', n, e, hok, -, hn⟩ := chunkSplitStepS_right κ t Lc hLc he hdir' hlabs hD.live.2 Fx.lLive.2 Fx.rLive.2
        (Ne.symm hxz) K.C K.G (fun g hg => (hmem g hg).1.2.1) (by have := hglL.2.1; have := K.G; omega)
        (fun hov => by have h2 : gSrc t (cLs t x) < t.Gs.size := (hG.ovf _ hglL hov).1.2.1; have := K.G; exact lt_of_lt_of_le h2 (by omega))
        (by rcases hI'.cF_lt (hI'.mem_chunks Fx.rLive) with h | h
            · rw [h]; have := hglL.2.1; have := K.G; unfold NIL; omega
            · have := K.G; omega)
      exact ⟨L', n, e, by rw [hok]; rfl, by omega⟩

/-- **The drive of a splitting chunk agrees** (the context of `cinv_drive`). -/
theorem cinv_driveAgree {X Y : Core → Prop} {s : Core} {A : Abs} {gh : GGh} {δ δu s₀ : Nat → Nat} {x : Nat}
    (hI : INV s A) (hG : GInv s A.elist gh (fun _ => 0)) (hC : CInvE s A.elist δ δu s₀ x)
    (hC1 : C1 s δ δu s₀ x) (hXs : CXSteps X Y A.elist δ δu s₀ x) (hX : X s) (hP : GParams s.P)
    (hCP : CParams s.P) (hxL : LiveC s x) (hst : cSt s x = .splitting)
    (hδ : ∀ c, c ≠ cLl s x → c ≠ x → c ≠ cRr s x → δ c = 0)
    (hδs : δ (cLl s x) + δ x + δ (cRr s x) ≤ 1)
    (hδle : δ (cLl s x) ≤ cSz s (cLl s x) ∧ δ x ≤ cSz s x ∧ δ (cRr s x) ≤ cSz s (cRr s x))
    {κ : Caps} (K : GCaps κ s) :
    ∃ s', CDriveAgree κ x s s' ∧ s'.Gs.size = s.Gs.size ∧ s'.C.size = s.C.size ∧ s'.E.size = s.E.size := by
  have Fx := hC.cfam x hxL hst
  generalize hl : cLl s x = y at *
  generalize hr : cRr s x = z at *
  generalize ha : cSz s y = a at *
  generalize hb : cSz s x = b at *
  generalize hc : cSz s z = c at *
  have hK2 := hCP.K2
  unfold C1 at hC1
  rw [hl, hr, ha, hb, hc] at hC1
  obtain ⟨hs0T, g1, g2, g3, g4⟩ := hC1
  generalize hσ : s₀ x = σ at hs0T g1 g2
  generalize hm : s.P.K_C - 1 = m at g2
  have hm1 : 1 ≤ m := by omega
  generalize hX0 : (a - δ y) + (b - δ x) + (c - δ z) - σ = Xs at g2
  have hXq : Xs ≤ unitsOf s.P σ / m := by
    rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]
    have := Nat.le_add_left (m * Xs) (units s x - δu x); omega
  have hU := unitsOf_mono s.P hs0T
  have hUd : unitsOf s.P σ / m ≤ unitsOf s.P s.P.T / m := Nat.div_le_div_right hU
  have hkC : kC s.P s.P.T = unitsOf s.P s.P.T / m + 1 := by unfold kC; rw [hm]
  have hThi : a + b + c ≤ s.P.T + kC s.P s.P.T := by rw [hkC]; omega
  have hbal0 : a ≤ c + umax s.P + 1 ∧ c ≤ a + umax s.P + 1 := by omega
  have hfam0 : a + b + c ≤ δ y + δ x + δ z + s₀ x + unitsOf s.P (s₀ x) / (s.P.K_C - 1) := by
    rw [hσ, hm]; omega
  let I' := fun j t => CDriveInv X s A.elist δ δu s₀ x y z a b c (units s x) j t ∧
    t.Gs.size = s.Gs.size ∧ t.C.size = s.C.size
  have h0 : I' 0 s := ⟨⟨hX, rfl, EFrame.refl s, ⟨A, hI, rfl⟩, ⟨gh, hG⟩, hC, hxL, hst, hl, hr, by omega, by omega,
      Or.inl ⟨rfl, ha, hc⟩⟩, rfl, rfl⟩
  have hs0 : s₀ x ≤ s.P.T := by rw [hσ]; exact hs0T
  have hstepM : ∀ j t, I' j t → ∃ bb t', (chunkSplitStep x).run t = .ok bb t' ∧ (bb = true → I' (j + 1) t') ∧
      CStepAgree κ x t t' bb ∧ t'.Gs.size = s.Gs.size ∧ t'.C.size = s.C.size ∧ t'.E.size = s.E.size := by
    intro j t ⟨hD, hGs, hCs⟩
    have K' : GCaps κ t := ⟨by rw [hGs]; exact K.G, by rw [hD.ef.size]; exact K.E, by rw [hCs]; exact K.C, K.fl, K.f0⟩
    obtain ⟨bb, t', hrun, hA, hG', hC', hE'⟩ := hD.stepAgree hXs hP hCP (by intro c' h1 h2 h3; exact hδ c' h1 h2 h3)
      hThi hbal0 hfam0 hδs hs0 K'
    refine ⟨bb, t', hrun, fun hb => ?_, hA, hG'.trans hGs, hC'.trans hCs, hE'.trans hD.ef.size⟩
    subst hb
    obtain ⟨t1, h1 | h1⟩ := hD.step hXs hP hCP (by intro c' h1 h2 h3; exact hδ c' h1 h2 h3) hThi hbal0 hfam0 hδs hs0
    · rw [h1.1] at hrun; injection hrun with _ e; subst e
      exact ⟨h1.2, hG'.trans hGs, hC'.trans hCs⟩
    · rw [h1.1] at hrun; injection hrun with e; cases e
  obtain ⟨s', hA⟩ := driveChunkFromS_agree' κ s I' h0 (fun j t h _ => by
    obtain ⟨bb, t', a1, a2, a3, -⟩ := hstepM j t h; exact ⟨bb, t', a1, a2, a3⟩)
  obtain ⟨t, hrun, hres⟩ := driveChunkFrom_ok (s := s) (x := x) I'
    (fun t => t.Gs.size = s.Gs.size ∧ t.C.size = s.C.size ∧ t.E.size = s.E.size) h0 (fun j t h _ => by
      obtain ⟨bb, t', a1, a2, -, a4, a5, a6⟩ := hstepM j t h
      cases bb
      · exact ⟨t', Or.inr ⟨a1, a4, a5, a6⟩⟩
      · exact ⟨t', Or.inl ⟨a1, a2 rfl⟩⟩)
  rw [hA.1] at hrun; injection hrun with _ e; subst e
  refine ⟨s', hA, ?_⟩
  rcases hres with ⟨hD, hGs, hCs⟩ | h
  · exact ⟨hGs, hCs, hD.ef.size⟩
  · exact h

theorem CDriveAgree.eq_of_run {κ : Caps} {q : Nat} {s s' s'' : Core} (hA : CDriveAgree κ q s s'')
    (h : (driveChunkFrom q).run s = .ok () s') : s'' = s' := by
  rw [hA.1] at h; injection h

/-- **The chunk phase agrees** (the context of `driveChunk_ok`). -/
theorem driveChunkAgree {t : Core} {A : Abs} {L : List Nat} {gh : GGh} {s₀ δu : Nat → Nat}
    {e : Nat → Nat} {pops c : Nat} (hI : INV t A) (hel : A.elist = L)
    (hG : GInv t L gh (fun _ => 0)) (hC : CInv t L (δ1 c) δu s₀) (hLX : LX s₀ (δ1 c) δu t)
    (hN : CountInv t e pops) (hGP : GParams t.P) (hCP : CParams t.P) (hcL : LiveC t c)
    (hcnd : cSt t c ≠ .dead) (hcsz : 1 ≤ cSz t c) {κ : Caps} (K : GCaps κ t) {t4 : Core}
    (h : (driveChunk c).run t = .ok () t4) :
    (∃ L' n, evalF κ driveChunkS t (OM.Machine.State.setLocs (fun _ => 0) ["x"] [c]) = .ok t4 L' n ∧
      n ≤ 30 + t.P.K_C * 751) ∧ t4.Gs.size = t.Gs.size ∧ t4.C.size = t.C.size ∧ t4.E.size = t.E.size := by
  have hδu := hC.δu
  have hcθ : cmax t.P ≤ t.P.theta := hCP.I4
  have drive : ∀ x, LiveC t x → cSt t x = .splitting →
      (c = cLl t x ∨ c = x ∨ c = cRr t x) → ∃ t4, CDriveAgree κ x t t4 ∧ t4.Gs.size = t.Gs.size ∧
        t4.C.size = t.C.size ∧ t4.E.size = t.E.size := by
    intro x hxL hxs hcx
    subst hel
    have Fx := hC.cfam x hxL hxs
    have hlx := Fx.lx hI hxL
    have hrx := Fx.rx hI hxL
    have hlr := Fx.lr hI hxL
    have hCx : CInvE t A.elist (δ1 c) δu s₀ x :=
      { hC with c1 := fun z hz hzs _ => hC.c1 z hz hzs (by unfold NIL; have := hz.1; omega) }
    have hC1 := hC.c1 x hxL hxs (by unfold NIL; have := hxL.1; omega)
    have hXs := cxsteps_count (cxsteps_dframe (cxsteps_linv (L := A.elist) (δ := δ1 c) (δu := δu)
      (s₀ := s₀) (x := x)) t hcθ)
    exact cinv_driveAgree hI hG hCx hC1 hXs ⟨⟨hLX, DFrame.refl t⟩, e, pops, hN⟩ hGP hCP
      hxL hxs (fun c' h1 h2 h3 => by
        unfold δ1; rw [if_neg]; rintro rfl; rcases hcx with h | h | h <;> contradiction)
      (by unfold δ1; rcases hcx with rfl | rfl | rfl <;> simp [hlx, hrx, hlr, Ne.symm hlx,
        Ne.symm hrx, Ne.symm hlr])
      (by
        unfold δ1
        refine ⟨?_, ?_, ?_⟩ <;> split <;> first | omega | (subst_vars; exact hcsz)) K
  have hxT : c < κ.tbl .C := by have := hcL.2; have := K.C; omega
  have hLx : OM.Machine.State.setLocs (fun _ => 0) ["x"] [c] "x" = c := by
    simp [OM.Machine.State.setLocs, OM.Machine.State.upd]
  cases hs : cSt t c with
  | splitting =>
    have hs' : (t.C.getX c).st = .splitting := hs
    obtain ⟨t5, hA, hsz⟩ := drive c hcL hs (Or.inr (Or.inl rfl))
    rw [driveChunk_split hs'] at h
    have e := hA.eq_of_run h; subst e
    refine ⟨driveChunkS_agree κ t _ hLx hxT (by rw [driveChunk_split hs']; exact h) (fun q hq => ?_), hsz⟩
    rcases hq with ⟨-, rfl⟩ | ⟨h', -⟩
    · exact hA
    · rw [hs'] at h'; cases h'
  | overflow =>
    have hs' : (t.C.getX c).st = .overflow := hs
    obtain ⟨hxL, hxs, hlr⟩ := hC.covf c hcL hs
    obtain ⟨t5, hA, hsz⟩ := drive _ hxL hxs
      (by rcases hlr with h | h; exact Or.inl h.symm; exact Or.inr (Or.inr h.symm))
    rw [driveChunk_ovf hs'] at h
    have e := hA.eq_of_run h; subst e
    refine ⟨driveChunkS_agree κ t _ hLx hxT (by rw [driveChunk_ovf hs']; exact h) (fun q hq => ?_), hsz⟩
    rcases hq with ⟨h', -⟩ | ⟨-, rfl⟩
    · rw [hs'] at h'; cases h'
    · exact hA
  | quiet =>
    have hs' : (t.C.getX c).st = .quiet := hs
    have h' := h
    rw [driveChunk_quiet hs'] at h'; injection h' with _ e; subst e
    refine ⟨driveChunkS_agree κ t _ hLx hxT h (fun q hq => ?_), rfl, rfl, rfl⟩
    rcases hq with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [hs'] at h' <;> cases h'
  | dead => exact absurd hs hcnd

theorem ResAgree.mono {κ : Caps} {t t' : Core} {stop : Bool} {D D' : Nat} (h : ResAgree κ t t' stop D)
    (hD : D ≤ D') : ResAgree κ t t' stop D' := fun L hdn => by
  obtain ⟨L', n, e, h1, h2⟩ := h L hdn; exact ⟨L', n, e, h1, by omega⟩

/-- **The reservation loop agrees**, from Level F's loop invariant and the agreement of each round:
a job step at a state with a job, a split start at a state with none. -/
theorem reservationAgreeOf {κ : Caps} {s : Core} (L : Loc) (I : Nat → Core → Prop) (Q : Core → Prop)
    {DJ DS : Nat} (h0 : I 0 s)
    (hstep : ∀ j t, I j t → j < s.P.K_R →
      (t.resJob = none → (t.pqHi = 0 ∧ Q t) ∨
        (t.pqHi ≠ 0 ∧ ∃ c t1 t2, pqPopMax.run t = .ok c t1 ∧ (splitChunkStart c).run t1 = .ok () t2 ∧
          I (j + 1) t2)) ∧
      (∀ job, t.resJob = some job → ∃ r t1, (jobStep job).run t = .ok r t1 ∧
        I (j + 1) { t1 with resJob := r }))
    (hJ : ∀ j t job, I j t → j < s.P.K_R → t.resJob = some job → JobAgree κ t job DJ)
    (hS : ∀ j t c t1, I j t → j < s.P.K_R → t.resJob = none → t.pqHi ≠ 0 → pqPopMax.run t = .ok c t1 →
      PQCaps κ t ∧ SplitAgree κ t1 c DS) :
    ∃ t' L' n, (reservation s.P.K_R).run s = .ok () t' ∧ evalF κ reservationS s L = .ok t' L' n ∧
      n ≤ 5 + s.P.K_R * (DJ + DS + 340 + 6) := by
  refine reservationS_agree κ s L (D := DJ + DS + 340) (fun j t => I j t) h0 (fun j t hI hj => ?_)
  obtain ⟨hn, hs⟩ := hstep j t hI hj
  cases hjob : t.resJob with
  | none =>
    rcases hn hjob with ⟨hq0, -⟩ | ⟨hq0, c, t1, t2, hp, hsc, hI'⟩
    · exact ⟨true, t, resF_empty hjob hq0, (fun h => absurd h (by decide)), (resAgree_empty hjob hq0).mono (by omega)⟩
    · obtain ⟨hq, hA⟩ := hS j t c t1 hI hj hjob hq0 hp
      exact ⟨false, t2, resF_split hjob hq0 hp hsc, fun _ => hI',
        (resAgree_split hjob hq hq0 hp hA hsc).mono (by omega)⟩
  | some job =>
    obtain ⟨r, t1, hr, hI'⟩ := hs job hjob
    exact ⟨false, _, resF_job hjob hr, fun _ => hI', (resAgree_job hjob (hJ j t job hI hj hjob) hr).mono (by omega)⟩

/-- The cost bound of the reservation loop of one insertion, from the bounds of a job step and a
split start. -/
def resBound (K_R : Nat) : Nat := 5 + K_R * (jobBound + splitBound + 340 + 6)

/-- **The reservation agrees** (the context of `reservation_cost`), relative to a predicate `Mc`
on cores that gives the Level M side conditions and that the rounds keep. -/
theorem reservationAgree_top {TI : Core → Prop} {μ : Core → Nat} {J n R : Nat} {cap : Params → Nat}
    {L : List Nat} {s : Core} {κ : Caps} (Lc : Loc) (hTC : TopContract TI μ J cap) (hTI : ∀ t, TI t → OM.Proof.Top.TopInv t)
    (h0 : ResInv TI s.P.K_R J n R μ L s 0 s) (hn : 1 ≤ n)
    (hsize : 2 + 2 * (s.count / (s.P.theta + 1 - cmax s.P)) ≤ n + 1)
    (hcap : 2 + 2 * (s.count / (s.P.theta + 1 - cmax s.P)) ≤ cap s.P)
    (hI5 : (s.P.theta : ℝ) + R * (OM.Zeroing.Hn (n - 1) + 1) ≤ s.P.T)
    (hpow : s.P.a = 2 ^ Nat.log2 s.P.a)
    (Mc : Core → Prop) (hM0 : Mc s)
    (hMc : ∀ t, Mc t → TopCaps κ t ∧ PQCaps κ t ∧ t.prep = none ∧
      ∀ c, t.C.size ≤ c → ∀ j, (t.path.getX c).getX j = 0)
    (hMpop : ∀ t c, Mc t → Mc (delSt t c))
    (hMjob : ∀ j t job r t1, ResInv TI s.P.K_R J n R μ L s j t → Mc t → t.resJob = some job →
      (jobStep job).run t = .ok r t1 → Mc { t1 with resJob := r })
    (hMsplit : ∀ j t c t1 t2, ResInv TI s.P.K_R J n R μ L s j t → Mc t → pqPopMax.run t = .ok c t1 →
      (splitChunkStart c).run t1 = .ok () t2 → Mc t2) :
    ∃ t' L' m, (reservation s.P.K_R).run s = .ok () t' ∧ evalF κ reservationS s Lc = .ok t' L' m ∧
      m ≤ resBound s.P.K_R := by
  have hstep := resInv_step (k := s.P.K_R) (L := L) hTC hn hsize hcap hI5
  obtain ⟨t', L', m, hrun, he, hm⟩ := reservationAgreeOf (κ := κ) (s := s) Lc
    (fun j t => ResInv TI s.P.K_R J n R μ L s j t ∧ Mc t) (fun _ => True) (DJ := jobBound) (DS := splitBound)
    ⟨h0, hM0⟩
    (fun j t ⟨hI, hM⟩ hj => by
      obtain ⟨hn', hs'⟩ := hstep j t hI hj
      refine ⟨fun hnone => ?_, fun job hjob => ?_⟩
      · rcases hn' hnone with ⟨h0, -⟩ | ⟨h0, c, t1, t2, hp, hsc, hI'⟩
        · exact Or.inl ⟨h0, trivial⟩
        · exact Or.inr ⟨h0, c, t1, t2, hp, hsc, hI', hMsplit j t c t1 t2 hI hM hp hsc⟩
      · obtain ⟨r, t1, hr, hI'⟩ := hs' job hjob
        exact ⟨r, t1, hr, hI', hMjob j t job r t1 hI hM hjob hr⟩)
    (fun j t job ⟨hI, hM⟩ _ hjob => by
      obtain ⟨hT, -, hpr, -⟩ := hMc t hM
      obtain ⟨-, hTt, -, hPt, -⟩ := hI
      exact jobAgree (hTI t hTt) hjob hpr (by rw [hPt]; exact hpow) hT)
    (fun j t c t1 ⟨hI, hM⟩ _ hnone hq0 hp => by
      obtain ⟨hL, hTt, -, -, -⟩ := hI
      obtain ⟨-, hPQ, -⟩ := hMc t hM
      refine ⟨hPQ, ?_⟩
      obtain ⟨bl, nb, hQ⟩ := hL.pq
      obtain ⟨c', hpop, hcin, -⟩ := pqPopMax_ok hQ hq0
      rw [hpop] at hp; injection hp with e1 e2; subst e1; subst e2
      have hcq := hcin
      unfold inQC at hcq; simp only [decide_eq_true_eq] at hcq
      obtain ⟨hcL, -, -⟩ := hcq
      obtain ⟨A, hIA, -⟩ := hL.inv
      have hD := delSt_only t c'
      have hI1 : INV (delSt t c') A := hIA.of_sameLinks hD.sameLinks (fun d => by simp only [cT, hD.C])
      have hT1 : TI (delSt t c') := hTC.frame _ _ hD.topSame hTt
      have hcL1 : LiveC (delSt t c') c' := by simp only [LiveC, hD.C]; exact hcL
      obtain ⟨hTC1, -, hpr1, hrow1⟩ := hMc _ (hMpop t c' hM)
      obtain ⟨D, hD', hA⟩ := splitAgree_top hI1 (hTI _ hT1) (by rw [hD.rest.2.2.2.2.2.2.2.2.1]; exact hnone) hcL1
        hpr1 hrow1 hTC1
      exact fun t2 h => by
        obtain ⟨L', m, e, hm⟩ := hA t2 h
        exact ⟨L', m, e, by omega⟩)
  exact ⟨t', L', m, hrun, he, by unfold resBound; omega⟩

end OM.Impl
