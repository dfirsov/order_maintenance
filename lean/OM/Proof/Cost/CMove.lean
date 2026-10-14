import OM.Proof.Cost.CSteps

/-!
# The invariants across a chunk-split move and a chunk removal
-/

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-! ### Counting -/

theorem length_filter_split {α : Type} (L : List α) (q P : α → Bool) (h : ∀ a ∈ L, P a → q a) :
    (L.filter fun a => q a && !P a).length + (L.filter P).length = (L.filter q).length := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    have ih' := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a List.mem_cons_self
    simp only [List.filter_cons]
    cases hp : P a <;> cases hq : q a <;> simp_all <;> omega

theorem length_filter_or {α : Type} (L : List α) (q P : α → Bool) (h : ∀ a ∈ L, P a → q a = false) :
    (L.filter fun a => q a || P a).length = (L.filter q).length + (L.filter P).length := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    have ih' := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a List.mem_cons_self
    simp only [List.filter_cons]
    cases hp : P a <;> cases hq : q a <;> simp_all <;> omega

/-- The elements in a set of groups, counted group by group. -/
theorem length_filter_mem (s : Core) (L : List Nat) (u : List Nat) (hnd : u.Nodup) :
    (L.filter fun e => decide (eG s e ∈ u)).length = (u.map fun g => (runOf s L g).length).sum := by
  induction u with
  | nil => simp
  | cons g u ih =>
    simp only [List.nodup_cons] at hnd
    have := length_filter_or L (fun e => decide (eG s e ∈ u)) (fun e => decide (eG s e = g))
      (fun e _ he => by simp at he ⊢; rw [he]; exact hnd.1)
    simp only [List.map_cons, List.sum_cons]
    rw [← ih hnd.2]
    unfold runOf
    have e1 : (L.filter fun e => decide (eG s e ∈ g :: u)) =
        L.filter (fun e => decide (eG s e ∈ u) || decide (eG s e = g)) := by
      congr 1; funext e; simp only [List.mem_cons]; rw [Bool.or_comm]; simp
    rw [e1, this]; omega

end OM.Proof

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-! ### The group invariant across a chunk-split move (invariant F) -/

theorem CMoveSpec.gfields {s s' : Core} {x dst : Nat} {u labs : List Nat}
    (M : CMoveSpec s s' x dst u labs) (g : Nat) :
    gSz s' g = gSz s g ∧ gSt s' g = gSt s g ∧ gSrc s' g = gSrc s g ∧ gLl s' g = gLl s g ∧
      gRr s' g = gRr s g ∧ gN s' g = gN s g ∧ gA s' g = gA s g ∧ gP s' g = gP s g ∧
      gF s' g = gF s g ∧ gLs s' g = gLs s g ∧
      gC s' g = (if g ∈ u then dst else gC s g) := by
  simp only [gSz, gSt, gSrc, gLl, gRr, gN, gA, gP, gF, gLs, gC, M.G g]
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem CMoveSpec.liveG {s s' : Core} {x dst : Nat} {u labs : List Nat}
    (M : CMoveSpec s s' x dst u labs) (g : Nat) : LiveG s' g ↔ LiveG s g := by
  simp only [LiveG, M.Gsize, (M.gfields g).2.2.2.2.2.2.1]

theorem CMoveSpec.runOf {s s' : Core} {x dst : Nat} {u labs : List Nat}
    (M : CMoveSpec s s' x dst u labs) (L : List Nat) (g : Nat) : runOf s' L g = runOf s L g := by
  unfold OM.Proof.runOf; simp only [eG, M.E]

theorem CMoveSpec.eL {s s' : Core} {x dst : Nat} {u labs : List Nat}
    (M : CMoveSpec s s' x dst u labs) : eL s' = eL s := by
  funext e; simp only [OM.Proof.eL, M.E]

/-- A set of groups closed under families. -/
def FamClosed (s : Core) (u : List Nat) : Prop :=
  ∀ p, LiveG s p → gSt s p = .splitting → (gLl s p ∈ u ↔ p ∈ u) ∧ (gRr s p ∈ u ↔ p ∈ u)

theorem ginv_cmove {s s' : Core} {L : List Nat} {gh : GGh} {δ : Nat → Nat} {ex x dst : Nat}
    {u labs : List Nat} (hG : GInvE s L gh δ ex) (M : CMoveSpec s s' x dst u labs)
    (hcl : FamClosed s u) : GInvE s' L gh δ ex := by
  have F := M.gfields
  have hL := M.liveG
  have hR := M.runOf L
  have hfam : ∀ p, famT s' p = famT s p := by intro p; simp only [famT, (F _).1, (F _).2.2.2.1, (F _).2.2.2.2.1]
  refine
    { sz := ?_, fam := ?_, ovf := ?_, notDead := ?_, quiet := ?_, split := ?_, gaps := ?_,
      range := ?_, ghQ := ?_, ghO := ?_, ghS := ?_ }
  · intro g hg; rw [hL] at hg; rw [(F g).1, hR]; exact hG.sz g hg
  · intro p hp hs
    rw [hL] at hp; rw [(F p).2.1] at hs
    have Fp := hG.fam p hp hs
    obtain ⟨c1, c2⟩ := hcl p hp hs
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [(F p).2.2.2.1, hL]; exact Fp.lLive
    · rw [(F p).2.2.2.2.1, hL]; exact Fp.rLive
    · rw [(F p).2.2.2.1, (F _).2.2.2.2.2.1]; exact Fp.lAdj
    · rw [(F p).2.2.2.2.1, (F p).2.2.2.2.2.1]; exact Fp.rAdj
    · rw [(F p).2.2.2.1, (F _).2.1]; exact Fp.lSt
    · rw [(F p).2.2.2.1, (F _).2.2.1]; exact Fp.lSrc
    · rw [(F p).2.2.2.2.1, (F _).2.1]; exact Fp.rSt
    · rw [(F p).2.2.2.2.1, (F _).2.2.1]; exact Fp.rSrc
    · rw [(F p).2.2.2.1, (F _).2.2.2.2.2.2.2.2.2.2, (F p).2.2.2.2.2.2.2.2.2.2]
      by_cases hpu : p ∈ u
      · rw [if_pos (c1.mpr hpu), if_pos hpu]
      · rw [if_neg (fun h => hpu (c1.mp h)), if_neg hpu]; exact Fp.lC
    · rw [(F p).2.2.2.2.1, (F _).2.2.2.2.2.2.2.2.2.2, (F p).2.2.2.2.2.2.2.2.2.2]
      by_cases hpu : p ∈ u
      · rw [if_pos (c2.mpr hpu), if_pos hpu]
      · rw [if_neg (fun h => hpu (c2.mp h)), if_neg hpu]; exact Fp.rC
  · intro g hg hs
    rw [hL] at hg; rw [(F g).2.1] at hs
    have := hG.ovf g hg hs
    rw [(F g).2.2.1, hL, (F _).2.1, (F _).2.2.2.1, (F _).2.2.2.2.1]; exact this
  · intro g hg; rw [hL] at hg; rw [(F g).2.1]; exact hG.notDead g hg
  · intro g hg hs
    rw [hL] at hg; rw [(F g).2.1] at hs
    rw [(F g).1, M.P, M.head, hR]; exact hG.quiet g hg hs
  · intro g hg hs hx
    rw [hL] at hg; rw [(F g).2.1] at hs
    have := hG.split g hg hs hx
    unfold G1 at this ⊢
    rw [M.P, (F g).2.2.2.1, (F g).2.2.2.2.1, (F _).1, (F g).1, (F _).1]; exact this
  · intro g hg; rw [hL] at hg; rw [hR, M.eL, M.P]; exact hG.gaps g hg
  · intro g hg e he; rw [hL] at hg; rw [hR] at he; rw [M.eL, M.P]; exact hG.range g hg e he
  · intro g hg hs; rw [hL] at hg; rw [(F g).2.1] at hs; rw [(F g).1, M.P]; exact hG.ghQ g hg hs
  · intro g hg hs; rw [hL] at hg; rw [(F g).2.1] at hs
    rw [(F g).1, M.P, (F g).2.2.1, hfam]; exact hG.ghO g hg hs
  · intro g hg hs; rw [hL] at hg; rw [(F g).2.1] at hs; rw [M.P, hfam]; exact hG.ghS g hg hs

end OM.Proof

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-! ### The chunk invariant across a chunk-split move -/

theorem units_erase1 {s s' : Core} {c c' a : Nat} (ha : UnitG s c a) (ha' : ¬ UnitG s' c' a)
    (h : ∀ g, g ≠ a → (UnitG s' c' g ↔ UnitG s c g)) : units s' c' + 1 = units s c := by
  unfold units
  have hS : (Finset.range s'.Gs.size).filter (UnitG s' c') =
      ((Finset.range s.Gs.size).filter (UnitG s c)).erase a := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
    by_cases hg : g = a
    · subst hg; simp only [ne_eq, not_true_eq_false, false_and, iff_false]
      exact fun ⟨_, h'⟩ => ha' h'
    · simp only [ne_eq, hg, not_false_eq_true, true_and]
      constructor
      · rintro ⟨_, h'⟩; have := (h g hg).mp h'; exact ⟨this.1.2.1, this⟩
      · rintro ⟨_, h'⟩; have := (h g hg).mpr h'; exact ⟨this.1.2.1, this⟩
  rw [hS, Finset.card_erase_of_mem (by simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨ha.1.2.1, ha⟩)]
  have : 0 < ((Finset.range s.Gs.size).filter (UnitG s c)).card :=
    Finset.card_pos.mpr ⟨a, by simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨ha.1.2.1, ha⟩⟩
  omega

theorem CFamOK.disjoint {s : Core} {x x' : Nat} (F : CFamOK s x) (F' : CFamOK s x') (hxx : x ≠ x')
    (hs : cSt s x = .splitting) (hs' : cSt s x' = .splitting) :
    x' ≠ cLl s x ∧ x' ≠ cRr s x ∧ cLl s x' ≠ x ∧ cRr s x' ≠ x ∧ cLl s x' ≠ cLl s x ∧
      cLl s x' ≠ cRr s x ∧ cRr s x' ≠ cLl s x ∧ cRr s x' ≠ cRr s x := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e; have := F.lSt; rw [← e, hs'] at this; cases this
  · intro e; have := F.rSt; rw [← e, hs'] at this; cases this
  · intro e; have := F'.lSt; rw [e, hs] at this; cases this
  · intro e; have := F'.rSt; rw [e, hs] at this; cases this
  · intro e; have h1 := F'.lSrc; rw [e, F.lSrc] at h1; exact hxx h1
  · intro e; have h1 := F'.lSrc; rw [e, F.rSrc] at h1; exact hxx h1
  · intro e; have h1 := F'.rSrc; rw [e, F.lSrc] at h1; exact hxx h1
  · intro e; have h1 := F'.rSrc; rw [e, F.rSrc] at h1; exact hxx h1

theorem cinv_cmove {s s' : Core} {A : Abs} {gh : GGh} {δ δu : Nat → Nat} {x dst : Nat}
    {u labs : List Nat} (hI : INV s A) (hG : GInv s A.elist gh (fun _ => 0))
    (hC : CInvE s A.elist δ δu x) (M : CMoveSpec s s' x dst u labs) (hxL : LiveC s x)
    (hst : cSt s x = .splitting) (hdst : dst = cLl s x ∨ dst = cRr s x) (hxd : x ≠ dst)
    (hu : ∀ g ∈ u, LiveG s g ∧ gC s g = x) (hnd : u.Nodup)
    (hone : ∃ um ∈ u, UnitG s x um ∧ ∀ g ∈ u, g ≠ um → gSt s g = .overflow) :
    CInvE s' A.elist δ δu x ∧ units s' x + 1 = units s x ∧
      (u.map fun g => gSz s g).sum ≤ cSz s x := by
  have F := M.gfields
  have Fx := hC.cfam x hxL hst
  have hdL : LiveC s dst := by rcases hdst with rfl | rfl; exact Fx.lLive; exact Fx.rLive
  have hdst' : cSt s dst = .overflow := by rcases hdst with rfl | rfl; exact Fx.lSt; exact Fx.rSt
  have hLC : ∀ c, LiveC s' c ↔ LiveC s c := by intro c; simp only [LiveC, M.Csize]
  -- counting the moved elements
  set moved := (u.map fun g => gSz s g).sum with hmoved
  have hP : (A.elist.filter fun e => decide (eG s e ∈ u)).length = moved := by
    rw [length_filter_mem s A.elist u hnd, hmoved]
    congr 1
    refine List.map_congr_left fun g hg => ?_
    rw [hG.sz g (hu g hg).1]
  have hPq : ∀ e ∈ A.elist, decide (eG s e ∈ u) = true → decide (gC s (eG s e) = x) = true := by
    intro e _ he; simp at he ⊢; exact (hu _ he).2
  have hgC' : ∀ e, gC s' (eG s' e) = if eG s e ∈ u then dst else gC s (eG s e) := by
    intro e; simp only [eG, M.E]; exact (F _).2.2.2.2.2.2.2.2.2.2
  have hcx : (celts s' A.elist x).length + moved = (celts s A.elist x).length := by
    have := length_filter_split A.elist (fun e => decide (gC s (eG s e) = x))
      (fun e => decide (eG s e ∈ u)) hPq
    rw [hP] at this
    unfold celts
    rw [← this]
    congr 2
    refine List.filter_congr fun e _ => ?_
    rw [hgC']
    by_cases he : eG s e ∈ u
    · simp [he, Ne.symm hxd]
    · simp [he]
  have hcd : (celts s' A.elist dst).length = (celts s A.elist dst).length + moved := by
    have := length_filter_or A.elist (fun e => decide (gC s (eG s e) = dst))
      (fun e => decide (eG s e ∈ u)) (fun e _ he => by
        simp at he ⊢; rw [(hu _ he).2]; exact hxd)
    rw [hP] at this
    unfold celts
    rw [← this]
    congr 1
    refine List.filter_congr fun e _ => ?_
    rw [hgC']
    by_cases he : eG s e ∈ u
    · simp [he]
    · simp [he]
  have hco : ∀ c, c ≠ x → c ≠ dst → celts s' A.elist c = celts s A.elist c := by
    intro c h1 h2
    unfold celts
    refine List.filter_congr fun e _ => ?_
    rw [hgC']
    by_cases he : eG s e ∈ u
    · simp only [he, if_true]; rw [(hu _ he).2]; simp [Ne.symm h1, Ne.symm h2]
    · simp [he]
  have hle : moved ≤ cSz s x := by rw [hC.csz x hxL]; omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hC.δu⟩, ?_, hle⟩
  · intro c hc
    rw [hLC] at hc
    rw [M.csz]
    by_cases h1 : c = x
    · subst h1; rw [if_pos rfl, hC.csz c hc]; omega
    · by_cases h2 : c = dst
      · subst h2; rw [if_neg h1, if_pos rfl, hC.csz c hc, hcd]
      · rw [if_neg h1, if_neg h2, hco c h1 h2]; exact hC.csz c hc
  · intro y hy hys
    rw [hLC] at hy; rw [M.cst] at hys
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hC.cfam y hy hys
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [hLC, M.cl, M.cr, M.cnext, M.cst, M.csrc] <;> assumption
  · intro c hc hcs
    rw [hLC] at hc; rw [M.cst] at hcs
    have := hC.covf c hc hcs
    simp only [hLC, M.csrc, M.cst, M.cl, M.cr]; exact this
  · intro g hg
    rw [M.liveG] at hg
    rw [hLC, M.cst, (F g).2.2.2.2.2.2.2.2.2.2]
    split
    · rw [hdst']; exact ⟨hdL, by simp⟩
    · exact hC.gchk g hg
  · intro y hy hys hyx
    rw [hLC] at hy; rw [M.cst] at hys
    have Fy := hC.cfam y hy hys
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := Fx.disjoint Fy (Ne.symm hyx) hst hys
    have hyd : y ≠ dst := by rcases hdst with rfl | rfl; exact d1; exact d2
    have hly : cLl s y ≠ dst := by rcases hdst with rfl | rfl; exact d5; exact d6
    have hry : cRr s y ≠ dst := by rcases hdst with rfl | rfl; exact d7; exact d8
    have hu' : units s' y = units s y := by
      apply units_congr
      intro g
      unfold UnitG
      rw [M.liveG, (F g).2.2.2.2.2.2.2.2.2.2, (F g).2.1]
      split
      · next hgu => simp only [Ne.symm hyd, false_and, and_false, false_iff, not_and]
                    intro _ h; exact absurd ((hu g hgu).2 ▸ h) (Ne.symm hyx)
      · rfl
    have := hC.c1 y hy hys hyx
    unfold C1 at this ⊢
    rw [M.P, M.cl, M.cr, M.csz, M.csz, M.csz, if_neg hyx, if_neg hyd, if_neg d3, if_neg hly,
      if_neg d4, if_neg hry, hu']
    exact this
  · obtain ⟨um, hum, humU, hrest⟩ := hone
    refine units_erase1 humU ?_ ?_
    · intro h; have := h.2.1; rw [(F um).2.2.2.2.2.2.2.2.2.2, if_pos hum] at this; exact hxd this.symm
    · intro g hg
      unfold UnitG
      rw [M.liveG, (F g).2.2.2.2.2.2.2.2.2.2, (F g).2.1]
      by_cases hgu : g ∈ u
      · rw [if_pos hgu]
        simp only [Ne.symm hxd, false_and, and_false, false_iff, not_and]
        intro _ _; rw [hrest g hgu hg]; simp
      · rw [if_neg hgu]

end OM.Proof
