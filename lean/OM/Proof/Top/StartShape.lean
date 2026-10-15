import OM.Proof.Top.StartShapeT

/-!
# M5: the order invariant after a drain starts
-/

namespace OM.Proof.Top

open OM.Model OM.Proof

set_option linter.deprecated false

theorem par_zero' (t : TS) (e : Nat) : par t 0 e = lpr t e := by unfold par; rw [if_pos rfl]

namespace SDCtx

variable {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat} {j : Job} {v : Nat}
  {side : List (Nat × Side)} (C : SDCtx s cl ord dr n0 j v side)
include C

local notation "S'" => ts (sdS (wiC s v) v side)
local notation "O'" => ordSD ord (Top.ht (ts s) v) v s.nodes.size

/-- The children of `v`'s parent after the split of `v`. -/
theorem kidsL : ∃ P Q, (nd (ts s) (nd (ts s) v).livePar).children = P ++ v :: Q ∧ v ∉ P ∧ v ∉ Q ∧
    (nd S' (nd (ts s) v).livePar).children = P ++ s.nodes.size :: (s.nodes.size + 1) :: Q := by
  obtain ⟨hl, hlh, hvL⟩ := C.up
  obtain ⟨P, Q, hPQ⟩ := List.mem_iff_append.mp hvL
  have hnd := (C.S.kids _ hl).1
  rw [hPQ] at hnd
  have h1 := List.nodup_append.mp hnd
  have hP : v ∉ P := fun h => h1.2.2 v h v (by simp) rfl
  have hQ : v ∉ Q := (List.nodup_cons.mp h1.2.1).1
  refine ⟨P, Q, hPQ, hP, hQ, ?_⟩
  have hLv : (nd (ts s) v).livePar ≠ v := C.H.hLv
  have hn := C.nN _ hl.1
  rw [C.children, if_neg hLv, if_neg hn.1, if_neg hn.2, if_pos rfl, hPQ, replace1_split _ hP]; simp

theorem sh_up : ∀ u, Top.liveN S' u → Top.ht S' u < (ts (sdS (wiC s v) v side)).P.H →
    Top.liveN S' (nd S' u).livePar ∧ Top.ht S' (nd S' u).livePar = Top.ht S' u + 1 ∧
      u ∈ (nd S' (nd S' u).livePar).children := by
  intro u hu hH
  have hP' := C.H.P
  have hvlt := C.H.hv
  obtain ⟨hl, hlh, hvL⟩ := C.up
  have hLn := C.nN _ hl.1
  have hLv : (nd (ts s) v).livePar ≠ v := C.H.hLv
  obtain ⟨P, Q, hPQ, hvP, hvQ, hkL⟩ := C.kidsL
  rw [C.liveN] at hu
  rcases hu with ⟨hul, huv⟩ | rfl | rfl
  · have hun := C.nN u hul.1
    have hnn : ¬(u = s.nodes.size ∨ u = s.nodes.size + 1) := fun h => h.elim hun.1 hun.2
    by_cases hk : Top.ht (ts s) v ≠ 1 ∧ u ∈ (nd (ts s) v).children
    · -- a child of `v` goes to `v1` or `v2`
      have huh : Top.ht (ts s) u = Top.ht (ts s) v - 1 := by
        have := ((C.S.mem_children C.vl).mp hk.2).1; rw [if_neg hk.1] at this; exact this.2
      rw [C.livePar, if_neg huv, if_neg hnn, C.ht u, if_neg hnn]
      rcases C.kids_split hk.2 with ⟨a, b⟩ | ⟨a, b⟩
      · rw [if_neg (fun h => b h.2), if_pos ⟨hk.1, a⟩, C.liveN, C.ht s.nodes.size, if_pos (Or.inl rfl), C.children,
          if_neg (by omega), if_pos rfl]
        exact ⟨Or.inr (Or.inl rfl), by have := C.h1; omega, a⟩
      · rw [if_pos ⟨hk.1, b⟩, C.liveN, C.ht (s.nodes.size + 1), if_pos (Or.inr rfl), C.children,
          if_neg (by omega), if_neg (by omega), if_pos rfl]
        exact ⟨Or.inr (Or.inr rfl), by have := C.h1; omega, b⟩
    · rw [C.livePar_old hul.1 huv (fun h1 h => hk ⟨h1, h⟩), C.ht u, if_neg hnn]
      rw [C.ht u, if_neg hnn, hP'] at hH
      obtain ⟨h1, h2, h3⟩ := C.S.up u hul hH
      have hpn := C.nN _ h1.1
      have hpnn : ¬((nd (ts s) u).livePar = s.nodes.size ∨ (nd (ts s) u).livePar = s.nodes.size + 1) :=
        fun h => h.elim hpn.1 hpn.2
      have hpv : (nd (ts s) u).livePar ≠ v := by
        intro e
        apply hk
        have h2' := h2; rw [e] at h2'
        have hh1 : Top.ht (ts s) v ≠ 1 := by
          have := (C.S.htN u hul.1).1; omega
        refine ⟨hh1, (C.S.mem_children C.vl).mpr ⟨by rw [if_neg hh1]; exact ⟨hul, by omega⟩, ?_⟩⟩
        rw [par_live (Or.inr hul), if_neg (by have := (C.S.htN u hul.1).1; omega), e]
      rw [C.liveN, C.ht (nd (ts s) u).livePar, if_neg hpnn, C.children, if_neg hpv,
        if_neg hpn.1, if_neg hpn.2]
      refine ⟨Or.inl ⟨h1, hpv⟩, h2, ?_⟩
      split
      · next he => rw [← he]; exact mem_replace1_of_ne h3 huv
      · exact h3
  all_goals
    have hLnn : ¬((nd (ts s) v).livePar = s.nodes.size ∨ (nd (ts s) v).livePar = s.nodes.size + 1) :=
      fun h => h.elim hLn.1 hLn.2
    rw [C.livePar, if_neg (by omega), if_pos (by omega), C.liveN, C.ht (nd (ts s) v).livePar, if_neg hLnn,
      C.ht _, if_pos (by omega), hkL]
    exact ⟨Or.inl ⟨hl, hLv⟩, hlh, by simp⟩

theorem sh_lp : ∀ c ∈ cl, Top.liveN S' (Top.lpr S' c) ∧ Top.ht S' (Top.lpr S' c) = 1 ∧
    c ∈ (nd S' (Top.lpr S' c)).children := by
  intro c hc
  have hvlt := C.H.hv
  obtain ⟨hcl, hch, hcm⟩ := C.S.lp c hc
  have hcn := C.nN _ hcl.1
  have hcnn : ¬(Top.lpr (ts s) c = s.nodes.size ∨ Top.lpr (ts s) c = s.nodes.size + 1) := fun h => h.elim hcn.1 hcn.2
  rw [C.lpr]
  by_cases h1 : Top.ht (ts s) v = 1
  · rw [if_pos h1]
    by_cases hk : c ∈ (nd (ts s) v).children
    · rcases C.kids_split hk with ⟨a, b⟩ | ⟨a, b⟩
      · rw [if_neg b, if_pos a, C.liveN, C.ht s.nodes.size, if_pos (Or.inl rfl), C.children, if_neg (by omega),
          if_pos rfl]
        exact ⟨Or.inr (Or.inl rfl), h1, a⟩
      · rw [if_pos b, C.liveN, C.ht (s.nodes.size + 1), if_pos (Or.inr rfl), C.children, if_neg (by omega),
          if_neg (by omega), if_pos rfl]
        exact ⟨Or.inr (Or.inr rfl), h1, b⟩
    · rw [if_neg (fun h => hk (List.mem_of_mem_drop h)), if_neg (fun h => hk (List.mem_of_mem_take h))]
      have hcv : Top.lpr (ts s) c ≠ v := by
        intro e; apply hk
        exact (C.S.mem_children C.vl).mpr ⟨by rw [if_pos h1]; exact hc, by
          rw [h1, Nat.sub_self, par_live (Or.inl rfl), if_pos rfl]; exact e⟩
      have hcL : Top.lpr (ts s) c ≠ (nd (ts s) v).livePar := by
        intro e; rw [e] at hch; have := C.up.2.1; omega
      rw [C.liveN, C.ht _, if_neg hcnn, C.children, if_neg hcv, if_neg hcn.1, if_neg hcn.2, if_neg hcL]
      exact ⟨Or.inl ⟨hcl, hcv⟩, hch, hcm⟩
  · rw [if_neg h1]
    have hcv : Top.lpr (ts s) c ≠ v := by intro e; rw [e] at hch; exact h1 hch
    have hcL : Top.lpr (ts s) c ≠ (nd (ts s) v).livePar := by
      intro e; rw [e] at hch; have := C.up.2.1; have := C.h1; omega
    rw [C.liveN, C.ht _, if_neg hcnn, C.children, if_neg hcv, if_neg hcn.1, if_neg hcn.2, if_neg hcL]
    exact ⟨Or.inl ⟨hcl, hcv⟩, hch, hcm⟩

/-- The parent of a live node is its live parent. -/
theorem par_live' {k e : Nat} (hk : k ≠ 0) (he : Top.liveN S' e) : par S' k e = (nd S' e).livePar := by
  unfold par; rw [if_neg hk, if_neg (by rw [he.2]; simp)]

theorem sh_kids : ∀ u, Top.liveN S' u → (nd S' u).children.Nodup ∧
    (nd S' u).children.Sublist (O' (Top.ht S' u - 1)) ∧
    ∀ e ∈ (nd S' u).children, par S' (Top.ht S' u - 1) e = u ∧ (2 ≤ Top.ht S' u → Top.liveN S' e) := by
  intro u hu
  have hvlt := C.H.hv
  have h1v := C.h1
  obtain ⟨hl, hlh, hvL⟩ := C.up
  have hLn := C.nN _ hl.1
  have hLv : (nd (ts s) v).livePar ≠ v := C.H.hLv
  obtain ⟨hknd, hksub, hkk⟩ := C.S.kids v C.vl
  have hO : O' (Top.ht (ts s) v - 1) = ord (Top.ht (ts s) v - 1) := by unfold ordSD; rw [if_neg (by omega)]
  -- the new nodes' children
  have hnew : ∀ (ch : List Nat) (w : Nat), ch.Sublist (nd (ts s) v).children →
      (w = s.nodes.size ∨ w = s.nodes.size + 1) → (nd S' w).children = ch →
      (∀ e ∈ ch, (Top.ht (ts s) v = 1 → Top.lpr S' e = w) ∧ (Top.ht (ts s) v ≠ 1 → (nd S' e).livePar = w)) →
      (nd S' w).children.Nodup ∧ (nd S' w).children.Sublist (O' (Top.ht S' w - 1)) ∧
        ∀ e ∈ (nd S' w).children, par S' (Top.ht S' w - 1) e = w ∧ (2 ≤ Top.ht S' w → Top.liveN S' e) := by
    intro ch w hch hw hc hpar
    rw [hc, C.ht w, if_pos hw, hO]
    refine ⟨hknd.sublist hch, hch.trans hksub, fun e he => ?_⟩
    have hek := hch.subset he
    by_cases h1 : Top.ht (ts s) v = 1
    · rw [h1, Nat.sub_self, par_zero']
      exact ⟨(hpar e he).1 h1, fun h => by omega⟩
    · have hel := (hkk e hek).2 (by omega)
      have hev : e ≠ v := by
        intro e'; have := ((C.S.mem_children C.vl).mp hek).1; rw [if_neg h1, e'] at this; omega
      have hel' : Top.liveN S' e := (C.liveN e).mpr (Or.inl ⟨hel, hev⟩)
      rw [C.par_live' (by omega) hel', (hpar e he).2 h1]
      exact ⟨rfl, fun _ => hel'⟩
  rw [C.liveN] at hu
  rcases hu with ⟨hul, huv⟩ | rfl | rfl
  · have hun := C.nN u hul.1
    have hnn : ¬(u = s.nodes.size ∨ u = s.nodes.size + 1) := fun h => h.elim hun.1 hun.2
    obtain ⟨hund, husub, huk⟩ := C.S.kids u hul
    by_cases huL : u = (nd (ts s) v).livePar
    · -- the parent of `v`
      subst huL
      obtain ⟨P, Q, hPQ, hvP, hvQ, hkL⟩ := C.kidsL
      obtain ⟨A, B, hAB, hA, hB, h'⟩ := C.ordh
      rw [hkL, C.ht _, if_neg hnn, hlh, Nat.add_sub_cancel, h']
      rw [hlh, Nat.add_sub_cancel, hPQ, hAB] at husub
      rw [hPQ] at hund
      have hfr : ∀ x ∈ P ++ v :: Q, x < s.nodes.size := fun x hx => by
        have := husub.subset hx; rw [← hAB] at this
        exact C.fresh h1v (by have := C.hH; omega) this
      have h1 := List.nodup_append.mp hund
      refine ⟨?_, ?_, fun e he => ?_⟩
      · rw [List.nodup_append]
        refine ⟨h1.1, ?_, ?_⟩
        · simp only [List.nodup_cons, List.mem_cons, not_or]
          refine ⟨⟨by omega, fun h => by have := hfr s.nodes.size (by simp [h]); omega⟩,
            fun h => by have := hfr (s.nodes.size + 1) (by simp [h]); omega, (List.nodup_cons.mp h1.2.1).2⟩
        · intro a ha b hb e; subst e
          simp only [List.mem_cons] at hb
          rcases hb with rfl | rfl | hb
          · have := hfr s.nodes.size (by simp [ha]); omega
          · have := hfr (s.nodes.size + 1) (by simp [ha]); omega
          · exact h1.2.2 a ha a (by simp [hb]) rfl
      · obtain ⟨hPA, hQB⟩ := sublist_split_mid husub hA hB
        exact hPA.append (((hQB.cons_cons _).cons _).cons_cons _)
      · have hnewe : ∀ w, (w = s.nodes.size ∨ w = s.nodes.size + 1) →
            par S' (Top.ht (ts s) v) w = (nd (ts s) v).livePar ∧ (2 ≤ Top.ht (ts s) v + 1 → Top.liveN S' w) := by
          intro w hw
          have hwl : Top.liveN S' w := (C.liveN w).mpr (Or.inr hw)
          rw [C.par_live' (by omega) hwl, C.livePar, if_neg (by omega), if_pos hw]
          exact ⟨rfl, fun _ => hwl⟩
        have holde : ∀ e, e ∈ P ∨ e ∈ Q →
            par S' (Top.ht (ts s) v) e = (nd (ts s) v).livePar ∧ (2 ≤ Top.ht (ts s) v + 1 → Top.liveN S' e) := by
          intro e he'
          have hemem : e ∈ (nd (ts s) (nd (ts s) v).livePar).children := by
            rw [hPQ]; rcases he' with h | h <;> simp [h]
          have hev : e ≠ v := by rintro rfl; rcases he' with h | h; exact hvP h; exact hvQ h
          obtain ⟨hp, hlv⟩ := huk e hemem
          have hel := hlv (by omega)
          have hel' : Top.liveN S' e := (C.liveN e).mpr (Or.inl ⟨hel, hev⟩)
          have heh : Top.ht (ts s) e = Top.ht (ts s) v := by
            have := ((C.S.mem_children hl).mp hemem).1; rw [if_neg (by omega)] at this; omega
          rw [C.par_live' (by omega) hel', C.livePar_old hel.1 hev (fun _ hk => by
            have := ((C.S.mem_children C.vl).mp hk).1; rw [if_neg (by omega)] at this; omega)]
          rw [hlh, Nat.add_sub_cancel, par_live (Or.inr hel), if_neg (by omega)] at hp
          exact ⟨hp, fun _ => hel'⟩
        simp only [List.mem_append, List.mem_cons] at he
        rcases he with he | rfl | rfl | he
        · exact holde e (Or.inl he)
        · exact hnewe _ (Or.inl rfl)
        · exact hnewe _ (Or.inr rfl)
        · exact holde e (Or.inr he)
    · rw [C.children, if_neg huv, if_neg hun.1, if_neg hun.2, if_neg huL, C.ht _, if_neg hnn]
      refine ⟨hund, husub.trans (C.ord_sub _), fun e he => ?_⟩
      obtain ⟨hp, hlv⟩ := huk e he
      have huh := (C.S.htN u hul.1).1
      by_cases hu1 : Top.ht (ts s) u = 1
      · rw [hu1, Nat.sub_self, par_zero', C.lpr]
        rw [hu1, Nat.sub_self, par_zero'] at hp
        refine ⟨?_, fun h => by omega⟩
        split
        · next h1 =>
          have hk : e ∉ (nd (ts s) v).children := by
            intro hk
            have := ((C.S.mem_children C.vl).mp hk).2
            rw [h1, Nat.sub_self, par_zero'] at this
            exact huv (hp.symm.trans this)
          rw [if_neg (fun h => hk (List.mem_of_mem_drop h)), if_neg (fun h => hk (List.mem_of_mem_take h))]
          exact hp
        · exact hp
      · have hel := hlv (by omega)
        have hev : e ≠ v := by
          rintro rfl
          rw [par_live (Or.inr hel), if_neg (by omega)] at hp
          exact huL hp.symm
        have hel' : Top.liveN S' e := (C.liveN e).mpr (Or.inl ⟨hel, hev⟩)
        rw [C.par_live' (by omega) hel', C.livePar_old hel.1 hev (fun h1 hk => by
          have := ((C.S.mem_children C.vl).mp hk).2
          rw [par_live (Or.inr hel), if_neg (by
            have := ((C.S.mem_children C.vl).mp hk).1; rw [if_neg h1] at this; omega)] at this
          rw [par_live (Or.inr hel), if_neg (by omega)] at hp
          exact huv (hp.symm.trans this))]
        rw [par_live (Or.inr hel), if_neg (by omega)] at hp
        exact ⟨hp, fun _ => hel'⟩
  · exact hnew _ _ (List.take_sublist _ _) (Or.inl rfl)
      (by rw [C.children, if_neg (by omega), if_pos rfl]) (fun e he => ⟨fun h1 => by
        rw [C.lpr, if_pos h1]
        rcases C.kids_split (List.mem_of_mem_take he) with ⟨a, b⟩ | ⟨a, b⟩
        · rw [if_neg b, if_pos a]
        · exact absurd he a, fun h1 => by
        have hek := List.mem_of_mem_take he
        have hev : e ≠ v := by
          intro e'; have := ((C.S.mem_children C.vl).mp hek).1; rw [if_neg h1, e'] at this; omega
        have hen := C.nN e ((hkk e hek).2 (by omega)).1
        rw [C.livePar, if_neg hev, if_neg (fun h => h.elim hen.1 hen.2)]
        rcases C.kids_split hek with ⟨a, b⟩ | ⟨a, b⟩
        · rw [if_neg (fun h => b h.2), if_pos ⟨h1, a⟩]
        · exact absurd he a⟩)
  · exact hnew _ _ (List.drop_sublist _ _) (Or.inr rfl)
      (by rw [C.children, if_neg (by omega), if_neg (by omega), if_pos rfl]) (fun e he => ⟨fun h1 => by
        rw [C.lpr, if_pos h1, if_pos he], fun h1 => by
        have hek := List.mem_of_mem_drop he
        have hev : e ≠ v := by
          intro e'; have := ((C.S.mem_children C.vl).mp hek).1; rw [if_neg h1, e'] at this; omega
        have hen := C.nN e ((hkk e hek).2 (by omega)).1
        rw [C.livePar, if_neg hev, if_neg (fun h => h.elim hen.1 hen.2), if_pos ⟨h1, he⟩]⟩)

end SDCtx

end OM.Proof.Top
