import OM.Proof.Top.StartShapeT

/-!
# M5: the order invariant after a drain starts
-/

namespace OM.Proof.Top

open OM.Model OM.Proof

set_option linter.deprecated false

theorem par_zero' (t : TS) (e : Nat) : par t 0 e = lpr t e := by unfold par; rw [if_pos rfl]

theorem infix_filter {T l : List Nat} {p : Nat → Bool} (h : T <:+: l) (hp : ∀ x ∈ T, p x = true) :
    T <:+: l.filter p := by
  obtain ⟨u, w, rfl⟩ := h
  rw [List.filter_append, List.filter_append, List.filter_eq_self.mpr hp]
  exact ⟨u.filter p, w.filter p, rfl⟩

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

theorem sh_src : ∀ t, Top.liveN S' t → Top.srcOf S' t ≠ NIL →
    Top.ghostN S' (Top.srcOf S' t) ∧ (t = (nd S' (Top.srcOf S' t)).t1 ∨ t = (nd S' (Top.srcOf S' t)).t2) := by
  intro t ht hs
  have hvlt := C.H.hv
  rw [C.liveN] at ht
  rcases ht with ⟨htl, htv⟩ | rfl | rfl
  · have htn := C.nN t htl.1
    have htnn : ¬(t = s.nodes.size ∨ t = s.nodes.size + 1) := fun h => h.elim htn.1 htn.2
    rw [C.srcOf t, if_neg htnn] at hs ⊢
    obtain ⟨hg, htg⟩ := C.S.src t htl hs
    have hgv : Top.srcOf (ts s) t ≠ v := fun e => by rw [e] at hg; exact absurd hg.2 (by rw [C.vl.2]; simp)
    refine ⟨(C.ghostN _).mpr (Or.inl hg), ?_⟩
    rw [C.H.t1, C.H.t2, if_neg hgv, if_neg hgv, if_neg (fun h => h.elim (C.nN _ hg.1).1 (C.nN _ hg.1).2),
      if_neg (fun h => h.elim (C.nN _ hg.1).1 (C.nN _ hg.1).2)]
    exact htg
  · rw [C.srcOf _, if_pos (Or.inl rfl)]
    exact ⟨(C.ghostN v).mpr (Or.inr rfl), Or.inl (by rw [C.H.t1, if_pos rfl])⟩
  · rw [C.srcOf _, if_pos (Or.inr rfl)]
    exact ⟨(C.ghostN v).mpr (Or.inr rfl), Or.inr (by rw [C.H.t2, if_pos rfl])⟩

theorem sh_ghost : ∀ g, Top.ghostN S' g →
    Top.liveN S' (nd S' g).t1 ∧ Top.liveN S' (nd S' g).t2 ∧ Top.ht S' (nd S' g).t1 = Top.ht S' g ∧
      Top.ht S' (nd S' g).t2 = Top.ht S' g ∧ Top.srcOf S' (nd S' g).t1 = g ∧ Top.srcOf S' (nd S' g).t2 = g ∧
      (nd S' g).livePar = NIL ∧ (nd S' g).children = [] ∧ Top.srcOf S' g = NIL ∧
      Top.ht S' g < (ts (sdS (wiC s v) v side)).P.H ∧
      (nd S' (nd S' g).t1).livePar = (nd S' (nd S' g).t2).livePar ∧
      [(nd S' g).t1, (nd S' g).t2] <:+: (nd S' (nd S' (nd S' g).t1).livePar).children ∧
      [(nd S' g).t1, g, (nd S' g).t2] <:+: O' (Top.ht S' g) := by
  intro g hg
  have hvlt := C.H.hv
  have hP' := C.H.P
  have hvn := C.nN v C.vl.1
  have hvnn : ¬(v = s.nodes.size ∨ v = s.nodes.size + 1) := fun h => h.elim hvn.1 hvn.2
  obtain ⟨hl, hlh, hvL⟩ := C.up
  have hLn := C.nN _ hl.1
  have hLv : (nd (ts s) v).livePar ≠ v := C.H.hLv
  obtain ⟨P, Q, hPQ, hvP, hvQ, hkL⟩ := C.kidsL
  rw [C.ghostN] at hg
  rcases hg with hg | hgv'
  · have hgv : g ≠ v := fun e => by rw [e] at hg; exact absurd hg.2 (by rw [C.vl.2]; simp)
    have hgn := C.nN g hg.1
    have hgnn : ¬(g = s.nodes.size ∨ g = s.nodes.size + 1) := fun h => h.elim hgn.1 hgn.2
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ := C.S.ghost g hg
    rw [C.H.t1, C.H.t2, if_neg hgv, if_neg hgv, if_neg hgnn, if_neg hgnn]
    have ht1v : (nd (ts s) g).t1 ≠ v := fun e => by rw [e] at g5; rw [show Top.srcOf (ts s) v = NIL from C.of] at g5; exact hg.1.1 g5.symm
    have ht2v : (nd (ts s) g).t2 ≠ v := fun e => by rw [e] at g6; rw [show Top.srcOf (ts s) v = NIL from C.of] at g6; exact hg.1.1 g6.symm
    have h1n := C.nN _ g1.1
    have h2n := C.nN _ g2.1
    have h1nn : ¬((nd (ts s) g).t1 = s.nodes.size ∨ (nd (ts s) g).t1 = s.nodes.size + 1) := fun h => h.elim h1n.1 h1n.2
    have h2nn : ¬((nd (ts s) g).t2 = s.nodes.size ∨ (nd (ts s) g).t2 = s.nodes.size + 1) := fun h => h.elim h2n.1 h2n.2
    have hgL : g ≠ (nd (ts s) v).livePar := fun e => by rw [e] at hg; exact absurd hg.2 (by rw [hl.2]; simp)
    have hgk : Top.ht (ts s) v ≠ 1 → g ∉ (nd (ts s) v).children := fun h1 hk => by
      obtain ⟨-, -, hkk⟩ := C.S.kids v C.vl
      have := (hkk g hk).2 (by have := C.h1; omega); exact absurd hg.2 (by rw [this.2]; simp)
    have hp1l := (C.S.up _ g1 (by rw [g3]; exact g10)).1
    have hab : (nd S' (nd (ts s) g).t1).livePar = (nd S' (nd (ts s) g).t2).livePar ∧
        [(nd (ts s) g).t1, (nd (ts s) g).t2] <:+: (nd S' (nd S' (nd (ts s) g).t1).livePar).children := by
      by_cases hk : Top.ht (ts s) v ≠ 1 ∧ (nd (ts s) g).t1 ∈ (nd (ts s) v).children
      · -- targets among the children of `v`
        have hp1 : (nd (ts s) (nd (ts s) g).t1).livePar = v := by
          obtain ⟨-, hp⟩ := (C.S.mem_children C.vl).mp hk.2
          rw [par_live (Or.inr g1), if_neg (by
            have := ((C.S.mem_children C.vl).mp hk.2).1; rw [if_neg hk.1] at this; have := C.h1; omega)] at hp
          exact hp
        have g12' := g12
        rw [hp1] at g12'
        have hk2 : (nd (ts s) g).t2 ∈ (nd (ts s) v).children := g12'.subset (by simp)
        have hns := sw_nosep' C.pc C.v0 C.I C.lp C.TP C.of C.W C.look (by have := C.h1; omega) g12' hg.1.1 g5 g6
        obtain ⟨hknd, -, -⟩ := C.S.kids v C.vl
        rw [C.livePar _, if_neg ht1v, if_neg h1nn, C.livePar (nd (ts s) g).t2, if_neg ht2v, if_neg h2nn]
        rcases C.kids_split hk.2 with ⟨a, b⟩ | ⟨a, b⟩
        · have a2 := hns.mp a
          have b2 : (nd (ts s) g).t2 ∉ (nd (ts s) v).children.drop (sK (wiC s v) v) := by
            rcases C.kids_split hk2 with ⟨-, h⟩ | ⟨h, -⟩
            · exact h
            · exact absurd a2 h
          rw [if_neg (fun h => b h.2), if_pos ⟨hk.1, a⟩, if_neg (fun h => b2 h.2), if_pos ⟨hk.1, a2⟩]
          refine ⟨rfl, ?_⟩
          rw [C.children, if_neg (by omega), if_pos rfl]
          exact infix_take hknd g12' a2
        · have a2 : (nd (ts s) g).t2 ∉ (nd (ts s) v).children.take (sK (wiC s v) v) := fun h => a (hns.mpr h)
          have b2 : (nd (ts s) g).t2 ∈ (nd (ts s) v).children.drop (sK (wiC s v) v) := by
            rcases C.kids_split hk2 with ⟨h, -⟩ | ⟨-, h⟩
            · exact absurd h a2
            · exact h
          rw [if_pos ⟨hk.1, b⟩, if_pos ⟨hk.1, b2⟩]
          refine ⟨rfl, ?_⟩
          rw [C.children, if_neg (by omega), if_neg (by omega), if_pos rfl]
          exact infix_drop hknd g12' b
      · have hk2 : Top.ht (ts s) v ≠ 1 → (nd (ts s) g).t2 ∉ (nd (ts s) v).children := by
          intro h1 hk2
          apply hk; refine ⟨h1, (C.S.mem_children C.vl).mpr ⟨?_, ?_⟩⟩
          · rw [if_neg h1]
            have := ((C.S.mem_children C.vl).mp hk2).1; rw [if_neg h1] at this
            exact ⟨g1, by rw [g3, ← g4]; exact this.2⟩
          · have := ((C.S.mem_children C.vl).mp hk2).2
            have hh : Top.ht (ts s) v - 1 ≠ 0 := by have := C.h1; omega
            rw [par_live (Or.inr g2), if_neg hh] at this
            rw [par_live (Or.inr g1), if_neg hh, g11]; exact this
        rw [C.livePar_old g1.1 ht1v (fun h1 h => hk ⟨h1, h⟩), C.livePar_old g2.1 ht2v hk2]
        refine ⟨g11, ?_⟩
        have hpv : (nd (ts s) (nd (ts s) g).t1).livePar ≠ v := by
          intro e
          by_cases h1 : Top.ht (ts s) v = 1
          · obtain ⟨-, hh, -⟩ := C.S.up _ g1 (by rw [g3]; exact g10)
            rw [e, h1] at hh; have := (C.S.htN _ g1.1).1; omega
          · apply hk; refine ⟨h1, (C.S.mem_children C.vl).mpr ⟨?_, ?_⟩⟩
            · rw [if_neg h1]
              obtain ⟨-, hh, -⟩ := C.S.up _ g1 (by rw [g3]; exact g10)
              rw [e] at hh; exact ⟨g1, by omega⟩
            · rw [par_live (Or.inr g1), if_neg (by have := C.h1; omega), e]
        have hpn := C.nN _ hp1l.1
        rw [C.children, if_neg hpv, if_neg hpn.1, if_neg hpn.2]
        split
        · next he => rw [← he]; exact infix_replace1 g12 (by simp [ht1v, ht2v, Ne.symm ht1v, Ne.symm ht2v])
        · exact g12
    refine ⟨(C.liveN _).mpr (Or.inl ⟨g1, ht1v⟩), (C.liveN _).mpr (Or.inl ⟨g2, ht2v⟩),
      by rw [C.ht _, if_neg h1nn, C.ht g, if_neg hgnn]; exact g3,
      by rw [C.ht _, if_neg h2nn, C.ht g, if_neg hgnn]; exact g4,
      by rw [C.srcOf _, if_neg h1nn]; exact g5, by rw [C.srcOf _, if_neg h2nn]; exact g6,
      by rw [C.livePar_old hg.1 hgv hgk]; exact g7,
      by rw [C.children, if_neg hgv, if_neg hgn.1, if_neg hgn.2, if_neg hgL]; exact g8,
      by rw [C.srcOf g, if_neg hgnn]; exact g9,
      by rw [C.ht g, if_neg hgnn, hP']; exact g10, hab.1, hab.2, ?_⟩
    -- the triple in the order
    rw [C.ht g, if_neg hgnn]
    unfold ordSD
    split
    · next he =>
      rw [he] at g13
      exact infix_replace1 g13 (by simp [ht1v, hgv, ht2v, Ne.symm ht1v, Ne.symm hgv, Ne.symm ht2v])
    · exact g13
  · -- the new ghost `v`
    rw [hgv']
    obtain ⟨A, B, hAB, hA, hB, h'⟩ := C.ordh
    have hN : Top.liveN S' s.nodes.size := (C.liveN _).mpr (Or.inr (Or.inl rfl))
    have hN1 : Top.liveN S' (s.nodes.size + 1) := (C.liveN _).mpr (Or.inr (Or.inr rfl))
    rw [C.H.t1, C.H.t2, if_pos rfl, if_pos rfl]
    have lN : (nd S' s.nodes.size).livePar = (nd (ts s) v).livePar := by
      rw [C.livePar, if_neg (by omega), if_pos (Or.inl rfl)]
    have lN1 : (nd S' (s.nodes.size + 1)).livePar = (nd (ts s) v).livePar := by
      rw [C.livePar, if_neg (by omega), if_pos (Or.inr rfl)]
    refine ⟨hN, hN1, by rw [C.ht _, if_pos (Or.inl rfl), C.ht v, if_neg hvnn],
      by rw [C.ht _, if_pos (Or.inr rfl), C.ht v, if_neg hvnn],
      by rw [C.srcOf _, if_pos (Or.inl rfl)], by rw [C.srcOf _, if_pos (Or.inr rfl)],
      by rw [C.livePar, if_pos rfl], by rw [C.children, if_pos rfl],
      by rw [C.srcOf v, if_neg hvnn]; exact C.of,
      by rw [C.ht v, if_neg hvnn, hP']; exact C.hH, by rw [lN, lN1], ?_, ?_⟩
    · rw [lN, hkL]; exact ⟨P, Q, by simp⟩
    · rw [C.ht v, if_neg hvnn, h']; exact ⟨A, B, by simp⟩

/-- **The parent of an entry that `v` held**: `v1` or `v2`, as its child goes. -/
theorem par_v {e : Nat} (he : Ent ord (Top.ht (ts s) v - 1) e) (hp : par (ts s) (Top.ht (ts s) v - 1) e = v) :
    let r := if 2 ≤ Top.ht (ts s) v ∧ (nd (ts s) e).draining = true then (nd (ts s) e).t1 else e
    r ∈ (nd (ts s) v).children ∧
      par S' (Top.ht (ts s) v - 1) e =
        if r ∈ (nd (ts s) v).children.take (sK (wiC s v) v) then s.nodes.size else s.nodes.size + 1 := by
  intro r
  have hvlt := C.H.hv
  obtain ⟨-, -, hkk⟩ := C.S.kids v C.vl
  by_cases h1 : Top.ht (ts s) v = 1
  · have hr : r = e := by simp only [r]; rw [if_neg (by omega)]
    rw [h1, Nat.sub_self] at he hp ⊢
    unfold Ent at he; rw [C.S.ord0] at he
    rw [par_zero'] at hp
    have hek : e ∈ (nd (ts s) v).children :=
      (C.S.mem_children C.vl).mpr ⟨by rw [if_pos h1]; exact he, by rw [h1, Nat.sub_self, par_zero']; exact hp⟩
    rw [hr]
    refine ⟨hek, ?_⟩
    rw [par_zero', C.lpr, if_pos h1]
    rcases C.kids_split hek with ⟨a, b⟩ | ⟨a, b⟩
    · rw [if_neg b, if_pos a, if_pos a]
    · rw [if_pos b, if_neg a]
  · have h2 : 2 ≤ Top.ht (ts s) v := by have := C.h1; omega
    obtain ⟨hn, hh⟩ := (C.S.ordMem _ (by omega) (by have := C.hH; show _ ≤ s.P.H; omega) e).mp he
    have hen := C.nN e hn
    have hev : e ≠ v := fun h => by rw [h] at hh; omega
    by_cases hd : (nd (ts s) e).draining = true
    · have hr : r = (nd (ts s) e).t1 := by simp only [r]; rw [if_pos ⟨h2, hd⟩]
      obtain ⟨g1, -, g3, -⟩ := C.S.ghost e ⟨hn, hd⟩
      unfold par at hp; rw [if_neg (by omega), if_pos hd] at hp
      have hk : (nd (ts s) e).t1 ∈ (nd (ts s) v).children :=
        (C.S.mem_children C.vl).mpr ⟨by rw [if_neg h1]; exact ⟨g1, by rw [g3]; exact hh⟩,
          by rw [par_live (Or.inr g1), if_neg (by omega)]; exact hp⟩
      have ht1v : (nd (ts s) e).t1 ≠ v := fun h => by rw [h] at g3; omega
      have ht1n := C.nN _ g1.1
      rw [hr]
      refine ⟨hk, ?_⟩
      have hnn : ¬(e = s.nodes.size ∨ e = s.nodes.size + 1) := fun h => h.elim hen.1 hen.2
      have hd' : (nd S' e).draining = true := by rw [C.draining', if_neg hev, if_neg hnn]; exact hd
      have ht1' : (nd S' e).t1 = (nd (ts s) e).t1 := by rw [C.H.t1, if_neg hev, if_neg hnn]
      unfold par
      rw [if_neg (by omega), if_pos hd', ht1', C.livePar, if_neg ht1v,
        if_neg (show ¬((nd (ts s) e).t1 = s.nodes.size ∨ (nd (ts s) e).t1 = s.nodes.size + 1) from
          fun h => h.elim ht1n.1 ht1n.2)]
      rcases C.kids_split hk with ⟨a, b⟩ | ⟨a, b⟩
      · rw [if_neg (fun h => b h.2), if_pos ⟨h1, a⟩, if_pos a]
      · rw [if_pos ⟨h1, b⟩, if_neg a]
    · have hr : r = e := by simp only [r]; rw [if_neg (fun h => hd h.2)]
      have hel : Top.liveN (ts s) e := ⟨hn, by simpa using hd⟩
      have hk : e ∈ (nd (ts s) v).children :=
        (C.S.mem_children C.vl).mpr ⟨by rw [if_neg h1]; exact ⟨hel, hh⟩, hp⟩
      rw [hr]
      refine ⟨hk, ?_⟩
      rw [C.par_live' (by omega) ((C.liveN e).mpr (Or.inl ⟨hel, hev⟩)), C.livePar, if_neg hev,
        if_neg (fun h => h.elim hen.1 hen.2)]
      rcases C.kids_split hk with ⟨a, b⟩ | ⟨a, b⟩
      · rw [if_neg (fun h => b h.2), if_pos ⟨h1, a⟩, if_pos a]
      · rw [if_pos ⟨h1, b⟩, if_neg a]

/-- **Other entries keep their parent.** -/
theorem par_keep {k e : Nat} (he : Ent ord k e) (hk : k ≤ s.P.H)
    (hne : ¬(k = Top.ht (ts s) v - 1 ∧ par (ts s) k e = v)) : par S' k e = par (ts s) k e := by
  have hvlt := C.H.hv
  by_cases hk0 : k = 0
  · subst hk0
    rw [par_zero', par_zero', C.lpr]
    split
    · next h1 =>
      have hekn : e ∉ (nd (ts s) v).children := by
        intro hek
        have := ((C.S.mem_children C.vl).mp hek).2
        rw [h1, Nat.sub_self, par_zero'] at this
        exact hne ⟨by omega, by rw [par_zero']; exact this⟩
      rw [if_neg (fun h => hekn (List.mem_of_mem_drop h)), if_neg (fun h => hekn (List.mem_of_mem_take h))]
    · rfl
  · obtain ⟨hn, hh⟩ := (C.S.ordMem k (by omega) hk e).mp he
    have hen := C.nN e hn
    have hnn : ¬(e = s.nodes.size ∨ e = s.nodes.size + 1) := fun h => h.elim hen.1 hen.2
    by_cases hev : e = v
    · rw [hev]
      have hd' : (nd S' v).draining = true := by rw [C.draining', if_pos rfl]
      have ht1' : (nd S' v).t1 = s.nodes.size := by rw [C.H.t1, if_pos rfl]
      unfold par
      rw [if_neg hk0, if_pos hd', ht1', if_neg hk0, if_neg (by rw [C.vl.2]; simp), C.livePar, if_neg (by omega),
        if_pos (Or.inl rfl)]
    · by_cases hd : (nd (ts s) e).draining = true
      · obtain ⟨g1, -, g3, -⟩ := C.S.ghost e ⟨hn, hd⟩
        have ht1v : (nd (ts s) e).t1 ≠ v := by
          intro h; obtain ⟨-, -, -, -, h5, -⟩ := C.S.ghost e ⟨hn, hd⟩
          rw [h] at h5; rw [show Top.srcOf (ts s) v = NIL from C.of] at h5; exact hn.1 h5.symm
        have hd' : (nd S' e).draining = true := by rw [C.draining', if_neg hev, if_neg hnn]; exact hd
        have ht1' : (nd S' e).t1 = (nd (ts s) e).t1 := by rw [C.H.t1, if_neg hev, if_neg hnn]
        unfold par
        rw [if_neg hk0, if_pos hd', ht1', if_neg hk0, if_pos hd]
        refine C.livePar_old g1.1 ht1v (fun h1 hk' => hne ⟨?_, ?_⟩)
        · have := ((C.S.mem_children C.vl).mp hk').1; rw [if_neg h1] at this; omega
        · have := ((C.S.mem_children C.vl).mp hk').2
          rw [par_live (Or.inr g1), if_neg (by have := C.h1; omega)] at this
          unfold par; rw [if_neg hk0, if_pos hd]; exact this
      · have hel : Top.liveN (ts s) e := ⟨hn, by simpa using hd⟩
        rw [C.par_live' hk0 ((C.liveN e).mpr (Or.inl ⟨hel, hev⟩)), par_live (Or.inr hel), if_neg hk0]
        refine C.livePar_old hn hev (fun h1 hk' => hne ⟨?_, ?_⟩)
        · have := ((C.S.mem_children C.vl).mp hk').1; rw [if_neg h1] at this; omega
        · have := ((C.S.mem_children C.vl).mp hk').2
          rw [par_live (Or.inr hel), if_neg (by have := C.h1; omega)] at this
          rw [par_live (Or.inr hel), if_neg hk0]; exact this

/-- A part's members are entries of `v`'s table. -/
theorem left_mem {e : Nat} (he : e ∈ sLeft (wiC s v) v side) : e ∈ Top.order (ts s) v :=
  ((sw_entries C.pc C.v0 C.I C.lp C.TP C.of C.W).mp (List.mem_of_mem_filter he)).1
theorem right_mem {e : Nat} (he : e ∈ sRight (wiC s v) v side) : e ∈ Top.order (ts s) v :=
  ((sw_entries C.pc C.v0 C.I C.lp C.TP C.of C.W).mp (List.mem_of_mem_filter he)).1

theorem order_ent {e : Nat} (he : e ∈ Top.order (ts s) v) : Ent ord (Top.ht (ts s) v - 1) e :=
  C.S.tabEnt v C.vl.1 e he

/-- **The tables of an old entry**: the new nodes join those of a part's members. -/
theorem tabs_old {k e : Nat} (he : Ent ord k e) (hk : k ≤ s.P.H) : tabs S' k e = tabs (ts s) k e ++
    (if k = Top.ht (ts s) v - 1 ∧ e ∈ sLeft (wiC s v) v side then [s.nodes.size] else []) ++
    (if k = Top.ht (ts s) v - 1 ∧ e ∈ sRight (wiC s v) v side then [s.nodes.size + 1] else []) := by
  by_cases hk0 : k = 0
  · subst hk0
    unfold tabs; rw [if_pos rfl, if_pos rfl, C.H.cin]
    by_cases h1 : Top.ht (ts s) v - 1 = 0
    · rw [if_pos h1]
      by_cases hr : e ∈ sRight (wiC s v) v side <;> by_cases hl : e ∈ sLeft (wiC s v) v side <;>
        simp [hr, hl, h1]
    · rw [if_neg h1, if_neg (fun h => h1 h.1.symm), if_neg (fun h => h1 h.1.symm)]; simp
  · obtain ⟨hn, hh⟩ := (C.S.ordMem k (by omega) hk e).mp he
    have hen := C.nN e hn
    unfold tabs; rw [if_neg hk0, if_neg hk0, C.H.inTables, if_neg (fun h => h.elim hen.1 hen.2)]
    have cl : (Top.ht (ts s) v - 1 ≠ 0 ∧ e ∈ sLeft (wiC s v) v side) ↔
        (k = Top.ht (ts s) v - 1 ∧ e ∈ sLeft (wiC s v) v side) := by
      constructor
      · rintro ⟨h1, hl⟩
        have := (C.S.ordMem _ (by omega) (by have := C.hH; show _ ≤ s.P.H; omega) e).mp (C.order_ent (C.left_mem hl))
        exact ⟨by omega, hl⟩
      · rintro ⟨rfl, hl⟩; exact ⟨hk0, hl⟩
    have cr : (Top.ht (ts s) v - 1 ≠ 0 ∧ e ∈ sRight (wiC s v) v side) ↔
        (k = Top.ht (ts s) v - 1 ∧ e ∈ sRight (wiC s v) v side) := by
      constructor
      · rintro ⟨h1, hl⟩
        have := (C.S.ordMem _ (by omega) (by have := C.hH; show _ ≤ s.P.H; omega) e).mp (C.order_ent (C.right_mem hl))
        exact ⟨by omega, hl⟩
      · rintro ⟨rfl, hl⟩; exact ⟨hk0, hl⟩
    by_cases a : k = Top.ht (ts s) v - 1 ∧ e ∈ sLeft (wiC s v) v side
    · rw [if_pos (cl.mpr a), if_pos a]
      by_cases b : k = Top.ht (ts s) v - 1 ∧ e ∈ sRight (wiC s v) v side
      · rw [if_pos (cr.mpr b), if_pos b]
      · rw [if_neg (fun h => b (cr.mp h)), if_neg b]
    · rw [if_neg (fun h => a (cl.mp h)), if_neg a]
      by_cases b : k = Top.ht (ts s) v - 1 ∧ e ∈ sRight (wiC s v) v side
      · rw [if_pos (cr.mpr b), if_pos b]
      · rw [if_neg (fun h => b (cr.mp h)), if_neg b]

theorem tabs_new {e : Nat} (hen : e = s.nodes.size ∨ e = s.nodes.size + 1) :
    tabs S' (Top.ht (ts s) v) e = (nd (ts s) v).inTables := by
  unfold tabs; rw [if_neg (by have := C.h1; omega), C.H.inTables, if_pos hen]

theorem order_mem {X e : Nat} : e ∈ Top.order S' X ↔
    (X = s.nodes.size ∧ e ∈ sLeft (wiC s v) v side) ∨ (X = s.nodes.size + 1 ∧ e ∈ sRight (wiC s v) v side) ∨
    (X ≠ s.nodes.size ∧ X ≠ s.nodes.size + 1 ∧ (e ∈ Top.order (ts s) X ∨
      (X ∈ (nd (ts s) v).inTables ∧ (e = s.nodes.size ∨ e = s.nodes.size + 1)))) := by
  rw [C.order]
  by_cases h1 : X = s.nodes.size
  · rw [if_pos h1]; simp [h1]
  · rw [if_neg h1]
    by_cases h2 : X = s.nodes.size + 1
    · rw [if_pos h2]; simp [h2]
    · rw [if_neg h2]
      simp only [h1, h2, false_and, false_or, ne_eq, not_false_eq_true, true_and]
      split
      · next hT =>
        have hv := (C.inTab X hT).2.2
        constructor
        · intro he
          rcases mem_replace1 he with h | h
          · exact Or.inl h
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl | rfl
            · exact Or.inr ⟨hT, Or.inl rfl⟩
            · exact Or.inl hv
            · exact Or.inr ⟨hT, Or.inr rfl⟩
        · rintro (h | ⟨-, rfl | rfl⟩)
          · by_cases hev : e = v
            · subst hev; exact mem_replace1_new hv (by simp)
            · exact mem_replace1_of_ne h hev
          · exact mem_replace1_new hv (by simp)
          · exact mem_replace1_new hv (by simp)
      · next hT => simp [hT]

theorem sh_tabEnt : ∀ X, Top.isN S' X → ∀ e ∈ Top.order S' X, Ent O' (Top.ht S' X - 1) e := by
  intro X hX e he
  have hvlt := C.H.hv
  unfold Ent
  rw [C.order_mem] at he
  rcases he with ⟨rfl, he⟩ | ⟨rfl, he⟩ | ⟨h1, h2, he⟩
  · rw [C.ht _, if_pos (Or.inl rfl), C.ord_mem]; exact Or.inl (C.order_ent (C.left_mem he))
  · rw [C.ht _, if_pos (Or.inr rfl), C.ord_mem]; exact Or.inl (C.order_ent (C.right_mem he))
  · rw [C.isN] at hX
    have hX' : Top.isN (ts s) X := by rcases hX with h | h | h; exact h; exact absurd h h1; exact absurd h h2
    rw [C.ht _, if_neg (fun h => h.elim h1 h2), C.ord_mem]
    rcases he with he | ⟨hT, hen⟩
    · exact Or.inl (C.S.tabEnt X hX' e he)
    · right; rw [(C.inTab X hT).2.1, Nat.add_sub_cancel]; exact ⟨rfl, hen⟩

theorem left_par {e : Nat} (he : e ∈ sLeft (wiC s v) v side) :
    par S' (Top.ht (ts s) v - 1) e = s.nodes.size := by
  have ho := C.left_mem he
  obtain ⟨hr, hp⟩ := C.par_v (C.order_ent ho) (sp_par C.pc C.v0 C.I C.lp C.TP C.of C.W ho)
  rw [hp, if_pos]
  obtain ⟨-, -, hkk⟩ := C.S.kids v C.vl
  rcases (sw_left C.pc C.v0 C.I C.lp C.TP C.of C.W C.look).mp he with h | ⟨h2, -, hd, -, ht1⟩
  · split
    · next hc => have := (hkk e (List.mem_of_mem_take h)).2 hc.1; rw [this.2] at hc; exact absurd hc.2 (by simp)
    · exact h
  · rw [if_pos ⟨h2, hd⟩]; exact ht1

theorem right_par {e : Nat} (he : e ∈ sRight (wiC s v) v side) :
    par S' (Top.ht (ts s) v - 1) e = s.nodes.size + 1 := by
  have ho := C.right_mem he
  obtain ⟨hr, hp⟩ := C.par_v (C.order_ent ho) (sp_par C.pc C.v0 C.I C.lp C.TP C.of C.W ho)
  rw [hp, if_neg]
  obtain ⟨-, -, hkk⟩ := C.S.kids v C.vl
  have hnot : ∀ x ∈ (nd (ts s) v).children.drop (sK (wiC s v) v),
      x ∉ (nd (ts s) v).children.take (sK (wiC s v) v) := fun x hx => by
    rcases C.kids_split (List.mem_of_mem_drop hx) with ⟨-, b⟩ | ⟨a, -⟩
    · exact absurd hx b
    · exact a
  rcases (sw_right C.pc C.v0 C.I C.lp C.TP C.of C.W C.look).mp he with h | ⟨h2, -, hd, -, ht1⟩
  · split
    · next hc => have := (hkk e (List.mem_of_mem_drop h)).2 hc.1; rw [this.2] at hc; exact absurd hc.2 (by simp)
    · exact hnot e h
  · rw [if_pos ⟨h2, hd⟩]; exact hnot _ ht1

theorem ent_cases {k e : Nat} (he : Ent O' k e) :
    (e ∈ ord k) ∨ (k = Top.ht (ts s) v ∧ (e = s.nodes.size ∨ e = s.nodes.size + 1)) := (C.ord_mem k e).mp he

theorem sh_tabsIff : ∀ k e X, Ent O' k e →
    (X ∈ tabs S' k e ↔ Top.isN S' X ∧ Top.ht S' X = k + 1 ∧ e ∈ Top.order S' X) := by
  intro k e X he
  have hvlt := C.H.hv
  have hP' := C.H.P
  rcases C.ent_cases he with he' | ⟨rfl, hen⟩
  · have hk : k ≤ s.P.H := by
      by_contra hk; have := C.S.ordHigh k (by show s.P.H < k; omega); rw [this] at he'; simp at he'
    rw [C.tabs_old he' hk]
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton]
    rw [C.S.tabsIff k e X he', C.isN, C.ht, C.order_mem]
    constructor
    · rintro ((⟨hX, hXh, heX⟩ | ⟨⟨rfl, hl⟩, rfl⟩) | ⟨⟨rfl, hr⟩, rfl⟩)
      · have hXn := C.nN X hX
        exact ⟨Or.inl hX, by rw [if_neg (fun h => h.elim hXn.1 hXn.2)]; exact hXh,
          Or.inr (Or.inr ⟨hXn.1, hXn.2, Or.inl heX⟩)⟩
      · exact ⟨Or.inr (Or.inl rfl), by rw [if_pos (Or.inl rfl)]; have := C.h1; omega, Or.inl ⟨rfl, hl⟩⟩
      · exact ⟨Or.inr (Or.inr rfl), by rw [if_pos (Or.inr rfl)]; have := C.h1; omega, Or.inr (Or.inl ⟨rfl, hr⟩)⟩
    · rintro ⟨hX, hXh, heX⟩
      rcases heX with ⟨rfl, hl⟩ | ⟨rfl, hr⟩ | ⟨h1, h2, heX⟩
      · rw [if_pos (Or.inl rfl)] at hXh; exact Or.inl (Or.inr ⟨⟨by omega, hl⟩, rfl⟩)
      · rw [if_pos (Or.inr rfl)] at hXh; exact Or.inr ⟨⟨by omega, hr⟩, rfl⟩
      · have hX' : Top.isN (ts s) X := by rcases hX with h | h | h; exact h; exact absurd h h1; exact absurd h h2
        rw [if_neg (fun h => h.elim h1 h2)] at hXh
        rcases heX with heX | ⟨hT, hen⟩
        · exact Or.inl (Or.inl ⟨hX', hXh, heX⟩)
        · exfalso
          have := (C.inTab X hT).2.1
          have hkh : k = Top.ht (ts s) v := by omega
          subst hkh
          have := C.fresh C.h1 (by have := C.hH; omega) he'
          omega
  · rw [C.tabs_new hen, C.isN, C.ht, C.order_mem]
    constructor
    · intro hT
      obtain ⟨hX, hXh, -⟩ := C.inTab X hT
      have hXn := C.nN X hX
      exact ⟨Or.inl hX, by rw [if_neg (fun h => h.elim hXn.1 hXn.2)]; exact hXh,
        Or.inr (Or.inr ⟨hXn.1, hXn.2, Or.inr ⟨hT, hen⟩⟩)⟩
    · rintro ⟨hX, hXh, heX⟩
      rcases heX with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨h1, h2, heX⟩
      · rw [if_pos (Or.inl rfl)] at hXh; omega
      · rw [if_pos (Or.inr rfl)] at hXh; omega
      · have hX' : Top.isN (ts s) X := by rcases hX with h | h | h; exact h; exact absurd h h1; exact absurd h h2
        rw [if_neg (fun h => h.elim h1 h2)] at hXh
        rcases heX with heX | ⟨hT, -⟩
        · exfalso
          have hent := C.S.tabEnt X hX' e heX
          rw [hXh, Nat.add_sub_cancel] at hent
          have := C.fresh C.h1 (by have := C.hH; omega) hent
          omega
        · exact hT

theorem sh_tabsNodup : ∀ k e, Ent O' k e → (tabs S' k e).Nodup := by
  intro k e he
  have hvlt := C.H.hv
  rcases C.ent_cases he with he' | ⟨rfl, hen⟩
  · have hk : k ≤ s.P.H := by
      by_contra hk; have := C.S.ordHigh k (by show s.P.H < k; omega); rw [this] at he'; simp at he'
    rw [C.tabs_old he' hk]
    have hnd := C.S.tabsNodup k e he'
    have hfr : ∀ X ∈ tabs (ts s) k e, X < s.nodes.size := fun X hX => ((C.S.tabsIff k e X he').mp hX).1.2.1
    rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨hnd, by split <;> simp, ?_⟩, by split <;> simp, ?_⟩
    · intro a ha b hb e; subst e; split at hb <;> simp at hb; have := hfr a ha; omega
    · intro a ha b hb e; subst e
      split at hb <;> simp at hb
      rcases List.mem_append.mp ha with ha | ha
      · have := hfr _ ha; omega
      · split at ha <;> simp at ha; omega
  · rw [C.tabs_new hen]; exact C.H.tnd

theorem sh_Q : ∀ k e X, Ent O' k e → X ∈ tabs S' k e →
    X = par S' k e ∨ X = Top.srcOf S' (par S' k e) := by
  intro k e X he hX
  have hvlt := C.H.hv
  obtain ⟨hl, hlh, hvL⟩ := C.up
  rcases C.ent_cases he with he' | ⟨rfl, hen⟩
  · have hk : k ≤ s.P.H := by
      by_contra hk; have := C.S.ordHigh k (by show s.P.H < k; omega); rw [this] at he'; simp at he'
    rw [C.tabs_old he' hk] at hX
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton] at hX
    rcases hX with (hX | ⟨⟨rfl, hle⟩, rfl⟩) | ⟨⟨rfl, hre⟩, rfl⟩
    · have hXn := ((C.S.tabsIff k e X he').mp hX).1
      by_cases hv : k = Top.ht (ts s) v - 1 ∧ par (ts s) k e = v
      · -- the entry's parent was `v`: the table is `v`, now the source of the new parent
        obtain ⟨rfl, hpv⟩ := hv
        obtain ⟨-, hp⟩ := C.par_v he' hpv
        rcases C.S.Q _ e X he' hX with h | h
        · right
          rw [h.trans hpv, hp, C.srcOf]
          split <;> simp
        · exfalso
          rw [hpv, show Top.srcOf (ts s) v = NIL from C.of] at h
          exact hXn.1 h
      · rw [C.par_keep he' hk hv]
        have hpl := C.S.par_liveN he' (by
          have := ((C.S.tabsIff k e X he').mp hX).2.1; have := (C.S.htN X hXn).2; omega)
        have hpn := C.nN _ hpl.1
        rw [C.srcOf (par (ts s) k e), if_neg (fun h => h.elim hpn.1 hpn.2)]
        exact C.S.Q k e X he' hX
    · exact Or.inl (C.left_par hle).symm
    · exact Or.inl (C.right_par hre).symm
  · rw [C.tabs_new hen] at hX
    have hent : Ent ord (Top.ht (ts s) v) v := (C.S.ordMem _ C.h1 (C.S.htN v C.vl.1).2 v).mpr ⟨C.vl.1, rfl⟩
    have hT : X ∈ tabs (ts s) (Top.ht (ts s) v) v := by unfold tabs; rw [if_neg (by have := C.h1; omega)]; exact hX
    have hen' : Top.liveN S' e := (C.liveN e).mpr (Or.inr hen)
    have hpe : par S' (Top.ht (ts s) v) e = (nd (ts s) v).livePar := by
      rw [C.par_live' (by have := C.h1; omega) hen', C.livePar, if_neg (by omega), if_pos hen]
    have hpv : par (ts s) (Top.ht (ts s) v) v = (nd (ts s) v).livePar := by
      rw [par_live (Or.inr C.vl), if_neg (by have := C.h1; omega)]
    have hLn := C.nN _ hl.1
    rw [hpe, C.srcOf (nd (ts s) v).livePar, if_neg (fun h => h.elim hLn.1 hLn.2), ← hpv]
    exact C.S.Q _ v X hent hT

end SDCtx

end OM.Proof.Top
