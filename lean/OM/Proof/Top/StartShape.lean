import OM.Proof.Top.StartShapeT

/-!
# M5: the order invariant after a drain starts
-/

namespace OM.Proof.Top

open OM.Model OM.Proof

set_option linter.deprecated false

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

end SDCtx

end OM.Proof.Top
