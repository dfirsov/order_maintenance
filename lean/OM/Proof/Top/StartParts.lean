import OM.Proof.Top.StartFrame

/-!
# M5: the sides and the parts at a drain start

Children before the boundary go left, the others right; a ghost entry goes with its targets.
-/

namespace OM.Proof.Top

open OM.Model OM.Proof

set_option linter.deprecated false

/-! ### Lists -/

/-- Two sublists of a list of distinct elements: inclusion is a sublist. -/
theorem sublist_of_subset_common : ∀ {A B L : List Nat}, A.Sublist L → B.Sublist L → L.Nodup → A ⊆ B →
    A.Sublist B
  | A, B, [], hA, hB, _, _ => by rw [List.sublist_nil.mp hA]; exact List.nil_sublist _
  | A, B, x :: L, hA, hB, hL, hsub => by
    have hx := List.nodup_cons.mp hL
    rcases List.sublist_cons_iff.mp hA with hA' | ⟨A', rfl, hA'⟩ <;>
      rcases List.sublist_cons_iff.mp hB with hB' | ⟨B', rfl, hB'⟩
    · exact sublist_of_subset_common hA' hB' hx.2 hsub
    · have hxA : x ∉ A := fun h => hx.1 (hA'.subset h)
      have : A ⊆ B' := fun a ha => by
        have := hsub ha; simp only [List.mem_cons] at this
        rcases this with e | e
        · subst e; exact absurd ha hxA
        · exact e
      exact (sublist_of_subset_common hA' hB' hx.2 this).cons x
    · exact absurd (hB'.subset (hsub (by simp))) hx.1
    · have hxA : x ∉ A' := fun h => hx.1 (hA'.subset h)
      have : A' ⊆ B' := fun a ha => by
        have := hsub (List.mem_cons_of_mem _ ha); simp only [List.mem_cons] at this
        rcases this with e | e
        · subst e; exact absurd ha hxA
        · exact e
      exact (sublist_of_subset_common hA' hB' hx.2 this).cons_cons x

theorem mem_left_iff_before {P Q : List Nat} {b e : Nat} (hnd : (P ++ b :: Q).Nodup) :
    e ∈ P ↔ Before (P ++ b :: Q) e b := by
  constructor
  · exact before_split
  · intro h
    have hm := h.mem_left
    simp only [List.mem_append, List.mem_cons] at hm
    rcases hm with hm | rfl | hm
    · exact hm
    · exact absurd rfl (h.ne hnd)
    · exfalso
      exact h.asymm hnd (before_append_right (before_cons.mpr (Or.inr ⟨rfl, hm⟩)))

/-- A list split at its `k`-th element. -/
theorem split_at {l : List Nat} {k : Nat} (hk : k < l.length) :
    l = l.take k ++ l.getD k 0 :: l.drop (k + 1) := by
  rw [List.getD_eq_getElem _ _ hk, ← List.drop_eq_getElem_cons hk, List.take_append_drop]

/-- **Before the boundary in a superlist iff before it in the list.** -/
theorem mem_take_iff_left {l o P Q : List Nat} {k e : Nat} (hlo : l.Sublist o) (ho : o.Nodup)
    (hk : k < l.length) (he : e ∈ l) (hsplit : o = P ++ l.getD k 0 :: Q) :
    e ∈ l.take k ↔ e ∈ P := by
  have hl : l.Nodup := ho.sublist hlo
  have hb : l.getD k 0 ∈ l := by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  have hsp := split_at hk
  have hnd' : (l.take k ++ l.getD k 0 :: l.drop (k + 1)).Nodup := hsp ▸ hl
  rw [mem_left_iff_before hnd', ← hsp, mem_left_iff_before (hsplit ▸ ho), ← hsplit]
  constructor
  · intro h; exact h.mono hlo
  · intro h; exact before_of_sublist hlo ho he hb h

/-- The parent of an entry below the root's height is live. -/
theorem Shape.par_liveN {s : TS} {cl : List Nat} {ord : Nat → List Nat} (S : Shape s cl ord) {h e : Nat}
    (he : Ent ord h e) (hh : h < s.P.H) : liveN s (par s h e) := by
  by_cases h0 : h = 0
  · subst h0
    unfold Ent at he; rw [S.ord0] at he
    rw [par_live (Or.inl rfl), if_pos rfl]; exact (S.lp e he).1
  · obtain ⟨hn, hht⟩ := (S.ordMem h (by omega) (by omega) e).mp he
    by_cases hd : (nd s e).draining = true
    · obtain ⟨g1, -, g3, -⟩ := S.ghost e ⟨hn, hd⟩
      unfold par; rw [if_neg h0, if_pos hd]
      exact (S.up _ g1 (by rw [g3]; omega)).1
    · have hl : liveN s e := ⟨hn, by simpa using hd⟩
      rw [par_live (Or.inr hl), if_neg h0]
      exact (S.up e hl (by omega)).1

/-! ### At a drain start -/

section parts
variable {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat} {j : Job} {v : Nat}
  (hpc : j.pc = .walk (some v)) (hv0 : v ≠ NIL) (hI : InvJ (ts s) cl ord dr n0 (some j))
  (hlp : (nd (ts s) v).livePar ≠ NIL) (hTP : TopParams s.P) (hof : (nd (ts s) v).overflowOf = NIL)
  (hW : Wd s.P (ht (ts s) v) < (nd (ts s) v).weight + 2)
include hpc hv0 hI hlp hTP hof hW

/-- The cut is inside. -/
theorem sp_k : 2 ≤ (nd (ts s) v).children.length ∧ 1 ≤ sK (wiC s v) v ∧
    sK (wiC s v) v < (nd (ts s) v).children.length := by
  obtain ⟨h1, -⟩ := sd_ht hpc hv0 hI hlp
  by_cases h2 : 2 ≤ ht (ts s) v
  · obtain ⟨a, b, c, -⟩ := sd_cut2 hpc hv0 hI hlp hTP h2 hof hW
    exact ⟨a, b, by omega⟩
  · obtain ⟨a, b, c, -⟩ := sd_cut1 hpc hv0 hI hlp (by omega) hof hW
    exact ⟨a, b, by omega⟩

/-- The children, in the order of `v`'s table. -/
theorem sp_kids_sub : (nd (ts s) v).children.Sublist (order (ts s) v) := by
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI hlp
  obtain ⟨-, hsub, -⟩ := S.kids v hvl
  exact sublist_of_subset_common hsub (S.O1 v hvl.1) (S.ordNodup _)
    (fun e he => S.kid_mem hI.time hvl he)

theorem sp_order_nodup : (order (ts s) v).Nodup := by
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI hlp
  exact (S.ordNodup _).sublist (S.O1 v hvl.1)

/-- The boundary child. -/
theorem sp_b : (nd (ts s) v).children.getD (sK (wiC s v) v) 0 ∈ (nd (ts s) v).children ∧
    ∃ P Q, order (ts s) v = P ++ (nd (ts s) v).children.getD (sK (wiC s v) v) 0 :: Q := by
  obtain ⟨-, -, hk⟩ := sp_k hpc hv0 hI hlp hTP hof hW
  have hb : (nd (ts s) v).children.getD (sK (wiC s v) v) 0 ∈ (nd (ts s) v).children := by
    rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  exact ⟨hb, List.mem_iff_append.mp ((sp_kids_sub hpc hv0 hI hlp hTP hof hW).subset hb)⟩

/-- An entry of `v`'s table has `v` as its parent. -/
theorem sp_par {e : Nat} (he : e ∈ order (ts s) v) : par (ts s) (ht (ts s) v - 1) e = v := by
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI hlp
  have hent := S.tabEnt v hvl.1 e he
  have hT : v ∈ tabs (ts s) (ht (ts s) v - 1) e := by
    have h1 := (sd_ht hpc hv0 hI hlp).1
    exact (S.tabsIff _ e v hent).mpr ⟨hvl.1, by omega, he⟩
  rcases S.Q _ e v hent hT with h | h
  · exact h.symm
  · exfalso
    have hpl := S.par_liveN hent (by have := (sd_ht hpc hv0 hI hlp).2; show _ < s.P.H; omega)
    obtain ⟨hg, -⟩ := S.src _ hpl (by rw [← h]; exact hv0)
    rw [← h] at hg
    exact absurd hg.2 (by rw [hvl.2]; simp)

end parts

end OM.Proof.Top
