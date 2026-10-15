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

theorem infix_pair_idx {l : List Nat} {a b : Nat} (h : [a, b] <:+: l) :
    ∃ i, i + 1 < l.length ∧ l.getD i 0 = a ∧ l.getD (i + 1) 0 = b := by
  obtain ⟨u, w, rfl⟩ := h
  refine ⟨u.length, by simp, ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ (by simp)]; simp
  · rw [List.getD_eq_getElem _ _ (by simp)]; simp

theorem getD_mem_take {l : List Nat} {i k : Nat} (hi : i < l.length) (hk : i < k) : l.getD i 0 ∈ l.take k := by
  rw [List.getD_eq_getElem _ _ hi, ← List.getElem_take (j := k) (h := by simp; omega)]
  exact List.getElem_mem _

theorem getD_not_mem_take {l : List Nat} (hl : l.Nodup) {i k : Nat} (hi : i < l.length) (hk : k ≤ i) :
    l.getD i 0 ∉ l.take k := by
  rw [List.getD_eq_getElem _ _ hi]
  intro hm
  obtain ⟨j, hj, e⟩ := List.getElem_of_mem hm
  rw [List.getElem_take] at e
  have := (List.Nodup.getElem_inj_iff hl).mp e
  simp at hj; omega

theorem filter_mem_take {l : List Nat} (hl : l.Nodup) (k : Nat) :
    l.filter (fun e => decide (e ∈ l.take k)) = l.take k ∧ l.filter (fun e => !decide (e ∈ l.take k)) = l.drop k := by
  have hsp : l = l.take k ++ l.drop k := (List.take_append_drop k l).symm
  have hnd : (l.take k ++ l.drop k).Nodup := hsp ▸ hl
  have hdis := (List.nodup_append.mp hnd).2.2
  constructor
  · conv_lhs => rw [hsp]
    rw [List.filter_append, List.filter_eq_self.mpr (fun e he => by simp [he]),
      List.filter_eq_nil_iff.mpr (fun e he => by simp; exact fun h => hdis e h e he rfl), List.append_nil]
  · conv_lhs => rw [hsp]
    rw [List.filter_append, List.filter_eq_nil_iff.mpr (fun e he => by simp [he]),
      List.filter_eq_self.mpr (fun e he => by simp; exact fun h => hdis e h e he rfl), List.nil_append]

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

theorem sp_entry {e : Nat} (he : e ∈ order (ts s) v) :
    (ht (ts s) v = 1 → e ∈ (nd (ts s) v).children) ∧
    (2 ≤ ht (ts s) v → isN (ts s) e ∧ ht (ts s) e = ht (ts s) v - 1 ∧
      ((nd (ts s) e).draining = false → e ∈ (nd (ts s) v).children)) := by
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI hlp
  have hp := sp_par hpc hv0 hI hlp hTP hof hW he
  have hent := S.tabEnt v hvl.1 e he
  constructor
  · intro h1
    rw [h1, Nat.sub_self] at hent hp
    unfold Ent at hent; rw [S.ord0] at hent
    exact (S.mem_children hvl).mpr ⟨by rw [if_pos h1]; exact hent, by rw [h1, Nat.sub_self]; exact hp⟩
  · intro h2
    obtain ⟨hn, hh⟩ := (S.ordMem _ (by omega) (by have := (sd_ht hpc hv0 hI hlp).2; show _ ≤ s.P.H; omega) e).mp hent
    refine ⟨hn, hh, fun hd => ?_⟩
    have hl : liveN (ts s) e := ⟨hn, hd⟩
    exact (S.mem_children hvl).mpr ⟨by rw [if_neg (by omega)]; exact ⟨hl, hh⟩, hp⟩

theorem sp_ghost (h2 : 2 ≤ ht (ts s) v) {g : Nat} (hg : g ∈ order (ts s) v) (hgd : (nd (ts s) g).draining = true) :
    (nd (ts s) g).t1 ∈ (nd (ts s) v).children ∧ (nd (ts s) g).t2 ∈ (nd (ts s) v).children ∧
      [(nd (ts s) g).t1, (nd (ts s) g).t2] <:+: (nd (ts s) v).children ∧
      [(nd (ts s) g).t1, g, (nd (ts s) g).t2] <:+: order (ts s) v := by
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI hlp
  obtain ⟨hn, hh, -⟩ := (sp_entry hpc hv0 hI hlp hTP hof hW hg).2 h2
  have hgh : ghostN (ts s) g := ⟨hn, hgd⟩
  have hp := sp_par hpc hv0 hI hlp hTP hof hW hg
  unfold par at hp; rw [if_neg (by omega), if_pos hgd] at hp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hinf2, hinf3⟩ := S.ghost g hgh
  rw [hp] at hinf2
  have hent : Ent ord (ht (ts s) g) g := (S.ordMem _ (by omega) (by
    have := (sd_ht hpc hv0 hI hlp).2; show _ ≤ s.P.H; omega) g).mpr ⟨hn, rfl⟩
  have hT : v ∈ tabs (ts s) (ht (ts s) g) g := (S.tabsIff _ g v hent).mpr ⟨hvl.1, by omega, hg⟩
  have hw := S.W1 g hgh v hT
  exact ⟨hinf2.subset (by simp), hinf2.subset (by simp), hinf2, hw⟩

/-- **The sides** `startDrain` computes. -/
theorem sp_side : ∃ side, sSideO (wiC s v) v = some side ∧ ∀ x, lookup side x =
    if 2 ≤ ht (ts s) v ∧ x ∈ sEntries (wiC s v) v ∧ (nd (ts s) x).draining = true then
      lookup (sidesOf (order (ts s) v) ((nd (ts s) v).children.getD (sK (wiC s v) v) 0)) (nd (ts s) x).t1
    else lookup (sidesOf (order (ts s) v) ((nd (ts s) v).children.getD (sK (wiC s v) v) 0)) x := by
  have S := hI.shape
  obtain ⟨-, P, Q, hsp⟩ := sp_b hpc hv0 hI hlp hTP hof hW
  have hnd := sp_order_nodup hpc hv0 hI hlp hTP hof hW
  have hord : ((wiC s v).nodes.getX v).order = order (ts s) v := (wiC_sameTree s v).order v
  have hh : ((wiC s v).nodes.getX v).height = ht (ts s) v := (wiC_sameTree s v).height v
  unfold sSideO drainSide sB
  rw [sd_kids_eq, hord, hh]
  by_cases h2 : 2 ≤ ht (ts s) v
  · rw [if_pos (by omega)]
    obtain ⟨side', h1, h2'⟩ := fixSides_spec (wiC s v).nodes (drainEntries (wiC s v).nodes ((wiC s v).nodes.getX v))
      (sidesOf (order (ts s) v) ((nd (ts s) v).children.getD (sK (wiC s v) v) 0)) (by
        intro e he hd
        have hd' : (nd (ts s) e).draining = true := by rw [← (wiC_sameTree s v).draining e]; exact hd
        have hem : e ∈ order (ts s) v := by rw [← hord]; exact List.mem_of_mem_filter he
        obtain ⟨ht1, -⟩ := sp_ghost hpc hv0 hI hlp hTP hof hW h2 hem hd'
        obtain ⟨hn, -⟩ := (sp_entry hpc hv0 hI hlp hTP hof hW hem).2 h2
        obtain ⟨g1, -⟩ := S.ghost e ⟨hn, hd'⟩
        have et1 : ((wiC s v).nodes.getX e).t1 = (nd (ts s) e).t1 := (wiC_sameTree s v).t1 e
        refine ⟨by rw [et1, show ((wiC s v).nodes.getX (nd (ts s) e).t1).draining = _ from
          (wiC_sameTree s v).draining _]; exact g1.2, ?_⟩
        rw [et1, hsp, sidesOf_spec (hsp ▸ hnd)]
        have hm := (sp_kids_sub hpc hv0 hI hlp hTP hof hW).subset ht1
        rw [hsp] at hm
        simp only [List.mem_append, List.mem_cons] at hm
        split_ifs <;> simp_all)
    refine ⟨side', h1, fun x => ?_⟩
    rw [h2']
    have e1 : ((wiC s v).nodes.getX x).draining = (nd (ts s) x).draining := (wiC_sameTree s v).draining x
    have e2 : ((wiC s v).nodes.getX x).t1 = (nd (ts s) x).t1 := (wiC_sameTree s v).t1 x
    rw [e1, e2]
    by_cases hx : x ∈ drainEntries (wiC s v).nodes ((wiC s v).nodes.getX v) ∧ (nd (ts s) x).draining = true
    · rw [if_pos hx, if_pos ⟨h2, hx⟩]
    · rw [if_neg hx, if_neg (fun h => hx h.2)]
  · rw [if_neg (by omega)]
    exact ⟨_, rfl, fun x => by rw [if_neg (fun h => h2 h.1)]⟩

section side
variable {side : List (Nat × Side)} (hside : sSideO (wiC s v) v = some side)
  (hlook : ∀ x, lookup side x =
    if 2 ≤ ht (ts s) v ∧ x ∈ sEntries (wiC s v) v ∧ (nd (ts s) x).draining = true then
      lookup (sidesOf (order (ts s) v) ((nd (ts s) v).children.getD (sK (wiC s v) v) 0)) (nd (ts s) x).t1
    else lookup (sidesOf (order (ts s) v) ((nd (ts s) v).children.getD (sK (wiC s v) v) 0)) x)
include hlook

/-- **A child's side**: left before the boundary. -/
theorem sw_kid {e : Nat} (he : e ∈ (nd (ts s) v).children) :
    lookup side e = some (if e ∈ (nd (ts s) v).children.take (sK (wiC s v) v) then .left else .right) := by
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI hlp
  obtain ⟨-, -, hk⟩ := S.kids v hvl
  obtain ⟨-, -, hkn⟩ := sp_k hpc hv0 hI hlp hTP hof hW
  obtain ⟨-, P, Q, hsp⟩ := sp_b hpc hv0 hI hlp hTP hof hW
  have hnd := sp_order_nodup hpc hv0 hI hlp hTP hof hW
  have hsub := sp_kids_sub hpc hv0 hI hlp hTP hof hW
  rw [hlook]
  rw [if_neg (fun h => by
    have := (hk e he).2 h.1
    rw [this.2] at h; exact absurd h.2.2 (by simp))]
  have hiff := mem_take_iff_left hsub hnd hkn he hsp
  rw [hsp, sidesOf_spec (hsp ▸ hnd)]
  have hm := hsub.subset he
  rw [hsp] at hm
  simp only [List.mem_append, List.mem_cons] at hm
  by_cases ht : e ∈ (nd (ts s) v).children.take (sK (wiC s v) v)
  · rw [if_pos (hiff.mp ht), if_pos ht]
  · have hP : e ∉ P := fun h => ht (hiff.mpr h)
    rw [if_neg hP, if_pos (by tauto), if_neg ht]

/-- **Pairs are not separated.** -/
theorem sw_nosep (h2 : 2 ≤ ht (ts s) v) {g : Nat} (hg : g ∈ order (ts s) v)
    (hgd : (nd (ts s) g).draining = true) :
    (nd (ts s) g).t1 ∈ (nd (ts s) v).children.take (sK (wiC s v) v) ↔
      (nd (ts s) g).t2 ∈ (nd (ts s) v).children.take (sK (wiC s v) v) := by
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI hlp
  obtain ⟨hnd, -, -⟩ := S.kids v hvl
  obtain ⟨-, -, hinf, -⟩ := sp_ghost hpc hv0 hI hlp hTP hof hW h2 hg hgd
  obtain ⟨-, -, -, hsep, -⟩ := sd_cut2 hpc hv0 hI hlp hTP h2 hof hW
  obtain ⟨i, hi, e1, e2⟩ := infix_pair_idx hinf
  rw [← e1, ← e2]
  set k := sK (wiC s v) v
  by_cases hik : i + 1 < k
  · exact ⟨fun _ => getD_mem_take hi hik, fun _ => getD_mem_take (by omega) (by omega)⟩
  · by_cases hik' : k ≤ i
    · exact ⟨fun h => absurd h (getD_not_mem_take hnd (by omega) hik'),
        fun h => absurd h (getD_not_mem_take hnd hi (by omega))⟩
    · exfalso
      have hk : k = i + 1 := by omega
      obtain ⟨hn, -⟩ := (sp_entry hpc hv0 hI hlp hTP hof hW hg).2 h2
      obtain ⟨-, -, -, -, h5, h6, -⟩ := S.ghost g ⟨hn, hgd⟩
      have : sPr (wiC s v) v k = true := by
        unfold sPr drainPr sameDrainN
        rw [sd_kids_eq, hk, Nat.add_sub_cancel, e1, e2]
        have o1 : ((wiC s v).nodes.getX (nd (ts s) g).t1).overflowOf = g := by
          rw [show ((wiC s v).nodes.getX (nd (ts s) g).t1).overflowOf = _ from (wiC_sameTree s v).overflowOf _]
          exact h5
        have o2 : ((wiC s v).nodes.getX (nd (ts s) g).t2).overflowOf = g := by
          rw [show ((wiC s v).nodes.getX (nd (ts s) g).t2).overflowOf = _ from (wiC_sameTree s v).overflowOf _]
          exact h6
        rw [o1, o2]; simp [hn.1]
      rw [hsep] at this; exact absurd this (by simp)

end side

end parts

end OM.Proof.Top
