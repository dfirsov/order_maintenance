import OM.Proof.Top.StartShape

/-!
# M5: weights, drain timing and label room after a drain starts
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

/-- **The weight of a new node**: its part's children's, stored as its true weight. -/
theorem tw_new (w : Nat) (hw : w = s.nodes.size ∨ w = s.nodes.size + 1) :
    tw S' cl w = (nd S' w).weight ∧
      tw S' cl w = if Top.ht (ts s) v = 1 then (nd S' w).children.length
        else ((nd S' w).children.map (tw (ts s) cl)).sum := by
  have SH := C.shape
  have hvlt := C.H.hv
  have hwl : Top.liveN S' w := (C.liveN w).mpr (Or.inr hw)
  obtain ⟨-, -, hkk⟩ := C.S.kids v C.vl
  have hch : ∀ e ∈ (nd S' w).children, e ∈ (nd (ts s) v).children := by
    intro e he
    rw [C.children, if_neg (by omega)] at he
    rcases hw with rfl | rfl
    · rw [if_pos rfl] at he; exact List.mem_of_mem_take he
    · rw [if_neg (by omega), if_pos rfl] at he; exact List.mem_of_mem_drop he
  have hwt : (nd S' w).weight = ((nd S' w).children.map (sWt (wiC s v) v)).sum := by
    rw [C.H.weight]
    rcases hw with rfl | rfl
    · rw [if_pos rfl, C.children, if_neg (by omega), if_pos rfl, C.ch.1]
    · rw [if_neg (by omega), if_pos rfl, C.children, if_neg (by omega), if_neg (by omega), if_pos rfl, C.ch.2]
  have hwh : Top.ht S' w = Top.ht (ts s) v := by rw [C.ht w, if_pos hw]
  by_cases h1 : Top.ht (ts s) v = 1
  · rw [if_pos h1, SH.tw_one hwl (by rw [hwh, h1]), hwt]
    have : ((nd S' w).children.map (sWt (wiC s v) v)) = List.replicate (nd S' w).children.length 1 := by
      rw [List.eq_replicate_iff]; simp only [List.length_map, true_and]
      intro x hx; obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
      unfold sWt drainWt; rw [sd_h_eq, h1]; rfl
    rw [this]; simp
  · have h2 : 2 ≤ Top.ht (ts s) v := by have := C.h1; omega
    have hsum : ((nd S' w).children.map (tw S' cl)) = ((nd S' w).children.map (tw (ts s) cl)) := by
      apply List.map_congr_left; intro e he
      have hek := hch e he
      have hel := (hkk e hek).2 h2
      have hev : e ≠ v := by
        intro e'; have := ((C.S.mem_children C.vl).mp hek).1; rw [if_neg h1, e'] at this; omega
      exact C.tw_old hel.1 hev
    have hws : ((nd S' w).children.map (sWt (wiC s v) v)) = ((nd S' w).children.map (tw (ts s) cl)) := by
      apply List.map_congr_left; intro e he
      have hek := hch e he
      have hev : e ≠ v := by
        intro e'; have := ((C.S.mem_children C.vl).mp hek).1; rw [if_neg h1, e'] at this; omega
      unfold sWt drainWt
      rw [sd_h_eq, if_neg (by simp; omega), ← sd_kid_weight C.pc C.v0 C.I C.lp hek h2]
      show ((s.nodes.modify v _).getX e).weight = _
      rw [Array.getX_modify, if_neg (fun h' => hev h'.1.symm)]; rfl
    rw [if_neg h1, SH.tw_kids hwl (by rw [hwh]; exact h2), hsum, hwt, hws]
    exact ⟨rfl, rfl⟩

/-- The drained node served what its two targets now serve. -/
theorem ew_v : ew S' cl v = tw (ts s) cl v := by
  have hvlt := C.H.hv
  have SH := C.shape
  obtain ⟨hknd, -, hkk⟩ := C.S.kids v C.vl
  have hd : (nd S' v).draining = true := by rw [C.draining', if_pos rfl]
  have ht1 : (nd S' v).t1 = s.nodes.size := by rw [C.H.t1, if_pos rfl]
  have ht2 : (nd S' v).t2 = s.nodes.size + 1 := by rw [C.H.t2, if_pos rfl]
  unfold ew
  rw [if_pos hd, ht1, ht2]
  obtain ⟨-, a1⟩ := C.tw_new _ (Or.inl rfl)
  obtain ⟨-, a2⟩ := C.tw_new _ (Or.inr rfl)
  rw [a1, a2, C.children s.nodes.size, if_neg (show ¬(s.nodes.size = v) by omega), if_pos rfl,
    C.children (s.nodes.size + 1), if_neg (show ¬(s.nodes.size + 1 = v) by omega),
    if_neg (show ¬(s.nodes.size + 1 = s.nodes.size) by omega), if_pos rfl]
  by_cases h1 : Top.ht (ts s) v = 1
  · rw [if_pos h1, if_pos h1, List.length_take, List.length_drop, C.S.tw_one C.vl h1]
    have := C.k; omega
  · rw [if_neg h1, if_neg h1, C.S.tw_kids C.vl (by have := C.h1; omega), ← List.sum_append, ← List.map_append,
      List.take_append_drop]

/-- An old node serves as before. -/
theorem ew_old {X : Nat} (hX : Top.isN (ts s) X) : ew S' cl X = ew (ts s) cl X := by
  have hvlt := C.H.hv
  by_cases hXv : X = v
  · rw [hXv, C.ew_v]; unfold ew; rw [if_neg (by rw [C.vl.2]; simp)]
  · have hXn := C.nN X hX
    have hnn : ¬(X = s.nodes.size ∨ X = s.nodes.size + 1) := fun h => h.elim hXn.1 hXn.2
    unfold ew
    rw [C.draining', if_neg hXv, if_neg hnn]
    split
    · next hd =>
      obtain ⟨g1, g2, -, -, h5, h6, -⟩ := C.S.ghost X ⟨hX, hd⟩
      have ht1v : (nd (ts s) X).t1 ≠ v := fun e => by rw [e] at h5; rw [show Top.srcOf (ts s) v = NIL from C.of] at h5; exact hX.1 h5.symm
      have ht2v : (nd (ts s) X).t2 ≠ v := fun e => by rw [e] at h6; rw [show Top.srcOf (ts s) v = NIL from C.of] at h6; exact hX.1 h6.symm
      rw [C.H.t1, C.H.t2, if_neg hXv, if_neg hXv, if_neg hnn, if_neg hnn, C.tw_old g1.1 ht1v, C.tw_old g2.1 ht2v]
    · exact C.tw_old hX hXv

/-- Live nodes above `v` keep their live parents. -/
theorem livePar_high {x : Nat} (hx : Top.liveN (ts s) x) (hh : Top.ht (ts s) v + 1 ≤ Top.ht (ts s) x) :
    (nd S' x).livePar = (nd (ts s) x).livePar :=
  C.livePar_old hx.1 (fun e => by rw [e] at hh; omega) (fun h1 hk => by
    have := ((C.S.mem_children C.vl).mp hk).1; rw [if_neg h1] at this; omega)

theorem upChain_high : ∀ f x, (x = NIL ∨ (Top.liveN (ts s) x ∧ Top.ht (ts s) v + 1 ≤ Top.ht (ts s) x)) →
    upChain S' f x = upChain (ts s) f x
  | 0, _, _ => rfl
  | f + 1, x, hx => by
    simp only [upChain]
    split
    · rfl
    · next hx0 =>
      rcases hx with h | ⟨hl, hh⟩
      · exact absurd h hx0
      rw [C.livePar_high hl hh]
      congr 1
      apply upChain_high
      by_cases hH : Top.ht (ts s) x < s.P.H
      · obtain ⟨h1, h2, -⟩ := C.S.up x hl hH
        exact Or.inr ⟨h1, by omega⟩
      · left
        have hc := C.Ti.chain
        have hroot : x = s.P.H := by
          have h' : Top.ht (ts s) x ≤ s.P.H := (C.S.htN x hl.1).2
          have hm := (C.S.ordMem (ts s).P.H (by have := C.S.H3; omega) le_rfl x).mpr ⟨hl.1, by
            show Top.ht (ts s) x = s.P.H; omega⟩
          rw [C.S.root.1] at hm
          have : x = (ts s).P.H := by simpa using hm
          exact this
        rw [hroot]; exact C.S.root.2.2

/-- **The lagging nodes after the drain starts**: `v` has caught up. -/
theorem pend_mem {x : Nat} : x ∈ pend S' (some { j with pc := .afterDrain v (nd (ts s) v).livePar }) ↔
    x ∈ pend (ts s) (some j) ∧ x ≠ v := by
  obtain ⟨hl, hlh, -⟩ := C.up
  have hpold := sd_pend C.pc C.v0 C.I C.lp
  rw [hpold]
  unfold pend wStart
  simp only
  rw [C.H.P, C.upChain_high _ _ (Or.inr ⟨hl, by omega⟩)]
  have e : (ts s).P.H = s.P.H := rfl
  rw [e]
  have hvn : v ∉ upChain (ts s) (s.P.H + 1) (nd (ts s) v).livePar := by
    intro hm
    have := (C.S.upChain_mem _ _ v hl hm).2; omega
  constructor
  · intro h; exact ⟨List.mem_cons_of_mem _ h, fun e => hvn (e ▸ h)⟩
  · rintro ⟨h, hxv⟩
    rcases List.mem_cons.mp h with h | h
    · exact absurd h hxv
    · exact h

end SDCtx

end OM.Proof.Top
