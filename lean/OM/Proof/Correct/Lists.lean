import OM.Proof.Correct.Inv

/-!
# Linked lists as `succOf` / `predOf`

Lemmas for reading and updating the doubly linked lists of INV-S: successors and predecessors
in appended and flattened lists, and sortedness under a change at one position.
-/

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

theorem headD_reverse (l : List Nat) (d : Nat) : l.reverse.headD d = l.getLastD d := by
  rcases l.eq_nil_or_concat with rfl | ⟨l', a, rfl⟩ <;> simp

/-! ### `succOf` -/

@[simp] theorem succOf_nil (x : Nat) : succOf [] x = NIL := rfl
@[simp] theorem succOf_single (a x : Nat) : succOf [a] x = NIL := rfl
theorem succOf_cons_cons (a b : Nat) (t : List Nat) (x : Nat) :
    succOf (a :: b :: t) x = if a = x then b else succOf (b :: t) x := rfl

theorem succOf_cons (a : Nat) (l : List Nat) (x : Nat) :
    succOf (a :: l) x = if a = x then l.headD NIL else succOf l x := by
  cases l with
  | nil => by_cases h : a = x <;> simp [h]
  | cons b t => rfl

theorem succOf_not_mem {l : List Nat} {x : Nat} (h : x ∉ l) : succOf l x = NIL := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [succOf_cons]
    simp only [List.mem_cons, not_or] at h
    rw [if_neg (Ne.symm h.1), ih h.2]

/-- Successors in an append of disjoint lists. -/
theorem succOf_append {l1 l2 : List Nat} (hnd : l1.Nodup) (x : Nat) :
    succOf (l1 ++ l2) x =
      if x ∈ l1 then (if l1.getLast? = some x then l2.headD NIL else succOf l1 x)
      else succOf l2 x := by
  induction l1 with
  | nil => simp
  | cons a t ih =>
    rw [List.cons_append, succOf_cons, succOf_cons]
    simp only [List.nodup_cons] at hnd
    by_cases hax : a = x
    · subst hax
      simp only [List.mem_cons, true_or, if_true]
      cases t with
      | nil => simp
      | cons b u =>
        have : (b :: u).getLast? ≠ some a := by
          intro h; exact hnd.1 (List.mem_of_getLast? h)
        simp [List.getLast?_cons_cons, this]
    · rw [if_neg hax, if_neg hax, ih hnd.2]
      simp only [List.mem_cons, Ne.symm hax, false_or]
      by_cases hxt : x ∈ t
      · simp only [hxt, if_true]
        cases t with
        | nil => simp at hxt
        | cons b u => simp [List.getLast?_cons_cons]
      · simp [hxt]

theorem succOf_mem_or {l : List Nat} {x : Nat} : succOf l x ∈ l ∨ succOf l x = NIL := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [succOf_cons]
    split
    · cases t with
      | nil => simp
      | cons b u => simp
    · rcases ih with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h

/-- In `l1 ++ x :: l2` with `x ∉ l1`, the successor of `x` is the head of `l2`. -/
theorem succOf_mid {l1 l2 : List Nat} {x : Nat} (hnd : (l1 ++ x :: l2).Nodup) :
    succOf (l1 ++ x :: l2) x = l2.headD NIL := by
  have h1 : l1.Nodup := (List.nodup_append.mp hnd).1
  have hx : x ∉ l1 := fun h => (List.nodup_append.mp hnd).2.2 x h x (by simp) rfl
  rw [succOf_append h1, if_neg hx, succOf_cons, if_pos rfl]

/-! ### `predOf` -/

theorem predOf_append {l1 l2 : List Nat} (hnd : l2.Nodup) (x : Nat) :
    predOf (l1 ++ l2) x =
      if x ∈ l2 then (if l2.head? = some x then l1.getLastD NIL else predOf l2 x)
      else predOf l1 x := by
  unfold predOf
  rw [List.reverse_append, succOf_append (List.nodup_reverse.mpr hnd)]
  simp only [List.mem_reverse, List.getLast?_reverse, headD_reverse]

theorem predOf_mid {l1 l2 : List Nat} {x : Nat} (hnd : (l1 ++ x :: l2).Nodup) :
    predOf (l1 ++ x :: l2) x = l1.getLastD NIL := by
  have h2 : (x :: l2).Nodup := (List.nodup_append.mp hnd).2.1
  rw [predOf_append h2]
  simp

theorem predOf_not_mem {l : List Nat} {x : Nat} (h : x ∉ l) : predOf l x = NIL :=
  succOf_not_mem (by simpa using h)

theorem predOf_mem_or {l : List Nat} {x : Nat} : predOf l x ∈ l ∨ predOf l x = NIL := by
  unfold predOf
  rcases succOf_mem_or (l := l.reverse) (x := x) with h | h
  · exact Or.inl (List.mem_reverse.mp h)
  · exact Or.inr h

/-! ### Blocks of a flattened list -/

/-- Inside a block, the successor in the flattened list is the successor in the block, unless
the element is the block's last. -/
theorem succOf_flatten {L : List (List Nat)} (hnd : L.flatten.Nodup) {b : List Nat} (hb : b ∈ L)
    {x : Nat} (hx : x ∈ b) (hlast : b.getLast? ≠ some x) :
    succOf L.flatten x = succOf b x := by
  obtain ⟨L1, L2, rfl⟩ := List.mem_iff_append.mp hb
  rw [List.flatten_append, List.flatten_cons] at hnd ⊢
  have hn1 := (List.nodup_append.mp hnd).1
  have hxL1 : x ∉ L1.flatten := fun h => (List.nodup_append.mp hnd).2.2 x h x (by simp [hx]) rfl
  have hn2 := (List.nodup_append.mp (List.nodup_append.mp hnd).2.1).1
  rw [succOf_append hn1, if_neg hxL1, succOf_append hn2, if_pos hx, if_neg hlast]

theorem predOf_flatten {L : List (List Nat)} (hnd : L.flatten.Nodup) {b : List Nat} (hb : b ∈ L)
    {x : Nat} (hx : x ∈ b) (hfirst : b.head? ≠ some x) :
    predOf L.flatten x = predOf b x := by
  unfold predOf
  rw [List.reverse_flatten]
  have hnd' : (L.map List.reverse).reverse.flatten.Nodup := by
    rw [← List.reverse_flatten]; exact List.nodup_reverse.mpr hnd
  exact succOf_flatten hnd' (List.mem_reverse.mpr (List.mem_map.mpr ⟨b, hb, rfl⟩))
    (by simpa using hx)
    (by simpa [List.getLast?_reverse] using hfirst)

/-- If the successor of a block member lies in the same block, it is the successor in the
block. -/
theorem succOf_flatten_of_mem {L : List (List Nat)} (hnd : L.flatten.Nodup) (hnil : NIL ∉ L.flatten)
    {b : List Nat} (hb : b ∈ L) {x : Nat} (hx : x ∈ b) (hs : succOf L.flatten x ∈ b) :
    succOf L.flatten x = succOf b x := by
  by_cases hlast : b.getLast? = some x
  · exfalso
    obtain ⟨L1, L2, rfl⟩ := List.mem_iff_append.mp hb
    rw [List.flatten_append, List.flatten_cons] at hnd hnil hs
    have hn1 := (List.nodup_append.mp hnd).1
    have hxL1 : x ∉ L1.flatten :=
      fun h => (List.nodup_append.mp hnd).2.2 x h x (by simp [hx]) rfl
    have h23 := (List.nodup_append.mp hnd).2.1
    rw [succOf_append hn1, if_neg hxL1, succOf_append (List.nodup_append.mp h23).1, if_pos hx,
      if_pos hlast] at hs
    -- the head of the following blocks is not in `b`
    rcases hL2 : L2.flatten with _ | ⟨y, t⟩
    · rw [hL2] at hs; simp at hs
      exact hnil (List.mem_append_right _ (List.mem_append_left _ hs))
    · rw [hL2] at hs h23
      simp only [List.headD_cons] at hs
      exact (List.nodup_append.mp h23).2.2 y hs y (by simp) rfl
  · exact succOf_flatten hnd hb hx hlast

/-! ### Sortedness after changing one position -/

/-- Changing the value at one member of a sorted list keeps it sorted when the new value lies
strictly between the values at its neighbours. -/
theorem isChain_update {l : List Nat} (hnd : l.Nodup) {f f' : Nat → Nat} (hs : (l.map f).IsChain (· < ·))
    {x : Nat} (hx : x ∈ l) (hother : ∀ y ∈ l, y ≠ x → f' y = f y)
    (hpred : predOf l x ≠ NIL → f (predOf l x) < f' x)
    (hsucc : succOf l x ≠ NIL → f' x < f (succOf l x)) (hnil : NIL ∉ l) :
    (l.map f').IsChain (· < ·) := by
  obtain ⟨l1, l2, rfl⟩ := List.mem_iff_append.mp hx
  have hp := predOf_mid hnd
  have hsu := succOf_mid hnd
  have hx1 : x ∉ l1 := fun h => (List.nodup_append.mp hnd).2.2 x h x (by simp) rfl
  have hx2 : x ∉ l2 := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
  have e1 : l1.map f' = l1.map f :=
    List.map_congr_left fun y hy => hother y (by simp [hy]) (fun h => hx1 (h ▸ hy))
  have e2 : l2.map f' = l2.map f :=
    List.map_congr_left fun y hy => hother y (by simp [hy]) (fun h => hx2 (h ▸ hy))
  simp only [List.map_append, List.map_cons, e1, e2] at hs ⊢
  rw [List.isChain_append] at hs ⊢
  rw [List.isChain_cons] at hs ⊢
  refine ⟨hs.1, ⟨?_, hs.2.1.2⟩, ?_⟩
  · intro y hy
    cases l2 with
    | nil => simp at hy
    | cons a t =>
      simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      have : a ≠ NIL := fun h => hnil (by simp [h])
      have := hsucc (by rw [hsu]; simpa using this)
      rw [hsu] at this; simpa using this
  · intro y hy z hz
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
    subst hz
    rcases l1.eq_nil_or_concat with h | ⟨l1', a, rfl⟩
    · subst h; simp at hy
    · simp only [List.concat_eq_append] at *
      simp only [List.map_append, List.map_cons, List.map_nil, List.getLast?_append,
        List.getLast?_singleton, Option.some_or, Option.mem_def, Option.some.injEq] at hy
      subst hy
      have : a ≠ NIL := fun h => hnil (by simp [h])
      have := hpred (by rw [hp]; simpa using this)
      rw [hp] at this; simpa using this

end OM.Proof
