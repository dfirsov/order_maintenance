import OM.Proof.Top.StartViews

/-!
# M5: what `startDrain` computes, under the invariant

The sides (`sidesOf`, `fixSides`), the cut (Lemma T0), and the parts.
-/

namespace OM.Proof.Top

open OM.Model OM.Proof

set_option linter.deprecated false

/-! ### `sidesOf` and `fixSides` -/

theorem lookup_assocSet (l : List (Nat × Side)) (k k' : Nat) (sd : Side) :
    lookup (assocSet l k sd) k' = if k' = k then some sd else lookup l k' := by
  by_cases h : k' = k
  · subst h; rw [if_pos rfl, lookup_assocSet_eq]
  · rw [if_neg h, lookup_assocSet_ne _ _ _ _ h]

/-- The step of `sidesOf`. -/
def sideStep (b : Nat) (acc : List (Nat × Side) × Side) (e : Nat) : List (Nat × Side) × Side :=
  let sd' := if e == b then Side.right else acc.2
  (assocSet acc.1 e sd', sd')

theorem sidesOf_eq (order : List Nat) (b : Nat) : sidesOf order b = (order.foldl (sideStep b) ([], .left)).1 := rfl

theorem sideStep_fold {b : Nat} : ∀ (l : List Nat), b ∉ l → ∀ (acc : List (Nat × Side)) (sd : Side),
    (l.foldl (sideStep b) (acc, sd)).2 = sd ∧
      ∀ e, lookup (l.foldl (sideStep b) (acc, sd)).1 e = if e ∈ l then some sd else lookup acc e
  | [], _, acc, sd => ⟨rfl, fun e => by simp⟩
  | x :: l, hb, acc, sd => by
    simp only [List.mem_cons, not_or] at hb
    simp only [List.foldl_cons]
    have hx : (sideStep b (acc, sd) x) = (assocSet acc x sd, sd) := by
      unfold sideStep; simp [Ne.symm hb.1]
    rw [hx]
    obtain ⟨h1, h2⟩ := sideStep_fold l hb.2 (assocSet acc x sd) sd
    refine ⟨h1, fun e => ?_⟩
    rw [h2, lookup_assocSet]
    by_cases he : e ∈ l
    · simp [he]
    · by_cases hex : e = x
      · simp [hex]
      · simp [he, hex]

/-- **`sidesOf`**: left before the boundary, right from it on. -/
theorem sidesOf_spec {P Q : List Nat} {b : Nat} (hnd : (P ++ b :: Q).Nodup) (e : Nat) :
    lookup (sidesOf (P ++ b :: Q) b) e =
      if e ∈ P then some .left else if e = b ∨ e ∈ Q then some .right else none := by
  have h1 := List.nodup_append.mp hnd
  have hbP : b ∉ P := fun h => h1.2.2 b h b (by simp) rfl
  have hbQ : b ∉ Q := (List.nodup_cons.mp h1.2.1).1
  rw [sidesOf_eq, List.foldl_append, List.foldl_cons]
  obtain ⟨p1, p2⟩ := sideStep_fold P hbP [] .left
  have hb : sideStep b (P.foldl (sideStep b) ([], .left)) b =
      (assocSet (P.foldl (sideStep b) ([], .left)).1 b .right, .right) := by
    unfold sideStep; simp
  rw [hb]
  obtain ⟨-, q2⟩ := sideStep_fold Q hbQ (assocSet (P.foldl (sideStep b) ([], .left)).1 b .right) .right
  rw [q2, lookup_assocSet, p2]
  by_cases heP : e ∈ P
  · have heQ : e ∉ Q := fun h => h1.2.2 e heP e (by simp [h]) rfl
    have heb : e ≠ b := fun h => hbP (h ▸ heP)
    simp [heP, heQ, heb]
  · by_cases heQ : e ∈ Q
    · simp [heP, heQ]
    · by_cases heb : e = b
      · simp [heP, heQ, heb, hbP]
      · simp [heP, heQ, heb, lookup]

/-- **`fixSides`**: a ghost entry takes the side of its first target (a live node). -/
theorem fixSides_spec (ns : Array Node) : ∀ (es : List Nat) (side : List (Nat × Side)),
    (∀ e ∈ es, (ns.getX e).draining = true → (ns.getX (ns.getX e).t1).draining = false ∧
      (lookup side (ns.getX e).t1).isSome) →
    ∃ side', fixSides ns es side = some side' ∧ ∀ x, lookup side' x =
      if x ∈ es ∧ (ns.getX x).draining = true then lookup side (ns.getX x).t1 else lookup side x
  | [], side, _ => ⟨side, rfl, fun x => by simp⟩
  | e :: es, side, h => by
    by_cases hd : (ns.getX e).draining = true
    · obtain ⟨hl, hs⟩ := h e (by simp) hd
      obtain ⟨st, hst⟩ := Option.isSome_iff_exists.mp hs
      have hrest : ∀ e' ∈ es, (ns.getX e').draining = true → (ns.getX (ns.getX e').t1).draining = false ∧
          (lookup (assocSet side e st) (ns.getX e').t1).isSome := by
        intro e' he' hd'
        obtain ⟨a, b⟩ := h e' (by simp [he']) hd'
        refine ⟨a, ?_⟩
        rw [lookup_assocSet]
        split
        · rfl
        · exact b
      obtain ⟨side', h1, h2⟩ := fixSides_spec ns es (assocSet side e st) hrest
      refine ⟨side', by simp only [fixSides, hd, if_true, hst]; exact h1, fun x => ?_⟩
      rw [h2]
      by_cases hx : x ∈ es ∧ (ns.getX x).draining = true
      · rw [if_pos hx, if_pos ⟨by simp [hx.1], hx.2⟩, lookup_assocSet]
        have : (ns.getX x).t1 ≠ e := by
          intro h'
          have := (h x (by simp [hx.1]) hx.2).1
          rw [h', hd] at this; exact absurd this (by simp)
        rw [if_neg this]
      · rw [if_neg hx, lookup_assocSet]
        by_cases hxe : x = e
        · subst hxe; rw [if_pos rfl, if_pos ⟨by simp, hd⟩, hst]
        · rw [if_neg hxe, if_neg]
          rintro ⟨hm, hd'⟩
          simp only [List.mem_cons, hxe, false_or] at hm
          exact hx ⟨hm, hd'⟩
    · have hrest : ∀ e' ∈ es, (ns.getX e').draining = true → (ns.getX (ns.getX e').t1).draining = false ∧
          (lookup side (ns.getX e').t1).isSome := fun e' he' hd' => h e' (by simp [he']) hd'
      obtain ⟨side', h1, h2⟩ := fixSides_spec ns es side hrest
      refine ⟨side', by simp only [fixSides, hd]; exact h1, fun x => ?_⟩
      rw [h2]
      by_cases hxe : x = e
      · subst hxe
        have : ¬(x ∈ es ∧ (ns.getX x).draining = true) := fun h' => hd h'.2
        rw [if_neg this, if_neg (fun h' => hd h'.2)]
      · simp only [List.mem_cons, hxe, false_or]

end OM.Proof.Top
