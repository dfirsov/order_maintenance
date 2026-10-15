import OM.Proof.Top.Labels

/-!
# M5: inserting two entries around one, in every table holding it

`insertAroundIn e n1 n2 (T, a, b)` puts `(n1, a)` right before and `(n2, b)` right after entry
`e` in table `T` (`insertAroundIn_run`); over a list of distinct tables, a fold
(`forM_around_run`). Both `insertAround` (new chunks) and `startDrain` (new targets) do this.
-/

namespace OM.Proof.Top

open OM.Model OM.Proof

set_option linter.deprecated false

/-- The side list after inserting `n1`, `n2` around `e`. -/
def sideAround (T : Node) (e n1 n2 : Nat) : List (Nat × Side) :=
  if T.draining then
    assocSet (assocSet T.side n1 ((lookup T.side e).getD .left)) n2 ((lookup T.side e).getD .left)
  else T.side

theorem lookup_map_replace {β : Type} (l : List (Nat × β)) (k k' : Nat) (v : β) (h : k' ≠ k) :
    (List.find? (fun x => x.1 == k') (l.map fun p => if p.1 == k then (k, v) else p)).map (·.2) =
      (List.find? (fun x => x.1 == k') l).map (·.2) := by
  have hkk : (k == k') = false := by simpa using Ne.symm h
  induction l with
  | nil => rfl
  | cons p t ih =>
    simp only [List.map_cons, List.find?_cons]
    by_cases hp : p.1 = k
    · have hpk : (p.1 == k') = false := by rw [hp]; exact hkk
      simp only [hp, beq_self_eq_true, if_true, hkk, hpk]
      rw [← hp] at ih ⊢; exact ih
    · simp only [show (p.1 == k) = false by simpa using hp, Bool.false_eq_true, if_false]
      split <;> [rfl; exact ih]

theorem lookup_assocSet_ne {β : Type} (l : List (Nat × β)) (k k' : Nat) (v : β) (h : k' ≠ k) :
    lookup (assocSet l k v) k' = lookup l k' := by
  unfold assocSet lookup
  have hkk : (k == k') = false := by simpa using Ne.symm h
  split
  · exact lookup_map_replace l k k' v h
  · simp only [List.find?_append, List.find?_cons, hkk, List.find?_nil]
    cases (List.find? (fun x => x.1 == k') l) <;> rfl

/-- The table of `T` after `insertAroundIn`. -/
def aroundTab (A Bs : List (Nat × Nat)) (e le n1 n2 a b : Nat) : List (Nat × Nat) :=
  A ++ (n1, a) :: (e, le) :: (n2, b) :: Bs

theorem insertAroundIn_run {s : Core} {e n1 n2 T a b : Nat} {A Bs : List (Nat × Nat)} {le : Nat}
    (htab : (s.nodes.getX T).table = A ++ (e, le) :: Bs) (hA : e ∉ A.map (·.1)) (hn1 : n1 ≠ e)
    (hside : (s.nodes.getX T).draining = true → (lookup (s.nodes.getX T).side e).isSome) :
    (insertAroundIn e n1 n2 (T, a, b)).run s = .ok ⟨⟩ { s with nodes := s.nodes.modify T (setTS (aroundTab A Bs e le n1 n2 a b) (sideAround (s.nodes.getX T) e n1 n2)) } := by
  unfold insertAroundIn
  rw [run_bind, tableInsert_run htab hA true a hside]
  have hT : T < s.nodes.size := by
    by_contra h
    have : s.nodes.getX T = default := by unfold Array.getX Array.getD; rw [dif_neg h]
    have hd : (default : Node).table = [] := rfl
    rw [this, hd] at htab; exact absurd htab.symm (by simp)
  set s1 : Core := { s with nodes := s.nodes.modify T (setTS (insTab A Bs e le n1 a true) (sideAfter (s.nodes.getX T) e n1)) } with hs1
  have h1 : s1.nodes.getX T = setTS (insTab A Bs e le n1 a true) (sideAfter (s.nodes.getX T) e n1) (s.nodes.getX T) := by
    rw [hs1]; show (s.nodes.modify T _).getX T = _; rw [Array.getX_modify, if_pos ⟨rfl, hT⟩]
  have htab1 : (s1.nodes.getX T).table = (A ++ [(n1, a)]) ++ (e, le) :: Bs := by
    rw [h1]; simp [setTS, insTab]
  have hA1 : e ∉ (A ++ [(n1, a)]).map (·.1) := by simp [hA, Ne.symm hn1]
  have hside1 : (s1.nodes.getX T).draining = true → (lookup (s1.nodes.getX T).side e).isSome := by
    rw [h1]; simp only [setTS]; intro hd
    unfold sideAfter; rw [if_pos hd, lookup_assocSet_ne _ _ _ _ hn1.symm]; exact hside hd
  show (tableInsert T e n2 false b).run s1 = _
  rw [tableInsert_run htab1 hA1 false b hside1]
  congr 1
  have hside2 : sideAfter (s1.nodes.getX T) e n2 = sideAround (s.nodes.getX T) e n1 n2 := by
    rw [h1]; unfold sideAfter sideAround setTS
    by_cases hd : (s.nodes.getX T).draining = true
    · simp only [hd, if_true]; rw [lookup_assocSet_ne _ _ _ _ hn1.symm]
    · simp only [hd, Bool.false_eq_true, if_false]
  have htab2 : insTab (A ++ [(n1, a)]) Bs e le n2 b false = aroundTab A Bs e le n1 n2 a b := by
    simp [insTab, aroundTab]
  rw [hside2, htab2]
  simp only [hs1]
  congr 1
  apply Array.ext
  · simp
  · intro i _ _
    simp only [Array.getElem_modify]
    split <;> rfl

end OM.Proof.Top
