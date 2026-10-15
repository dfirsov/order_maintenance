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

theorem foldl_ext {α β : Type} {f g : β → α → β} :
    ∀ (l : List α) (init : β), (∀ x ∈ l, ∀ acc, f acc x = g acc x) → l.foldl f init = l.foldl g init
  | [], _, _ => rfl
  | x :: t, init, h => by
    simp only [List.foldl_cons]
    rw [h x (by simp) init]
    exact foldl_ext t _ fun y hy acc => h y (List.mem_cons_of_mem _ hy) acc

/-- `aroundTab`, computed from the table itself. -/
def aroundT (tab : List (Nat × Nat)) (e n1 n2 a b : Nat) : List (Nat × Nat) :=
  let i := (tab.findIdx? (·.1 == e)).getD 0
  (tab.insertIdx (i + 1) (n2, b)).insertIdx i (n1, a)

theorem aroundT_eq {A Bs : List (Nat × Nat)} {e le n1 n2 a b : Nat} (hA : e ∉ A.map (·.1)) :
    aroundT (A ++ (e, le) :: Bs) e n1 n2 a b = aroundTab A Bs e le n1 n2 a b := by
  unfold aroundT aroundTab
  simp only [findIdx_split hA, Option.getD_some]
  rw [insertIdx_len1, insertIdx_len]

/-- The update `insertAroundIn` makes to table `T`. -/
def aroundF (s : Core) (e n1 n2 : Nat) (f : Nat → Nat × Nat) (T : Nat) : Node → Node :=
  setTS (aroundT (s.nodes.getX T).table e n1 n2 (f T).1 (f T).2) (sideAround (s.nodes.getX T) e n1 n2)

/-- Entry `e` is in table `T`, once (as the table's keys are distinct). -/
def AroundOK (s : Core) (e T : Nat) : Prop :=
  ∃ A le Bs, (s.nodes.getX T).table = A ++ (e, le) :: Bs ∧ e ∉ A.map (·.1) ∧
    ((s.nodes.getX T).draining = true → (lookup (s.nodes.getX T).side e).isSome)

/-- **Insertions around `e` in a list of distinct tables.** -/
theorem forM_around_run (e n1 n2 : Nat) (f : Nat → Nat × Nat) (hne : n1 ≠ e) :
    ∀ (tbs : List Nat) (s : Core), tbs.Nodup → (∀ T ∈ tbs, AroundOK s e T) →
      ((tbs.map fun T => (T, f T)).forM (insertAroundIn e n1 n2)).run s =
        .ok ⟨⟩ { s with nodes := tbs.foldl (fun ns T => ns.modify T (aroundF s e n1 n2 f T)) s.nodes }
  | [], s, _, _ => rfl
  | T :: rest, s, hnd, hok => by
    have hT := List.nodup_cons.mp hnd
    obtain ⟨A, le, Bs, htab, hA, hside⟩ := hok T (by simp)
    show (do insertAroundIn e n1 n2 (T, f T); (rest.map fun T => (T, f T)).forM (insertAroundIn e n1 n2)).run s = _
    rw [run_bind, insertAroundIn_run htab hA hne hside]
    simp only
    set s1 : Core := { s with nodes := s.nodes.modify T (setTS (aroundTab A Bs e le n1 n2 (f T).1 (f T).2) (sideAround (s.nodes.getX T) e n1 n2)) } with hs1
    have hsame : ∀ T', T' ≠ T → s1.nodes.getX T' = s.nodes.getX T' := fun T' h => by
      rw [hs1]; show (s.nodes.modify T _).getX T' = _; rw [Array.getX_modify, if_neg (fun h' => h h'.1.symm)]
    have hok1 : ∀ T' ∈ rest, AroundOK s1 e T' := fun T' hT' => by
      have hne' : T' ≠ T := fun h => hT.1 (h ▸ hT')
      unfold AroundOK; rw [hsame T' hne']; exact hok T' (by simp [hT'])
    rw [forM_around_run e n1 n2 f hne rest s1 hT.2 hok1]
    congr 1
    simp only [hs1, List.foldl_cons]
    have hTF : aroundF s e n1 n2 f T = setTS (aroundTab A Bs e le n1 n2 (f T).1 (f T).2)
        (sideAround (s.nodes.getX T) e n1 n2) := by
      unfold aroundF; rw [htab, aroundT_eq hA]
    rw [hTF]
    congr 1
    apply foldl_ext
    intro T' hT' acc
    have hne' : T' ≠ T := fun h => hT.1 (h ▸ hT')
    unfold aroundF; rw [hsame T' hne']

end OM.Proof.Top
