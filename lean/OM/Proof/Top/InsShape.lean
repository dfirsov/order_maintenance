import OM.Proof.Top.PresIns

/-!
# M5: the order invariant after a chunk split

The chunk list gains `y` right before and `z` right after `x`; `y` and `z` carry `x`'s path, are
entries of `x`'s tables next to it, and children of `x`'s live parent next to it.
-/

namespace OM.Proof.Top

open OM.Model OM.Proof

set_option linter.deprecated false

/-- The chunk list after the split. -/
def clIns (cl : List Nat) (x y z : Nat) : List Nat := cl.replace1 x [y, x, z]

theorem replace1_split {A B : List Nat} {x : Nat} (ys : List Nat) (hA : x ∉ A) :
    (A ++ x :: B).replace1 x ys = A ++ ys ++ B := by
  induction A with
  | nil => simp [List.replace1]
  | cons a t ih =>
    simp only [List.mem_cons, not_or] at hA
    simp only [List.cons_append, List.replace1, if_neg (Ne.symm hA.1), ih hA.2]

/-- The order after the split: the chunk list changes. -/
def ordIns (ord : Nat → List Nat) (cl : List Nat) (x y z : Nat) : Nat → List Nat :=
  fun k => if k = 0 then clIns cl x y z else ord k

section shape
variable {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat}
  (hI : InvJ (ts s) cl ord dr n0 none) (hTP : TopParams s.P)
  (hcs : ∀ c, c ∈ cl ↔ 1 ≤ c ∧ c < s.C.size) {x : Nat} (hx : x ∈ cl)
include hI hcs hx

theorem ins_cl : ∃ A B, cl = A ++ x :: B ∧ x ∉ A ∧ x ∉ B ∧
    clIns cl x s.C.size (s.C.size + 1) = A ++ s.C.size :: x :: (s.C.size + 1) :: B := by
  have hnd : cl.Nodup := hI.shape.ord0 ▸ hI.shape.ordNodup 0
  obtain ⟨A, B, rfl⟩ := List.mem_iff_append.mp hx
  have h1 := List.nodup_append.mp hnd
  have hA : x ∉ A := fun h => h1.2.2 x h x (by simp) rfl
  have hB : x ∉ B := fun h => (List.nodup_cons.mp h1.2.1).1 h
  refine ⟨A, B, rfl, hA, hB, ?_⟩
  unfold clIns; rw [replace1_split _ hA]; simp

theorem ins_fresh : s.C.size ∉ cl ∧ s.C.size + 1 ∉ cl := by
  constructor <;> intro h <;> have := (hcs _).mp h <;> omega

theorem ins_cl_nodup : (clIns cl x s.C.size (s.C.size + 1)).Nodup := by
  obtain ⟨A, B, hcl, hA, hB, hcl'⟩ := ins_cl hI hcs hx
  have hnd : cl.Nodup := hI.shape.ord0 ▸ hI.shape.ordNodup 0
  obtain ⟨hy, hz⟩ := ins_fresh hI hcs hx
  rw [hcl'];  rw [hcl] at hnd hy hz
  simp only [List.mem_append, List.mem_cons, not_or] at hy hz
  have h1 := List.nodup_append.mp hnd
  rw [List.nodup_append]
  refine ⟨h1.1, ?_, ?_⟩
  · simp only [List.nodup_cons, List.mem_cons, not_or]
    refine ⟨⟨by omega, by omega, fun h => hy.2.2 h⟩, ⟨by omega, hB⟩, fun h => hz.2.2 h,
      (List.nodup_cons.mp h1.2.1).2⟩
  · intro a ha b hb e
    subst e
    simp only [List.mem_cons] at hb
    rcases hb with rfl | rfl | rfl | hb
    · exact hy.1 ha
    · exact hA ha
    · exact hz.1 ha
    · exact h1.2.2 a ha a (by simp [hb]) rfl

theorem ins_sub : cl.Sublist (clIns cl x s.C.size (s.C.size + 1)) := by
  obtain ⟨A, B, hcl, -, -, hcl'⟩ := ins_cl hI hcs hx
  rw [hcl', hcl]
  exact (List.Sublist.refl A).append (((List.sublist_cons_self _ _).cons_cons x).cons _)

variable {f1x i1 : Nat} {t : TS} (F : InsFrame s x f1x i1 t)
include F

/-- The tables of `x` after the split: `y` right before and `z` right after `x`. -/
theorem ins_table (hTP : TopParams s.P) {T : Nat} (hT : T ∈ s.cin.getX x) :
    ∃ A le Bs a b, (s.nodes.getX T).table = A ++ (x, le) :: Bs ∧ x ∉ A.map (·.1) ∧
      (nd t T).table = A ++ (s.C.size, a) :: (x, le) :: (s.C.size + 1, b) :: Bs ∧
      GapsGe s.P.beta (gapB s.P.beta (n0 T) (dr T + 1))
        ((A ++ (s.C.size, a) :: (x, le) :: (s.C.size + 1, b) :: Bs).map (·.2)) ∧
      1 ≤ gapB s.P.beta (n0 T) (dr T + 1) ∧
      ((s.nodes.getX T).draining = true → (lookup (s.nodes.getX T).side x).isSome) := by
  obtain ⟨A, le, Bs, htab, hA, hside, h1, h2, hB, hg⟩ :=
    start_room hI hTP hx (T := T) hT s.C.size (s.C.size + 1)
  simp only [ts_P] at hB hg h1 h2
  have hTs : T < s.nodes.size := by
    have hent : Ent ord 0 x := by unfold Ent; rw [hI.shape.ord0]; exact hx
    have hT' : T ∈ tabs (ts s) 0 x := by unfold tabs; rw [if_pos rfl]; exact hT
    exact ((hI.shape.tabsIff 0 x T hent).mp hT').1.2.1
  refine ⟨A, le, Bs, _, _, htab, hA, ?_, by rw [gapB_succ]; exact hg, by rw [gapB_succ]; omega, hside⟩
  · rw [F.table, if_pos ⟨hT, hTs⟩]
    show aroundT (nd (ts s) T).table x _ _ _ _ = _
    rw [htab, aroundT_eq hA]
    unfold insF aroundTab
    have e1 := roomL_eq (β := s.P.beta) (Bs := Bs) (le := le) hA true
    have e2 := roomL_eq (β := s.P.beta) (Bs := Bs) (le := le) hA false
    show A ++ (s.C.size, roomL s.P.beta (s.nodes.getX T).table x true) :: (x, le) ::
      (s.C.size + 1, roomL s.P.beta (s.nodes.getX T).table x false) :: Bs = _
    have htab' : (s.nodes.getX T).table = A ++ (x, le) :: Bs := htab
    rw [htab', e1, e2]

end shape

end OM.Proof.Top
