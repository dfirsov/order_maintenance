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

/-- The split chunk's level-1 path node holds `x`. -/
theorem ins_pp1 : pp (ts s) x 1 ∈ s.cin.getX x := by
  have S := hI.shape
  have hent : Ent ord 0 x := by unfold Ent; rw [S.ord0]; exact hx
  have h3 := S.H3
  have hw := S.W3 x hx 1 le_rfl (by omega)
  have he := S.pathEnt x hx 1 (by omega)
  have hm := (S.ordMem 1 le_rfl (by omega) _).mp he
  have : pp (ts s) x 1 ∈ tabs (ts s) 0 x :=
    (S.tabsIff 0 x _ hent).mpr ⟨hm.1, hm.2, hw⟩
  unfold tabs at this; rw [if_pos rfl] at this; exact this

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

theorem ins_order_old {X : Nat} (hX : X ∉ s.cin.getX x) : order t X = order (ts s) X := by
  unfold order Node.order; rw [F.table, if_neg (fun h => hX h.1)]; rfl

theorem ins_labs_old {X : Nat} (hX : X ∉ s.cin.getX x) : labs t X = labs (ts s) X := by
  unfold labs; rw [F.table, if_neg (fun h => hX h.1)]; rfl

/-- Entries only gain: every old entry of a table is still one. -/
theorem ins_order_sup (hTP : TopParams s.P) (X e : Nat) (he : e ∈ order (ts s) X) : e ∈ order t X := by
  by_cases hX : X ∈ s.cin.getX x
  · obtain ⟨A, le, Bs, a, b, htab, -, htab', -⟩ := ins_table hI hcs hx F hTP hX
    unfold order Node.order at he ⊢
    rw [htab']
    have he' : e ∈ (s.nodes.getX X).table.map (·.1) := he
    rw [htab] at he'
    simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons] at he' ⊢
    tauto
  · rw [ins_order_old hI hcs hx F hX]; exact he

/-- **The tag-ordering part of the invariant after the split.** -/
theorem ins_shapeT (hTP : TopParams s.P) :
    ShapeT t (clIns cl x s.C.size (s.C.size + 1)) (ordIns ord cl x s.C.size (s.C.size + 1)) := by
  have S := hI.shape
  have h3 := S.H3
  have eP : (ts s).P = s.P := rfl
  rw [eP] at h3
  obtain ⟨A, B, hcl, hA, hB, hcl'⟩ := ins_cl hI hcs hx
  obtain ⟨hy, hz⟩ := ins_fresh hI hcs hx
  have hnd : cl.Nodup := S.ord0 ▸ S.ordNodup 0
  have hmem : ∀ c, c ∈ clIns cl x s.C.size (s.C.size + 1) ↔ c ∈ cl ∨ c = s.C.size ∨ c = s.C.size + 1 := by
    intro c; rw [hcl', hcl]; simp only [List.mem_append, List.mem_cons]; tauto
  have hord : ∀ k, 1 ≤ k → ordIns ord cl x s.C.size (s.C.size + 1) k = ord k := fun k hk => by
    unfold ordIns; rw [if_neg (by omega)]
  -- the chunk standing for `c` before the split
  have hpp : ∀ c ∈ clIns cl x s.C.size (s.C.size + 1), ∀ j, 1 ≤ j → j ≤ s.P.H →
      pp t c j = pp (ts s) (if c = s.C.size ∨ c = s.C.size + 1 then x else c) j := by
    intro c _ j hj1 hj
    by_cases hc : c = s.C.size ∨ c = s.C.size + 1
    · rw [if_pos hc]; exact F.pp_new c hc j hj1 hj
    · rw [if_neg hc]; push_neg at hc; exact F.pp_old c hc.1 hc.2 j
  have hproj : ∀ c ∈ clIns cl x s.C.size (s.C.size + 1),
      (if c = s.C.size ∨ c = s.C.size + 1 then x else c) ∈ cl := by
    intro c hc; split
    · exact hx
    · rcases (hmem c).mp hc with h | h | h
      · exact h
      all_goals tauto
  refine ⟨by rw [F.P]; exact h3, rfl, fun k => ?_, fun k hk1 hk v => ?_, fun k hk => ?_, fun v hv => ?_,
    ⟨?_, ?_, ?_⟩, fun c hc j hj => ?_, fun c hc j hj1 hj => ?_, fun j hj c d hcd => ?_,
    fun X hX => ?_, fun X hX => ?_⟩
  · by_cases hk : k = 0
    · unfold ordIns; rw [if_pos hk]; exact ins_cl_nodup hI hcs hx
    · rw [hord k (by omega)]; exact S.ordNodup k
  · rw [F.P] at hk
    rw [hord k hk1, S.ordMem k hk1 hk, F.isN, F.ht]
  · rw [F.P] at hk
    rw [hord k (by omega)]; exact S.ordHigh k hk
  · rw [F.isN] at hv; rw [F.ht, F.P]; exact S.htN v hv
  · rw [F.P, hord _ (by omega)]; exact S.root.1
  · rw [F.P, F.liveN]; exact S.root.2.1
  · rw [F.P, F.livePar]; exact S.root.2.2
  · rw [F.P] at hj
    by_cases hj0 : j = 0
    · subst hj0; simp only [Ent, ordIns, pp, ↓reduceIte]; exact hc
    · show _ ∈ _; rw [hord j (by omega), hpp c hc j (by omega) hj]
      exact S.pathEnt _ (hproj c hc) j hj
  · rw [F.P] at hj
    by_cases hj2 : 2 ≤ j
    · rw [hpp c hc j hj1 hj, hpp c hc (j - 1) (by omega) (by omega)]
      exact ins_order_sup hI hcs hx F hTP _ _ (S.W3 _ (hproj c hc) j hj1 hj)
    · have e1 : j = 1 := by omega
      subst e1
      by_cases hcn : c = s.C.size ∨ c = s.C.size + 1
      · rw [F.pp_new c hcn 1 le_rfl (by omega)]
        show c ∈ order t (pp (ts s) x 1)
        obtain ⟨A', le, Bs, a, b, -, -, htab', -⟩ := ins_table hI hcs hx F hTP (ins_pp1 hI hcs hx)
        unfold order Node.order; rw [htab']
        simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
        omega
      · have hc0 : c ∈ cl := by have := hproj c hc; rwa [if_neg hcn] at this
        rw [hpp c hc 1 le_rfl (by omega), if_neg hcn]
        push_neg at hcn
        rw [F.pp_old c hcn.1 hcn.2 0]
        exact ins_order_sup hI hcs hx F hTP _ _ (S.W3 c hc0 1 le_rfl hj)
  · rw [F.P] at hj
    by_cases hj0 : j = 0
    · subst hj0; right; unfold pp; rw [if_pos rfl, if_pos rfl]; unfold ordIns; rw [if_pos rfl]; exact hcd
    · rw [hord j (by omega), hpp c hcd.mem_left j (by omega) hj, hpp d hcd.mem_right j (by omega) hj]
      rw [hcl'] at hcd
      have hyA : s.C.size ∉ A := fun h => hy (by rw [hcl]; simp [h])
      have hzA : s.C.size + 1 ∉ A := fun h => hz (by rw [hcl]; simp [h])
      have hyB : s.C.size ∉ B := fun h => hy (by rw [hcl]; simp [h])
      have hzB : s.C.size + 1 ∉ B := fun h => hz (by rw [hcl]; simp [h])
      rcases before_proj hyA hzA hyB hzB hcd with e | e <;> simp only at e
      · left; rw [e]
      · rw [← hcl] at e; exact S.O2 j hj _ _ e
  · rw [F.isN] at hX
    rw [F.ht]
    by_cases hXc : X ∈ s.cin.getX x
    · have hent : Ent ord 0 x := by unfold Ent; rw [S.ord0]; exact hx
      have hT' : X ∈ tabs (ts s) 0 x := by unfold tabs; rw [if_pos rfl]; exact hXc
      have hX1 := ((S.tabsIff 0 x X hent).mp hT').2.1
      obtain ⟨A', le, Bs, a, b, htab, hA', htab', -⟩ := ins_table hI hcs hx F hTP hXc
      have hO := S.O1 X hX
      rw [hX1, S.ord0] at hO
      unfold order Node.order at hO ⊢
      rw [htab']; rw [show (nd (ts s) X).table = A' ++ (x, le) :: Bs from htab] at hO
      rw [hX1]; simp only [Nat.sub_self]; unfold ordIns; rw [if_pos rfl, hcl']
      rw [hcl] at hO hnd
      simp only [List.map_append, List.map_cons] at hO ⊢
      exact sublist_around hO hA hB
    · rw [ins_order_old hI hcs hx F hXc]
      by_cases h1 : ht (ts s) X - 1 = 0
      · rw [h1]; unfold ordIns; rw [if_pos rfl]
        exact (h1 ▸ S.O1 X hX).trans (S.ord0 ▸ ins_sub hI hcs hx)
      · rw [hord _ (by omega)]; exact S.O1 X hX
  · rw [F.isN] at hX
    rw [F.P]
    by_cases hXc : X ∈ s.cin.getX x
    · obtain ⟨A', le, Bs, a, b, -, -, htab', hg, h1, -⟩ := ins_table hI hcs hx F hTP hXc
      unfold labs; rw [htab']; exact gapsGe_mono h1 hg
    · rw [ins_labs_old hI hcs hx F hXc]; exact S.labsOk X hX

end shape

end OM.Proof.Top
