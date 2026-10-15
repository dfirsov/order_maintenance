import OM.Proof.Top.CopyRest

/-!
# M5: the state after a chunk split, with the path copy completed

`insFin s x`: the top structure after `insertAround x y z` (`y, z` the new chunks) on the linked
core, with the job's path copy completed. Its views, field by field.
-/

namespace OM.Proof.Top

open OM.Model OM.Proof

set_option linter.deprecated false

theorem ts_tag (t : Core) (c : Nat) : (ts t).tag c = (t.C.getX c).tag := rfl
theorem ts_nodes (t : Core) : (ts t).nodes = t.nodes := rfl
theorem ts_path (t : Core) : (ts t).path = t.path := rfl
theorem ts_cin (t : Core) : (ts t).cin = t.cin := rfl
theorem ts_lpar (t : Core) : (ts t).lpar = t.lpar := rfl
theorem ts_P (t : Core) : (ts t).P = t.P := rfl

theorem ts_markState (t : Core) (x y z : Nat) (j : Job) : ts (markState t x y z j) = ts t := by
  unfold ts markState
  congr 1
  funext c
  simp only [Array.getX_modify]
  split_ifs <;> rfl

section defs
variable (s : Core) (x : Nat)

/-- The split's job. -/
def insJob : Job := { x := x, y := s.C.size, z := s.C.size + 1, pc := .copy 1 }

/-- The core with the two new chunks linked around `x`. -/
def ins0 : Core := linkChunkPair (push2 s) x s.C.size (s.C.size + 1)

/-- The labels of the new entries in table `T`. -/
def insF (T : Nat) : Nat × Nat :=
  (roomL s.P.beta (s.nodes.getX T).table x true, roomL s.P.beta (s.nodes.getX T).table x false)

variable (f1x i1 : Nat)

/-- The core after `insertAround`. -/
def ins3 : Core :=
  insFinS (tagsS (ins0 s x) s.C.size (s.C.size + 1) (tagY (ins0 s x) x f1x i1) (tagZ (ins0 s x) x f1x i1))
    x s.C.size (s.C.size + 1) (insF s x)

/-- The top structure after the split, path copy completed. -/
def insFin : TS := copyRest (insJob s x) s.P.H (ts (ins3 s x f1x i1)) 1

end defs

/-! ### The core after `insertAround` -/

section generic
variable (t : Core) (x y z : Nat) (f : Nat → Nat × Nat)

theorem insFinS_P : (insFinS t x y z f).P = t.P := by unfold insFinS joinS; rfl
theorem insFinS_C : (insFinS t x y z f).C = t.C := by unfold insFinS joinS; rfl
theorem insFinS_path : (insFinS t x y z f).path =
    (t.path.setX y (Array.replicate (t.P.H + 1) NIL)).setX z (Array.replicate (t.P.H + 1) NIL) := by
  unfold insFinS joinS; rfl
theorem insFinS_cin : (insFinS t x y z f).cin = (t.cin.setX y (t.cin.getX x)).setX z (t.cin.getX x) := by
  unfold insFinS joinS; rfl
theorem insFinS_lpar : (insFinS t x y z f).lpar = (t.lpar.setX y (t.lpar.getX x)).setX z (t.lpar.getX x) := by
  unfold insFinS joinS; rfl
theorem insFinS_nodes : (insFinS t x y z f).nodes =
    ((t.cin.getX x).foldl (fun ns T => ns.modify T (aroundF t x y z f T)) t.nodes).modify (t.lpar.getX x)
        (fun n => { n with children := n.children.replace1 x [y, x, z] }) := by
  unfold insFinS joinS; rfl

variable (a b : Nat)
theorem tagsS_top : (tagsS t y z a b).P = t.P ∧ (tagsS t y z a b).path = t.path ∧
    (tagsS t y z a b).cin = t.cin ∧ (tagsS t y z a b).lpar = t.lpar ∧ (tagsS t y z a b).nodes = t.nodes ∧
    (tagsS t y z a b).C = (t.C.modify y fun C => { C with tag := a }).modify z fun C => { C with tag := b } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end generic

section views
variable (s : Core) (x f1x i1 : Nat)

theorem ins0_top : (ins0 s x).nodes = s.nodes ∧ (ins0 s x).path = s.path ∧ (ins0 s x).cin = s.cin ∧
    (ins0 s x).lpar = s.lpar ∧ (ins0 s x).P = s.P ∧ (ins0 s x).C.size = s.C.size + 2 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  unfold ins0
  rw [(linkChunkPair_rest (s := push2 s) (x := x) (y := s.C.size) (z := s.C.size + 1)).2.2.2.2.2.2.1]
  simp [push2]

/-- The core right before `insertAroundFinish`: both tags written. -/
abbrev ins2 : Core :=
  tagsS (ins0 s x) s.C.size (s.C.size + 1) (tagY (ins0 s x) x f1x i1) (tagZ (ins0 s x) x f1x i1)

theorem ins3_eq : ins3 s x f1x i1 = insFinS (ins2 s x f1x i1) x s.C.size (s.C.size + 1) (insF s x) := rfl

theorem ins2_top : (ins2 s x f1x i1).P = s.P ∧ (ins2 s x f1x i1).path = s.path ∧
    (ins2 s x f1x i1).cin = s.cin ∧ (ins2 s x f1x i1).lpar = s.lpar ∧ (ins2 s x f1x i1).nodes = s.nodes := by
  obtain ⟨t1, t2, t3, t4, t5, -⟩ := tagsS_top (ins0 s x) s.C.size (s.C.size + 1)
    (tagY (ins0 s x) x f1x i1) (tagZ (ins0 s x) x f1x i1)
  obtain ⟨u1, u2, u3, u4, u5, -⟩ := ins0_top s x
  exact ⟨t1.trans u5, t2.trans u2, t3.trans u3, t4.trans u4, t5.trans u1⟩

theorem ins3_P : (ins3 s x f1x i1).P = s.P := by rw [ins3_eq, insFinS_P, (ins2_top s x f1x i1).1]
theorem ins3_path : (ins3 s x f1x i1).path =
    (s.path.setX s.C.size (Array.replicate (s.P.H + 1) NIL)).setX (s.C.size + 1) (Array.replicate (s.P.H + 1) NIL) := by
  rw [ins3_eq, insFinS_path, (ins2_top s x f1x i1).1, (ins2_top s x f1x i1).2.1]
theorem ins3_cin : (ins3 s x f1x i1).cin = (s.cin.setX s.C.size (s.cin.getX x)).setX (s.C.size + 1) (s.cin.getX x) := by
  rw [ins3_eq, insFinS_cin, (ins2_top s x f1x i1).2.2.1]
theorem ins3_lpar : (ins3 s x f1x i1).lpar =
    (s.lpar.setX s.C.size (s.lpar.getX x)).setX (s.C.size + 1) (s.lpar.getX x) := by
  rw [ins3_eq, insFinS_lpar, (ins2_top s x f1x i1).2.2.2.1]
theorem ins3_nodes : (ins3 s x f1x i1).nodes =
    ((s.cin.getX x).foldl (fun ns T => ns.modify T (aroundF (ins2 s x f1x i1) x s.C.size (s.C.size + 1) (insF s x) T)) s.nodes).modify (s.lpar.getX x) (fun n => { n with children := n.children.replace1 x [s.C.size, x, s.C.size + 1] }) := by
  rw [ins3_eq, insFinS_nodes, (ins2_top s x f1x i1).2.2.1, (ins2_top s x f1x i1).2.2.2.1,
    (ins2_top s x f1x i1).2.2.2.2]

theorem ins3_tag (c : Nat) :
    (ts (ins3 s x f1x i1)).tag c = if c = s.C.size + 1 then tagZ (ins0 s x) x f1x i1
      else if c = s.C.size then tagY (ins0 s x) x f1x i1 else (s.C.getX c).tag := by
  rw [ts_tag, ins3_eq, insFinS_C, (tagsS_top (ins0 s x) s.C.size (s.C.size + 1)
    (tagY (ins0 s x) x f1x i1) (tagZ (ins0 s x) x f1x i1)).2.2.2.2.2]
  show ((((ins0 s x).C.modify s.C.size fun C => { C with tag := tagY (ins0 s x) x f1x i1 }).modify
      (s.C.size + 1) fun C => { C with tag := tagZ (ins0 s x) x f1x i1 }).getX c).tag = _
  have hsz := (ins0_top s x).2.2.2.2.2
  rw [Array.getX_modify, Array.getX_modify, Array.size_modify', hsz]
  by_cases hz : c = s.C.size + 1
  · subst hz; simp
  · by_cases hy : c = s.C.size
    · subst hy; simp
    · simp only [Ne.symm hz, Ne.symm hy, false_and, if_false, hz, hy]
      have := linkChunkPair_cT (s := push2 s) (x := x) (y := s.C.size) (z := s.C.size + 1) c
      unfold cT at this; unfold ins0; rw [this]
      by_cases hc : c < s.C.size
      · simp [push2, Array.getX_push, Nat.ne_of_lt hc, show c ≠ s.C.size + 1 by omega]
      · have h1 : s.C.getX c = default := by unfold Array.getX Array.getD; rw [dif_neg hc]
        simp only [push2, Array.getX_push, Array.size_push, hz, hy, if_false, h1]

end views

end OM.Proof.Top
