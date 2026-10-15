import OM.Proof.Top.PresStart
import OM.Proof.Cost.Fresh

/-!
# M5: the deferred construction of the initial chain (runs of `initStep`)
-/

namespace OM.Proof.Top

open OM.Model OM.Proof

set_option linter.deprecated false

/-! ### Arrays as total maps -/

theorem getX_push' {α : Type} [Inhabited α] (a : Array α) (x : α) (i : Nat) :
    (a.push x).getX i = if i = a.size then x else a.getX i := by
  simp only [Array.getX, Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split <;> rfl

theorem size_setX' {α : Type} [Inhabited α] (a : Array α) (i : Nat) (v : α) :
    (a.setX i v).size = max a.size (i + 1) := by
  unfold Array.setX
  split
  · simp; omega
  · simp; omega

theorem getX_setX' {α : Type} [Inhabited α] (a : Array α) (i : Nat) (v : α) (j : Nat) :
    (a.setX i v).getX j = if j = i then v else a.getX j := by
  unfold Array.setX
  split
  · next hi =>
    simp only [Array.getX, Array.getD_eq_getD_getElem?, Array.set!, Array.getElem?_setIfInBounds]
    by_cases hj : i = j
    · subst hj; simp [hi]
    · simp [hj, Ne.symm hj]
  · next hi =>
    rw [getX_push']
    have hs : (a ++ Array.replicate (i - a.size) default).size = i := by simp; omega
    rw [hs]
    by_cases hj : j = i
    · rw [if_pos hj, if_pos hj]
    · rw [if_neg hj, if_neg hj]
      simp only [Array.getX, Array.getD_eq_getD_getElem?, Array.getElem?_append]
      split
      · rfl
      · rw [Array.getElem?_replicate]
        split
        · simp; rw [Array.getElem?_eq_none (by omega)]; rfl
        · rw [Array.getElem?_eq_none (by omega)]

theorem getX_modify' {α : Type} [Inhabited α] (a : Array α) (f : α → α) (i j : Nat) :
    (a.modify i f).getX j = if j = i ∧ i < a.size then f (a.getX j) else a.getX j := by
  simp only [Array.getX, Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases e : i = j
  · subst e
    by_cases hi : i < a.size
    · simp [hi]
    · rw [if_neg (show ¬(i = i ∧ i < a.size) from fun h => hi h.2), Array.getElem?_eq_none (by omega)]; simp
  · rw [if_neg (show ¬(j = i ∧ i < a.size) from fun h => e h.1.symm)]; simp [e]

/-- The new chain node of height `pr.h`, before it is linked from below. -/
def chainNew (P : Params) (pr : Prep) (n : Node) : Node :=
  { n with
    children := [pr.below], table := [(pr.below, 1 <<< (P.beta - 1))],
    weight := 1, first := pr.chunk, last := pr.chunk }

/-- The prep record after building height `pr.h` as node `v`. -/
def prepNext (P : Params) (pr : Prep) (v : Nat) : Prep :=
  { pr with
    h := pr.h + 1, below := v, path := pr.path.setX pr.h v,
    tag := pr.tag ||| ((1 <<< (P.beta - 1)) <<< ((pr.h - 1) * P.beta)) }

/-- A middle step: node `v = |nodes|` of height `pr.h ≥ 2`. -/
theorem initStep_mid (s : Core) (pr : Prep) (hp : s.prep = some pr) (h1 : pr.h ≠ 1) (hH : pr.h ≤ s.P.H) :
    initStep.run s = .ok false { s with
      nodes := ((s.nodes.push { height := pr.h }).modify s.nodes.size (chainNew s.P pr)).modify pr.below
        (fun n => { n with inTables := [s.nodes.size], livePar := s.nodes.size }),
      prep := some (prepNext s.P pr s.nodes.size) } := by
  unfold initStep
  simp [hp, h1, hH, newNode, setInTables, prepNext]
  rfl

/-- The first step: reset, then node `1` of height `1` above chunk `pr.chunk`. -/
theorem initStep_first (s : Core) (pr : Prep) (hp : s.prep = some pr) (h1 : pr.h = 1) (hH : 1 ≤ s.P.H) :
    initStep.run s = .ok false { s with
      nodes := (#[default].push { height := 1 }).modify 1 (chainNew s.P pr), path := #[],
      cin := ((#[] : Array (List Nat)).setX pr.chunk []).setX pr.chunk [1],
      lpar := (#[] : Array Nat).setX pr.chunk 1,
      prep := some (prepNext s.P pr 1) } := by
  unfold initStep
  simp [hp, h1, hH, newNode, setInTables, prepNext, resetTop, setLpar]
  rfl

/-- The last step: store the path and the tag. -/
theorem initStep_last (s : Core) (pr : Prep) (hp : s.prep = some pr) (h1 : pr.h ≠ 1) (hH : s.P.H < pr.h) :
    initStep.run s = .ok true { s with
      path := s.path.setX pr.chunk pr.path, C := s.C.modify pr.chunk (fun C => { C with tag := pr.tag }),
      prep := none } := by
  unfold initStep
  simp [hp, h1, show ¬(pr.h ≤ s.P.H) by omega, setPath]
  rfl

end OM.Proof.Top
