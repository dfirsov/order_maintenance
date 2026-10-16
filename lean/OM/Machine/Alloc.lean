import OM.Machine.Frame

/-!
# Allocating a list of arrays

`allocAll l` allocates the arrays of `l` in turn, each with the capacity its expression gives.
When the expressions read only locals (`Expr.noLoad`), they evaluate the same throughout, and
the result is exact (`exec_allocAll`): each listed array has its capacity and reads 0, every other
array is unchanged, and so are the locals.
-/

namespace OM.Machine

/-- The expression reads no array. -/
def Expr.noLoad : Expr → Bool
  | .lit _ => true
  | .var _ => true
  | .load _ _ => false
  | .bin _ a b => a.noLoad && b.noLoad
  | .un _ a => a.noLoad

theorem Expr.eval_noLoad {s s' : State} (hl : s'.loc = s.loc) : ∀ (e : Expr), e.noLoad → e.eval s' = e.eval s
  | .lit _, _ => rfl
  | .var x, _ => by simp [eval, hl]
  | .load _ _, h => by simp [noLoad] at h
  | .bin op a b, h => by
    simp only [noLoad, Bool.and_eq_true] at h
    simp only [eval, Expr.eval_noLoad hl a h.1, Expr.eval_noLoad hl b h.2]
  | .un op a, h => by simp only [noLoad] at h; simp only [eval, Expr.eval_noLoad hl a h]

def allocAll (l : List (Arr × Expr)) : Stmt := l.foldr (fun ae c => .seq (.alloc ae.1 ae.2) c) .skip

def allocCost (l : List (Arr × Expr)) : Nat := (l.map fun ae => 1 + ae.2.cost).sum + 1

/-- **Allocating a list of arrays.** -/
theorem exec_allocAll : ∀ (l : List (Arr × Expr)) (s : State),
    (∀ ae ∈ l, ae.2.noLoad ∧ (ae.2.eval s).isSome) → (l.map Prod.fst).Nodup →
    (exec (allocAll l) s).status = .ok ∧ (exec (allocAll l) s).cost = allocCost l ∧
      (exec (allocAll l) s).st.loc = s.loc ∧
      (∀ ae ∈ l, (exec (allocAll l) s).st.cap ae.1 = (ae.2.eval s).getD 0 ∧
        ∀ i, (exec (allocAll l) s).st.mem ae.1 i = 0) ∧
      (∀ b, b ∉ l.map Prod.fst → Same b s (exec (allocAll l) s).st)
  | [], s, _, _ => ⟨rfl, rfl, rfl, fun _ h => by simp at h, fun _ _ => ⟨rfl, rfl⟩⟩
  | (a, e) :: l, s, h, hnd => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hne, hnd⟩ := hnd
    obtain ⟨hn, hev0⟩ := h (a, e) (by simp)
    obtain ⟨va, hev⟩ := Option.isSome_iff_exists.mp hev0
    obtain ⟨s1, hs1⟩ : ∃ s1, s1 = (s.bump (e.maxv s)).alloc a va := ⟨_, rfl⟩
    have hl1 : s1.loc = s.loc := by rw [hs1]; rfl
    have h' : ∀ ae ∈ l, ae.2.noLoad ∧ (ae.2.eval s1).isSome := fun ae hae => by
      obtain ⟨a1, a2⟩ := h ae (by simp [hae])
      exact ⟨a1, by rw [Expr.eval_noLoad hl1 _ a1]; exact a2⟩
    obtain ⟨r1, r2, r3, r4, r5⟩ := exec_allocAll l s1 h' hnd
    have he : exec (allocAll ((a, e) :: l)) s = (Out.bind ⟨s1, 1 + e.cost, .ok⟩ (exec (allocAll l))) := by
      simp only [allocAll, List.foldr_cons, exec, hev]; rw [hs1]
    rw [he]
    simp only [Out.bind, r1]
    refine ⟨trivial, ?_, r3.trans hl1, fun ae hae => ?_, fun b hb => ?_⟩
    · show 1 + e.cost + (exec (allocAll l) s1).cost = allocCost ((a, e) :: l)
      rw [r2]; simp only [allocCost, List.map_cons, List.sum_cons]; omega
    · simp only [List.mem_cons] at hae
      rcases hae with rfl | hae
      · have := r5 a hne
        refine ⟨by rw [this.2, hs1, hev]; simp [State.alloc, State.upd], fun i => by rw [this.1, hs1]; simp [State.alloc]⟩
      · obtain ⟨c1, c2⟩ := r4 ae hae
        obtain ⟨a1, -⟩ := h ae (by simp [hae])
        exact ⟨by rw [c1, Expr.eval_noLoad hl1 _ a1], c2⟩
    · simp only [List.map_cons, List.mem_cons, not_or] at hb
      have := r5 b hb.2
      refine ⟨by rw [this.1, hs1]; simp [State.alloc, State.bump, hb.1], by rw [this.2, hs1]; simp [State.alloc,
        State.bump, State.upd, hb.1]⟩

end OM.Machine
