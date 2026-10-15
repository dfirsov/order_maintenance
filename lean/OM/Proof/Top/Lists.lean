import OM.Proof.Top.Frame
import OM.Proof.Correct.Wrapper

/-!
# M5: list facts

* filters whose predicate changes at one element (`filter_erase_of`, `filter_snoc_of`,
  `filter_cons_of`): how a range changes when one chunk moves;
* a convex filter is an infix (`filter_infix_of_convex`): ranges are blocks of the chunk list;
* neighbours in an infix triple `[a, b, c]` (`Infix3.*`).
-/

namespace OM.Proof.Top

open OM.Model OM.Proof

set_option linter.deprecated false

theorem Array.size_setX {α : Type} [Inhabited α] (a : Array α) (i : Nat) (v : α) :
    (a.setX i v).size = if i < a.size then a.size else i + 1 := by
  unfold Array.setX
  split
  · simp
  · simp; omega

/-! ### Filters changed at one element -/

theorem filter_erase_of {l : List Nat} (hl : l.Nodup) {p p' : Nat → Bool} {c : Nat}
    (hpp : ∀ x ∈ l, x ≠ c → p' x = p x) (hc : p' c = false) :
    l.filter p' = (l.filter p).erase c := by
  induction l with
  | nil => simp
  | cons x t ih =>
    have hx := List.nodup_cons.mp hl
    have ih' := ih hx.2 (fun y hy hyc => hpp y (List.mem_cons_of_mem _ hy) hyc)
    by_cases hxc : x = c
    · subst hxc
      rw [List.filter_cons, hc]
      simp only [Bool.false_eq_true, if_false, ih']
      by_cases hpx : p x = true
      · rw [List.filter_cons, if_pos hpx, List.erase_cons_head]
        exact List.erase_of_not_mem (fun h => hx.1 (List.mem_of_mem_filter h))
      · rw [List.filter_cons, if_neg hpx]
    · rw [List.filter_cons, List.filter_cons, hpp x (by simp) hxc, ih']
      split
      · rw [List.erase_cons_tail (by simpa using hxc)]
      · rfl

theorem filter_snoc_of {l : List Nat} (hl : l.Nodup) {p p' : Nat → Bool} {c : Nat}
    (hpp : ∀ x ∈ l, x ≠ c → p' x = p x) (hc : p' c = true) (hpc : p c = false) (hcl : c ∈ l)
    (hbefore : ∀ x ∈ l, p x = true → x ≠ c → Before l x c) :
    l.filter p' = l.filter p ++ [c] := by
  induction l with
  | nil => simp at hcl
  | cons x t ih =>
    have hx := List.nodup_cons.mp hl
    by_cases hxc : x = c
    · subst hxc
      rw [List.filter_cons, hc, if_pos rfl]
      have h1 : t.filter p' = t.filter p := by
        apply List.filter_congr; intro y hy
        exact hpp y (List.mem_cons_of_mem _ hy) (fun e => hx.1 (e ▸ hy))
      have h2 : t.filter p = [] := by
        rw [List.filter_eq_nil_iff]; intro y hy hpy
        have hb := hbefore y (List.mem_cons_of_mem _ hy) hpy (fun e => hx.1 (e ▸ hy))
        rw [before_cons] at hb
        rcases hb with hb | ⟨rfl, -⟩
        · exact hx.1 hb.mem_right
        · exact hx.1 hy
      rw [h1, h2, List.filter_cons, hpc]
      simp only [Bool.false_eq_true, if_false, h2, List.nil_append]
    · have hct : c ∈ t := by
        rcases List.mem_cons.mp hcl with h | h
        · exact absurd h.symm hxc
        · exact h
      have ih' := ih hx.2 (fun y hy hyc => hpp y (List.mem_cons_of_mem _ hy) hyc) hct (by
        intro y hy hpy hyc
        have hb := hbefore y (List.mem_cons_of_mem _ hy) hpy hyc
        rw [before_cons] at hb
        rcases hb with hb | ⟨rfl, -⟩
        · exact hb
        · exact absurd hy hx.1)
      rw [List.filter_cons, List.filter_cons, hpp x (by simp) hxc, ih']
      split <;> simp

theorem filter_cons_of {l : List Nat} (hl : l.Nodup) {p p' : Nat → Bool} {c : Nat}
    (hpp : ∀ x ∈ l, x ≠ c → p' x = p x) (hc : p' c = true) (hpc : p c = false) (hcl : c ∈ l)
    (hafter : ∀ x ∈ l, p x = true → x ≠ c → Before l c x) :
    l.filter p' = c :: l.filter p := by
  induction l with
  | nil => simp at hcl
  | cons x t ih =>
    have hx := List.nodup_cons.mp hl
    by_cases hxc : x = c
    · subst hxc
      rw [List.filter_cons, hc, if_pos rfl]
      have h1 : t.filter p' = t.filter p := by
        apply List.filter_congr; intro y hy
        exact hpp y (List.mem_cons_of_mem _ hy) (fun e => hx.1 (e ▸ hy))
      rw [h1, List.filter_cons, hpc]; simp
    · have hct : c ∈ t := by
        rcases List.mem_cons.mp hcl with h | h
        · exact absurd h.symm hxc
        · exact h
      have hpx : p x = false := by
        by_contra hpx
        have hb := hafter x (by simp) (by simpa using hpx) hxc
        rw [before_cons] at hb
        rcases hb with hb | ⟨e, -⟩
        · exact hx.1 hb.mem_right
        · exact hxc e.symm
      rw [List.filter_cons, List.filter_cons, hpp x (by simp) hxc, hpx]
      simp only [Bool.false_eq_true, if_false]
      exact ih hx.2 (fun y hy hyc => hpp y (List.mem_cons_of_mem _ hy) hyc) hct (by
        intro y hy hpy hyc
        have hb := hafter y (List.mem_cons_of_mem _ hy) hpy hyc
        rw [before_cons] at hb
        rcases hb with hb | ⟨e, -⟩
        · exact hb
        · exact absurd e.symm hxc)

/-! ### Convex filters -/

/-- A filter that is convex (closed under betweenness) is a block of the list. -/
theorem filter_infix_of_convex {l : List Nat} (hl : l.Nodup) {p : Nat → Bool}
    (hcv : ∀ a b d, p a = true → p d = true → Before l a b → Before l b d → p b = true) :
    l.filter p <:+: l := by
  induction l with
  | nil => simp
  | cons x t ih =>
    have hx := List.nodup_cons.mp hl
    have ih' := ih hx.2 (fun a b d ha hd hab hbd => hcv a b d ha hd (hab.cons x) (hbd.cons x))
    by_cases hpx : p x = true
    · rw [List.filter_cons, if_pos hpx]
      -- the rest of the block is a prefix of `t`
      have hpre : t.filter p <+: t := by
        obtain ⟨u, w, e⟩ := ih'
        cases u with
        | nil => exact ⟨w, by simpa using e⟩
        | cons y u =>
          cases hf : t.filter p with
          | nil => exact List.nil_prefix
          | cons z r =>
            exfalso
            -- `y` lies between `x` and `z`, so it satisfies `p`, so it is in the filter before `z`
            have hzt : z ∈ t := List.mem_of_mem_filter (by rw [hf]; simp)
            have hpz : p z = true := (List.mem_filter.mp (by rw [hf]; simp)).2
            have hyz : Before t y z := by
              rw [← e, hf]
              have : y :: u ++ z :: r ++ w = [y] ++ (u ++ z :: r ++ w) := by simp
              rw [this]; exact before_append_mem (by simp) (by simp)
            have hpy : p y = true := hcv x y z hpx hpz (by
              rw [before_cons]; exact Or.inr ⟨rfl, hyz.mem_left⟩) (hyz.cons x)
            have hyf : y ∈ t.filter p := List.mem_filter.mpr ⟨hyz.mem_left, hpy⟩
            rw [hf] at hyf
            have hnd : (y :: u ++ z :: r ++ w).Nodup := by rw [← hf, e]; exact hx.2
            have : y ∉ z :: r := by
              intro hm
              have := List.nodup_append.mp (List.nodup_append.mp hnd).1
              exact this.2.2 y (by simp) y hm rfl
            exact this hyf
      exact (List.cons_prefix_cons.mpr ⟨rfl, hpre⟩).isInfix
    · rw [List.filter_cons, if_neg hpx]
      exact ih'.trans (List.suffix_cons x t).isInfix

/-! ### Ends of a list -/

theorem headD_mem {l : List Nat} (h : l ≠ []) (d : Nat) : l.headD d ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => simp

theorem getLastD_mem {l : List Nat} (h : l ≠ []) (d : Nat) : l.getLastD d ∈ l := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast h]
  simp [List.getLast_mem]

theorem before_headD {l : List Nat} {c d : Nat} (hc : c ∈ l) (hne : c ≠ l.headD d) :
    Before l (l.headD d) c := by
  cases l with
  | nil => simp at hc
  | cons a t =>
    simp only [List.headD_cons] at hne ⊢
    rw [before_cons]
    rcases List.mem_cons.mp hc with h | h
    · exact absurd h hne
    · exact Or.inr ⟨rfl, h⟩

theorem before_getLastD {l : List Nat} {c d : Nat} (hc : c ∈ l) (hne : c ≠ l.getLastD d) :
    Before l c (l.getLastD d) := by
  have hl : l ≠ [] := List.ne_nil_of_mem hc
  obtain ⟨u, a, rfl⟩ := List.eq_nil_or_concat l |>.resolve_left hl
  rw [List.concat_eq_append] at hc hne ⊢
  simp only [List.getLastD_eq_getLast?, List.getLast?_append, List.getLast?_singleton,
    Option.some_or, Option.getD_some] at hne ⊢
  rcases List.mem_append.mp hc with h | h
  · exact before_append_mem h (by simp)
  · simp at h; exact absurd h hne

/-- In a block `y :: z :: _` of a nodup list, `z` follows `y`. -/
theorem succOf_infix {l r : List Nat} {y z : Nat} (hl : l.Nodup) (h : y :: z :: r <:+: l) :
    succOf l y = z := by
  obtain ⟨u, w, rfl⟩ := h
  have : u ++ y :: z :: r ++ w = u ++ y :: (z :: (r ++ w)) := by simp
  rw [this] at hl ⊢; rw [succOf_mid hl]; rfl

theorem predOf_infix {l r : List Nat} {y z : Nat} (hl : l.Nodup) (h : r ++ [z, y] <:+: l) :
    predOf l y = z := by
  obtain ⟨u, w, rfl⟩ := h
  have : u ++ (r ++ [z, y]) ++ w = (u ++ r ++ [z]) ++ y :: w := by simp
  rw [this] at hl ⊢; rw [predOf_mid hl]; simp

theorem headD_ne_nil' {l : List Nat} (hnil : NIL ∉ l) (hl : l ≠ []) : l.headD NIL ≠ NIL :=
  fun e => hnil (e ▸ headD_mem hl NIL)

theorem getLastD_ne_nil' {l : List Nat} (hnil : NIL ∉ l) (hl : l ≠ []) : l.getLastD NIL ≠ NIL :=
  fun e => hnil (e ▸ getLastD_mem hl NIL)

/-! ### Infix triples -/

theorem before_of_infix2 {l : List Nat} {a b : Nat} (h : [a, b] <:+: l) : Before l a b :=
  h.sublist

theorem infix3_left {l : List Nat} {a b c : Nat} (h : [a, b, c] <:+: l) : [a, b] <:+: l :=
  (show [a, b] <:+: [a, b, c] from ⟨[], [c], rfl⟩).trans h

theorem infix3_right {l : List Nat} {a b c : Nat} (h : [a, b, c] <:+: l) : [b, c] <:+: l :=
  (show [b, c] <:+: [a, b, c] from ⟨[a], [], rfl⟩).trans h

/-- What precedes `b` in a nodup list, with `a` right before `b`, is `a` or precedes `a`. -/
theorem before_pred {l : List Nat} (hl : l.Nodup) {a b x : Nat} (h : [a, b] <:+: l)
    (hx : Before l x b) : x = a ∨ Before l x a := by
  obtain ⟨u, w, rfl⟩ := h
  have e : u ++ [a, b] ++ w = (u ++ [a]) ++ b :: w := by simp
  rw [e] at hx hl
  have hxm := mem_of_before_split hl hx
  rcases List.mem_append.mp hxm with h1 | h1
  · right
    rw [e]
    have : (u ++ [a]) ++ b :: w = u ++ a :: (b :: w) := by simp
    rw [this]; exact before_split h1
  · left; simpa using h1

/-- What follows `b` in a nodup list, with `c` right after `b`, is `c` or follows `c`. -/
theorem before_succ {l : List Nat} (hl : l.Nodup) {b c x : Nat} (h : [b, c] <:+: l)
    (hx : Before l b x) : x = c ∨ Before l c x := by
  obtain ⟨u, w, rfl⟩ := h
  have hm := hx.mem_right
  have hb : b ∉ u := fun hu => by
    have := List.nodup_append.mp hl
    exact (List.nodup_append.mp this.1).2.2 b hu b (by simp) rfl
  have hbw : b ∉ c :: w := by
    intro hm'
    have h1 := List.nodup_append.mp hl
    have h2 := (List.nodup_append.mp h1.1).2.1
    rcases List.mem_cons.mp hm' with e | e
    · subst e; simp at h2
    · exact h1.2.2 b (by simp) b e rfl
  rcases List.mem_append.mp hm with h1 | h1
  · rcases List.mem_append.mp h1 with h2 | h2
    · exfalso
      -- `x ∈ u` comes before `b`
      have hxb : Before (u ++ [b, c] ++ w) x b := by
        have : u ++ [b, c] ++ w = u ++ b :: (c :: w) := by simp
        rw [this]; exact before_split h2
      exact hx.asymm hl hxb
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h2
      rcases h2 with rfl | rfl
      · exact absurd rfl (hx.ne hl)
      · left; rfl
  · right
    have : u ++ [b, c] ++ w = (u ++ [b]) ++ c :: w := by simp
    rw [this]
    have : (u ++ [b]) ++ c :: w = (u ++ [b] ++ [c]) ++ w := by simp
    rw [this]
    exact before_append_mem (by simp) h1

end OM.Proof.Top
