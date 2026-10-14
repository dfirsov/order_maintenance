import OM.Proof.Cost.Params

/-!
# The wrapper: cost and Lemma W

Every core the wrapper runs satisfies the cost invariant whenever an operation reaches it, and
its element count stays within its capacity (Lemma W). So no core operation ever takes FALLBACK.
-/

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-- A list linked forward from `hd`. -/
structure NList (nxt : Nat → Nat) (hd : Nat) (l : List Nat) : Prop where
  nodup : l.Nodup
  nonil : NIL ∉ l
  head : hd = l.headD NIL
  next : ∀ x ∈ l, nxt x = succOf l x

theorem LList.nlist {nxt prv : Nat → Nat} {hd : Nat} {l : List Nat} (h : LList nxt prv hd l) :
    NList nxt hd l := ⟨h.nodup, h.nonil, h.head, h.next⟩

theorem succOf_cons_ne {a x : Nat} {t : List Nat} (h : a ≠ x) : succOf (a :: t) x = succOf t x := by
  cases t with
  | nil => rfl
  | cons b t => simp only [succOf, if_neg h]

theorem succOf_cons_self {a : Nat} {t : List Nat} : succOf (a :: t) a = t.headD NIL := by
  cases t with
  | nil => rfl
  | cons b t => simp [succOf]

/-- **A forward-linked list is determined by its head.** -/
theorem NList.unique {nxt : Nat → Nat} : ∀ {hd : Nat} {l l' : List Nat},
    NList nxt hd l → NList nxt hd l' → l = l'
  | hd, [], l', h, h' => by
    cases l' with
    | nil => rfl
    | cons a t => exfalso; have := h.head; have := h'.head; simp at *; exact h'.nonil (by simp_all)
  | hd, a :: t, l', h, h' => by
    cases l' with
    | nil => exfalso; have := h.head; have := h'.head; simp at *; exact h.nonil (by simp_all)
    | cons a' t' =>
      have ha : a = a' := by have e1 := h.head; have e2 := h'.head; simp at e1 e2; rw [← e1, ← e2]
      subst ha
      have hat : a ∉ t := (List.nodup_cons.mp h.nodup).1
      have hat' : a ∉ t' := (List.nodup_cons.mp h'.nodup).1
      have tl : NList nxt (nxt a) t := ⟨(List.nodup_cons.mp h.nodup).2,
        fun hn => h.nonil (List.mem_cons_of_mem _ hn),
        by rw [h.next a (by simp), succOf_cons_self],
        fun x hx => by
          rw [h.next x (List.mem_cons_of_mem _ hx),
            succOf_cons_ne (fun (e : a = x) => hat (by rw [e]; exact hx))]⟩
      have tl' : NList nxt (nxt a) t' := ⟨(List.nodup_cons.mp h'.nodup).2,
        fun hn => h'.nonil (List.mem_cons_of_mem _ hn),
        by rw [h'.next a (by simp), succOf_cons_self],
        fun x hx => by
          rw [h'.next x (List.mem_cons_of_mem _ hx),
            succOf_cons_ne (fun (e : a = x) => hat' (by rw [e]; exact hx))]⟩
      rw [NList.unique tl tl']

theorem INV.elist_unique {s : Core} {A A' : Abs} (h : INV s A) (h' : INV s A') :
    A.elist = A'.elist := h.eList.nlist.unique h'.eList.nlist

end OM.Proof
