import OM.Proof.Correct

/-!
# The bucket priority queue (`OM/Model/PQ.lean`)

`QRep s k inQ bl nb`: the queue of state `s` holds exactly the chunks `c` with `inQ c`, with key
`k c > θ`. Bucket `b` is the doubly linked list `bl b` (from `pqHead b` along `pqNext`, back along
`pqPrev`); the non-empty buckets form the increasing doubly linked list `nb` (from `pqLo` along
`nbNext`), and `pqHi` is its last bucket.

Results: adding and deleting keep the representation; the `+1` adjustment of a quiet chunk's size
never takes the slow path (K2); `pqPopMax` returns a chunk of largest key; `pqEmpty` is exact.
-/

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

structure QRep (s : Core) (k : Nat → Nat) (inQ : Nat → Bool) (bl : Nat → List Nat) (nb : List Nat) :
    Prop where
  where_ : ∀ c, s.pqWhere.getX c = if inQ c then k c else 0
  pos : ∀ c, inQ c = true → s.P.theta < k c
  bucket : ∀ b, LList (fun c => s.pqNext.getX c) (fun c => s.pqPrev.getX c) (s.pqHead.getX b) (bl b)
  bmem : ∀ b c, c ∈ bl b ↔ inQ c = true ∧ k c = b
  nbl : LList (fun b => s.nbNext.getX b) (fun b => s.nbPrev.getX b) s.pqLo nb
  nbmem : ∀ b, b ∈ nb ↔ bl b ≠ []
  sorted : nb.IsChain (· < ·)
  hi : s.pqHi = nb.getLastD 0

/-- The queue holds exactly `inQ`, keyed by `k`. -/
def QInv (s : Core) (k : Nat → Nat) (inQ : Nat → Bool) : Prop := ∃ bl nb, QRep s k inQ bl nb

/-! ### Linked lists under pointwise-equal links -/

theorem LList.congr {nxt prv nxt' prv' : Nat → Nat} {hd hd' : Nat} {l : List Nat}
    (h : LList nxt prv hd l) (hn : ∀ x ∈ l, nxt' x = nxt x) (hp : ∀ x ∈ l, prv' x = prv x)
    (hh : hd' = hd) : LList nxt' prv' hd' l :=
  ⟨h.nodup, h.nonil, hh ▸ h.head, fun x hx => (hn x hx).trans (h.next x hx),
   fun x hx => (hp x hx).trans (h.prev x hx)⟩

theorem LList.nil_iff {nxt prv : Nat → Nat} {hd : Nat} {l : List Nat} (h : LList nxt prv hd l) :
    l = [] ↔ hd = NIL := by
  constructor
  · rintro rfl; exact h.head
  · intro e
    cases l with
    | nil => rfl
    | cons a t => exfalso; have := h.head; simp at this; exact h.nonil (by rw [← this, e]; simp)

end OM.Proof

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-! ### The operations as functions of the state -/

/-- `pqLinkAfter s p`: make bucket `s` non-empty, right after bucket `p` (0: at the front). -/
def linkSt (st : Core) (s p : Nat) : Core :=
  let n := if p = 0 then st.pqLo else st.nbNext.getX p
  let st1 : Core := if p = 0 then { st with pqLo := s } else { st with nbNext := st.nbNext.setX p s }
  let st2 : Core := { st1 with nbPrev := st1.nbPrev.setX s p, nbNext := st1.nbNext.setX s n }
  if n ≠ 0 then { st2 with nbPrev := st2.nbPrev.setX n s } else { st2 with pqHi := s }

/-- `pqAdd c s p`: push `c` at the head of bucket `s`. -/
def addSt (st : Core) (c s p : Nat) : Core :=
  let hd := st.pqHead.getX s
  let st1 : Core := if hd ≠ NIL then
      { st with pqNext := st.pqNext.setX c hd, pqPrev := (st.pqPrev.setX hd c).setX c NIL,
                pqHead := st.pqHead.setX s c }
    else linkSt { st with pqNext := st.pqNext.setX c NIL, pqPrev := st.pqPrev.setX c NIL,
                          pqHead := st.pqHead.setX s c } s p
  { st1 with pqWhere := st1.pqWhere.setX c s }

/-- `pqDel c`: remove `c` from its bucket, and the bucket from the list if it became empty. -/
def delSt (st : Core) (c : Nat) : Core :=
  let s := st.pqWhere.getX c
  let nx := st.pqNext.getX c
  let pv := st.pqPrev.getX c
  let st1 : Core := { st with pqWhere := st.pqWhere.setX c 0 }
  let st2 : Core := if pv ≠ NIL then { st1 with pqNext := st1.pqNext.setX pv nx }
    else { st1 with pqHead := st1.pqHead.setX s nx }
  let st3 : Core := if nx ≠ NIL then { st2 with pqPrev := st2.pqPrev.setX nx pv } else st2
  if st3.pqHead.getX s = NIL then
    let p := st3.nbPrev.getX s
    let n := st3.nbNext.getX s
    let st4 : Core := { st3 with nbPrev := st3.nbPrev.setX s 0, nbNext := st3.nbNext.setX s 0 }
    let st5 : Core := if p ≠ 0 then { st4 with nbNext := st4.nbNext.setX p n }
      else { st4 with pqLo := n }
    if n ≠ 0 then { st5 with nbPrev := st5.nbPrev.setX n p } else { st5 with pqHi := p }
  else st3

theorem pqLinkAfter_run (st : Core) (s p : Nat) :
    (pqLinkAfter s p).run st = .ok () (linkSt st s p) := by
  unfold pqLinkAfter linkSt
  by_cases hp : p = 0
  · subst hp
    by_cases hn : st.pqLo = 0 <;> simp [hn]
  · by_cases hn : st.nbNext.getX p = 0 <;> simp [hp, hn]

theorem pqAdd_run (st : Core) (c s p : Nat) : (pqAdd c s p).run st = .ok () (addSt st c s p) := by
  unfold pqAdd addSt
  by_cases hh : st.pqHead.getX s = NIL
  · simp [run_bind, pqLinkAfter_run, hh]
  · simp [run_bind, hh]

theorem pqDel_run (st : Core) (c : Nat) (hw : st.pqWhere.getX c ≠ 0) :
    (pqDel c).run st = .ok () (delSt st c) := by
  unfold pqDel delSt
  simp only [run_get_bind]
  rw [if_neg (by simpa using hw)]
  by_cases hpv : st.pqPrev.getX c = NIL <;> by_cases hnx : st.pqNext.getX c = NIL <;>
    simp [hpv, hnx, run_bind] <;> split_ifs <;> simp_all

end OM.Proof

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-! ### Sorted lists -/

theorem sorted_split {l : List Nat} (hs : l.IsChain (· < ·)) (s : Nat) (hsl : s ∉ l) :
    l = l.filter (· < s) ++ l.filter (s < ·) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have hst := (List.isChain_cons.mp hs).2
    have hat : ∀ b ∈ t, a < b := by
      have := List.isChain_iff_pairwise.mp hs; exact (List.pairwise_cons.mp this).1
    simp only [List.mem_cons, not_or] at hsl
    by_cases has : a < s
    · simp only [List.filter_cons, has, decide_true, if_true]
      have : ¬ s < a := by omega
      simp only [this, decide_false, Bool.false_eq_true, if_false, List.cons_append]
      congr 1; exact ih hst hsl.2
    · have hsa : s < a := by omega
      simp only [List.filter_cons, has, decide_false, Bool.false_eq_true, if_false, hsa, decide_true,
        if_true]
      have h1 : t.filter (· < s) = [] := by
        rw [List.filter_eq_nil_iff]; intro b hb; have := hat b hb; simp; omega
      have h2 : t.filter (s < ·) = t := by
        rw [List.filter_eq_self]; intro b hb; have := hat b hb; simp; omega
      rw [h1, h2]; rfl

theorem sorted_insert {l : List Nat} (hs : l.IsChain (· < ·)) (s : Nat) :
    (l.filter (· < s) ++ s :: l.filter (s < ·)).IsChain (· < ·) := by
  rw [List.isChain_iff_pairwise] at hs ⊢
  rw [List.pairwise_append, List.pairwise_cons]
  refine ⟨hs.sublist (List.filter_sublist), ⟨fun b hb => by simp at hb; exact hb.2,
    hs.sublist (List.filter_sublist)⟩, fun a ha b hb => ?_⟩
  simp only [List.mem_filter, decide_eq_true_eq] at ha
  simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq] at hb
  rcases hb with rfl | ⟨_, hb⟩ <;> omega

end OM.Proof

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-! ### Linking a bucket into the list of non-empty buckets -/

section link
variable (st : Core) (s p : Nat)

theorem linkSt_nbNext (b : Nat) : (linkSt st s p).nbNext.getX b =
    if b = s then (if p = 0 then st.pqLo else st.nbNext.getX p)
    else if p ≠ 0 ∧ b = p then s else st.nbNext.getX b := by
  unfold linkSt
  by_cases hp : p = 0 <;> simp only [hp] <;> split_ifs <;> simp_all [Array.getX_setX]

theorem linkSt_nbPrev (b : Nat) (hsn : s ≠ (if p = 0 then st.pqLo else st.nbNext.getX p)) :
    (linkSt st s p).nbPrev.getX b =
    if (if p = 0 then st.pqLo else st.nbNext.getX p) ≠ 0 ∧ b = (if p = 0 then st.pqLo else st.nbNext.getX p)
    then s else if b = s then p else st.nbPrev.getX b := by
  unfold linkSt
  generalize hn : (if p = 0 then st.pqLo else st.nbNext.getX p) = n at hsn ⊢
  by_cases hp : p = 0 <;> simp only [hp, if_true, if_false] <;> split_ifs <;>
    simp_all [Array.getX_setX]

theorem linkSt_pqLo : (linkSt st s p).pqLo = if p = 0 then s else st.pqLo := by
  unfold linkSt; by_cases hp : p = 0 <;> simp only [hp] <;> split_ifs <;> rfl

theorem linkSt_pqHi : (linkSt st s p).pqHi =
    if (if p = 0 then st.pqLo else st.nbNext.getX p) ≠ 0 then st.pqHi else s := by
  unfold linkSt; by_cases hp : p = 0 <;> simp only [hp] <;> split_ifs <;> rfl

theorem linkSt_rest : (linkSt st s p).pqHead = st.pqHead ∧ (linkSt st s p).pqNext = st.pqNext ∧
    (linkSt st s p).pqPrev = st.pqPrev ∧ (linkSt st s p).pqWhere = st.pqWhere ∧
    (linkSt st s p).P = st.P := by
  unfold linkSt; by_cases hp : p = 0 <;> simp only [hp] <;> split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end link

/-- After `linkSt` with the predecessor `p` and the successor bucket `n` of `s`: the new list. -/
theorem link_llist_core {st : Core} {nb1 nb2 : List Nat}
    (h : LList (fun b => st.nbNext.getX b) (fun b => st.nbPrev.getX b) st.pqLo (nb1 ++ nb2))
    {s p n : Nat} (hsn : s ∉ nb1 ++ nb2) (hs0 : s ≠ 0) (hp : p = nb1.getLastD 0)
    (hn : n = nb2.headD 0) (hn' : (if p = 0 then st.pqLo else st.nbNext.getX p) = n) :
    LList (fun b => (linkSt st s p).nbNext.getX b) (fun b => (linkSt st s p).nbPrev.getX b)
      (linkSt st s p).pqLo (nb1 ++ s :: nb2) := by
  have hsn' : s ≠ n := by
    rw [hn]; intro e
    cases nb2 with
    | nil => exact hs0 e
    | cons a t => exact hsn (by simp at e; simp [e])
  have hn0 : n ≠ 0 → n ∈ nb2 := by
    rw [hn]; intro h0
    cases nb2 with
    | nil => exact absurd rfl h0
    | cons a t => simp
  have hnext : ∀ b, (linkSt st s p).nbNext.getX b =
      if b = s then n else if p ≠ 0 ∧ b = p then s else st.nbNext.getX b := by
    intro b; rw [linkSt_nbNext, hn']
  have hprev : ∀ b, (linkSt st s p).nbPrev.getX b =
      if n ≠ 0 ∧ b = n then s else if b = s then p else st.nbPrev.getX b := by
    intro b; rw [linkSt_nbPrev st s p b (by rw [hn']; exact hsn'), hn']
  rcases nb1.eq_nil_or_concat with rfl | ⟨nb1', q, rfl⟩
  · have hp0 : p = 0 := by simpa using hp
    subst hp0
    simp only [List.nil_append] at h hsn ⊢
    have hlo : st.pqLo = n := by simpa using hn'
    rw [linkSt_pqLo, if_pos rfl]
    refine LList.insert_front h hsn hs0 (fun z _ => ?_) (fun z hzm => ?_)
    · rw [hnext, hlo]; by_cases hz : z = s <;> simp [hz]
    · rw [hprev, hlo]
      by_cases hz : z = s
      · subst hz; simp [hsn']
      · rw [if_neg hz]
        by_cases hz2 : z = n
        · subst hz2; by_cases hz0 : z = 0
          · exfalso; subst hz0
            rcases List.mem_cons.mp hzm with e | e
            · exact hs0 e.symm
            · exact h.nonil e
          · simp [hz0, hz]
        · simp [hz2, hz]
  · rw [List.concat_eq_append] at h hsn hp ⊢
    have hpq : p = q := by simpa using hp
    subst hpq
    have hq0 : p ≠ 0 := fun e => h.nonil (by rw [e]; simp)
    rw [linkSt_pqLo, if_neg hq0]
    have h' : LList (fun b => st.nbNext.getX b) (fun b => st.nbPrev.getX b) st.pqLo
        (nb1' ++ p :: nb2) := by simpa using h
    have hsn2 : s ∉ nb1' ++ p :: nb2 := by simpa using hsn
    have hnq : st.nbNext.getX p = n := by simpa [hq0] using hn'
    have e : nb1' ++ [p] ++ s :: nb2 = nb1' ++ p :: s :: nb2 := by simp
    rw [e]
    refine LList.insert_after h' hsn2 hs0 (fun z _ => ?_) (fun z hzm => ?_)
    · simp only [hnext, hnq]
      by_cases hzp : z = p
      · subst hzp; simp [hq0, show z ≠ s from fun e' => hsn2 (e' ▸ by simp)]
      · by_cases hzs : z = s
        · subst hzs; simp [hzp]
        · simp [hzp, hzs]
    · simp only [hprev, hnq]
      by_cases hzs : z = s
      · subst hzs; simp [hsn']
      · rw [if_neg hzs]
        by_cases hz2 : z = n
        · subst hz2; by_cases hz0 : z = 0
          · exfalso; subst hz0
            have : (0 : Nat) ∈ nb1' ++ p :: nb2 := by
              simp only [List.mem_append, List.mem_cons] at hzm ⊢
              rcases hzm with h1 | h1 | h1 | h1
              · exact Or.inl h1
              · exact Or.inr (Or.inl h1)
              · exact absurd h1.symm hs0
              · exact Or.inr (Or.inr h1)
            exact h'.nonil this
          · simp [hz0, hzs]
        · simp [hz2, hzs]

theorem link_llist {st : Core} {nb : List Nat}
    (h : LList (fun b => st.nbNext.getX b) (fun b => st.nbPrev.getX b) st.pqLo nb)
    (hs : nb.IsChain (· < ·)) {s p : Nat} (hsn : s ∉ nb) (hs0 : s ≠ 0)
    (hp : p = (nb.filter (· < s)).getLastD 0) :
    LList (fun b => (linkSt st s p).nbNext.getX b) (fun b => (linkSt st s p).nbPrev.getX b)
      (linkSt st s p).pqLo (nb.filter (· < s) ++ s :: nb.filter (s < ·)) ∧
    (linkSt st s p).pqHi = if nb.filter (s < ·) = [] then s else st.pqHi := by
  have hsplit := sorted_split hs s hsn
  generalize h1 : nb.filter (· < s) = nb1 at hp hsplit ⊢
  generalize h2 : nb.filter (s < ·) = nb2 at hsplit ⊢
  subst hsplit
  -- the bucket after `p`
  have hn : (if p = 0 then st.pqLo else st.nbNext.getX p) = nb2.headD 0 := by
    rcases nb1.eq_nil_or_concat with rfl | ⟨nb1', q, rfl⟩
    · have hp0 : p = 0 := by simpa using hp
      subst hp0; simp only [if_true]; rw [h.head]; rfl
    · rw [List.concat_eq_append] at h hp
      have hpq : p = q := by simpa using hp
      rw [hpq]
      have hq0 : q ≠ 0 := fun e => h.nonil (by rw [e]; simp)
      rw [if_neg hq0]
      have := h.next q (by simp)
      rw [this, show nb1' ++ [q] ++ nb2 = nb1' ++ q :: nb2 by simp, succOf_mid
        (by have := h.nodup; simpa using this)]
  refine ⟨link_llist_core h hsn hs0 hp rfl hn, ?_⟩
  rw [linkSt_pqHi, hn]
  cases nb2 with
  | nil => simp
  | cons a t =>
    have ha : a ≠ 0 := fun e => h.nonil (by simp [e])
    simp [ha]

end OM.Proof
