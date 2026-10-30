import OM.Impl.ListLib

/-!
# M6: removing from lists

* `eraseIdxP k`: remove element `p` of list `k` of record `i` (`List.eraseIdx`): the tail shifts
  left by one, then the last cell goes.
* `filterP k`: keep the elements whose key is not `x` (`List.filter`, Level F's `assocErase`): the
  kept elements are compacted in place, then the list shrinks.
-/

namespace OM.Impl

open OM.Model
open OM.Machine (Reg BinOp UnOp)

/-- Element `src` of list `k` of record `i` is copied to position `dst`. -/
def mvS (k : LK) (dst src : Exp) : Stm :=
  cm{ k[i][‹dst›].fst := k[i][‹src›].fst; k[i][‹dst›].snd := k[i][‹src›].snd }

theorem LK.view_put_self {s : Core} {i : Nat} {l : List (Nat × Nat)} {k : LK} (hr : k.recOk s i = true)
    (hv : k.valid l = true) : k.view (k.put s i l) i = l := by
  rw [LK.view_put hr hv]; simp

theorem valid_getD {k : LK} {B : List (Nat × Nat)} (hv : k.valid B = true) {m : Nat} (hm : m < B.length) :
    k.valid [B.getD m (0, 0)] = true := by
  rw [List.getD_eq_getElem _ _ hm]; exact (LK.valid_iff B k).mp hv _ (List.getElem_mem hm)

theorem valid_snd {k : LK} {a : Nat × Nat} (h : k.valid [a] = true) (u : Nat) : k.valid [(u, a.2)] = true :=
  LK.valid_pair_snd (u := a.1) h

theorem mvS_ok {κ : Caps} {k : LK} {s : Core} {L : Loc} {i q q' : Nat} {B : List (Nat × Nat)} {dst src : Exp}
    (hLi : L "i" = i) (hd : ∀ S : Core, dst.ev κ S L = some q) (hs : ∀ S : Core, src.ev κ S L = some q')
    (hq : q < B.length) (hq' : q' < B.length) (hr : k.recOk s i = true) (hir : i < κ.lrec k)
    (hv : k.valid B = true) (hlen : B.length ≤ κ.lcap k) :
    ∃ c, evalF κ (mvS k dst src) (k.put s i B) L = .ok (k.put s i (B.set q (B.getD q' (0, 0)))) L c ∧
      c ≤ 2 * (10 + dst.cost + src.cost) := by
  have hview := LK.view_put_self (s := s) (i := i) (k := k) hr hv
  have w1 := lwr_put_ok (κ := κ) (k := k) (s := s) (Lc := L) (i := i) (y := q) (w := (B.getD q' (0, 0)).1) (L0 := B)
    false (jx := dst) (ex := .lrd k false "i" src) hLi (hd _)
    (by simp [Exp.ev, hLi, hs, hir, hview, hq']) hq hr hir hv (valid_snd (valid_getD hv hq) _) hlen
  simp only [Bool.false_eq_true, if_false] at w1
  set B1 := B.set q ((B.getD q' (0, 0)).1, (B.getD q (0, 0)).2)
  have hv1 : k.valid B1 = true := LK.valid_set hv (valid_snd (valid_getD hv hq) _)
  have hB1 : B1.length = B.length := by simp [B1]
  have hview1 := LK.view_put_self (s := s) (i := i) (k := k) hr hv1
  have hg1 : (B1.getD q' (0, 0)).2 = (B.getD q' (0, 0)).2 := by
    simp only [B1, getD_set']; by_cases e : q = q' <;> simp [e, hq]
  have w2 := lwr_put_ok (κ := κ) (k := k) (s := s) (Lc := L) (i := i) (y := q) (w := (B.getD q' (0, 0)).2) (L0 := B1)
    true (jx := dst) (ex := .lrd k true "i" src) hLi (hd _)
    (by simp only [Exp.ev, hLi, hs, Option.bind_some, hview1, hB1, hq', hir, and_self, if_true, hg1])
    (by rw [hB1]; exact hq) hr hir hv1 (by simp only [if_true]; exact valid_snd (valid_getD hv hq') _)
    (by rw [hB1]; exact hlen)
  simp only [if_true] at w2
  have hfin : B1.set q ((B1.getD q (0, 0)).1, (B.getD q' (0, 0)).2) = B.set q (B.getD q' (0, 0)) := by
    have : B1.getD q (0, 0) = ((B.getD q' (0, 0)).1, (B.getD q (0, 0)).2) := by simp [B1, getD_set', hq]
    rw [this]; simp only [B1, List.set_set]
  rw [hfin] at w2
  exact ⟨_, evalF_seq_ok2 w1 w2, by simp [Exp.cost]; omega⟩

/-! ### Removing an element -/

/-- The list after `t` steps of shifting the tail of `l` left over position `p`. -/
def shiftL (l : List (Nat × Nat)) (p t : Nat) : List (Nat × Nat) :=
  (List.range l.length).map fun m => if p ≤ m ∧ m < p + t then l.getD (m + 1) (0, 0) else l.getD m (0, 0)

theorem length_shiftL (l : List (Nat × Nat)) (p t : Nat) : (shiftL l p t).length = l.length := by simp [shiftL]

theorem shiftL_getElem (l : List (Nat × Nat)) (p t m : Nat) (hm : m < (shiftL l p t).length) :
    (shiftL l p t)[m] = if p ≤ m ∧ m < p + t then l.getD (m + 1) (0, 0) else l.getD m (0, 0) := by
  simp [shiftL]

theorem shiftL_zero (l : List (Nat × Nat)) (p : Nat) : shiftL l p 0 = l := by
  apply List.ext_getElem (length_shiftL l p 0)
  intro m h1 h2
  rw [shiftL_getElem, if_neg (by omega), List.getD_eq_getElem _ _ h2]

theorem shiftL_succ {l : List (Nat × Nat)} {p t : Nat} (h : p + t + 1 < l.length) :
    (shiftL l p t).set (p + t) ((shiftL l p t).getD (p + t + 1) (0, 0)) = shiftL l p (t + 1) := by
  have hg : (shiftL l p t).getD (p + t + 1) (0, 0) = l.getD (p + t + 1) (0, 0) := by
    rw [List.getD_eq_getElem _ _ (by rw [length_shiftL]; omega), shiftL_getElem]; simp
  rw [hg]
  apply List.ext_getElem (by simp [length_shiftL])
  intro m h1 h2
  rw [List.getElem_set, shiftL_getElem, shiftL_getElem]
  by_cases e : p + t = m
  · subst e; simp
  · rw [if_neg e]; by_cases e2 : p ≤ m ∧ m < p + t
    · rw [if_pos e2, if_pos (by omega)]
    · rw [if_neg e2, if_neg (by omega)]

theorem shiftL_end {l : List (Nat × Nat)} {p : Nat} (h : p < l.length) :
    (shiftL l p (l.length - 1 - p)).dropLast = l.eraseIdx p := by
  apply List.ext_getElem (by simp [length_shiftL, List.length_eraseIdx, h])
  intro m h1 h2
  rw [List.getElem_dropLast, shiftL_getElem, List.getElem_eraseIdx]
  simp only [List.length_dropLast, length_shiftL] at h1
  by_cases e : m < p
  · rw [if_neg (by omega), dif_pos e, List.getD_eq_getElem _ _ (by omega)]
  · rw [if_pos (by omega), dif_neg e, List.getD_eq_getElem _ _ (by omega)]

theorem valid_default (k : LK) : k.valid [((0 : Nat), (0 : Nat))] = true := by cases k <;> rfl

theorem valid_shiftL {k : LK} {l : List (Nat × Nat)} (hv : k.valid l = true) (p t : Nat) :
    k.valid (shiftL l p t) = true := by
  rw [LK.valid_iff]
  intro z hz
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hz
  rw [shiftL_getElem]
  have g : ∀ j, k.valid [l.getD j (0, 0)] = true := fun j => by
    by_cases hj : j < l.length
    · exact valid_getD hv hj
    · rw [List.getD_eq_default _ _ (by omega)]; exact valid_default k
  split <;> exact g _

def eraseIdxP (k : LK) : Proc where
  name := "eraseIdx"
  params := ["i", "p"]
  rets := []
  body := cm{
    n := len k[i]; c := n ∸ 1 ∸ p
    for t < c do ‹mvS k ("p" + "t") ("p" + "t" + 1)›
    pop k[i] }

/-- **`eraseIdxP` computes `eraseIdx`.** -/
theorem eraseIdxP_agree (κ : Caps) (k : LK) (s : Core) (L : Loc) {i p : Nat} (hi : L "i" = i) (hp : L "p" = p)
    (hpl : p < (k.view s i).length) (hid : k.idOk s i) (hr : k.recOk s i = true) (hir : i < κ.lrec k)
    (hcap : (k.view s i).length ≤ κ.lcap k) :
    ∃ L' c, evalF κ (eraseIdxP k).body s L = .ok (k.put s i ((k.view s i).eraseIdx p)) L' c ∧
      c ≤ 100 + 70 * (k.view s i).length := by
  set l := k.view s i
  have hvl : k.valid l = true := LK.valid_view s i k
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "n") (e := .llen k "i") (v := l.length)
    (by simp [Exp.ev, hi, hir, l])
  set L1 := OM.Machine.State.upd L "n" l.length
  have a2 := evalF_assign_ok (κ := κ) (s := s) (L := L1) (x := "c") (e := .monus (.monus "n" 1) "p")
    (v := l.length - 1 - p) (Exp.ev_monus κ s L1 (Exp.ev_monus κ s L1 (by simp [Exp.ev, L1, OM.Machine.State.upd])
      rfl) (by simp [Exp.ev, L1, OM.Machine.State.upd, hp]))
  set L2 := OM.Machine.State.upd L1 "c" (l.length - 1 - p)
  obtain ⟨S', L', c, he, hc, hS', hi', -⟩ := evalF_loop (κ := κ) (x := "t") (n := .var "c")
    (b := mvS k ("p" + "t") ("p" + "t" + 1)) (s := s) (L := L2) (N := l.length - 1 - p)
    (by simp [Exp.ev, L2, OM.Machine.State.upd])
    (fun t S L' => S = k.put s i (shiftL l p t) ∧ L' "i" = i ∧ L' "p" = p) 60
    ⟨by rw [shiftL_zero, LK.put_view hid], by simp [L2, L1, OM.Machine.State.upd, hi],
      by simp [L2, L1, OM.Machine.State.upd, hp]⟩
    (by
      intro t ht S L3 ⟨hS, h3i, h3p⟩
      subst hS
      obtain ⟨c4, e4, hc4⟩ := mvS_ok (κ := κ) (k := k) (s := s) (L := OM.Machine.State.upd L3 "t" t) (i := i)
        (q := p + t) (q' := p + t + 1) (B := shiftL l p t) (dst := "p" + "t") (src := "p" + "t" + 1)
        (by simp [OM.Machine.State.upd, h3i])
        (fun _ => by simp [Exp.ev, OM.Machine.State.upd, h3p, OM.Machine.BinOp.eval])
        (fun _ => by simp [Exp.ev, OM.Machine.State.upd, h3p, OM.Machine.BinOp.eval])
        (by rw [length_shiftL]; omega) (by rw [length_shiftL]; omega) hr hir (valid_shiftL hvl p t)
        (by rw [length_shiftL]; exact hcap)
      rw [shiftL_succ (by omega)] at e4
      exact ⟨_, _, _, e4, by simp [Exp.cost, Exp.ofNat_def] at hc4 ⊢; omega, rfl,
        by simp [OM.Machine.State.upd, h3i], by simp [OM.Machine.State.upd, h3p]⟩)
  subst hS'
  set X := shiftL l p (l.length - 1 - p)
  have hvX : k.valid X = true := valid_shiftL hvl p _
  have hXl : X.length = l.length := length_shiftL l p _
  have e5 : evalF κ (.lshrink k "i") (k.put s i X) L' = .ok (k.put s i X.dropLast) L' (4 + 2 * 1) := by
    have hso := LK.set_ok (κ := κ) (s := k.put s i X) (i := i) (l := X.dropLast) (k := k)
      (by rw [LK.recOk_put]; exact hr) (by rw [LK.valid_iff] at hvX ⊢; exact fun z hz => hvX z (List.mem_of_mem_dropLast hz))
      (by simp [List.length_dropLast, hXl]; omega) hir
    rw [LK.put_put] at hso
    simp [evalF, Exp.ev, hi', LK.view_put_self hr hvX, hXl, show l.length ≠ 0 by omega, hso, Exp.cost]
  rw [shiftL_end hpl] at e5
  refine ⟨L', _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 he e5)), ?_⟩
  have : (l.length - 1 - p) * (1 + 60) ≤ 61 * l.length := by
    have := Nat.mul_le_mul_right (1 + 60) (show l.length - 1 - p ≤ l.length by omega); omega
  simp only [Exp.cost, Exp.monus, Exp.max, Exp.sub_def, Exp.add_def, Exp.mul_def, Exp.ofNat_def] at hc ⊢
  omega

/-! ### Filtering by key -/

/-- The kept prefix after `j` elements. -/
abbrev keepF (l : List (Nat × Nat)) (x j : Nat) : List (Nat × Nat) := (l.take j).filter (·.1 != x)

theorem length_keepF_le (l : List (Nat × Nat)) (x j : Nat) : (keepF l x j).length ≤ min j l.length := by
  have := List.length_filter_le (·.1 != x) (l.take j); simp at this ⊢ <;> omega

theorem keepF_succ {l : List (Nat × Nat)} {x j : Nat} (hj : j < l.length) :
    keepF l x (j + 1) = keepF l x j ++ (if l[j].1 != x then [l[j] ] else []) := by
  simp only [keepF, List.take_succ_eq_append_getElem hj, List.filter_append]
  congr 1; cases h : (l[j].1 != x) <;> simp [h]

theorem getElem_append_drop {A l : List (Nat × Nat)} {j : Nat} (hA : A.length ≤ j) (hj : j < l.length)
    (h : j < (A ++ l.drop A.length).length) : (A ++ l.drop A.length)[j] = l[j] := by
  rw [List.getElem_append_right (by omega)]
  simp; congr 1; omega

theorem getD_append_drop {A l : List (Nat × Nat)} {j : Nat} (hA : A.length ≤ j) (hj : j < l.length) :
    (A ++ l.drop A.length).getD j (0, 0) = l[j] := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), getElem_append_drop hA hj]

theorem set_append_drop {A l : List (Nat × Nat)} (hA : A.length < l.length) (a : Nat × Nat) :
    (A ++ l.drop A.length).set A.length a = (A ++ [a]) ++ l.drop (A ++ [a]).length := by
  rw [List.set_append_right _ _ (by omega), Nat.sub_self, List.drop_eq_getElem_cons hA, List.set_cons_zero]
  simp

theorem valid_append_drop {k : LK} {l A : List (Nat × Nat)} (hv : k.valid l = true) (hA : k.valid A = true) (w : Nat) :
    k.valid (A ++ l.drop w) = true := by
  rw [LK.valid_iff] at hv hA ⊢
  intro z hz; rcases List.mem_append.mp hz with h | h
  · exact hA z h
  · exact hv z (List.mem_of_mem_drop h)

theorem valid_keepF {k : LK} {l : List (Nat × Nat)} (hv : k.valid l = true) (x j : Nat) :
    k.valid (keepF l x j) = true := by
  rw [LK.valid_iff] at hv ⊢
  intro z hz; exact hv z (List.mem_of_mem_take (List.mem_of_mem_filter hz))

def filterBody (k : LK) : Stm :=
  cm{ if k[i][j].fst = x then skip else { ‹mvS k "w" "j"›; w := w + 1 } }

def filterP (k : LK) : Proc where
  name := "filter"
  params := ["i", "x"]
  rets := []
  body := cm{
    n := len k[i]; w := 0; for j < n do ‹filterBody k›
    c := n ∸ w; for t < c do pop k[i] }

/-- **`filterP` keeps the elements whose key is not `x`.** -/
theorem filterP_agree (κ : Caps) (k : LK) (s : Core) (L : Loc) {i x : Nat} (hi : L "i" = i) (hx : L "x" = x)
    (hid : k.idOk s i) (hr : k.recOk s i = true) (hir : i < κ.lrec k) (hcap : (k.view s i).length ≤ κ.lcap k) :
    ∃ L' c, evalF κ (filterP k).body s L = .ok (k.put s i ((k.view s i).filter (·.1 != x))) L' c ∧
      c ≤ 50 + 90 * (k.view s i).length := by
  set l := k.view s i
  set n := l.length
  have hvl : k.valid l = true := LK.valid_view s i k
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "n") (e := .llen k "i") (v := n)
    (by simp [Exp.ev, hi, hir, l, n])
  have a2 := evalF_assign_ok (κ := κ) (s := s) (L := OM.Machine.State.upd L "n" n) (x := "w") (e := (0 : Exp))
    (v := 0) rfl
  set L2 := OM.Machine.State.upd (OM.Machine.State.upd L "n" n) "w" 0
  -- compaction
  obtain ⟨S', L', c, he, hc, hS', hi', hx', hn', hw'⟩ := evalF_loop (κ := κ) (x := "j") (n := .var "n")
    (b := filterBody k) (s := s) (L := L2) (N := n) (by simp [Exp.ev, L2, OM.Machine.State.upd])
    (fun j S L' => S = k.put s i (keepF l x j ++ l.drop (keepF l x j).length) ∧ L' "i" = i ∧ L' "x" = x ∧
      L' "n" = n ∧ L' "w" = (keepF l x j).length) 40
    ⟨by simp only [keepF, List.take_zero, List.filter_nil, List.length_nil, List.drop_zero, List.nil_append]
        exact (LK.put_view hid).symm, by simp [L2, OM.Machine.State.upd, hi], by simp [L2, OM.Machine.State.upd, hx],
      by simp [L2, OM.Machine.State.upd], by simp [L2, OM.Machine.State.upd, keepF]⟩
    (by
      intro j hj S L3 ⟨hS, h3i, h3x, h3n, h3w⟩
      subst hS
      set A := keepF l x j
      have hAj : A.length ≤ j := (length_keepF_le l x j).trans (Nat.min_le_left _ _)
      set V := A ++ l.drop A.length
      have hvV : k.valid V = true := valid_append_drop hvl (valid_keepF hvl x j) _
      have hVl : V.length = n := by simp [V]; omega
      have hview := LK.view_put_self (s := s) (i := i) (k := k) hr hvV
      set L4 := OM.Machine.State.upd L3 "j" j
      have hc : (.lrd k false "i" "j" =ₑ "x" : Exp).ev κ (k.put s i V) L4 =
          some (if l[j].1 = x then 1 else 0) := by
        simp [Exp.ev, L4, OM.Machine.State.upd, h3i, h3x, hir, hview, hVl, hj, OM.Machine.BinOp.eval, V,
          getElem_append_drop hAj hj]
      by_cases hk : l[j].1 = x
      · have hA' : keepF l x (j + 1) = A := by rw [keepF_succ hj]; simp [hk, A]
        refine ⟨_, L4, _, evalF_ite_t (by rw [hc, if_pos hk]) one_ne_zero evalF_skip, by simp [Exp.cost], ?_⟩
        rw [hA']
        exact ⟨rfl, by simp [L4, OM.Machine.State.upd, h3i], by simp [L4, OM.Machine.State.upd, h3x],
          by simp [L4, OM.Machine.State.upd, h3n], by simp [L4, OM.Machine.State.upd, h3w]⟩
      · have hA' : keepF l x (j + 1) = A ++ [l[j] ] := by rw [keepF_succ hj]; simp [hk, A]
        obtain ⟨c5, e5, hc5⟩ := mvS_ok (κ := κ) (k := k) (s := s) (L := L4) (i := i) (q := A.length) (q' := j)
          (B := V) (dst := .var "w") (src := .var "j") (by simp [L4, OM.Machine.State.upd, h3i])
          (fun _ => by simp [Exp.ev, L4, OM.Machine.State.upd, h3w]) (fun _ => by simp [Exp.ev, L4, OM.Machine.State.upd])
          (by omega) (by omega) hr hir hvV (by rw [hVl]; exact hcap)
        rw [getD_append_drop hAj hj, set_append_drop (by omega), ← hA'] at e5
        have a6 := evalF_assign_ok (κ := κ) (s := k.put s i (keepF l x (j + 1) ++ l.drop (keepF l x (j + 1)).length))
          (L := L4) (x := "w") (e := "w" + 1) (v := A.length + 1)
          (by simp [Exp.ev, L4, OM.Machine.State.upd, h3w, OM.Machine.BinOp.eval])
        refine ⟨_, _, _, evalF_ite_f (by rw [hc, if_neg hk]) (evalF_seq_ok2 e5 a6), ?_, rfl, ?_, ?_, ?_, ?_⟩
        · simp [Exp.cost] at hc5 ⊢; omega
        · simp [L4, OM.Machine.State.upd, h3i]
        · simp [L4, OM.Machine.State.upd, h3x]
        · simp [L4, OM.Machine.State.upd, h3n]
        · simp [OM.Machine.State.upd, hA'])
  subst hS'
  set F := keepF l x n
  have hF : F = l.filter (·.1 != x) := by simp [F, keepF, n]
  have hFn : F.length ≤ n := (length_keepF_le l x n).trans (Nat.min_le_left _ _)
  set D := l.drop F.length
  have hFD : (F ++ D).length = n := by simp [D]; omega
  have hvFD : k.valid (F ++ D) = true := valid_append_drop hvl (valid_keepF hvl x n) _
  have a7 := evalF_assign_ok (κ := κ) (s := k.put s i (F ++ D)) (L := L') (x := "c") (e := .monus "n" "w")
    (v := n - F.length) (Exp.ev_monus κ _ L' (by simp [Exp.ev, hn']) (by simp [Exp.ev, hw']))
  set L7 := OM.Machine.State.upd L' "c" (n - F.length)
  -- shrinking
  obtain ⟨S'', L'', c', he', hc', hS'', -⟩ := evalF_loop (κ := κ) (x := "t") (n := .var "c") (b := .lshrink k "i")
    (s := k.put s i (F ++ D)) (L := L7) (N := n - F.length) (by simp [Exp.ev, L7, OM.Machine.State.upd])
    (fun t S L' => S = k.put s i ((F ++ D).take (n - t)) ∧ L' "i" = i) 6
    ⟨by rw [Nat.sub_zero, List.take_of_length_le (by omega)], by simp [L7, OM.Machine.State.upd, hi']⟩
    (by
      intro t ht S L3 ⟨hS, h3i⟩
      subst hS
      set Y := (F ++ D).take (n - t)
      have hvY : k.valid Y = true := by
        rw [LK.valid_iff] at hvFD ⊢; exact fun z hz => hvFD z (List.mem_of_mem_take hz)
      have hYl : Y.length = n - t := by simp [Y, hFD] <;> omega
      have hso := LK.set_ok (κ := κ) (s := k.put s i Y) (i := i) (l := Y.dropLast) (k := k)
        (by rw [LK.recOk_put]; exact hr)
        (by rw [LK.valid_iff] at hvY ⊢; exact fun z hz => hvY z (List.mem_of_mem_dropLast hz))
        (by simp [List.length_dropLast, hYl]; omega) hir
      rw [LK.put_put] at hso
      have hdl : Y.dropLast = (F ++ D).take (n - (t + 1)) := by
        simp only [Y, List.dropLast_eq_take, List.take_take, List.length_take, hFD]; congr 1; omega
      refine ⟨_, OM.Machine.State.upd L3 "t" t, _, ?_, le_refl _, by rw [← hdl], by simp [OM.Machine.State.upd, h3i]⟩
      simp [evalF, Exp.ev, OM.Machine.State.upd, h3i, LK.view_put_self hr hvY, hYl, show n - t ≠ 0 by omega, hso,
        Exp.cost])
  subst hS''
  have hfin : (F ++ D).take (n - (n - F.length)) = l.filter (·.1 != x) := by
    rw [show n - (n - F.length) = F.length by omega, List.take_left' rfl, hF]
  rw [hfin] at he'
  refine ⟨L'', _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 he (evalF_seq_ok2 a7 he'))), ?_⟩
  have h1 : n * (1 + 40) = 41 * n := by ring
  have h2 : (n - F.length) * (1 + 6) ≤ 7 * n := by
    have := Nat.mul_le_mul_right (1 + 6) (show n - F.length ≤ n by omega); omega
  simp only [Exp.cost, Exp.monus, Exp.max, Exp.sub_def, Exp.add_def, Exp.mul_def, Exp.ofNat_def] at hc hc' ⊢
  omega

end OM.Impl
