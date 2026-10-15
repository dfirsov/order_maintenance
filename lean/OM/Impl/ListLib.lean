import OM.Impl.Loop

/-!
# M6: a list library for the core language

Procedures on list `k` of record `i`, each with its agreement lemma:
* `findP k`: the position of the first element with key `x` (`List.findIdx`), or the length.
* `assocSetP k`: `assocSet` with key `x` and value `y`.
-/

namespace OM.Impl

open OM.Model
open OM.Machine (Reg BinOp UnOp)

/-- The key of element `m` of a list (0 past the end). -/
abbrev key (l : List (Nat × Nat)) (m : Nat) : Nat := (l.getD m (0, 0)).1

def findP (k : LK) : Proc where
  name := "find"
  params := ["i", "x"]
  rets := ["r"]
  body :=
    "n" ::= .llen k "i" ;;
    "r" ::= "n" ;;
    "f" ::= 0 ;;
    .loop "j" "n" (.ite (("f" =ₑ 0) &&ₑ (.lrd k false "i" "j" =ₑ "x")) ("r" ::= "j" ;; "f" ::= 1) .skip)

theorem findIdx_key (l : List (Nat × Nat)) (x : Nat) :
    (∀ m < l.length, key l m ≠ x) → l.findIdx (·.1 == x) = l.length := by
  intro h
  apply List.findIdx_eq_length.mpr
  intro y hy
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hy
  have := h m hm
  simp only [key, List.getD_eq_getElem _ _ hm] at this
  simpa using this

theorem findIdx_key_eq (l : List (Nat × Nat)) (x r : Nat) (hr : r < l.length) (h1 : key l r = x)
    (h2 : ∀ m < r, key l m ≠ x) : l.findIdx (·.1 == x) = r := by
  apply (List.findIdx_eq hr).mpr
  refine ⟨?_, fun m hm => ?_⟩
  · simp only [key, List.getD_eq_getElem _ _ hr] at h1; simpa using h1
  · have := h2 m hm
    simp only [key] at this; rw [List.getD_eq_getElem _ _ (by omega)] at this; simpa using this

/-- **`findP` computes `findIdx`.** -/
theorem findP_agree (κ : Caps) (k : LK) (s : Core) (L : Loc) {i x : Nat} (hi : L "i" = i) (hx : L "x" = x)
    (hir : i < κ.lrec k) :
    ∃ L' c, evalF κ (findP k).body s L = .ok s L' c ∧ L' "r" = (k.view s i).findIdx (·.1 == x) ∧
      c ≤ 20 + 20 * (k.view s i).length := by
  set l := k.view s i
  have hlen : (Exp.llen k (.var "i")).ev κ s L = some l.length := by simp [Exp.ev, hi, hir, l]
  -- the three assignments
  let I : Nat → Core → Loc → Prop := fun j s' L' => s' = s ∧ L' "i" = i ∧ L' "x" = x ∧ L' "n" = l.length ∧
    ((L' "f" = 0 ∧ L' "r" = l.length ∧ ∀ m < j, key l m ≠ x) ∨
     (L' "f" = 1 ∧ L' "r" < j ∧ key l (L' "r") = x ∧ ∀ m < L' "r", key l m ≠ x))
  have hn : (Exp.var "n").ev κ s
      (OM.Machine.State.upd (OM.Machine.State.upd (OM.Machine.State.upd L "n" l.length) "r" l.length) "f" 0) =
      some l.length := by simp [Exp.ev, OM.Machine.State.upd]
  obtain ⟨s', L', c, he, hc, hI⟩ := evalF_loop (x := "j") (b := .ite (("f" =ₑ 0) &&ₑ (.lrd k false "i" "j" =ₑ "x"))
    ("r" ::= "j" ;; "f" ::= 1) .skip) hn I 17
    ⟨rfl, by simp [OM.Machine.State.upd, hi], by simp [OM.Machine.State.upd, hx], by simp [OM.Machine.State.upd],
      Or.inl ⟨by simp [OM.Machine.State.upd], by simp [OM.Machine.State.upd], fun m hm => absurd hm (by omega)⟩⟩
    (by
      intro j hj s1 L1 ⟨hs, h1, h2, h3, h4⟩
      subst hs
      have hjl : j < l.length := hj
      by_cases hf : L1 "f" = 0 ∧ key l j = x
      · refine ⟨s1, OM.Machine.State.upd (OM.Machine.State.upd (OM.Machine.State.upd L1 "j" j) "r" j) "f" 1, 17,
          ?_, by omega, rfl, by simp [OM.Machine.State.upd, h1], by simp [OM.Machine.State.upd, h2],
          by simp [OM.Machine.State.upd, h3], Or.inr ⟨by simp [OM.Machine.State.upd], by simp [OM.Machine.State.upd],
          by simp [OM.Machine.State.upd]; exact hf.2, ?_⟩⟩
        · have : (l.getD j (0, 0)).1 = x := hf.2
          rw [List.getD_eq_getElem _ _ hjl] at this
          simp [evalF, Exp.ev, OM.Machine.State.upd, h1, h2, hir, hjl, hf.1, this, Res.bind, Res.addCost,
            Exp.cost, l]
        · simp only [OM.Machine.State.upd, if_true]
          rcases h4 with ⟨-, -, h⟩ | ⟨h, -⟩
          · exact h
          · rw [hf.1] at h; simp at h
      · refine ⟨s1, OM.Machine.State.upd L1 "j" j, 14, ?_, by omega, rfl, by simp [OM.Machine.State.upd, h1],
          by simp [OM.Machine.State.upd, h2], by simp [OM.Machine.State.upd, h3], ?_⟩
        · have hc : ¬(L1 "f" = 0 ∧ (LK.view s1 i k)[j].1 = x) := by
            intro h; apply hf; refine ⟨h.1, ?_⟩
            show (l.getD j (0, 0)).1 = x; rw [List.getD_eq_getElem _ _ hjl]; exact h.2
          have hc' : L1 "f" = 0 → ¬(LK.view s1 i k)[j].1 = x := fun a b => hc ⟨a, b⟩
          simp [evalF, Exp.ev, OM.Machine.State.upd, h1, h2, hir, hjl, Res.bind, Res.addCost, Exp.cost, l]
          rw [if_pos hc']
        · simp only [OM.Machine.State.upd, show ("f" = "j") = False by decide, show ("r" = "j") = False by decide,
            ite_false]
          rcases h4 with ⟨h5, h6, h7⟩ | ⟨h5, h6, h7, h8⟩
          · refine Or.inl ⟨h5, h6, fun m hm => ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
            · exact h7 m hm
            · exact fun e => hf ⟨h5, e⟩
          · exact Or.inr ⟨h5, by omega, h7, h8⟩)
  obtain ⟨hss, -, -, -, hI⟩ := hI; rw [hss] at he
  have a1 := evalF_assign_ok (x := "n") hlen
  have a2 := evalF_assign_ok (κ := κ) (s := s) (x := "r") (e := .var "n")
    (L := OM.Machine.State.upd L "n" l.length) (v := l.length) (by simp [Exp.ev, OM.Machine.State.upd])
  have a3 := evalF_assign_ok (κ := κ) (s := s) (x := "f") (e := (0 : Exp))
    (L := OM.Machine.State.upd (OM.Machine.State.upd L "n" l.length) "r" l.length) (v := 0) (by simp [Exp.ev])
  refine ⟨L', (1 + (Exp.llen k (.var "i")).cost) + ((1 + (Exp.var "n").cost) + ((1 + (0 : Exp).cost) + c)),
    ?_, ?_, ?_⟩
  · show evalF κ (_ ;; (_ ;; (_ ;; _))) s L = _
    rw [evalF_seq_ok a1, evalF_seq_ok a2, evalF_seq_ok a3, he]; rfl
  · rcases hI with ⟨-, h6, h7⟩ | ⟨-, h6, h7, h8⟩
    · rw [h6]; exact (findIdx_key l x h7).symm
    · exact (findIdx_key_eq l x _ h6 h7 h8).symm
  · simp only [Exp.cost] at hc ⊢; nlinarith

/-! ### List replacement -/

theorem Array.ext_getX {α : Type} [Inhabited α] {a b : Array α} (h : a.size = b.size)
    (h2 : ∀ j, a.getX j = b.getX j) : a = b := by
  apply Array.ext h
  intro j h1 h3
  have := h2 j
  simp only [Array.getX, Array.getD, h1, h3, dite_true] at this
  exact this

theorem size_setX {α : Type} [Inhabited α] (a : Array α) (i : Nat) (v : α) :
    (a.setX i v).size = if i < a.size then a.size else i + 1 := by
  unfold Array.setX; split <;> simp <;> omega

theorem setX_setX {α : Type} [Inhabited α] (a : Array α) (i : Nat) (u v : α) :
    (a.setX i u).setX i v = a.setX i v := by
  apply Array.ext_getX
  · simp only [size_setX]; split <;> (try split) <;> omega
  · intro j; simp only [OM.Proof.Top.getX_setX']; split <;> rfl

theorem setX_getX {α : Type} [Inhabited α] (a : Array α) {i : Nat} (h : i < a.size) : a.setX i (a.getX i) = a := by
  apply Array.ext_getX
  · simp only [size_setX, if_pos h]
  · intro j; simp only [OM.Proof.Top.getX_setX']; split
    · next e => rw [e]
    · rfl

/-- The list can be put back without change. -/
def LK.idOk (s : Core) (i : Nat) : LK → Prop
  | .cin => i < s.cin.size
  | k => k.recOk s i = true

theorem LK.put_put (s : Core) (i : Nat) (l1 l2 : List (Nat × Nat)) (k : LK) :
    k.put (k.put s i l1) i l2 = k.put s i l2 := by
  cases k <;> simp only [LK.put, Array.modify_modify_same, setX_setX] <;> rfl

theorem LK.put_view {s : Core} {i : Nat} {k : LK} (h : k.idOk s i) : k.put s i (k.view s i) = s := by
  cases k <;> simp only [LK.idOk, LK.recOk, decide_eq_true_eq] at h
  · simp only [LK.put, LK.view, List.map_map, Function.comp_def, List.map_id']
    congr 1; apply Array.ext
    · simp
    · intro j h1 h2; simp only [Array.getElem_modify]; split
      · next e => subst e; simp [Array.getX, Array.getD, h]
      · rfl
  · simp only [LK.put, LK.view]
    congr 1; apply Array.ext
    · simp
    · intro j h1 h2; simp only [Array.getElem_modify]; split
      · next e => subst e; simp [Array.getX, Array.getD, h]
      · rfl
  · simp only [LK.put, LK.view, List.map_map, Function.comp_def, List.map_id']
    congr 1; apply Array.ext
    · simp
    · intro j h1 h2; simp only [Array.getElem_modify]; split
      · next e => subst e; simp [Array.getX, Array.getD, h]
      · rfl
  · simp only [LK.put, LK.view, List.map_map, Function.comp_def]
    have : ∀ (l : List (Nat × Side)), l.map (fun q => (q.1, sideOfN (sideN q.2))) = l := by
      intro l; induction l with
      | nil => rfl
      | cons q t ih => rw [List.map_cons, ih]; obtain ⟨a, b⟩ := q; cases b <;> rfl
    simp only [this]
    congr 1; apply Array.ext
    · simp
    · intro j h1 h2; simp only [Array.getElem_modify]; split
      · next e => subst e; simp [Array.getX, Array.getD, h]
      · rfl
  · simp only [LK.put, LK.view, List.map_map, Function.comp_def, List.map_id']
    rw [setX_getX _ h]
  · subst h; simp [LK.put, LK.view, List.map_map, Function.comp_def]

/-- Every element of a valid list is valid on its own. -/
theorem LK.valid_iff (l : List (Nat × Nat)) (k : LK) : k.valid l = true ↔ ∀ q ∈ l, k.valid [q] = true := by
  cases k <;> simp [LK.valid]

theorem LK.valid_view (s : Core) (i : Nat) (k : LK) : k.valid (k.view s i) = true := by
  cases k <;> simp [LK.valid, LK.view]
  · intro a b _; cases b <;> simp [sideN]
  · intros; omega

theorem LK.set_ok {κ : Caps} {s : Core} {i : Nat} {l : List (Nat × Nat)} {k : LK} (hr : k.recOk s i = true)
    (hv : k.valid l = true) (hc : l.length ≤ κ.lcap k) (hi : i < κ.lrec k) : k.set κ s i l = some (k.put s i l) := by
  simp [LK.set, hr, hv, hc, hi]

theorem LK.recOk_put (s : Core) (i j : Nat) (l : List (Nat × Nat)) (k k' : LK) :
    k'.recOk (k.put s i l) j = k'.recOk s j := by
  have := (LK.put_keep s i l k).2.1 .N
  cases k' <;> simp only [LK.recOk] <;> simp only [Tbl.size] at this <;> rw [this]

/-! ### `assocSet` -/

/-- The list after `j` rounds of `assocSetP`: entries before `j` with key `x` get value `y`. -/
def preSet (l : List (Nat × Nat)) (x y j : Nat) : List (Nat × Nat) :=
  (l.take j).map (fun p => if p.1 = x then (p.1, y) else p) ++ l.drop j

theorem preSet_zero (l : List (Nat × Nat)) (x y : Nat) : preSet l x y 0 = l := by simp [preSet]

theorem length_preSet (l : List (Nat × Nat)) (x y j : Nat) : (preSet l x y j).length = l.length := by
  simp [preSet]; omega

theorem preSet_getD {l : List (Nat × Nat)} {x y j : Nat} (hj : j < l.length) :
    (preSet l x y j).getD j (0, 0) = l[j] := by
  rw [List.getD_eq_getElem _ _ (by rw [length_preSet]; exact hj)]
  simp only [preSet]
  rw [List.getElem_append_right (by simp <;> omega)]
  simp only [List.getElem_drop, List.length_map, List.length_take]
  congr 1; omega

theorem preSet_succ {l : List (Nat × Nat)} {x y j : Nat} (hj : j < l.length) :
    preSet l x y (j + 1) = (preSet l x y j).set j (if l[j].1 = x then (l[j].1, y) else l[j]) := by
  apply List.ext_getElem
  · simp [length_preSet]
  · intro m h1 h2
    simp only [List.getElem_set]
    simp only [preSet, length_preSet] at h1 h2 ⊢
    by_cases hm : m < j
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]
      simp
      intro e; omega
    · by_cases e : m = j
      · subst e
        rw [if_pos rfl, List.getElem_append_left (by simp; omega)]
        simp
      · rw [if_neg (Ne.symm e), List.getElem_append_right (by simp; omega),
          List.getElem_append_right (by simp; omega)]
        simp only [List.getElem_drop, List.length_map, List.length_take]
        congr 1; omega

theorem preSet_len (l : List (Nat × Nat)) (x y : Nat) :
    preSet l x y l.length = l.map (fun p => if p.1 = x then (p.1, y) else p) := by simp [preSet]

theorem assocSet_eq (l : List (Nat × Nat)) (x y : Nat) :
    assocSet l x y = if l.any (·.1 == x) then preSet l x y l.length else l ++ [(x, y)] := by
  unfold assocSet; rw [preSet_len]
  split
  · congr 1; funext p; by_cases h : p.1 = x <;> simp [h]
  · rfl

theorem preSet_noMatch {l : List (Nat × Nat)} {x y : Nat} (h : l.any (·.1 == x) = false) :
    preSet l x y l.length = l := by
  rw [preSet_len]
  conv => rhs; rw [← List.map_id l]
  apply List.map_congr_left
  intro p hp
  have : p.1 ≠ x := by
    intro e; have := List.any_eq_false.mp h p hp; simp [e] at this
  simp [this]

theorem valid_preSet {k : LK} {l : List (Nat × Nat)} {x y j : Nat} (hl : k.valid l = true)
    (hy : ∀ a, k.valid [(a, y)] = true) : k.valid (preSet l x y j) = true := by
  rw [LK.valid_iff] at hl ⊢
  intro q hq
  simp only [preSet, List.mem_append, List.mem_map] at hq
  rcases hq with ⟨p, hp, rfl⟩ | hq
  · split
    · exact hy _
    · exact hl p (List.mem_of_mem_take hp)
  · exact hl q (List.mem_of_mem_drop hq)

def assocSetP (k : LK) : Proc where
  name := "assocSet"
  params := ["i", "x", "y"]
  rets := []
  body :=
    "n" ::= .llen k "i" ;; "f" ::= 0 ;;
    .loop "j" "n" (.ite (.lrd k false "i" "j" =ₑ "x") (.lwr k true "i" "j" "y" ;; "f" ::= 1) .skip) ;;
    .ite ("f" =ₑ 0) (.lgrow k "i" "x" "y") .skip

theorem take_succ_any (l : List (Nat × Nat)) (x j : Nat) (hj : j < l.length) :
    (l.take (j + 1)).any (·.1 == x) = ((l.take j).any (·.1 == x) || l[j].1 == x) := by
  rw [List.take_succ_eq_append_getElem hj, List.any_append]; simp

/-- **`assocSetP` computes `assocSet`.** -/
theorem assocSetP_agree (κ : Caps) (k : LK) (s : Core) (L : Loc) {i x y : Nat} (hi : L "i" = i) (hx : L "x" = x)
    (hy : L "y" = y) (hid : k.idOk s i) (hr : k.recOk s i = true) (hir : i < κ.lrec k)
    (hyv : ∀ a, k.valid [(a, y)] = true) (hcap : (assocSet (k.view s i) x y).length ≤ κ.lcap k) :
    ∃ L' c, evalF κ (assocSetP k).body s L = .ok (k.put s i (assocSet (k.view s i) x y)) L' c ∧
      c ≤ 40 + 25 * (k.view s i).length := by
  set l := k.view s i
  have hlv : k.valid l = true := LK.valid_view s i k
  have hcap0 : l.length ≤ κ.lcap k := by
    rw [assocSet_eq] at hcap; split at hcap
    · rw [length_preSet] at hcap; exact hcap
    · simp at hcap; omega
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "n") (e := .llen k "i") (v := l.length)
    (by simp [Exp.ev, hi, hir, l])
  have a2 := evalF_assign_ok (κ := κ) (s := s) (L := OM.Machine.State.upd L "n" l.length) (x := "f")
    (e := (0 : Exp)) (v := 0) rfl
  set L0 := OM.Machine.State.upd (OM.Machine.State.upd L "n" l.length) "f" 0
  have hL0 : ∀ r, r ≠ "n" → r ≠ "f" → L0 r = L r := fun r h1 h2 => by
    simp [L0, OM.Machine.State.upd, h1, h2]
  let I : Nat → Core → Loc → Prop := fun j s' L' => s' = k.put s i (preSet l x y j) ∧ L' "i" = i ∧
    L' "x" = x ∧ L' "y" = y ∧ L' "n" = l.length ∧ L' "f" = if (l.take j).any (·.1 == x) then 1 else 0
  obtain ⟨s', L', c, he, hc, hI⟩ := evalF_loop (x := "j") (n := .var "n")
    (b := .ite (.lrd k false "i" "j" =ₑ "x") (.lwr k true "i" "j" "y" ;; "f" ::= 1) .skip)
    (s := s) (L := L0) (N := l.length) (by simp [Exp.ev, L0, OM.Machine.State.upd]) I 22
    ⟨by rw [preSet_zero, LK.put_view hid], by rw [hL0 "i" (by decide) (by decide), hi],
      by rw [hL0 "x" (by decide) (by decide), hx], by rw [hL0 "y" (by decide) (by decide), hy],
      by simp [L0, OM.Machine.State.upd], by simp [L0, OM.Machine.State.upd]⟩
    (by
      intro j hj s1 L1 ⟨hs1, hi1, hx1, hy1, hn1, hf1⟩
      subst hs1
      have hview : k.view (k.put s i (preSet l x y j)) i = preSet l x y j := by
        rw [LK.view_put hr (valid_preSet hlv hyv)]; simp
      set L2 := OM.Machine.State.upd L1 "j" j
      have hL2 : ∀ r, r ≠ "j" → L2 r = L1 r := fun r h => by simp [L2, OM.Machine.State.upd, h]
      have hkey : (Exp.lrd k false "i" "j").ev κ (k.put s i (preSet l x y j)) L2 = some l[j].1 := by
        simp only [Exp.ev, hL2 "i" (by decide), hi1, show L2 "j" = j by simp [L2, OM.Machine.State.upd],
          Option.bind_some, hview, length_preSet, preSet_getD hj]
        simp [hir, hj]
      have hL2j : L2 "j" = j := by simp [L2, OM.Machine.State.upd]
      have hcond : (Exp.lrd k false "i" "j" =ₑ "x").ev κ (k.put s i (preSet l x y j)) L2 =
          some (if l[j].1 = x then 1 else 0) := by
        simp only [Exp.ev] at hkey ⊢
        rw [hkey]; simp [OM.Machine.BinOp.eval, hL2 "x" (by decide), hx1]
      by_cases hm : l[j].1 = x
      · have hw : (preSet l x y j).set j (((preSet l x y j).getD j (0, 0)).1, y) = preSet l x y (j + 1) := by
          rw [preSet_succ hj, if_pos hm, preSet_getD hj]
        have hset : k.set κ (k.put s i (preSet l x y j)) i
            ((preSet l x y j).set j (((preSet l x y j).getD j (0, 0)).1, y)) =
            some (k.put s i (preSet l x y (j + 1))) := by
          rw [hw, LK.set_ok (by rw [LK.recOk_put]; exact hr) (valid_preSet hlv hyv)
            (by rw [length_preSet]; exact hcap0) hir, LK.put_put]
        have ew : evalF κ (.lwr k true "i" "j" "y") (k.put s i (preSet l x y j)) L2 =
            .ok (k.put s i (preSet l x y (j + 1))) L2 7 := by
          simp only [evalF, Exp.ev, hL2 "i" (by decide), hi1, hL2j, hL2 "y" (by decide), hy1, hview,
            length_preSet, if_pos hj, if_true, hset, Exp.cost]
        have ef := evalF_assign_ok (κ := κ) (s := k.put s i (preSet l x y (j + 1))) (L := L2) (x := "f")
          (e := (1 : Exp)) (v := 1) rfl
        refine ⟨_, _, _, evalF_ite_t hcond (by simp [hm]) (evalF_seq_ok2 ew ef), ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
        · simp [Exp.cost]
        · simp [OM.Machine.State.upd, L2, hi1]
        · simp [OM.Machine.State.upd, L2, hx1]
        · simp [OM.Machine.State.upd, L2, hy1]
        · simp [OM.Machine.State.upd, L2, hn1]
        · rw [take_succ_any l x j hj]; simp [OM.Machine.State.upd, hm]
      · have hs : k.put s i (preSet l x y (j + 1)) = k.put s i (preSet l x y j) := by
          rw [preSet_succ hj, if_neg hm]
          congr 1
          conv => rhs; rw [← List.set_getElem_self (as := preSet l x y j) (i := j) (by rw [length_preSet]; exact hj)]
          congr 1
          rw [← preSet_getD (x := x) (y := y) hj, List.getD_eq_getElem]
        refine ⟨_, _, _, evalF_ite_f (by rw [hcond, if_neg hm]) evalF_skip, ?_, hs.symm, ?_, ?_, ?_, ?_, ?_⟩
        · simp [Exp.cost]
        · rw [hL2 "i" (by decide), hi1]
        · rw [hL2 "x" (by decide), hx1]
        · rw [hL2 "y" (by decide), hy1]
        · rw [hL2 "n" (by decide), hn1]
        · have hb : (l[j].1 == x) = false := by simpa using hm
          rw [hL2 "f" (by decide), hf1, take_succ_any l x j hj, hb, Bool.or_false])
  obtain ⟨hs', hi', hx', hy', hn', hf'⟩ := hI
  rw [List.take_of_length_le le_rfl] at hf'
  subst hs'
  have hview : k.view (k.put s i (preSet l x y l.length)) i = preSet l x y l.length := by
    rw [LK.view_put hr (valid_preSet hlv hyv)]; simp
  rw [assocSet_eq] at hcap ⊢
  by_cases ha : l.any (·.1 == x) = true
  · rw [if_pos ha] at hcap ⊢
    rw [if_pos ha] at hf'
    refine ⟨L', _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 he
      (evalF_ite_f (by simp [Exp.ev, OM.Machine.BinOp.eval, hf']) evalF_skip))), ?_⟩
    simp [Exp.cost] at hc ⊢; omega
  · have ha' : l.any (·.1 == x) = false := by revert ha; cases l.any (·.1 == x) <;> simp
    rw [if_neg ha] at hcap ⊢
    rw [if_neg ha] at hf'
    rw [preSet_noMatch ha'] at hview he
    have hg : evalF κ (.lgrow k "i" "x" "y") (k.put s i l) L' =
        .ok (k.put s i (l ++ [(x, y)])) L' 22 := by
      have hval : k.valid (l ++ [(x, y)]) = true := by
        rw [LK.valid_iff] at hlv ⊢
        intro q hq; simp only [List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact hlv q hq
        · exact hyv x
      have hso := LK.set_ok (κ := κ) (s := k.put s i l) (i := i) (l := l ++ [(x, y)]) (k := k)
        (by rw [LK.recOk_put]; exact hr) hval hcap hir
      simp only [evalF, Exp.ev, hi', hx', hy', hview, hso, LK.put_put, Exp.cost]
    refine ⟨L', _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 he
      (evalF_ite_t (by simp [Exp.ev, OM.Machine.BinOp.eval, hf']) one_ne_zero hg))), ?_⟩
    simp [Exp.cost] at hc ⊢; omega

end OM.Impl
