import OM.Impl.ListLib
import OM.Model.Top

/-!
# M6: `startDrain`'s cut (`drainCut`) as loops

Each loop of `drainCutP` only changes locals; its result is a fold over the iterations, and the
lemmas here identify those folds with `List.sum`, `cutLen`, `shiftR` and `shiftL`.
-/

namespace OM.Impl

open OM.Model

/-! ### The folds -/

theorem foldl_sum (w : Nat → Nat) : ∀ (l : List Nat) (a : Nat),
    l.foldl (fun a j => a + w j) a = a + (l.map w).sum
  | [], a => by simp
  | j :: l, a => by simp only [List.foldl_cons, List.map_cons, List.sum_cons]; rw [foldl_sum w l]; omega

/-- One step of the greedy cut: count `cnt`, remaining budget `b`, and a stop flag. -/
def cutStep (st : Nat × Nat × Nat) (w : Nat) : Nat × Nat × Nat :=
  if st.2.2 = 0 ∧ w ≤ st.2.1 then (st.1 + 1, st.2.1 - w, 0) else (st.1, st.2.1, 1)

theorem foldl_cutStep_stop : ∀ (l : List Nat) (cnt b : Nat), l.foldl cutStep (cnt, b, 1) = (cnt, b, 1)
  | [], _, _ => rfl
  | w :: l, cnt, b => by simp only [List.foldl_cons, cutStep]; simpa using foldl_cutStep_stop l cnt b

theorem foldl_cutStep : ∀ (l : List Nat) (cnt b : Nat), (l.foldl cutStep (cnt, b, 0)).1 = cnt + cutLen l b
  | [], _, _ => rfl
  | w :: l, cnt, b => by
    simp only [List.foldl_cons, cutLen]
    by_cases h : w ≤ b
    · simp only [cutStep, h, and_self, if_true]; rw [foldl_cutStep l]; omega
    · simp only [cutStep, h, and_false, if_false]; rw [foldl_cutStep_stop]; simp

/-- One step of `shiftR` (the iteration number is not used). -/
def shRStep (pr : Nat → Bool) (n : Nat) (st : Nat × Nat) : Nat × Nat :=
  if st.2 = 0 ∧ 0 < st.1 ∧ st.1 < n ∧ pr st.1 = true then (st.1 + 1, 0) else (st.1, 1)

theorem foldl_shRStep_stop (pr : Nat → Bool) (n : Nat) : ∀ (l : List Nat) (k : Nat),
    l.foldl (fun st _ => shRStep pr n st) (k, 1) = (k, 1)
  | [], _ => rfl
  | _ :: l, k => by
    rw [List.foldl_cons, show shRStep pr n (k, 1) = (k, 1) by simp [shRStep] ]; exact foldl_shRStep_stop pr n l k

theorem foldl_shRStep (pr : Nat → Bool) (n : Nat) : ∀ (l : List Nat) (k : Nat),
    (l.foldl (fun st _ => shRStep pr n st) (k, 0)).1 = shiftR pr n l.length k
  | [], _ => rfl
  | _ :: l, k => by
    simp only [List.foldl_cons, List.length_cons, shiftR]
    by_cases h : 0 < k ∧ k < n ∧ pr k = true
    · rw [show shRStep pr n (k, 0) = (k + 1, 0) by simp [shRStep, h] ]
      rw [foldl_shRStep pr n l]; simp [h]
    · rw [show shRStep pr n (k, 0) = (k, 1) by simp only [shRStep]; rw [if_neg (by simpa using h)] ]
      rw [foldl_shRStep_stop]
      by_cases h1 : 0 < k ∧ k < n
      · have : pr k = false := by simpa [h1] using h
        simp [h1, this]
      · simp only [decide_eq_true_eq, Bool.and_eq_true]; rw [if_neg (by simpa using h1)]

/-- One step of `shiftL`. -/
def shLStep (pr : Nat → Bool) (st : Nat × Nat) : Nat × Nat :=
  if st.2 = 0 ∧ 0 < st.1 ∧ pr st.1 = true then (st.1 - 1, 0) else (st.1, 1)

theorem foldl_shLStep_stop (pr : Nat → Bool) : ∀ (l : List Nat) (k : Nat),
    l.foldl (fun st _ => shLStep pr st) (k, 1) = (k, 1)
  | [], _ => rfl
  | _ :: l, k => by
    rw [List.foldl_cons, show shLStep pr (k, 1) = (k, 1) by simp [shLStep] ]; exact foldl_shLStep_stop pr l k

theorem foldl_shLStep (pr : Nat → Bool) : ∀ (l : List Nat) (k : Nat),
    (l.foldl (fun st _ => shLStep pr st) (k, 0)).1 = shiftL pr l.length k
  | [], _ => rfl
  | _ :: l, k => by
    simp only [List.foldl_cons, List.length_cons, shiftL]
    by_cases h : 0 < k ∧ pr k = true
    · rw [show shLStep pr (k, 0) = (k - 1, 0) by simp [shLStep, h] ]
      rw [foldl_shLStep pr l]; simp [h.1, h.2]
    · rw [show shLStep pr (k, 0) = (k, 1) by simp only [shLStep]; rw [if_neg (by simpa using h)] ]
      rw [foldl_shLStep_stop]
      by_cases h1 : 0 < k
      · have : pr k = false := by simpa [h1] using h
        simp [h1, this]
      · simp [show k = 0 by omega]

theorem range_map_getD (l : List Nat) (g : Nat → Nat) {m : Nat} (hm : m ≤ l.length) :
    (List.range m).map (fun j => g (l.getD j 0)) = (l.map g).take m := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [List.getElem?_eq_getElem (show i < l.length by omega)]

/-! ### The procedure -/

open OM.Machine (Reg BinOp UnOp)

local notation "upd" => OM.Machine.State.upd

/-- `w := drainWt h e`. -/
def wtS : Stm := .ite ("h" =ₑ 1) ("w" ::= 1) ("w" ::= .rd (.n .weight) "e")

theorem wtS_ok {κ : Caps} {s : Core} {L : Loc} {h e : Nat} (hh : L "h" = h) (he : L "e" = e)
    (heN : e < κ.tbl .N) : ∃ c, evalF κ wtS s L = .ok s (upd L "w" (drainWt s.nodes h e)) c ∧ c ≤ 10 := by
  unfold wtS drainWt
  by_cases h1 : h = 1
  · simp [evalF, Exp.ev, hh, he, h1, Res.addCost, Exp.cost, OM.Machine.BinOp.eval]
  · simp [evalF, Exp.ev, hh, he, h1, heN, Res.addCost, Exp.cost, OM.Machine.BinOp.eval, Fld.cap, Fld.get,
      NF.get]

/-- `t := the sum of the weights of the children of `v``. -/
def sumBody : Stm := "e" ::= .lrd .children false "v" "j" ;; wtS ;; "t" ::= "t" + "w"
def sumS : Stm := "t" ::= 0 ;; .loop "j" "n" sumBody

theorem sumS_ok {κ : Caps} {s : Core} {L : Loc} {v h : Nat} (hv : L "v" = v) (hh : L "h" = h)
    (hn : L "n" = (s.nodes.getX v).children.length) (hvr : v < κ.lrec .children)
    (hkN : ∀ e ∈ (s.nodes.getX v).children, e < κ.tbl .N) :
    ∃ L' c, evalF κ sumS s L = .ok s L' c ∧ c ≤ 10 + 40 * (s.nodes.getX v).children.length ∧
      L' "t" = ((s.nodes.getX v).children.map (drainWt s.nodes h)).sum ∧
      ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "w" → r ≠ "t" → L' r = L r := by
  set kids := (s.nodes.getX v).children
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "t") (e := (0 : Exp)) (v := 0) rfl
  obtain ⟨L', c, he, hc, hF, ha⟩ := evalF_loop_pure (κ := κ) (x := "j") (n := .var "n") (b := sumBody)
    (s := s) (L := upd L "t" 0) (N := kids.length) (by simp [Exp.ev, OM.Machine.State.upd, hn, kids])
    (fun L' => ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "w" → r ≠ "t" → L' r = L r) (fun L' => L' "t")
    (fun t j => t + drainWt s.nodes h (kids.getD j 0)) 38
    (fun r h1 h2 h3 h4 => by simp [OM.Machine.State.upd, h4])
    (by
      intro k hk L1 hF
      have hv1 : L1 "v" = v := by rw [hF "v" (by decide) (by decide) (by decide) (by decide), hv]
      have hh1 : L1 "h" = h := by rw [hF "h" (by decide) (by decide) (by decide) (by decide), hh]
      have hkk : kids.getD k 0 < κ.tbl .N := hkN _ (by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk)
      have e1 := evalF_assign_ok (κ := κ) (s := s) (L := upd L1 "j" k) (x := "e")
        (e := .lrd .children false "v" "j") (v := kids.getD k 0) (by
          simp [Exp.ev, OM.Machine.State.upd, hv1, hvr, LK.view, kids, hk])
      obtain ⟨c2, e2, hc2⟩ := wtS_ok (κ := κ) (s := s) (L := upd (upd L1 "j" k) "e" (kids.getD k 0))
        (h := h) (e := kids.getD k 0) (by simp [OM.Machine.State.upd, hh1]) (by simp [OM.Machine.State.upd]) hkk
      have e3 := evalF_assign_ok (κ := κ) (s := s)
        (L := upd (upd (upd L1 "j" k) "e" (kids.getD k 0)) "w" (drainWt s.nodes h (kids.getD k 0))) (x := "t")
        (e := "t" + "w") (v := L1 "t" + drainWt s.nodes h (kids.getD k 0))
        (by simp [Exp.ev, OM.Machine.State.upd, OM.Machine.BinOp.eval])
      refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 e3), ?_, ?_, ?_⟩
      · simp [Exp.cost]; omega
      · intro r h1 h2 h3 h4; simp [OM.Machine.State.upd, h1, h2, h3, h4]; exact hF r h1 h2 h3 h4
      · simp [OM.Machine.State.upd])
  refine ⟨L', _, evalF_seq_ok2 a1 he, ?_, ?_, hF⟩
  · simp [Exp.cost] at hc ⊢; nlinarith
  · rw [ha, foldl_sum]
    rw [range_map_getD kids (drainWt s.nodes h) le_rfl,
      List.take_of_length_le (by simp)]
    simp [OM.Machine.State.upd]

/-- The greedy cut over the first `n - 1` children, with budget `t / 2`. -/
def cutBody : Stm :=
  "e" ::= .lrd .children false "v" "j" ;; wtS ;;
  .ite (("d" =ₑ 0) &&ₑ ("w" ≤ₑ "b")) ("c" ::= "c" + 1 ;; "b" ::= "b" - "w") ("d" ::= 1)
def cutS : Stm := "b" ::= "t" / 2 ;; "c" ::= 0 ;; "d" ::= 0 ;; .loop "j" (.monus "n" 1) cutBody

theorem cutS_ok {κ : Caps} {s : Core} {L : Loc} {v h : Nat} (hv : L "v" = v) (hh : L "h" = h)
    (hn : L "n" = (s.nodes.getX v).children.length) (hvr : v < κ.lrec .children)
    (hkN : ∀ e ∈ (s.nodes.getX v).children, e < κ.tbl .N) :
    ∃ L' c, evalF κ cutS s L = .ok s L' c ∧ c ≤ 40 + 60 * (s.nodes.getX v).children.length ∧
      L' "c" = cutLen (((s.nodes.getX v).children.map (drainWt s.nodes h)).take
        ((s.nodes.getX v).children.length - 1)) (L "t" / 2) ∧
      ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "w" → r ≠ "b" → r ≠ "c" → r ≠ "d" → L' r = L r := by
  set kids := (s.nodes.getX v).children
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "b") (e := "t" / 2) (v := L "t" / 2)
    (by simp [Exp.ev, OM.Machine.BinOp.eval])
  have a2 := evalF_assign_ok (κ := κ) (s := s) (L := upd L "b" (L "t" / 2)) (x := "c") (e := (0 : Exp)) (v := 0) rfl
  have a3 := evalF_assign_ok (κ := κ) (s := s) (L := upd (upd L "b" (L "t" / 2)) "c" 0) (x := "d")
    (e := (0 : Exp)) (v := 0) rfl
  obtain ⟨L', c, he, hc, hF, ha⟩ := evalF_loop_pure (κ := κ) (x := "j") (n := .monus "n" 1) (b := cutBody)
    (s := s) (L := upd (upd (upd L "b" (L "t" / 2)) "c" 0) "d" 0) (N := kids.length - 1)
    (Exp.ev_monus κ s _ (by simp [Exp.ev, OM.Machine.State.upd, hn, kids]) rfl)
    (fun L' => ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "w" → r ≠ "b" → r ≠ "c" → r ≠ "d" → L' r = L r)
    (fun L' => (L' "c", L' "b", L' "d"))
    (fun st j => cutStep st (drainWt s.nodes h (kids.getD j 0))) 50
    (fun r h1 h2 h3 h4 h5 h6 => by simp [OM.Machine.State.upd, h4, h5, h6])
    (by
      intro k hk L1 hF
      have hk' : k < kids.length := by omega
      have hv1 : L1 "v" = v := by rw [hF "v" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hv]
      have hh1 : L1 "h" = h := by rw [hF "h" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hh]
      have hkk : kids.getD k 0 < κ.tbl .N := hkN _ (by rw [List.getD_eq_getElem _ _ hk']; exact List.getElem_mem hk')
      have e1 := evalF_assign_ok (κ := κ) (s := s) (L := upd L1 "j" k) (x := "e")
        (e := .lrd .children false "v" "j") (v := kids.getD k 0) (by
          simp [Exp.ev, OM.Machine.State.upd, hv1, hvr, LK.view, kids, hk'])
      obtain ⟨c2, e2, hc2⟩ := wtS_ok (κ := κ) (s := s) (L := upd (upd L1 "j" k) "e" (kids.getD k 0))
        (h := h) (e := kids.getD k 0) (by simp [OM.Machine.State.upd, hh1]) (by simp [OM.Machine.State.upd]) hkk
      set w := drainWt s.nodes h (kids.getD k 0)
      set L2 := upd (upd (upd L1 "j" k) "e" (kids.getD k 0)) "w" w
      have hL2 : ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "w" → L2 r = L1 r := by
        intro r h1 h2 h3; simp [L2, OM.Machine.State.upd, h1, h2, h3]
      have hd2 : L2 "d" = L1 "d" := hL2 "d" (by decide) (by decide) (by decide)
      have hb2 : L2 "b" = L1 "b" := hL2 "b" (by decide) (by decide) (by decide)
      have hc2' : L2 "c" = L1 "c" := hL2 "c" (by decide) (by decide) (by decide)
      have hw2 : L2 "w" = w := by simp [L2, OM.Machine.State.upd]
      by_cases hcond : L1 "d" = 0 ∧ w ≤ L1 "b"
      · have e3 := evalF_assign_ok (κ := κ) (s := s) (L := L2) (x := "c") (e := "c" + 1) (v := L1 "c" + 1)
          (by simp [Exp.ev, OM.Machine.BinOp.eval, hc2'])
        have e4 := evalF_assign_ok (κ := κ) (s := s) (L := upd L2 "c" (L1 "c" + 1)) (x := "b") (e := "b" - "w")
          (v := L1 "b" - w) (by simp [Exp.ev, OM.Machine.BinOp.eval, OM.Machine.State.upd, hb2, hw2, hcond.2])
        have e5 := evalF_ite_t (κ := κ) (s := s) (L := L2) (v := 1) (c := ("d" =ₑ 0) &&ₑ ("w" ≤ₑ "b"))
          (f := "d" ::= 1) (by simp [Exp.ev, OM.Machine.BinOp.eval, hd2, hb2, hw2, hcond.1, hcond.2]) one_ne_zero
          (evalF_seq_ok2 e3 e4)
        refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 e5), ?_, ?_, ?_⟩
        · simp [Exp.cost]; omega
        · intro r h1 h2 h3 h4 h5 h6
          simp only [OM.Machine.State.upd, if_neg h4, if_neg h5]; rw [hL2 r h1 h2 h3]; exact hF r h1 h2 h3 h4 h5 h6
        · simp [OM.Machine.State.upd, cutStep, hcond, hd2]
      · have e3 := evalF_assign_ok (κ := κ) (s := s) (L := L2) (x := "d") (e := (1 : Exp)) (v := 1) rfl
        have e5 := evalF_ite_f (κ := κ) (s := s) (L := L2) (c := ("d" =ₑ 0) &&ₑ ("w" ≤ₑ "b"))
          (t := "c" ::= "c" + 1 ;; "b" ::= "b" - "w") (by
            by_cases h1 : L1 "d" = 0 <;> by_cases h2 : w ≤ L1 "b" <;>
              simp [Exp.ev, OM.Machine.BinOp.eval, hd2, hb2, hw2, h1, h2] <;> exact absurd ⟨h1, h2⟩ hcond) e3
        refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 e5), ?_, ?_, ?_⟩
        · simp [Exp.cost]; omega
        · intro r h1 h2 h3 h4 h5 h6
          simp only [OM.Machine.State.upd, if_neg h6]; rw [hL2 r h1 h2 h3]; exact hF r h1 h2 h3 h4 h5 h6
        · rw [show cutStep (L1 "c", L1 "b", L1 "d") w = (L1 "c", L1 "b", 1) from if_neg hcond]
          simp [OM.Machine.State.upd, hb2, hc2'])
  refine ⟨L', _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 a3 he)), ?_, ?_, hF⟩
  · have : (kids.length - 1) * (1 + 50) ≤ kids.length * 51 := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    simp [Exp.cost] at hc ⊢; omega
  · have := congrArg Prod.fst ha
    simp only at this
    have hfm : ∀ (m : Nat) init, (List.range m).foldl (fun st j => cutStep st (drainWt s.nodes h (kids.getD j 0)))
        init = ((List.range m).map fun j => drainWt s.nodes h (kids.getD j 0)).foldl cutStep init :=
      fun m init => by rw [List.foldl_map]
    rw [this, hfm, range_map_getD kids (drainWt s.nodes h) (by omega)]
    simp only [OM.Machine.State.upd]
    simp only [show ("c" = "d") = False by decide, show ("b" = "d") = False by decide,
      show ("b" = "c") = False by decide, show ("d" = "d") = True by decide, show ("c" = "c") = True by decide,
      show ("b" = "b") = True by decide, if_true, if_false]
    rw [foldl_cutStep]; simp

/-- Read children `k - 1` and `k` into `a`, `e` (for `0 < k < n`). -/
def prS : Stm := "a" ::= .lrd .children false "v" ("k" - 1) ;; "e" ::= .lrd .children false "v" "k"
/-- `drainPr`: children `a`, `e` are targets of one drain. -/
def prE : Exp := (!ₑ (.rd (.n .overflow) "a" =ₑ 0)) &&ₑ (.rd (.n .overflow) "a" =ₑ .rd (.n .overflow) "e")

theorem prS_ok {κ : Caps} {s : Core} {L : Loc} {v k : Nat} (hv : L "v" = v) (hk : L "k" = k) (hk0 : 0 < k)
    (hkn : k < (s.nodes.getX v).children.length) (hvr : v < κ.lrec .children)
    (hkN : ∀ e ∈ (s.nodes.getX v).children, e < κ.tbl .N) :
    ∃ L' c, evalF κ prS s L = .ok s L' c ∧ c ≤ 20 ∧
      prE.ev κ s L' = some (if drainPr s.nodes (s.nodes.getX v).children k then 1 else 0) ∧
      ∀ r, r ≠ "a" → r ≠ "e" → L' r = L r := by
  set kids := (s.nodes.getX v).children
  have hk1 : k - 1 < kids.length := by omega
  have e1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "a") (e := .lrd .children false "v" ("k" - 1))
    (v := kids.getD (k - 1) 0) (by
      simp [Exp.ev, OM.Machine.BinOp.eval, hv, hk, hvr, LK.view, kids, hk1, show 1 ≤ k by omega])
  have e2 := evalF_assign_ok (κ := κ) (s := s) (L := upd L "a" (kids.getD (k - 1) 0)) (x := "e")
    (e := .lrd .children false "v" "k") (v := kids.getD k 0) (by
      simp [Exp.ev, OM.Machine.State.upd, hv, hk, hvr, LK.view, kids, hkn])
  have ha : kids.getD (k - 1) 0 < κ.tbl .N := hkN _ (by rw [List.getD_eq_getElem _ _ hk1]; exact List.getElem_mem hk1)
  have hb : kids.getD k 0 < κ.tbl .N := hkN _ (by rw [List.getD_eq_getElem _ _ hkn]; exact List.getElem_mem hkn)
  refine ⟨_, _, evalF_seq_ok2 e1 e2, by simp [Exp.cost], ?_, ?_⟩
  · unfold drainPr sameDrainN
    simp only [prE, Exp.ev, OM.Machine.State.upd, show ("a" = "e") = False by decide, if_true, if_false,
      Option.bind_some, ha, hb, Fld.cap, Fld.get, NF.get, OM.Machine.BinOp.eval, OM.Machine.UnOp.eval,
      Exp.ofNat_def, Option.map_some]
    by_cases h1 : (s.nodes.getX (kids.getD (k - 1) 0)).overflowOf = 0 <;>
      by_cases h2 : (s.nodes.getX (kids.getD (k - 1) 0)).overflowOf = (s.nodes.getX (kids.getD k 0)).overflowOf <;>
      simp [h1, h2, NIL]
  · intro r h1 h2; simp [OM.Machine.State.upd, h1, h2]

/-- `shiftR`: move the cut `k` right past pairs, at most `n` times. -/
def shRC : Exp := (("d" =ₑ 0) &&ₑ (0 <ₑ "k")) &&ₑ ("k" <ₑ "n")
def shRBody : Stm := .ite shRC (prS ;; .ite prE ("k" ::= "k" + 1) ("d" ::= 1)) ("d" ::= 1)
def shRS : Stm := "d" ::= 0 ;; .loop "j" "n" shRBody

theorem shRS_ok {κ : Caps} {s : Core} {L : Loc} {v : Nat} (hv : L "v" = v)
    (hn : L "n" = (s.nodes.getX v).children.length) (hvr : v < κ.lrec .children)
    (hkN : ∀ e ∈ (s.nodes.getX v).children, e < κ.tbl .N) :
    ∃ L' c, evalF κ shRS s L = .ok s L' c ∧ c ≤ 10 + 60 * (s.nodes.getX v).children.length ∧
      L' "k" = shiftR (drainPr s.nodes (s.nodes.getX v).children) (s.nodes.getX v).children.length
        (s.nodes.getX v).children.length (L "k") ∧
      ∀ r, r ≠ "j" → r ≠ "a" → r ≠ "e" → r ≠ "k" → r ≠ "d" → L' r = L r := by
  set kids := (s.nodes.getX v).children
  set pr := drainPr s.nodes kids
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "d") (e := (0 : Exp)) (v := 0) rfl
  obtain ⟨L', c, he, hc, hF, ha⟩ := evalF_loop_pure (κ := κ) (x := "j") (n := .var "n") (b := shRBody)
    (s := s) (L := upd L "d" 0) (N := kids.length) (by simp [Exp.ev, OM.Machine.State.upd, hn, kids])
    (fun L' => ∀ r, r ≠ "j" → r ≠ "a" → r ≠ "e" → r ≠ "k" → r ≠ "d" → L' r = L r)
    (fun L' => (L' "k", L' "d")) (fun st _ => shRStep pr kids.length st) 50
    (fun r h1 h2 h3 h4 h5 => by simp [OM.Machine.State.upd, h5])
    (by
      intro j hj L1 hF
      have hv1 : L1 "v" = v := by rw [hF "v" (by decide) (by decide) (by decide) (by decide) (by decide), hv]
      have hn1 : L1 "n" = kids.length := by
        rw [hF "n" (by decide) (by decide) (by decide) (by decide) (by decide), hn]
      set L2 := upd L1 "j" j
      have hL2 : ∀ r, r ≠ "j" → L2 r = L1 r := fun r h => by simp [L2, OM.Machine.State.upd, h]
      by_cases hcond : L1 "d" = 0 ∧ 0 < L1 "k" ∧ L1 "k" < kids.length
      · obtain ⟨L3, c3, e3, hc3, hp, hL3⟩ := prS_ok (κ := κ) (s := s) (L := L2) (k := L1 "k")
          (by rw [hL2 "v" (by decide), hv1]) (hL2 "k" (by decide)) hcond.2.1 hcond.2.2 hvr hkN
        have hc0 : shRC.ev κ s L2 = some 1 := by
          simp [shRC, Exp.ev, OM.Machine.BinOp.eval, hL2 "d" (by decide), hL2 "k" (by decide),
            hL2 "n" (by decide), hn1, hcond.1, hcond.2.1, hcond.2.2]
        have hk3 : L3 "k" = L1 "k" := by rw [hL3 "k" (by decide) (by decide), hL2 "k" (by decide)]
        have hd3 : L3 "d" = L1 "d" := by rw [hL3 "d" (by decide) (by decide), hL2 "d" (by decide)]
        by_cases hpr : pr (L1 "k") = true
        · have e4 := evalF_assign_ok (κ := κ) (s := s) (L := L3) (x := "k") (e := "k" + 1) (v := L1 "k" + 1)
            (by simp [Exp.ev, OM.Machine.BinOp.eval, hk3])
          have e5 := evalF_ite_t (κ := κ) (s := s) (L := L3) (c := prE) (f := "d" ::= 1) (v := 1)
            (by rw [hp, if_pos hpr]) one_ne_zero e4
          refine ⟨_, _, evalF_ite_t hc0 one_ne_zero (evalF_seq_ok2 e3 e5), ?_, ?_, ?_⟩
          · simp [Exp.cost, prE, shRC]; omega
          · intro r h1 h2 h3 h4 h5
            simp only [OM.Machine.State.upd, if_neg h4]; rw [hL3 r h2 h3, hL2 r h1]; exact hF r h1 h2 h3 h4 h5
          · simp [OM.Machine.State.upd, shRStep, hcond, hpr, hd3]
        · have e4 := evalF_assign_ok (κ := κ) (s := s) (L := L3) (x := "d") (e := (1 : Exp)) (v := 1) rfl
          have e5 := evalF_ite_f (κ := κ) (s := s) (L := L3) (c := prE) (t := "k" ::= "k" + 1)
            (by rw [hp, if_neg hpr]) e4
          refine ⟨_, _, evalF_ite_t hc0 one_ne_zero (evalF_seq_ok2 e3 e5), ?_, ?_, ?_⟩
          · simp [Exp.cost, prE, shRC]; omega
          · intro r h1 h2 h3 h4 h5
            simp only [OM.Machine.State.upd, if_neg h5]; rw [hL3 r h2 h3, hL2 r h1]; exact hF r h1 h2 h3 h4 h5
          · rw [show shRStep pr kids.length (L1 "k", L1 "d") = (L1 "k", 1) by
              simp only [shRStep]; rw [if_neg (by simp [hpr])] ]
            simp [OM.Machine.State.upd, hk3]
      · have e4 := evalF_assign_ok (κ := κ) (s := s) (L := L2) (x := "d") (e := (1 : Exp)) (v := 1) rfl
        have hc0 : shRC.ev κ s L2 = some 0 := by
          by_cases h1 : L1 "d" = 0 <;> by_cases h2 : 0 < L1 "k" <;> by_cases h3 : L1 "k" < kids.length <;>
            simp [shRC, Exp.ev, OM.Machine.BinOp.eval, hL2 "d" (by decide), hL2 "k" (by decide), hL2 "n" (by decide),
              hn1, h1, h2, h3] <;> exact absurd ⟨h1, h2, h3⟩ hcond
        refine ⟨_, _, evalF_ite_f hc0 e4, ?_, ?_, ?_⟩
        · simp [Exp.cost, shRC]
        · intro r h1 h2 h3 h4 h5
          simp only [OM.Machine.State.upd, if_neg h5]; rw [hL2 r h1]; exact hF r h1 h2 h3 h4 h5
        · rw [show shRStep pr kids.length (L1 "k", L1 "d") = (L1 "k", 1) by
            simp only [shRStep]; rw [if_neg (by tauto)] ]
          simp [OM.Machine.State.upd, L2])
  refine ⟨L', _, evalF_seq_ok2 a1 he, ?_, ?_, hF⟩
  · simp [Exp.cost] at hc ⊢; omega
  · have := congrArg Prod.fst ha
    simp only at this
    have h0 : (upd L "d" 0 "k", upd L "d" 0 "d") = (L "k", 0) := by simp [OM.Machine.State.upd]
    rw [this, h0, foldl_shRStep, List.length_range]

/-- `shiftL` from `n - 1`: move the cut left past pairs, at most `n` times. -/
def shLC : Exp := ("d" =ₑ 0) &&ₑ (0 <ₑ "k")
def shLBody : Stm := .ite shLC (prS ;; .ite prE ("k" ::= "k" - 1) ("d" ::= 1)) ("d" ::= 1)
def shLS : Stm := "k" ::= .monus "n" 1 ;; "d" ::= 0 ;; .loop "j" "n" shLBody

theorem shLS_ok {κ : Caps} {s : Core} {L : Loc} {v : Nat} (hv : L "v" = v)
    (hn : L "n" = (s.nodes.getX v).children.length) (hvr : v < κ.lrec .children)
    (hkN : ∀ e ∈ (s.nodes.getX v).children, e < κ.tbl .N) :
    ∃ L' c, evalF κ shLS s L = .ok s L' c ∧ c ≤ 40 + 60 * (s.nodes.getX v).children.length ∧
      L' "k" = shiftL (drainPr s.nodes (s.nodes.getX v).children) (s.nodes.getX v).children.length
        ((s.nodes.getX v).children.length - 1) ∧
      ∀ r, r ≠ "j" → r ≠ "a" → r ≠ "e" → r ≠ "k" → r ≠ "d" → L' r = L r := by
  set kids := (s.nodes.getX v).children
  set pr := drainPr s.nodes kids
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "k") (e := .monus "n" 1) (v := kids.length - 1)
    (Exp.ev_monus κ s L (by simp [Exp.ev, hn, kids]) rfl)
  have a2 := evalF_assign_ok (κ := κ) (s := s) (L := upd L "k" (kids.length - 1)) (x := "d") (e := (0 : Exp))
    (v := 0) rfl
  obtain ⟨L', c, he, hc, hF, ha⟩ := evalF_loop_pure (κ := κ) (x := "j") (n := .var "n") (b := shLBody)
    (s := s) (L := upd (upd L "k" (kids.length - 1)) "d" 0) (N := kids.length)
    (by simp [Exp.ev, OM.Machine.State.upd, hn, kids])
    (fun L' => L' "k" ≤ kids.length - 1 ∧ ∀ r, r ≠ "j" → r ≠ "a" → r ≠ "e" → r ≠ "k" → r ≠ "d" → L' r = L r)
    (fun L' => (L' "k", L' "d")) (fun st _ => shLStep pr st) 50
    ⟨by simp [OM.Machine.State.upd], fun r h1 h2 h3 h4 h5 => by simp [OM.Machine.State.upd, h4, h5]⟩
    (by
      intro j hj L1 ⟨hkle, hF⟩
      have hv1 : L1 "v" = v := by rw [hF "v" (by decide) (by decide) (by decide) (by decide) (by decide), hv]
      set L2 := upd L1 "j" j
      have hL2 : ∀ r, r ≠ "j" → L2 r = L1 r := fun r h => by simp [L2, OM.Machine.State.upd, h]
      by_cases hcond : L1 "d" = 0 ∧ 0 < L1 "k"
      · obtain ⟨L3, c3, e3, hc3, hp, hL3⟩ := prS_ok (κ := κ) (s := s) (L := L2) (k := L1 "k")
          (by rw [hL2 "v" (by decide), hv1]) (hL2 "k" (by decide)) hcond.2 (show L1 "k" < kids.length by omega) hvr hkN
        have hc0 : shLC.ev κ s L2 = some 1 := by
          simp [shLC, Exp.ev, OM.Machine.BinOp.eval, hL2 "d" (by decide), hL2 "k" (by decide), hcond.1, hcond.2]
        have hk3 : L3 "k" = L1 "k" := by rw [hL3 "k" (by decide) (by decide), hL2 "k" (by decide)]
        have hd3 : L3 "d" = L1 "d" := by rw [hL3 "d" (by decide) (by decide), hL2 "d" (by decide)]
        by_cases hpr : pr (L1 "k") = true
        · have e4 := evalF_assign_ok (κ := κ) (s := s) (L := L3) (x := "k") (e := "k" - 1) (v := L1 "k" - 1)
            (by simp [Exp.ev, OM.Machine.BinOp.eval, hk3, show 1 ≤ L1 "k" by omega])
          have e5 := evalF_ite_t (κ := κ) (s := s) (L := L3) (c := prE) (f := "d" ::= 1) (v := 1)
            (by rw [hp, if_pos hpr]) one_ne_zero e4
          refine ⟨_, _, evalF_ite_t hc0 one_ne_zero (evalF_seq_ok2 e3 e5), ?_, ⟨?_, ?_⟩, ?_⟩
          · simp [Exp.cost, prE, shLC]; omega
          · simp [OM.Machine.State.upd]; omega
          · intro r h1 h2 h3 h4 h5
            simp only [OM.Machine.State.upd, if_neg h4]; rw [hL3 r h2 h3, hL2 r h1]; exact hF r h1 h2 h3 h4 h5
          · simp [OM.Machine.State.upd, shLStep, hcond, hpr, hd3]
        · have e4 := evalF_assign_ok (κ := κ) (s := s) (L := L3) (x := "d") (e := (1 : Exp)) (v := 1) rfl
          have e5 := evalF_ite_f (κ := κ) (s := s) (L := L3) (c := prE) (t := "k" ::= "k" - 1)
            (by rw [hp, if_neg hpr]) e4
          refine ⟨_, _, evalF_ite_t hc0 one_ne_zero (evalF_seq_ok2 e3 e5), ?_, ⟨?_, ?_⟩, ?_⟩
          · simp [Exp.cost, prE, shLC]; omega
          · simp [OM.Machine.State.upd, hk3]; omega
          · intro r h1 h2 h3 h4 h5
            simp only [OM.Machine.State.upd, if_neg h5]; rw [hL3 r h2 h3, hL2 r h1]; exact hF r h1 h2 h3 h4 h5
          · rw [show shLStep pr (L1 "k", L1 "d") = (L1 "k", 1) by
              simp only [shLStep]; rw [if_neg (by simp [hpr])] ]
            simp [OM.Machine.State.upd, hk3]
      · have e4 := evalF_assign_ok (κ := κ) (s := s) (L := L2) (x := "d") (e := (1 : Exp)) (v := 1) rfl
        have hc0 : shLC.ev κ s L2 = some 0 := by
          by_cases h1 : L1 "d" = 0 <;> by_cases h2 : 0 < L1 "k" <;>
            simp [shLC, Exp.ev, OM.Machine.BinOp.eval, hL2 "d" (by decide), hL2 "k" (by decide), h1, h2] <;>
            exact absurd ⟨h1, h2⟩ hcond
        refine ⟨_, _, evalF_ite_f hc0 e4, ?_, ⟨?_, ?_⟩, ?_⟩
        · simp [Exp.cost, shLC]
        · simp [OM.Machine.State.upd, L2]; omega
        · intro r h1 h2 h3 h4 h5
          simp only [OM.Machine.State.upd, if_neg h5]; rw [hL2 r h1]; exact hF r h1 h2 h3 h4 h5
        · rw [show shLStep pr (L1 "k", L1 "d") = (L1 "k", 1) by
            simp only [shLStep]; rw [if_neg (by tauto)] ]
          simp [OM.Machine.State.upd, L2])
  refine ⟨L', _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 he), ?_, ?_, hF.2⟩
  · simp [Exp.cost] at hc ⊢; omega
  · have := congrArg Prod.fst ha
    simp only at this
    have h0 : (upd (upd L "k" (kids.length - 1)) "d" 0 "k", upd (upd L "k" (kids.length - 1)) "d" 0 "d") =
        (kids.length - 1, 0) := by simp [OM.Machine.State.upd]
    rw [this, h0, foldl_shLStep, List.length_range]

/-- **`startDrain`'s cut**: `k := drainCut (children of v) …` for a node `v` of height `h`. -/
def drainCutS : Stm :=
  "n" ::= .llen .children "v" ;; sumS ;; cutS ;; "k" ::= Exp.max "c" 1 ;;
  .ite (1 <ₑ "h") (shRS ;; .ite ("n" ≤ₑ "k") shLS .skip) .skip

theorem drainCutS_ok {κ : Caps} {s : Core} {L : Loc} {v h : Nat} (hv : L "v" = v) (hh : L "h" = h)
    (hvr : v < κ.lrec .children) (hkN : ∀ e ∈ (s.nodes.getX v).children, e < κ.tbl .N) :
    ∃ L' c, evalF κ drainCutS s L = .ok s L' c ∧ c ≤ 200 + 300 * (s.nodes.getX v).children.length ∧
      L' "k" = drainCut ((s.nodes.getX v).children.map (drainWt s.nodes h))
        (drainPr s.nodes (s.nodes.getX v).children) (decide (h > 1)) ∧
      ∀ r, r ≠ "n" → r ≠ "j" → r ≠ "e" → r ≠ "w" → r ≠ "t" → r ≠ "b" → r ≠ "c" → r ≠ "d" → r ≠ "a" →
        r ≠ "k" → L' r = L r := by
  set kids := (s.nodes.getX v).children
  set pr := drainPr s.nodes kids
  set n := kids.length
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "n") (e := .llen .children "v") (v := n)
    (by simp [Exp.ev, hv, hvr, LK.view, n, kids])
  set L1 := upd L "n" n
  have hL1 : ∀ r, r ≠ "n" → L1 r = L r := fun r h => by simp [L1, OM.Machine.State.upd, h]
  obtain ⟨L2, c2, e2, hc2, ht2, hF2⟩ := sumS_ok (κ := κ) (s := s) (L := L1) (v := v) (h := h)
    (by rw [hL1 "v" (by decide), hv]) (by rw [hL1 "h" (by decide), hh]) (by simp [L1, OM.Machine.State.upd, n, kids])
    hvr hkN
  have hL2 : ∀ r, r ≠ "n" → r ≠ "j" → r ≠ "e" → r ≠ "w" → r ≠ "t" → L2 r = L r :=
    fun r a b c d e => by rw [hF2 r b c d e, hL1 r a]
  have hn2 : L2 "n" = n := by rw [hF2 "n" (by decide) (by decide) (by decide) (by decide)]; simp [L1, OM.Machine.State.upd]
  obtain ⟨L3, c3, e3, hc3, hk3, hF3⟩ := cutS_ok (κ := κ) (s := s) (L := L2) (v := v) (h := h)
    (by rw [hL2 "v" (by decide) (by decide) (by decide) (by decide) (by decide), hv])
    (by rw [hL2 "h" (by decide) (by decide) (by decide) (by decide) (by decide), hh]) hn2 hvr hkN
  rw [ht2] at hk3
  set k0 := Nat.max (cutLen ((kids.map (drainWt s.nodes h)).take (n - 1)) ((kids.map (drainWt s.nodes h)).sum / 2)) 1
  have hn3 : L3 "n" = n := by
    rw [hF3 "n" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hn2]
  have hv3 : L3 "v" = v := by
    rw [hF3 "v" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hL2 "v" (by decide) (by decide) (by decide) (by decide) (by decide), hv]
  have hh3 : L3 "h" = h := by
    rw [hF3 "h" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hL2 "h" (by decide) (by decide) (by decide) (by decide) (by decide), hh]
  have a4 := evalF_assign_ok (κ := κ) (s := s) (L := L3) (x := "k") (e := Exp.max "c" 1) (v := k0)
    (Exp.ev_max κ s L3 (by simp [Exp.ev, hk3]; rfl) rfl)
  set L4 := upd L3 "k" k0
  have hL4 : ∀ r, r ≠ "k" → L4 r = L3 r := fun r h => by simp [L4, OM.Machine.State.upd, h]
  have hF4 : ∀ r, r ≠ "n" → r ≠ "j" → r ≠ "e" → r ≠ "w" → r ≠ "t" → r ≠ "b" → r ≠ "c" → r ≠ "d" → r ≠ "a" →
      r ≠ "k" → L4 r = L r := fun r a b c d e f g hd _ hk => by
    rw [hL4 r hk, hF3 r b c d f g hd, hL2 r a b c d e]
  have hnb : (s.nodes.getX v).children.length = n := rfl
  have hdc : drainCut (kids.map (drainWt s.nodes h)) pr (decide (h > 1)) =
      (if h > 1 then (if shiftR pr n n k0 ≥ n then shiftL pr n (n - 1) else shiftR pr n n k0) else k0) := by
    unfold drainCut
    simp only [List.length_map]
    by_cases h1 : h > 1
    · simp [h1, k0, n]
    · simp [h1, k0, n]
  rw [hdc]
  by_cases h1 : h > 1
  · obtain ⟨L5, c5, e5, hc5, hk5, hF5⟩ := shRS_ok (κ := κ) (s := s) (L := L4) (v := v)
      (by rw [hL4 "v" (by decide), hv3]) (by rw [hL4 "n" (by decide), hn3]) hvr hkN
    have hk5' : L5 "k" = shiftR pr n n k0 := by rw [hk5]; simp [L4, OM.Machine.State.upd]; rfl
    have hn5 : L5 "n" = n := by
      rw [hF5 "n" (by decide) (by decide) (by decide) (by decide) (by decide), hL4 "n" (by decide), hn3]
    have hv5 : L5 "v" = v := by
      rw [hF5 "v" (by decide) (by decide) (by decide) (by decide) (by decide), hL4 "v" (by decide), hv3]
    have hc1 : (1 <ₑ "h" : Exp).ev κ s L4 = some 1 := by
      simp [Exp.ev, OM.Machine.BinOp.eval, hL4 "h" (by decide), hh3, h1]
    by_cases h2 : shiftR pr n n k0 ≥ n
    · obtain ⟨L6, c6, e6, hc6, hk6, hF6⟩ := shLS_ok (κ := κ) (s := s) (L := L5) (v := v) hv5 hn5 hvr hkN
      have hc2' : ("n" ≤ₑ "k" : Exp).ev κ s L5 = some 1 := by
        simp [Exp.ev, OM.Machine.BinOp.eval, hn5, hk5', h2]
      refine ⟨L6, _, evalF_seq_ok2 a1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 a4
        (evalF_ite_t hc1 one_ne_zero (evalF_seq_ok2 e5 (evalF_ite_t hc2' one_ne_zero e6)))))), ?_, ?_, ?_⟩
      · simp [Exp.cost, Exp.max] at hc2 hc3 hc5 hc6 ⊢; omega
      · rw [if_pos h1, if_pos h2]; exact hk6
      · intro r a b c d e f g hd i k
        rw [hF6 r b i c k hd, hF5 r b i c k hd, hF4 r a b c d e f g hd i k]
    · have hc2' : ("n" ≤ₑ "k" : Exp).ev κ s L5 = some 0 := by
        simp [Exp.ev, OM.Machine.BinOp.eval, hn5, hk5']; omega
      refine ⟨L5, _, evalF_seq_ok2 a1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 a4
        (evalF_ite_t hc1 one_ne_zero (evalF_seq_ok2 e5 (evalF_ite_f hc2' evalF_skip)))))), ?_, ?_, ?_⟩
      · simp [Exp.cost, Exp.max] at hc2 hc3 hc5 ⊢; omega
      · rw [if_pos h1, if_neg h2]; exact hk5'
      · intro r a b c d e f g hd i k
        rw [hF5 r b i c k hd, hF4 r a b c d e f g hd i k]
  · have hc1 : (1 <ₑ "h" : Exp).ev κ s L4 = some 0 := by
      simp [Exp.ev, OM.Machine.BinOp.eval, hL4 "h" (by decide), hh3]; omega
    refine ⟨L4, _, evalF_seq_ok2 a1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 a4
      (evalF_ite_f hc1 evalF_skip)))), ?_, ?_, hF4⟩
    · simp [Exp.cost, Exp.max] at hc2 hc3 ⊢; omega
    · rw [if_neg h1]; simp [L4, OM.Machine.State.upd]

end OM.Impl
