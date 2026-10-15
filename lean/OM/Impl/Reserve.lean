import OM.Impl.ChunkStep
import OM.Impl.StartDrain
import OM.Proof.Top.RunIns
import OM.Proof.Cost.Reserve

/-!
# M6: reservation at Level M (`insertAround`, `splitChunkStart`)

`insertAround x y z` puts the new chunks `y`, `z` around `x` in every table holding `x`. Level F
computes all the labels first, then inserts. The program computes the two labels of a table right
before inserting into it: the tables are distinct, so a table is still untouched when its turn
comes, and the labels agree.
-/

namespace OM.Impl

open OM.Model
open OM.Proof.Top
open OM.Machine (Reg BinOp UnOp)

local notation "upd" => OM.Machine.State.upd

/-! ### The tables holding `x` -/

/-- The labels of `y` and `z` in table `T` (Level F's `ly`, `lz`). -/
def cLab (S0 : Core) (x : Nat) (T : Nat) : Nat × Nat :=
  (roomL S0.P.beta (S0.nodes.getX T).table x true, roomL S0.P.beta (S0.nodes.getX T).table x false)

def cStep (S0 : Core) (x y z : Nat) (ns : Array Node) (T : Nat) : Array Node :=
  ns.modify T (aroundF S0 x y z (cLab S0 x) T)

/-- Level F after the insertions into the first `j` tables holding `x`. -/
def cJ (S0 : Core) (x y z j : Nat) : Core :=
  { S0 with nodes := ((S0.cin.getX x).take j).foldl (cStep S0 x y z) S0.nodes }

theorem cStep_getX (S0 : Core) (x y z : Nat) (ns : Array Node) (T u : Nat) (h : u ≠ T) :
    (cStep S0 x y z ns T).getX u = ns.getX u := by
  simp only [cStep, getX_modify']; rw [if_neg (fun e => h e.1)]

theorem cStep_size (S0 : Core) (x y z : Nat) (ns : Array Node) (T : Nat) :
    (cStep S0 x y z ns T).size = ns.size := by simp [cStep]

theorem cJ_getX_notin {S0 : Core} {x y z j u : Nat} (hu : u ∉ (S0.cin.getX x).take j) :
    (cJ S0 x y z j).nodes.getX u = S0.nodes.getX u := by
  simp only [cJ]; rw [fold_modify_getX_notin (cStep_getX S0 x y z) _ _ hu]

theorem cJ_size (S0 : Core) (x y z j : Nat) : (cJ S0 x y z j).nodes.size = S0.nodes.size := by
  simp only [cJ]; rw [fold_modify_size (cStep_size S0 x y z)]

theorem cJ_zero (S0 : Core) (x y z : Nat) : cJ S0 x y z 0 = S0 := by simp [cJ]

def cinsBody : Stm :=
  "T" ::= .lrd .cin false "x" "j" ;;
  roomP.call [.var "T", .var "x", 1] ["a"] ;;
  roomP.call [.var "T", .var "x", 0] ["b"] ;;
  tableInsertP.call [.var "T", .var "x", .var "y", 1, .var "a"] [] ;;
  tableInsertP.call [.var "T", .var "x", .var "z", 0, .var "b"] []

def cinsS : Stm := "m" ::= .llen .cin "x" ;; .loop "j" "m" cinsBody

theorem cinsStep_ok {κ : Caps} {S0 : Core} {L : Loc} {x y z j B : Nat}
    (hnd : (S0.cin.getX x).Nodup) (hyx : y ≠ x)
    (hroom : ∀ T ∈ S0.cin.getX x, RoomOK S0 x T) (hj : j < (S0.cin.getX x).length)
    (hLx : L "x" = x) (hLy : L "y" = y) (hLz : L "z" = z) (hxi : x < κ.lrec .cin)
    (hcapT : ∀ T ∈ S0.cin.getX x, T < κ.lrec .table ∧ T < κ.lrec .side ∧ T < κ.tbl .N ∧
      (S0.nodes.getX T).table.length + 2 ≤ κ.lcap .table ∧ (S0.nodes.getX T).side.length + 2 ≤ κ.lcap .side)
    (hB : ∀ T ∈ S0.cin.getX x, (S0.nodes.getX T).table.length ≤ B ∧ (S0.nodes.getX T).side.length ≤ B) :
    ∃ L' c, evalF κ cinsBody (cJ S0 x y z j) (upd L "j" j) = .ok (cJ S0 x y z (j + 1)) L' c ∧
      c ≤ 1000 + 400 * B ∧ ∀ r, r ≠ "j" → r ≠ "T" → r ≠ "a" → r ≠ "b" → L' r = L r := by
  set tabs := S0.cin.getX x
  set T := tabs[j]
  set S := cJ S0 x y z j
  have hTm : T ∈ tabs := List.getElem_mem hj
  have hTn : T ∉ tabs.take j := nodup_getElem_notin_take hnd hj
  have hTN : T < S0.nodes.size := (hroom T hTm).lt
  have hST : S.nodes.getX T = S0.nodes.getX T := cJ_getX_notin hTn
  have hSx : S.cin.getX x = tabs := rfl
  have hroomS : RoomOK S x T := by unfold RoomOK; rw [hST]; exact hroom T hTm
  obtain ⟨hTt, hTs, hTNc, hcT, hcS⟩ := hcapT T hTm
  obtain ⟨hBt, hBs⟩ := hB T hTm
  -- the table
  set L0 := upd L "j" j
  have e1 := evalF_assign_ok (κ := κ) (s := S) (L := L0) (x := "T") (e := .lrd .cin false "x" "j") (v := T) (by
    simp [Exp.ev, L0, OM.Machine.State.upd, hLx, hxi, LK.view, hSx, hj, T])
  set L1 := upd L0 "T" T
  have hL1 : ∀ r, r ≠ "j" → r ≠ "T" → L1 r = L r := fun r h1 h2 => by simp [L1, L0, OM.Machine.State.upd, h1, h2]
  -- the two labels
  set a := roomL S.P.beta (S.nodes.getX T).table x true
  set b := roomL S.P.beta (S.nodes.getX T).table x false
  have hLx' : L1 "x" = x := by rw [hL1 "x" (by decide) (by decide), hLx]
  obtain ⟨-, La, ca, ea, hla, hca⟩ := roomP_agree κ S
    (OM.Machine.State.setLocs (fun _ => 0) ["t", "e", "bf"] [T, x, 1]) (t := T) (e := x) (before := true)
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd, b2n]) hTt (roomNextTo_run' hroomS true)
  have e2 := evalF_call_ok (q := roomP) (args := [.var "T", .var "x", 1]) (ds := ["a"]) (L := L1)
    (by simp [evList, Exp.ev, L1, L0, OM.Machine.State.upd, hLx]) ea
  set L2 := OM.Machine.State.setLocs L1 ["a"] (roomP.rets.map La)
  obtain ⟨-, Lb, cb, eb, hlb, hcb⟩ := roomP_agree κ S
    (OM.Machine.State.setLocs (fun _ => 0) ["t", "e", "bf"] [T, x, 0]) (t := T) (e := x) (before := false)
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd, b2n]) hTt (roomNextTo_run' hroomS false)
  have e3 := evalF_call_ok (q := roomP) (args := [.var "T", .var "x", 0]) (ds := ["b"]) (L := L2)
    (by simp [evList, Exp.ev, L2, L1, L0, roomP, OM.Machine.State.setLocs, OM.Machine.State.upd, hLx]) eb
  set L3 := OM.Machine.State.setLocs L2 ["b"] (roomP.rets.map Lb)
  have hL3 : ∀ r, r ≠ "j" → r ≠ "T" → r ≠ "a" → r ≠ "b" → L3 r = L r := fun r h1 h2 h3 h4 => by
    simp only [L3, L2, roomP, OM.Machine.State.setLocs, List.map, OM.Machine.State.upd, if_neg h3, if_neg h4]
    exact hL1 r h1 h2
  have hL3T : L3 "T" = T := by simp [L3, L2, L1, roomP, OM.Machine.State.setLocs, OM.Machine.State.upd]
  have hL3a : L3 "a" = a := by simp [L3, L2, roomP, OM.Machine.State.setLocs, OM.Machine.State.upd, hla]; rfl
  have hL3b : L3 "b" = b := by simp [L3, roomP, OM.Machine.State.setLocs, OM.Machine.State.upd, hlb]; rfl
  -- the two insertions
  obtain ⟨A, le, Bs, htab, hA, hside, -, -⟩ := hroomS
  have hins := insertAroundIn_run (s := S) (T := T) (a := a) (b := b) (n2 := z) htab hA hyx hside
  have h1' := tableInsert_run (s := S) (t := T) (new := y) htab hA true a hside
  unfold insertAroundIn at hins
  obtain ⟨u, s1, h1, h2⟩ := run_bind_ok hins
  rw [h1'] at h1
  injection h1 with _ hs1
  subst hs1
  set s1 := { S with nodes := S.nodes.modify T (setTS (insTab A Bs x le y a true) (sideAfter (S.nodes.getX T) x y)) }
  have hTS : T < S.nodes.size := by rw [cJ_size]; exact hTN
  have hs1T : s1.nodes.getX T = setTS (insTab A Bs x le y a true) (sideAfter (S.nodes.getX T) x y) (S.nodes.getX T) := by
    simp only [s1, getX_modify', hTS, and_self, if_true]
  have hlenS : (S.nodes.getX T).table.length = A.length + Bs.length + 1 := by rw [htab]; simp; omega
  obtain ⟨L4', c4, e4', hc4⟩ := tableInsertP_agree κ S
    (OM.Machine.State.setLocs (fun _ => 0) ["t", "e", "w", "bf", "lab"] [T, x, y, 1, a]) (t := T) (e := x)
    (w := y) (before := true) (lab := a)
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd, b2n])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd]) hTt hTs hTNc
    (by rw [hST]; omega) (by rw [hST]; omega) h1'
  have e4 := evalF_call_ok (q := tableInsertP) (args := [.var "T", .var "x", .var "y", 1, .var "a"]) (ds := [])
    (L := L3) (by
      simp [evList, Exp.ev, hL3T, hL3a, hL3 "x" (by decide) (by decide) (by decide) (by decide), hLx,
        hL3 "y" (by decide) (by decide) (by decide) (by decide), hLy]) e4'
  set L4 := OM.Machine.State.setLocs L3 [] (tableInsertP.rets.map L4')
  have hlen1 : (s1.nodes.getX T).table.length = (S.nodes.getX T).table.length + 1 := by
    rw [hs1T, hlenS]; simp [setTS, insTab]; omega
  have hside1 : (s1.nodes.getX T).side.length ≤ (S.nodes.getX T).side.length + 1 := by
    rw [hs1T]; simp only [setTS, sideAfter]; split
    · exact length_assocSet_le' _ _ _
    · omega
  obtain ⟨L5', c5, e5', hc5⟩ := tableInsertP_agree κ s1
    (OM.Machine.State.setLocs (fun _ => 0) ["t", "e", "w", "bf", "lab"] [T, x, z, 0, b]) (t := T) (e := x)
    (w := z) (before := false) (lab := b)
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd, b2n])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd]) hTt hTs hTNc
    (by rw [hlen1, hST]; omega) (by rw [hST] at hside1; omega) h2
  have e5 := evalF_call_ok (q := tableInsertP) (args := [.var "T", .var "x", .var "z", 0, .var "b"]) (ds := [])
    (L := L4) (by
      simp [evList, Exp.ev, L4, OM.Machine.State.setLocs, hL3T, hL3b,
        hL3 "x" (by decide) (by decide) (by decide) (by decide), hLx,
        hL3 "z" (by decide) (by decide) (by decide) (by decide), hLz]) e5'
  have hG : aroundF S0 x y z (cLab S0 x) T =
      setTS (aroundTab A Bs x le y z a b) (sideAround (S.nodes.getX T) x y z) := by
    have ha : a = roomL S0.P.beta (A ++ (x, le) :: Bs) x true := by
      show roomL S.P.beta (S.nodes.getX T).table x true = _; rw [htab]; rfl
    have hb : b = roomL S0.P.beta (A ++ (x, le) :: Bs) x false := by
      show roomL S.P.beta (S.nodes.getX T).table x false = _; rw [htab]; rfl
    unfold aroundF cLab
    rw [← hST, htab, aroundT_eq hA, ha, hb]
  have hfin : { S with nodes := S.nodes.modify T (setTS (aroundTab A Bs x le y z a b)
      (sideAround (S.nodes.getX T) x y z)) } = cJ S0 x y z (j + 1) := by
    have hn : (cJ S0 x y z (j + 1)).nodes = cStep S0 x y z S.nodes T := by
      simp only [cJ, S]; rw [List.take_succ_eq_append_getElem hj, List.foldl_append]; rfl
    rw [show cJ S0 x y z (j + 1) = { S with nodes := (cJ S0 x y z (j + 1)).nodes } from rfl, hn]
    simp only [cStep, hG]
  rw [hfin] at e5
  refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 e4 e5))), ?_, ?_⟩
  · rw [hST] at hca hcb hc4
    rw [hlen1, hST] at hc5
    rw [hST] at hside1
    have : (s1.nodes.getX T).side.length ≤ B + 1 := by omega
    simp only [Exp.cost, costList, List.map, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
      Exp.ofNat_def] at hca hcb hc4 hc5 ⊢
    omega
  · intro r h1 h2 h3 h4
    simp only [OM.Machine.State.setLocs, tableInsertP, List.map]
    exact hL3 r h1 h2 h3 h4

theorem cinsS_ok {κ : Caps} {S0 : Core} {L : Loc} {x y z B : Nat}
    (hnd : (S0.cin.getX x).Nodup) (hyx : y ≠ x) (hroom : ∀ T ∈ S0.cin.getX x, RoomOK S0 x T)
    (hLx : L "x" = x) (hLy : L "y" = y) (hLz : L "z" = z) (hxi : x < κ.lrec .cin)
    (hcapT : ∀ T ∈ S0.cin.getX x, T < κ.lrec .table ∧ T < κ.lrec .side ∧ T < κ.tbl .N ∧
      (S0.nodes.getX T).table.length + 2 ≤ κ.lcap .table ∧ (S0.nodes.getX T).side.length + 2 ≤ κ.lcap .side)
    (hB : ∀ T ∈ S0.cin.getX x, (S0.nodes.getX T).table.length ≤ B ∧ (S0.nodes.getX T).side.length ≤ B) :
    ∃ L' c, evalF κ cinsS S0 L = .ok (cJ S0 x y z (S0.cin.getX x).length) L' c ∧
      c ≤ 5 + (S0.cin.getX x).length * (1001 + 400 * B) ∧
      ∀ r, r ≠ "m" → r ≠ "j" → r ≠ "T" → r ≠ "a" → r ≠ "b" → L' r = L r := by
  set m := (S0.cin.getX x).length
  have a1 := evalF_assign_ok (κ := κ) (s := S0) (L := L) (x := "m") (e := .llen .cin "x") (v := m)
    (by simp [Exp.ev, hLx, hxi, LK.view, m])
  set L1 := upd L "m" m
  obtain ⟨S', L', c, he, hc, hs', hF⟩ := evalF_loop (κ := κ) (x := "j") (n := .var "m") (b := cinsBody)
    (s := S0) (L := L1) (N := m) (by simp [Exp.ev, L1, OM.Machine.State.upd])
    (fun j S L' => S = cJ S0 x y z j ∧
      ∀ r, r ≠ "m" → r ≠ "j" → r ≠ "T" → r ≠ "a" → r ≠ "b" → L' r = L r) (1000 + 400 * B)
    ⟨by rw [cJ_zero], fun r h1 _ _ _ _ => by simp [L1, OM.Machine.State.upd, h1]⟩
    (by
      intro j hj S1 L2 ⟨hS1, hF2⟩
      subst hS1
      obtain ⟨L3, c3, e3, hc3, hF3⟩ := cinsStep_ok (κ := κ) (L := L2) (B := B) hnd hyx hroom hj
        (by rw [hF2 "x" (by decide) (by decide) (by decide) (by decide) (by decide), hLx])
        (by rw [hF2 "y" (by decide) (by decide) (by decide) (by decide) (by decide), hLy])
        (by rw [hF2 "z" (by decide) (by decide) (by decide) (by decide) (by decide), hLz]) hxi hcapT hB
      exact ⟨_, L3, c3, e3, hc3, rfl, fun r h1 h2 h3 h4 h5 => (hF3 r h2 h3 h4 h5).trans (hF2 r h1 h2 h3 h4 h5)⟩)
  rw [hs'] at he
  refine ⟨L', _, evalF_seq_ok2 a1 he, ?_, hF⟩
  simp only [Exp.cost] at hc ⊢
  have e : m * (1 + (1000 + 400 * B)) = m * (1001 + 400 * B) := by ring
  rw [e] at hc; omega

/-! ### `joinChunk` -/

/-- `joinChunk (cin x) lp w` (locals `w x lp`). The list of `w` is cleared first, so that the copy
starts from a row that exists. -/
def joinCS : Stm := .rowReset "w" ;; .lclear .cin "w" ;; "a" ::= .var "x" ;; copyS .cin ;; .wr (.a .lpar) "w" "lp"

theorem joinCS_ok {κ : Caps} {s : Core} {L : Loc} {w x lp : Nat} (hw : L "w" = w) (hx : L "x" = x)
    (hlp : L "lp" = lp) (hwx : w ≠ x) (hwC : w < κ.tbl .C) (hz : rowZero κ s w) (hnp : notPrep s w)
    (hH : s.P.H + 1 ≤ κ.pw) (hwi : w < κ.lrec .cin) (hxi : x < κ.lrec .cin)
    (hcap : (s.cin.getX x).length ≤ κ.lcap .cin) (hwa : w < κ.arr .lpar) :
    ∃ L' c, evalF κ joinCS s L = .ok (joinS s (s.cin.getX x) lp w) L' c ∧
      c ≤ 20 + 40 * (s.cin.getX x).length ∧ ∀ r, r ≠ "a" → r ≠ "n" → r ≠ "j" → L' r = L r := by
  set s1 : Core := { s with path := s.path.setX w (Array.replicate (s.P.H + 1) NIL) }
  have e1 : evalF κ (.rowReset "w") s L = .ok s1 L 1 := by
    simp [evalF, Exp.ev, hw, hwC, hz, hnp, hH, s1]
  set s2 := LK.put s1 w [] .cin
  have e2 : evalF κ (.lclear .cin "w") s1 L = .ok s2 L 3 := by
    simp [evalF, Exp.ev, hw, LK.set, LK.recOk, LK.valid, hwi, s2, Exp.cost]
  have a3 := evalF_assign_ok (κ := κ) (s := s2) (L := L) (x := "a") (e := .var "x") (v := x) (by simp [Exp.ev, hx])
  set L3 := upd L "a" x
  have hv2w : LK.view s2 w .cin = [] := by
    rw [LK.view_put (by rfl) (by rfl)]; simp
  have hv2x : LK.view s2 x .cin = (s.cin.getX x).map fun e => (e, 0) := by
    rw [LK.view_put (by rfl) (by rfl)]; simp [Ne.symm hwx, LK.view, s1]
  have hid : LK.idOk s2 w .cin := by
    simp only [LK.idOk, s2, LK.put, size_setX']; omega
  obtain ⟨L4, c4, e4, hc4, hF4⟩ := copyS_ok (κ := κ) (k := .cin) (s := s2) (L := L3) (a := x) (w := w)
    (by simp [L3, OM.Machine.State.upd]) (by simp [L3, OM.Machine.State.upd, hw]) hwx hid (by rfl) hxi hwi
    (by rw [hv2w, hv2x]; simpa using hcap)
  rw [hv2w, hv2x, List.nil_append, LK.put_put] at e4
  have h4w : L4 "w" = w := by rw [hF4 "w" (by decide) (by decide)]; simp [L3, OM.Machine.State.upd, hw]
  have h4lp : L4 "lp" = lp := by rw [hF4 "lp" (by decide) (by decide)]; simp [L3, OM.Machine.State.upd, hlp]
  have e5 : evalF κ (.wr (.a .lpar) "w" "lp") (LK.put s1 w ((s.cin.getX x).map fun e => (e, 0)) .cin) L4 =
      .ok (joinS s (s.cin.getX x) lp w) L4 3 := by
    simp [evalF, Exp.ev, h4w, h4lp, Fld.set, hwa, AF.set, AF.get, LK.put, s1, joinS, Exp.cost]
    congr 1; induction s.cin.getX x <;> simp_all
  refine ⟨L4, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 a3 (evalF_seq_ok2 e4 e5))), ?_, ?_⟩
  · rw [hv2x, List.length_map] at hc4; simp only [Exp.cost]; omega
  · intro r h1 h2 h3
    rw [hF4 r h2 h3]; simp [L3, OM.Machine.State.upd, h1]

end OM.Impl
