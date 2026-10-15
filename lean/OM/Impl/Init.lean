import OM.Impl.Background

/-!
# M6: building a core at Level M (`initCore`, `initStep`, `prepareStep`)

A new core lives in freshly allocated machine arrays, which read 0 everywhere: the core
`freshC P`, with every array empty. `initStateS` pushes and writes it into Level F's
`initState P`. The top structure is then built one level per `initStep`; `resetTop` runs only on
the fresh top structure, where it changes nothing.
-/

namespace OM.Impl

open OM.Model
open OM.Proof.Top
open OM.Machine (Reg BinOp UnOp)

local notation "upd" => OM.Machine.State.upd

/-- A core in fresh memory: every array empty (all cells read 0). -/
def freshC (P : Params) : Core := { P := P, E := #[], Gs := #[], C := #[], nodes := #[] }

def initEltS : Stm :=
  .push .E "t" ;; .push .E "t" ;;
  .weF .grp 1 1 ;; .weF .lab 1 (.bin .shl 1 (.prm .Be - 1)) ;; .weF .dead 1 1
def initGrpS : Stm :=
  .push .G "t" ;; .push .G "t" ;;
  .wgF .chk 1 1 ;; .wgF .lab 1 (.bin .shl 1 (.prm .Bg - 1)) ;; .wgF .first 1 1 ;; .wgF .last 1 1 ;;
  .wgF .size 1 1
def initChkS : Stm :=
  .push .C "t" ;; .push .C "t" ;; .wcF .first 1 1 ;; .wcF .last 1 1 ;; .wcF .size 1 1
def initScS : Stm :=
  .push .N "t" ;; .wr (.s .firstGroup) 0 1 ;; .wr (.s .firstChunk) 0 1 ;; .wr (.s .head) 0 1 ;; .wr (.s .tail) 0 1 ;;
  .wr (.s .count) 0 1
/-- `set (initState P)`, from fresh memory. -/
def initStateS : Stm := initEltS ;; initGrpS ;; initChkS ;; initScS

theorem evalF_push_ok {κ : Caps} {s : Core} {L : Loc} {t : Tbl} {x : Reg} (h : t.size s < κ.tbl t) :
    evalF κ (.push t x) s L = .ok (t.push s) (upd L x (t.size s)) pushCost := by
  simp [evalF, h]

/-- The stages of `initStateS` on fresh memory. -/
def iE (P : Params) : Core :=
  { freshC P with E := #[default, { grp := 1, lab := 1 <<< (P.B_e - 1), h := 0, live := false }] }
def iG (P : Params) : Core :=
  { iE P with Gs := #[default, { chk := 1, lab := 1 <<< (P.B_g - 1), first := 1, last := 1, size := 1 }] }
def iC (P : Params) : Core := { iG P with C := #[default, { first := 1, last := 1, size := 1 }] }

theorem initEltS_ok {κ : Caps} {P : Params} {L : Loc} (hBe : 1 ≤ P.B_e) (hE : 2 ≤ κ.tbl .E) :
    ∃ L' c, evalF κ initEltS (freshC P) L = .ok (iE P) L' c ∧ c ≤ 60 := by
  have p1 := evalF_push_ok (κ := κ) (s := freshC P) (L := L) (t := .E) (x := "t") (by simp [Tbl.size, freshC]; omega)
  have p2 := evalF_push_ok (κ := κ) (s := Tbl.push (freshC P) .E) (L := upd L "t" 0) (t := .E) (x := "t")
    (by simp [Tbl.size, Tbl.push, freshC]; omega)
  set s2 := Tbl.push (Tbl.push (freshC P) .E) .E
  have hs2 : s2.E.size = 2 := by simp [s2, Tbl.push, freshC]
  have w1 := evalF_wrE_ok (κ := κ) (s := s2) (L := upd (upd L "t" 0) "t" 1) (k := .grp) (i := (1 : Exp)) (e := (1 : Exp))
    (j := 1) (w := 1) rfl rfl (by omega) (by omega) rfl
  set s3 : Core := { s2 with E := s2.E.modify 1 (EF.set · 1 .grp) }
  have w2 := evalF_wrE_ok (κ := κ) (s := s3) (L := upd (upd L "t" 0) "t" 1) (k := .lab) (i := (1 : Exp))
    (e := .bin .shl 1 (.prm .Be - 1)) (j := 1) (w := 1 <<< (P.B_e - 1)) rfl
    (by simp [Exp.ev, OM.Machine.BinOp.eval, PF.get, s3, s2, Tbl.push, freshC, hBe, Nat.shiftLeft_eq])
    (by simp [s3, hs2]) (by omega) rfl
  set s4 : Core := { s3 with E := s3.E.modify 1 (EF.set · (1 <<< (P.B_e - 1)) .lab) }
  have w3 := evalF_wrE_ok (κ := κ) (s := s4) (L := upd (upd L "t" 0) "t" 1) (k := .dead) (i := (1 : Exp))
    (e := (1 : Exp)) (j := 1) (w := 1) rfl rfl (by simp [s4, s3, hs2]) (by omega) rfl
  have hfin : ({ s4 with E := s4.E.modify 1 (EF.set · 1 .dead) } : Core) = iE P := by
    simp only [s4, s3, s2, iE, freshC, Tbl.push]
    congr 1
  refine ⟨_, _, evalF_seq_ok2 p1 (evalF_seq_ok2 p2 (evalF_seq_ok2 (by simp only [Stm.weF]; exact w1)
    (evalF_seq_ok2 (by simp only [Stm.weF]; exact w2) (by simp only [Stm.weF]; rw [← hfin]; exact w3)))), ?_⟩
  simp [pushCost, Exp.cost]

theorem initGrpS_ok {κ : Caps} {P : Params} {L : Loc} (hBg : 1 ≤ P.B_g) (hG : 2 ≤ κ.tbl .G) :
    ∃ L' c, evalF κ initGrpS (iE P) L = .ok (iG P) L' c ∧ c ≤ 80 := by
  have p1 := evalF_push_ok (κ := κ) (s := iE P) (L := L) (t := .G) (x := "t") (by simp [Tbl.size, iE, freshC]; omega)
  have p2 := evalF_push_ok (κ := κ) (s := Tbl.push (iE P) .G) (L := upd L "t" 0) (t := .G) (x := "t")
    (by simp [Tbl.size, Tbl.push, iE, freshC]; omega)
  set s2 := Tbl.push (Tbl.push (iE P) .G) .G
  have hs2 : s2.Gs.size = 2 := by simp [s2, Tbl.push, iE, freshC]
  set L2 := upd (upd L "t" 0) "t" 1
  have w1 := evalF_wrG_ok (κ := κ) (s := s2) (L := L2) (k := .chk) (i := (1 : Exp)) (e := (1 : Exp))
    (j := 1) (w := 1) rfl rfl (by omega) (by omega) rfl
  set s3 : Core := { s2 with Gs := s2.Gs.modify 1 (GF.set · 1 .chk) }
  have w2 := evalF_wrG_ok (κ := κ) (s := s3) (L := L2) (k := .lab) (i := (1 : Exp))
    (e := .bin .shl 1 (.prm .Bg - 1)) (j := 1) (w := 1 <<< (P.B_g - 1)) rfl
    (by simp [Exp.ev, OM.Machine.BinOp.eval, PF.get, s3, s2, Tbl.push, iE, freshC, hBg, Nat.shiftLeft_eq])
    (by simp [s3, hs2]) (by omega) rfl
  set s4 : Core := { s3 with Gs := s3.Gs.modify 1 (GF.set · (1 <<< (P.B_g - 1)) .lab) }
  have w3 := evalF_wrG_ok (κ := κ) (s := s4) (L := L2) (k := .first) (i := (1 : Exp)) (e := (1 : Exp))
    (j := 1) (w := 1) rfl rfl (by simp [s4, s3, hs2]) (by omega) rfl
  set s5 : Core := { s4 with Gs := s4.Gs.modify 1 (GF.set · 1 .first) }
  have w4 := evalF_wrG_ok (κ := κ) (s := s5) (L := L2) (k := .last) (i := (1 : Exp)) (e := (1 : Exp))
    (j := 1) (w := 1) rfl rfl (by simp [s5, s4, s3, hs2]) (by omega) rfl
  set s6 : Core := { s5 with Gs := s5.Gs.modify 1 (GF.set · 1 .last) }
  have w5 := evalF_wrG_ok (κ := κ) (s := s6) (L := L2) (k := .size) (i := (1 : Exp)) (e := (1 : Exp))
    (j := 1) (w := 1) rfl rfl (by simp [s6, s5, s4, s3, hs2]) (by omega) rfl
  have hfin : ({ s6 with Gs := s6.Gs.modify 1 (GF.set · 1 .size) } : Core) = iG P := by
    simp only [s6, s5, s4, s3, s2, iG, iE, freshC, Tbl.push]
    congr 1
  refine ⟨_, _, evalF_seq_ok2 p1 (evalF_seq_ok2 p2 (evalF_seq_ok2 (by simp only [Stm.wgF]; exact w1)
    (evalF_seq_ok2 (by simp only [Stm.wgF]; exact w2) (evalF_seq_ok2 (by simp only [Stm.wgF]; exact w3)
    (evalF_seq_ok2 (by simp only [Stm.wgF]; exact w4) (by simp only [Stm.wgF]; rw [← hfin]; exact w5)))))), ?_⟩
  simp [pushCost, Exp.cost]

theorem initChkS_ok {κ : Caps} {P : Params} {L : Loc} (hC : 2 ≤ κ.tbl .C) :
    ∃ L' c, evalF κ initChkS (iG P) L = .ok (iC P) L' c ∧ c ≤ 60 := by
  have p1 := evalF_push_ok (κ := κ) (s := iG P) (L := L) (t := .C) (x := "t")
    (by simp [Tbl.size, iG, iE, freshC]; omega)
  have p2 := evalF_push_ok (κ := κ) (s := Tbl.push (iG P) .C) (L := upd L "t" 0) (t := .C) (x := "t")
    (by simp [Tbl.size, Tbl.push, iG, iE, freshC]; omega)
  set s2 := Tbl.push (Tbl.push (iG P) .C) .C
  have hs2 : s2.C.size = 2 := by simp [s2, Tbl.push, iG, iE, freshC]
  set L2 := upd (upd L "t" 0) "t" 1
  have w1 := evalF_wrC_ok (κ := κ) (s := s2) (L := L2) (k := .first) (i := (1 : Exp)) (e := (1 : Exp))
    (j := 1) (w := 1) rfl rfl (by omega) (by omega) rfl
  set s3 : Core := { s2 with C := s2.C.modify 1 (CF.set · 1 .first) }
  have w2 := evalF_wrC_ok (κ := κ) (s := s3) (L := L2) (k := .last) (i := (1 : Exp)) (e := (1 : Exp))
    (j := 1) (w := 1) rfl rfl (by simp [s3, hs2]) (by omega) rfl
  set s4 : Core := { s3 with C := s3.C.modify 1 (CF.set · 1 .last) }
  have w3 := evalF_wrC_ok (κ := κ) (s := s4) (L := L2) (k := .size) (i := (1 : Exp)) (e := (1 : Exp))
    (j := 1) (w := 1) rfl rfl (by simp [s4, s3, hs2]) (by omega) rfl
  have hfin : ({ s4 with C := s4.C.modify 1 (CF.set · 1 .size) } : Core) = iC P := by
    simp only [s4, s3, s2, iC, iG, iE, freshC, Tbl.push]
    congr 1
  refine ⟨_, _, evalF_seq_ok2 p1 (evalF_seq_ok2 p2 (evalF_seq_ok2 (by simp only [Stm.wcF]; exact w1)
    (evalF_seq_ok2 (by simp only [Stm.wcF]; exact w2) (by simp only [Stm.wcF]; rw [← hfin]; exact w3)))), ?_⟩
  simp [pushCost, Exp.cost]

theorem initScS_ok {κ : Caps} {P : Params} {L : Loc} (hN : 1 ≤ κ.tbl .N) :
    ∃ L' c, evalF κ initScS (iC P) L = .ok (initState P) L' c ∧ c ≤ 40 := by
  have p1 := evalF_push_ok (κ := κ) (s := iC P) (L := L) (t := .N) (x := "t")
    (by simp [Tbl.size, iC, iG, iE, freshC]; omega)
  set L1 := upd L "t" (Tbl.size (iC P) .N)
  set t0 := Tbl.push (iC P) .N
  have hst : SF.set (SF.set (SF.set (SF.set (SF.set t0 1 .firstGroup) 1 .firstChunk) 1 .head) 1 .tail) 1 .count =
      initState P := rfl
  have e2 := evalF_seq_ok2 (evalF_wrS_ok (κ := κ) (s := t0) (L := L1) (k := .firstGroup) (e := (1 : Exp)) (w := 1) rfl rfl)
    (evalF_seq_ok2 (evalF_wrS_ok (k := .firstChunk) (e := (1 : Exp)) (w := 1) rfl rfl)
    (evalF_seq_ok2 (evalF_wrS_ok (k := .head) (e := (1 : Exp)) (w := 1) rfl rfl)
    (evalF_seq_ok2 (evalF_wrS_ok (k := .tail) (e := (1 : Exp)) (w := 1) rfl rfl)
      (evalF_wrS_ok (k := .count) (e := (1 : Exp)) (w := 1) rfl rfl))))
  rw [hst] at e2
  exact ⟨_, _, evalF_seq_ok2 p1 e2, by simp [pushCost, Exp.cost]⟩

theorem initStateS_ok {κ : Caps} {P : Params} {L : Loc} (hBe : 1 ≤ P.B_e) (hBg : 1 ≤ P.B_g)
    (hE : 2 ≤ κ.tbl .E) (hG : 2 ≤ κ.tbl .G) (hC : 2 ≤ κ.tbl .C) (hN : 1 ≤ κ.tbl .N) :
    ∃ L' c, evalF κ initStateS (freshC P) L = .ok (initState P) L' c ∧ c ≤ 300 := by
  obtain ⟨L1, c1, e1, hc1⟩ := initEltS_ok (κ := κ) (L := L) hBe hE
  obtain ⟨L2, c2, e2, hc2⟩ := initGrpS_ok (κ := κ) (L := L1) hBg hG
  obtain ⟨L3, c3, e3, hc3⟩ := initChkS_ok (κ := κ) (L := L2) (P := P) hC
  obtain ⟨L4, c4, e4, hc4⟩ := initScS_ok (κ := κ) (L := L3) (P := P) hN
  exact ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 e4)), by omega⟩

/-! ### `initStep` -/

def isLink : Stm :=
  .ite ("h" =ₑ 1) (.lclear .cin "c" ;; .lgrow .cin "c" "v" 0 ;; .wr (.a .lpar) "c" "v")
    (.lclear .inTab "bl" ;; .lgrow .inTab "bl" "v" 0 ;; .wr (.n .livePar) "bl" "v")
def isNode : Stm :=
  .push .N "v" ;; .wr (.n .height) "v" "h" ;; .lgrow .children "v" "bl" 0 ;; .lgrow .table "v" "bl" "ctr" ;;
  .wr (.n .weight) "v" 1 ;; .wr (.n .first) "v" "c" ;; .wr (.n .last) "v" "c"
def isBuild : Stm :=
  "ctr" ::= .bin .shl 1 (.prm .beta - 1) ;; isNode ;; isLink ;;
  .prepSet ("h" + 1) "v" ("tg" + "ctr" * .bin .shl 1 (("h" - 1) * .prm .beta)) ;;
  .prepPath "h" "v" ;; "done" ::= 0
def isFinish : Stm := .wcF .tag "c" "tg" ;; .prepCommit ;; "done" ::= 1
def isPre : Stm :=
  "c" ::= .opt .prepChunk ;; "h" ::= .opt .prepH ;; "bl" ::= .opt .prepBelow ;; "tg" ::= .opt .prepTag ;;
  .ite ("h" =ₑ 1) (.lclear .cin "c") .skip

/-- `done := initStep`. -/
def initStepP : Proc where
  name := "initStep"
  params := []
  rets := ["done"]
  body := .ite (.opt .prepOn) (isPre ;; .ite ("h" ≤ₑ .prm .H) isBuild isFinish) ("done" ::= 1)

theorem initStepP_none {κ : Caps} {s : Core} {L : Loc} (hp : s.prep = none) :
    ∃ L' c, evalF κ initStepP.body s L = .ok s L' c ∧ L' "done" = 1 ∧ c ≤ 10 := by
  refine ⟨_, _, evalF_ite_f (by simp [Exp.ev, OF.get, hp, b2n]) (evalF_assign_ok (v := 1) rfl),
    by simp [OM.Machine.State.upd], by simp [Exp.cost]⟩

/-- The locals after the reads. -/
def isL (L : Loc) (pr : Prep) : Loc :=
  upd (upd (upd (upd L "c" pr.chunk) "h" pr.h) "bl" pr.below) "tg" pr.tag

theorem isPre_ok {κ : Caps} {s : Core} {L : Loc} {pr : Prep} (hp : s.prep = some pr)
    (hc : pr.h = 1 → pr.chunk < κ.lrec .cin) :
    evalF κ isPre s L = .ok (if pr.h = 1 then { s with cin := s.cin.setX pr.chunk [] } else s) (isL L pr)
      (if pr.h = 1 then 19 else 17) := by
  have b1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "c") (e := .opt .prepChunk) (v := pr.chunk)
    (by simp [Exp.ev, OF.get, hp])
  have b2 := evalF_assign_ok (κ := κ) (s := s) (L := upd L "c" pr.chunk) (x := "h") (e := .opt .prepH) (v := pr.h)
    (by simp [Exp.ev, OF.get, hp])
  have b3 := evalF_assign_ok (κ := κ) (s := s) (L := upd (upd L "c" pr.chunk) "h" pr.h) (x := "bl")
    (e := .opt .prepBelow) (v := pr.below) (by simp [Exp.ev, OF.get, hp])
  have b4 := evalF_assign_ok (κ := κ) (s := s) (L := upd (upd (upd L "c" pr.chunk) "h" pr.h) "bl" pr.below)
    (x := "tg") (e := .opt .prepTag) (v := pr.tag) (by simp [Exp.ev, OF.get, hp])
  have hr := evalF_seq_ok2 b1 (evalF_seq_ok2 b2 (evalF_seq_ok2 b3 b4))
  by_cases h1 : pr.h = 1
  · have e5 : evalF κ (.ite ("h" =ₑ 1) (.lclear .cin "c") .skip) s (isL L pr) =
        .ok { s with cin := s.cin.setX pr.chunk [] } (isL L pr) 7 := by
      simp [evalF, Exp.ev, isL, OM.Machine.State.upd, h1, OM.Machine.BinOp.eval, LK.set, LK.recOk, LK.valid,
        hc h1, LK.put, Exp.cost, Res.addCost]
    rw [if_pos h1, if_pos h1]
    simp only [isPre]; exact evalF_seq_ok2 b1 (evalF_seq_ok2 b2 (evalF_seq_ok2 b3 (evalF_seq_ok2 b4 e5)))
  · have e5 : evalF κ (.ite ("h" =ₑ 1) (.lclear .cin "c") .skip) s (isL L pr) = .ok s (isL L pr) 5 := by
      simp [evalF, Exp.ev, isL, OM.Machine.State.upd, h1, OM.Machine.BinOp.eval, Exp.cost, Res.addCost]
    rw [if_neg h1, if_neg h1]
    simp only [isPre]; exact evalF_seq_ok2 b1 (evalF_seq_ok2 b2 (evalF_seq_ok2 b3 (evalF_seq_ok2 b4 e5)))

/-- The state after the last step (`initStep_last`). -/
def isLastS (s : Core) (pr : Prep) : Core :=
  { s with path := s.path.setX pr.chunk pr.path, C := s.C.modify pr.chunk (fun C => { C with tag := pr.tag }), prep := none }

theorem initStepP_last {κ : Caps} {s : Core} {L : Loc} {pr : Prep} (hp : s.prep = some pr) (h1 : pr.h ≠ 1)
    (hH : s.P.H < pr.h) (hcs : pr.chunk < s.C.size) (hcC : pr.chunk < κ.tbl .C) :
    ∃ L' c, evalF κ initStepP.body s L = .ok (isLastS s pr) L' c ∧ L' "done" = 1 ∧ c ≤ 80 := by
  have e1 := isPre_ok (κ := κ) (L := L) hp (fun h => absurd h h1)
  rw [if_neg h1, if_neg h1] at e1
  set L1 := isL L pr
  have w2 := evalF_wrC_ok (κ := κ) (s := s) (L := L1) (k := .tag) (i := .var "c") (e := .var "tg") (j := pr.chunk)
    (w := pr.tag) (by simp [Exp.ev, L1, isL, OM.Machine.State.upd]) (by simp [Exp.ev, L1, isL, OM.Machine.State.upd])
    hcs hcC rfl
  set s2 : Core := { s with C := s.C.modify pr.chunk (CF.set · pr.tag .tag) }
  have e3 : evalF κ .prepCommit s2 L1 = .ok (isLastS s pr) L1 15 := by
    simp [evalF, s2, hp]; rfl
  have e4 := evalF_assign_ok (κ := κ) (s := isLastS s pr) (L := L1) (x := "done") (e := (1 : Exp)) (v := 1) rfl
  have hc : ("h" ≤ₑ .prm .H : Exp).ev κ s L1 = some 0 := by
    simp [Exp.ev, L1, isL, OM.Machine.State.upd, OM.Machine.BinOp.eval, PF.get]; omega
  refine ⟨_, _, evalF_ite_t (v := 1) (by simp [Exp.ev, OF.get, hp, b2n]) one_ne_zero
    (evalF_seq_ok2 e1 (evalF_ite_f hc (evalF_seq_ok2 (by simp only [Stm.wcF]; exact w2) (evalF_seq_ok2 e3 e4)))),
    by simp [OM.Machine.State.upd], by simp [Exp.cost]⟩

theorem evalF_lgrow_ok {κ : Caps} {s s' : Core} {L : Loc} {k : LK} {i a b : Exp} {x va vb : Nat}
    (hi : i.ev κ s L = some x) (ha : a.ev κ s L = some va) (hb : b.ev κ s L = some vb)
    (hs : k.set κ s x (k.view s x ++ [(va, vb)]) = some s') :
    evalF κ (.lgrow k i a b) s L = .ok s' L (14 + 6 * i.cost + a.cost + b.cost) := by
  simp [evalF, hi, ha, hb, hs]

/-- Level F's new chain node, as `initStep` makes it (`chainNew`). -/
def nodeS (S : Core) (pr : Prep) : Core :=
  { S with nodes := (S.nodes.push { height := pr.h }).modify S.nodes.size (chainNew S.P pr) }

/-- The locals after the reads and the label `ctr`. -/
def isL2 (L : Loc) (pr : Prep) (β : Nat) : Loc := upd (isL L pr) "ctr" (1 <<< (β - 1))

theorem isNode_ok {κ : Caps} {S : Core} {L : Loc} {pr : Prep} (hN : S.nodes.size < κ.tbl .N)
    (hrc : S.nodes.size < κ.lrec .children) (hrt : S.nodes.size < κ.lrec .table)
    (hcc : 1 ≤ κ.lcap .children) (hct : 1 ≤ κ.lcap .table) :
    ∃ c, evalF κ isNode S (isL2 L pr S.P.beta) =
      .ok (nodeS S pr) (upd (isL2 L pr S.P.beta) "v" S.nodes.size) c ∧ c ≤ 120 := by
  set v := S.nodes.size
  set L0 := isL2 L pr S.P.beta
  set L1 := upd L0 "v" v
  have h1v : L1 "v" = v := by simp [L1, OM.Machine.State.upd]
  have h1h : L1 "h" = pr.h := by simp [L1, L0, isL2, isL, OM.Machine.State.upd]
  have h1bl : L1 "bl" = pr.below := by simp [L1, L0, isL2, isL, OM.Machine.State.upd]
  have h1c : L1 "c" = pr.chunk := by simp [L1, L0, isL2, isL, OM.Machine.State.upd]
  have h1ctr : L1 "ctr" = 1 <<< (S.P.beta - 1) := by simp [L1, L0, isL2, OM.Machine.State.upd]
  have p1 := evalF_push_ok (κ := κ) (s := S) (L := L0) (t := .N) (x := "v") (by simpa [Tbl.size] using hN)
  set S1 := Tbl.push S .N
  have hS1 : S1.nodes.size = v + 1 := by simp [S1, Tbl.push, v]
  have w2 := evalF_wrN_ok (κ := κ) (s := S1) (L := L1) (k := .height) (i := .var "v") (e := .var "h") (j := v)
    (w := pr.h) (by simp [Exp.ev, h1v]) (by simp [Exp.ev, h1h]) (by omega) hN rfl
  set S2 : Core := { S1 with nodes := S1.nodes.modify v (NF.set · pr.h .height) }
  have hS2v : S2.nodes.getX v = { height := pr.h } := by
    simp only [S2, S1, Tbl.push, v]; rw [Array.modify_push_size, getX_push', if_pos rfl]; rfl
  have hS2n : S2.nodes.size = v + 1 := by simp [S2, hS1]
  set S3 := LK.put S2 v (LK.view S2 v .children ++ [(pr.below, 0)]) .children
  have e3 := evalF_lgrow_ok (κ := κ) (s := S2) (s' := S3) (L := L1) (k := .children) (i := .var "v") (a := .var "bl")
    (b := (0 : Exp)) (x := v) (va := pr.below) (vb := 0) (by simp [Exp.ev, h1v]) (by simp [Exp.ev, h1bl]) rfl
    (by simp [LK.set, LK.recOk, LK.valid, LK.view, hS2v, hS2n, hrc, hcc, S3])
  have hS3v : S3.nodes.getX v = { height := pr.h, children := [pr.below] } := by
    simp only [S3, LK.put, LK.view, hS2v, getX_modify', hS2n, show v < v + 1 by omega, and_self, if_true]; simp
  have hS3n : S3.nodes.size = v + 1 := by simp [S3, hS2n]
  set S4 := LK.put S3 v (LK.view S3 v .table ++ [(pr.below, 1 <<< (S.P.beta - 1))]) .table
  have e4 := evalF_lgrow_ok (κ := κ) (s := S3) (s' := S4) (L := L1) (k := .table) (i := .var "v") (a := .var "bl")
    (b := .var "ctr") (x := v) (va := pr.below) (vb := 1 <<< (S.P.beta - 1)) (by simp [Exp.ev, h1v])
    (by simp [Exp.ev, h1bl]) (by simp [Exp.ev, h1ctr])
    (by simp [LK.set, LK.recOk, LK.valid, LK.view, hS3v, hS3n, hrt, hct, S4])
  have hS4n : S4.nodes.size = v + 1 := by simp [S4, hS3n]
  have w5 := evalF_wrN_ok (κ := κ) (s := S4) (L := L1) (k := .weight) (i := .var "v") (e := (1 : Exp)) (j := v)
    (w := 1) (by simp [Exp.ev, h1v]) rfl (by omega) hN rfl
  set S5 : Core := { S4 with nodes := S4.nodes.modify v (NF.set · 1 .weight) }
  have w6 := evalF_wrN_ok (κ := κ) (s := S5) (L := L1) (k := .first) (i := .var "v") (e := .var "c") (j := v)
    (w := pr.chunk) (by simp [Exp.ev, h1v]) (by simp [Exp.ev, h1c]) (by simp [S5, hS4n]) hN rfl
  set S6 : Core := { S5 with nodes := S5.nodes.modify v (NF.set · pr.chunk .first) }
  have w7 := evalF_wrN_ok (κ := κ) (s := S6) (L := L1) (k := .last) (i := .var "v") (e := .var "c") (j := v)
    (w := pr.chunk) (by simp [Exp.ev, h1v]) (by simp [Exp.ev, h1c]) (by simp [S6, S5, hS4n]) hN rfl
  have hfin : ({ S6 with nodes := S6.nodes.modify v (NF.set · pr.chunk .last) } : Core) = nodeS S pr := by
    have hv2 : LK.view S2 v .children = [] := by simp [LK.view, hS2v]
    have hv3 : LK.view S3 v .table = [] := by simp [LK.view, hS3v]
    have hS3' : S3 = LK.put S2 v [(pr.below, 0)] .children := by simp only [S3, hv2, List.nil_append]
    have hS4' : S4 = LK.put S3 v [(pr.below, 1 <<< (S.P.beta - 1))] .table := by simp only [S4, hv3, List.nil_append]
    simp only [S6, S5, hS4', hS3', S2, S1, nodeS, Tbl.push, LK.put, Array.modify_modify_same, v]
    rw [Array.modify_push_size, Array.modify_push_size]
    rfl
  rw [hfin] at w7
  exact ⟨_, evalF_seq_ok2 p1 (evalF_seq_ok2 w2 (evalF_seq_ok2 e3 (evalF_seq_ok2 e4 (evalF_seq_ok2 w5
    (evalF_seq_ok2 w6 w7))))), by simp [pushCost, Exp.cost]⟩

end OM.Impl
