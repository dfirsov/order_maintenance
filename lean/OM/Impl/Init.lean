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

end OM.Impl
