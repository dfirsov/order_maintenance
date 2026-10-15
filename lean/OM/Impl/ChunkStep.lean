import OM.Impl.GroupStep
import OM.Proof.Cost.CDrive

/-!
# M6: chunk split steps (`removeChunk`, `moveUnit`, `chunkSplitStep`, `driveChunk`)

As for groups, the agreement lemmas cover the cases Level F's cost proof uses, and reach the states
it names (`cremoveState`, `cmoveLState`, `cmoveRState`). A unit has at most three groups, kept in
locals.
-/

namespace OM.Impl

open OM.Model
open OM.Machine (Reg BinOp UnOp)
open OM.Proof.Top (getX_modify')

local notation "upd" => OM.Machine.State.upd

/-! ### `removeChunk` -/

theorem pqEnterIfAbove_noop {σ : Core} {c : Nat} (h : (σ.C.getX c).size ≤ σ.P.theta) :
    (pqEnterIfAbove c).run σ = .ok () σ := by
  unfold pqEnterIfAbove
  simp [OM.Proof.run_getC_bind, OM.Proof.run_getP_bind, Nat.not_lt.mpr h]

def cquietE (y : Reg) : Exp := (.cF .st y =ₑ 1) &&ₑ (.cF .src y =ₑ "x")
def cquietS (y : Reg) : Stm :=
  .ite (cquietE y) (.wcF .st y 0 ;; .wcF .src y 0 ;; pqEnterIfAboveP.call [.var y] []) .skip

/-- `removeChunk x`: `x` is dead, its overflow siblings quiet (and offered to the queue). -/
def removeChunkS : Stm :=
  .wcF .st "x" 3 ;; "xl" ::= .cF .l "x" ;; "xr" ::= .cF .r "x" ;; cquietS "xl" ;; cquietS "xr"

theorem cquietS_ok {κ : Caps} {S0 : Core} {L : Loc} {y : Reg} {j x : Nat} (hy : L y = j) (hx : L "x" = x)
    (hst : (S0.C.getX j).st = .overflow) (hsrc : (S0.C.getX j).src = x) (hsz : (S0.C.getX j).size ≤ S0.P.theta)
    (hj : j < S0.C.size) (hjT : j < κ.tbl .C) :
    ∃ n, evalF κ (cquietS y) S0 L = .ok { S0 with C := S0.C.modify j OM.Proof.quietC } L n ∧ n ≤ 50 := by
  have hv : ∀ s' : Core, (Exp.var y).ev κ s' L = some j := fun _ => by simp [Exp.ev, hy]
  have w1 := evalF_wrC_ok (κ := κ) (s := S0) (L := L) (k := .st) (e := (0 : Exp)) (w := 0) (hv _) rfl hj hjT rfl
  have w2 := evalF_wrC_ok (κ := κ) (s := { S0 with C := S0.C.modify j (CF.set · 0 .st) }) (L := L) (k := .src)
    (e := (0 : Exp)) (w := 0) (hv _) rfl (by simp [hj]) hjT rfl
  have hfin : (S0.C.modify j (CF.set · 0 .st)).modify j (CF.set · 0 .src) = S0.C.modify j OM.Proof.quietC := by
    rw [Array.modify_modify_same]; rfl
  rw [hfin] at w2
  set S2 : Core := { S0 with C := S0.C.modify j OM.Proof.quietC }
  have hsz2 : (S2.C.getX j).size ≤ S2.P.theta := by
    simp only [S2, getX_modify', hj, and_self, if_true]; exact hsz
  obtain ⟨Lq, cq, eq, hcq⟩ := pqEnterIfAbove_agree κ S2 (OM.Machine.State.setLocs (fun _ => 0) ["c"] [j]) (c := j)
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd]) hjT hsz2 (pqEnterIfAbove_noop hsz2)
  have ec := evalF_call_ok (q := pqEnterIfAboveP) (args := [.var y]) (ds := []) (L := L) (by simp [evList, Exp.ev, hy]) eq
  have hc : (cquietE y).ev κ S0 L = some 1 := by
    simp [cquietE, Exp.cF, Exp.ev, OM.Machine.BinOp.eval, hy, hx, hjT, Fld.cap, Fld.get, CF.get, hst, hsrc]; rfl
  refine ⟨_, evalF_ite_t hc one_ne_zero (evalF_seq_ok2 (by simp only [Stm.wcF]; exact w1)
    (evalF_seq_ok2 (by simp only [Stm.wcF]; exact w2) ec)), ?_⟩
  simp [Exp.cost, cquietE, Exp.cF, costList] at hcq ⊢; omega

open OM.Proof in
theorem removeChunkS_agree (κ : Caps) (s : Core) (L : Loc) {x : Nat} (hx : L "x" = x)
    (hlr : cLl s x ≠ cRr s x) (hlx : cLl s x ≠ x) (hrx : cRr s x ≠ x) (hxs : x < s.C.size)
    (hl : cSt s (cLl s x) = .overflow ∧ cSrc s (cLl s x) = x)
    (hr : cSt s (cRr s x) = .overflow ∧ cSrc s (cRr s x) = x)
    (hszl : cSz s (cLl s x) ≤ s.P.theta) (hszr : cSz s (cRr s x) ≤ s.P.theta)
    (hlS : cLl s x < s.C.size) (hrS : cRr s x < s.C.size) (hC : s.C.size ≤ κ.tbl .C) :
    ∃ L' n, evalF κ removeChunkS s L = .ok (cremoveState s x) L' n ∧ n ≤ 150 := by
  set l := cLl s x
  set r := cRr s x
  have hxT : x < κ.tbl .C := by omega
  have w1 := evalF_wrC_ok (κ := κ) (s := s) (L := L) (k := .st) (i := .var "x") (e := (3 : Exp)) (j := x) (w := 3)
    (by simp [Exp.ev, hx]) rfl hxs hxT rfl
  set S1 : Core := { s with C := s.C.modify x (CF.set · 3 .st) }
  have hd : s.C.modify x (CF.set · 3 .st) = s.C.modify x deadC := Array.modify_congr_getX _ _ _ _ rfl
  have g1 : ∀ z, z ≠ x → S1.C.getX z = s.C.getX z := by
    intro z hz; simp only [S1, getX_modify']; rw [if_neg (fun h => hz h.1)]
  have g1x : (S1.C.getX x).l = l ∧ (S1.C.getX x).r = r := by
    simp only [S1, getX_modify', hxs, and_self, if_true]; exact ⟨rfl, rfl⟩
  have a2 := evalF_assign_ok (κ := κ) (s := S1) (L := L) (x := "xl") (e := .cF .l "x") (v := l)
    (by simp [Exp.cF, Exp.ev, hx, hxT, Fld.cap, Fld.get, CF.get, g1x.1])
  have a3 := evalF_assign_ok (κ := κ) (s := S1) (L := upd L "xl" l) (x := "xr") (e := .cF .r "x") (v := r)
    (by simp [Exp.cF, Exp.ev, OM.Machine.State.upd, hx, hxT, Fld.cap, Fld.get, CF.get, g1x.2])
  set L3 := upd (upd L "xl" l) "xr" r
  obtain ⟨n4, e4, hn4⟩ := cquietS_ok (κ := κ) (S0 := S1) (L := L3) (y := "xl") (j := l) (x := x)
    (by simp [L3, OM.Machine.State.upd]) (by simp [L3, OM.Machine.State.upd, hx])
    (by rw [g1 l hlx]; exact hl.1) (by rw [g1 l hlx]; exact hl.2) (by rw [g1 l hlx]; exact hszl)
    (by simp [S1, hlS]) (by omega)
  set S2 : Core := { S1 with C := S1.C.modify l quietC }
  have g2 : (S2.C.getX r) = s.C.getX r := by
    simp only [S2, getX_modify']; rw [if_neg (fun h => hlr h.1.symm), g1 r hrx]
  obtain ⟨n5, e5, hn5⟩ := cquietS_ok (κ := κ) (S0 := S2) (L := L3) (y := "xr") (j := r) (x := x)
    (by simp [L3, OM.Machine.State.upd]) (by simp [L3, OM.Machine.State.upd, hx])
    (by rw [g2]; exact hr.1) (by rw [g2]; exact hr.2) (by rw [g2]; exact hszr) (by simp [S2, S1, hrS]) (by omega)
  have hfin : ({ S2 with C := S2.C.modify r quietC } : Core) = cremoveState s x := by
    simp only [S2, S1, cremoveState, hd]; rfl
  rw [hfin] at e5
  refine ⟨L3, _, evalF_seq_ok2 (by simp only [Stm.wcF]; exact w1) (evalF_seq_ok2 a2 (evalF_seq_ok2 a3
    (evalF_seq_ok2 e4 e5))), ?_⟩
  simp only [Exp.cost, Exp.cF] at hn4 hn5 ⊢; omega

/-! ### The unit at an end of a chunk -/

/-- The unit held in locals: `[u0]`, or `[u0, u1, u2]` when `uk = 3`. -/
def unitOf (L : Loc) : List Nat := if L "uk" = 1 then [L "u0"] else [L "u0", L "u1", L "u2"]

def unitLE : Exp := "lf" &&ₑ (.gF .l "sr" =ₑ "g0")
def unitRE : Exp := (!ₑ "lf") &&ₑ (.gF .r "sr" =ₑ "g0")
/-- `unitCand x (lf = 1)` into `uk, u0, u1, u2` (locals `x lf`). -/
def unitS : Stm :=
  .ite "lf" ("g0" ::= .cF .first "x") ("g0" ::= .cF .last "x") ;;
  "uk" ::= 1 ;; "u0" ::= "g0" ;;
  .ite (.gF .st "g0" =ₑ 1)
    ("sr" ::= .gF .src "g0" ;;
     .ite unitLE ("uk" ::= 3 ;; "u0" ::= "g0" ;; "u1" ::= "sr" ;; "u2" ::= .gF .r "sr")
       (.ite unitRE ("uk" ::= 3 ;; "u0" ::= .gF .l "sr" ;; "u1" ::= "sr" ;; "u2" ::= "g0") .skip))
    .skip

theorem unitCand_eq (s : Core) (x : Nat) (left : Bool) :
    unitCand s x left =
      (let g0 := if left then (s.C.getX x).first else (s.C.getX x).last
       let G0 := s.Gs.getX g0
       if G0.st = .overflow then
         (let S := s.Gs.getX G0.src
          if left = true ∧ S.l = g0 then [g0, G0.src, S.r]
          else if left = false ∧ S.r = g0 then [S.l, G0.src, g0] else [g0])
       else [g0]) := by
  unfold unitCand
  dsimp only
  by_cases h : (s.Gs.getX (if left = true then (s.C.getX x).first else (s.C.getX x).last)).st = St.overflow
  · simp only [h, bne_self_eq_false, Bool.false_eq_true, if_false, if_true]
    cases left <;> simp
  · simp [h]

theorem unitS_ok {κ : Caps} {s : Core} {L : Loc} {x : Nat} {left : Bool} (hx : L "x" = x) (hlf : L "lf" = b2n left)
    (hxT : x < κ.tbl .C) (hg0T : (if left then (s.C.getX x).first else (s.C.getX x).last) < κ.tbl .G)
    (hsrT : (s.Gs.getX (if left then (s.C.getX x).first else (s.C.getX x).last)).src < κ.tbl .G) :
    ∃ L' n, evalF κ unitS s L = .ok s L' n ∧ unitOf L' = unitCand s x left ∧ (L' "uk" = 1 ∨ L' "uk" = 3) ∧
      n ≤ 80 ∧ ∀ r, r ≠ "g0" → r ≠ "uk" → r ≠ "u0" → r ≠ "u1" → r ≠ "u2" → r ≠ "sr" → L' r = L r := by
  set g0 := if left then (s.C.getX x).first else (s.C.getX x).last
  set G0 := s.Gs.getX g0
  have e1 : ∃ c1, evalF κ (.ite "lf" ("g0" ::= .cF .first "x") ("g0" ::= .cF .last "x")) s L =
      .ok s (upd L "g0" g0) c1 ∧ c1 ≤ 6 := by
    cases left
    · exact ⟨_, evalF_ite_f (by simp [Exp.ev, hlf, b2n]) (evalF_assign_ok (by simp [Exp.cF, Exp.ev, hx, hxT, Fld.cap,
        Fld.get, CF.get, g0])), by simp [Exp.cost, Exp.cF]⟩
    · exact ⟨_, evalF_ite_t (v := 1) (by simp [Exp.ev, hlf, b2n]) one_ne_zero (evalF_assign_ok (by simp [Exp.cF,
        Exp.ev, hx, hxT, Fld.cap, Fld.get, CF.get, g0])), by simp [Exp.cost, Exp.cF]⟩
  obtain ⟨c1, e1, hc1⟩ := e1
  set L1 := upd L "g0" g0
  have a2 := evalF_assign_ok (κ := κ) (s := s) (L := L1) (x := "uk") (e := (1 : Exp)) (v := 1) rfl
  have a3 := evalF_assign_ok (κ := κ) (s := s) (L := upd L1 "uk" 1) (x := "u0") (e := .var "g0") (v := g0)
    (by simp [Exp.ev, L1, OM.Machine.State.upd])
  set L3 := upd (upd L1 "uk" 1) "u0" g0
  have h3 : ∀ r, r ≠ "g0" → r ≠ "uk" → r ≠ "u0" → L3 r = L r := fun r h1 h2 h3 => by
    simp [L3, L1, OM.Machine.State.upd, h1, h2, h3]
  have h3g0 : L3 "g0" = g0 := by simp [L3, L1, OM.Machine.State.upd]
  have h3lf : L3 "lf" = b2n left := by rw [h3 "lf" (by decide) (by decide) (by decide), hlf]
  have hc4 : (.gF .st "g0" =ₑ 1 : Exp).ev κ s L3 = some (if G0.st.toN = 1 then 1 else 0) := by
    simp [Exp.gF, Exp.ev, OM.Machine.BinOp.eval, h3g0, hg0T, Fld.cap, Fld.get, GF.get, G0]
  have hfr3 : ∀ L' : Loc, (∀ r, r ≠ "g0" → r ≠ "uk" → r ≠ "u0" → r ≠ "u1" → r ≠ "u2" → r ≠ "sr" → L' r = L3 r) →
      ∀ r, r ≠ "g0" → r ≠ "uk" → r ≠ "u0" → r ≠ "u1" → r ≠ "u2" → r ≠ "sr" → L' r = L r :=
    fun L' hL' r h1 h2 hx3 h4 h5 h6 => (hL' r h1 h2 hx3 h4 h5 h6).trans (h3 r h1 h2 hx3)
  by_cases hov : G0.st = .overflow
  · have hc4' : (.gF .st "g0" =ₑ 1 : Exp).ev κ s L3 = some 1 := by rw [hc4, hov]; rfl
    set sr := G0.src
    set S := s.Gs.getX sr
    have a5 := evalF_assign_ok (κ := κ) (s := s) (L := L3) (x := "sr") (e := .gF .src "g0") (v := sr)
      (by simp [Exp.gF, Exp.ev, h3g0, hg0T, Fld.cap, Fld.get, GF.get, sr, G0])
    set L5 := upd L3 "sr" sr
    have h5 : L5 "sr" = sr := by simp [L5, OM.Machine.State.upd]
    have h5g0 : L5 "g0" = g0 := by simp [L5, OM.Machine.State.upd, h3g0]
    have h5lf : L5 "lf" = b2n left := by simp [L5, OM.Machine.State.upd, h3lf]
    have hsrT' : sr < κ.tbl .G := hsrT
    have hcL : unitLE.ev κ s L5 = some (if left = true ∧ S.l = g0 then 1 else 0) := by
      cases left <;> by_cases e : S.l = g0 <;>
        simp [unitLE, Exp.gF, Exp.ev, OM.Machine.BinOp.eval, h5, h5g0, h5lf, hsrT', Fld.cap, Fld.get, GF.get, b2n, e, S]
    have hcR : unitRE.ev κ s L5 = some (if left = false ∧ S.r = g0 then 1 else 0) := by
      cases left <;> by_cases e : S.r = g0 <;>
        simp [unitRE, Exp.gF, Exp.ev, OM.Machine.BinOp.eval, OM.Machine.UnOp.eval, h5, h5g0, h5lf, hsrT', Fld.cap,
          Fld.get, GF.get, b2n, e, S]
    have hcand : unitCand s x left = if left = true ∧ S.l = g0 then [g0, sr, S.r]
        else if left = false ∧ S.r = g0 then [S.l, sr, g0] else [g0] := by
      rw [unitCand_eq]; exact if_pos hov
    by_cases hL : left = true ∧ S.l = g0
    · rw [if_pos hL] at hcL hcand
      have b1 := evalF_assign_ok (κ := κ) (s := s) (L := L5) (x := "uk") (e := (3 : Exp)) (v := 3) rfl
      have b2 := evalF_assign_ok (κ := κ) (s := s) (L := upd L5 "uk" 3) (x := "u0") (e := .var "g0") (v := g0)
        (by simp [Exp.ev, OM.Machine.State.upd, h5g0])
      have b3 := evalF_assign_ok (κ := κ) (s := s) (L := upd (upd L5 "uk" 3) "u0" g0) (x := "u1") (e := .var "sr")
        (v := sr) (by simp [Exp.ev, OM.Machine.State.upd, h5])
      have b4 := evalF_assign_ok (κ := κ) (s := s) (L := upd (upd (upd L5 "uk" 3) "u0" g0) "u1" sr) (x := "u2")
        (e := .gF .r "sr") (v := S.r) (by simp [Exp.gF, Exp.ev, OM.Machine.State.upd, h5, hsrT', Fld.cap, Fld.get,
          GF.get, S])
      refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 a2 (evalF_seq_ok2 a3 (evalF_ite_t hc4' one_ne_zero
        (evalF_seq_ok2 a5 (evalF_ite_t hcL one_ne_zero (evalF_seq_ok2 b1 (evalF_seq_ok2 b2 (evalF_seq_ok2 b3 b4)))))))),
        by rw [hcand]; simp [unitOf, OM.Machine.State.upd], by simp [OM.Machine.State.upd], ?_,
        hfr3 _ fun r h1 h2 h3 h4 h5 h6 => by simp [L5, OM.Machine.State.upd, h2, h3, h4, h5, h6]⟩
      simp [Exp.cost, Exp.gF, unitLE] at hc1 ⊢; omega
    · rw [if_neg hL] at hcL hcand
      by_cases hR : left = false ∧ S.r = g0
      · rw [if_pos hR] at hcR hcand
        have b1 := evalF_assign_ok (κ := κ) (s := s) (L := L5) (x := "uk") (e := (3 : Exp)) (v := 3) rfl
        have b2 := evalF_assign_ok (κ := κ) (s := s) (L := upd L5 "uk" 3) (x := "u0") (e := .gF .l "sr") (v := S.l)
          (by simp [Exp.gF, Exp.ev, OM.Machine.State.upd, h5, hsrT', Fld.cap, Fld.get, GF.get, S])
        have b3 := evalF_assign_ok (κ := κ) (s := s) (L := upd (upd L5 "uk" 3) "u0" S.l) (x := "u1") (e := .var "sr")
          (v := sr) (by simp [Exp.ev, OM.Machine.State.upd, h5])
        have b4 := evalF_assign_ok (κ := κ) (s := s) (L := upd (upd (upd L5 "uk" 3) "u0" S.l) "u1" sr) (x := "u2")
          (e := .var "g0") (v := g0) (by simp [Exp.ev, OM.Machine.State.upd, h5g0])
        refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 a2 (evalF_seq_ok2 a3 (evalF_ite_t hc4' one_ne_zero
          (evalF_seq_ok2 a5 (evalF_ite_f hcL (evalF_ite_t hcR one_ne_zero (evalF_seq_ok2 b1 (evalF_seq_ok2 b2
          (evalF_seq_ok2 b3 b4))))))))),
          by rw [hcand]; simp [unitOf, OM.Machine.State.upd], by simp [OM.Machine.State.upd], ?_,
          hfr3 _ fun r h1 h2 h3 h4 h5 h6 => by simp [L5, OM.Machine.State.upd, h2, h3, h4, h5, h6]⟩
        simp [Exp.cost, Exp.gF, unitLE, unitRE] at hc1 ⊢; omega
      · rw [if_neg hR] at hcR hcand
        refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 a2 (evalF_seq_ok2 a3 (evalF_ite_t hc4' one_ne_zero
          (evalF_seq_ok2 a5 (evalF_ite_f hcL (evalF_ite_f hcR evalF_skip)))))),
          by rw [hcand]; simp [unitOf, L5, L3, OM.Machine.State.upd], by simp [L5, L3, OM.Machine.State.upd], ?_,
          hfr3 _ fun r h1 h2 h3 h4 h5 h6 => by simp [L5, OM.Machine.State.upd, h6]⟩
        simp [Exp.cost, Exp.gF, unitLE, unitRE] at hc1 ⊢; omega
  · have hc4' : (.gF .st "g0" =ₑ 1 : Exp).ev κ s L3 = some 0 := by
      rw [hc4]; cases h : G0.st <;> simp_all [St.toN]
    have hcand : unitCand s x left = [g0] := by
      rw [unitCand_eq]; exact if_neg hov
    refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 a2 (evalF_seq_ok2 a3 (evalF_ite_f hc4' evalF_skip))),
      by rw [hcand]; simp [unitOf, L3, OM.Machine.State.upd], by simp [L3, OM.Machine.State.upd], ?_,
      hfr3 _ fun r _ _ _ _ _ _ => rfl⟩
    simp [Exp.cost, Exp.gF] at hc1 ⊢; omega

end OM.Impl
