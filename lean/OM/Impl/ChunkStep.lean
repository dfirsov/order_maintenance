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

/-! ### Labels for a moved unit -/

theorem pushBackLabs_inv {c D B k : Nat} {prev : Option Nat} {s s' : Core} {labs : List Nat}
    (h : (pushBackLabs c D B prev (k + 1)).run s = .ok labs s') :
    ∃ l rest, labs = l :: rest ∧ (pushBackLabs c D B (some l) k).run s = .ok rest s' ∧
      (prev = none → l = c) ∧ (∀ p, prev = some p → p + D < 1 <<< B ∧ p < p + D ∧ l = p + D) := by
  unfold pushBackLabs at h
  cases prev with
  | none =>
    simp only [OM.Proof.run_pure_bind] at h
    obtain ⟨rest, s2, h2, h⟩ := run_bind_ok h
    simp only [OM.Proof.run_pure] at h
    injection h with h3 h4; subst h3 h4
    exact ⟨_, _, rfl, h2, fun _ => rfl, fun _ h => absurd h (by simp)⟩
  | some p =>
    dsimp only at h
    obtain ⟨l, s1, h1, h⟩ := run_bind_ok h
    obtain ⟨rest, s2, h2, h⟩ := run_bind_ok h
    simp only [OM.Proof.run_pure] at h
    injection h with h3 h4; subst h3 h4
    obtain ⟨hs, ha, hb, rfl⟩ := after_inv h1
    subst s1
    exact ⟨_, _, rfl, h2, fun h => absurd h (by simp), fun q hq => by
      simp only [Option.some.injEq] at hq; subst hq; exact ⟨ha, hb, rfl⟩⟩

theorem pushFrontLabs_inv {c D k : Nat} {nxt : Option Nat} {s s' : Core} {labs : List Nat}
    (h : (pushFrontLabs c D nxt (k + 1)).run s = .ok labs s') :
    ∃ l rest, labs = rest ++ [l] ∧ (pushFrontLabs c D (some l) k).run s = .ok rest s' ∧
      (nxt = none → l = c) ∧ (∀ n, nxt = some n → D ≤ n ∧ D ≠ 0 ∧ l = n - D) := by
  unfold pushFrontLabs at h
  cases nxt with
  | none =>
    simp only [OM.Proof.run_pure_bind] at h
    obtain ⟨rest, s2, h2, h⟩ := run_bind_ok h
    simp only [OM.Proof.run_pure] at h
    injection h with h3 h4; subst h3 h4
    exact ⟨_, _, rfl, h2, fun _ => rfl, fun _ h => absurd h (by simp)⟩
  | some n =>
    dsimp only at h
    obtain ⟨l, s1, h1, h⟩ := run_bind_ok h
    obtain ⟨rest, s2, h2, h⟩ := run_bind_ok h
    simp only [OM.Proof.run_pure] at h
    injection h with h3 h4; subst h3 h4
    obtain ⟨hs, ha, hb, rfl⟩ := before_inv h1
    subst s1
    exact ⟨_, _, rfl, h2, fun h => absurd h (by simp), fun q hq => by
      simp only [Option.some.injEq] at hq; subst hq; exact ⟨ha, hb, rfl⟩⟩

theorem pushBackLabs_zero {c D B : Nat} {prev : Option Nat} {s s' : Core} {labs : List Nat}
    (h : (pushBackLabs c D B prev 0).run s = .ok labs s') : labs = [] ∧ s' = s := by
  unfold pushBackLabs at h; simp only [OM.Proof.run_pure] at h; injection h with h1 h2; exact ⟨h1.symm, h2.symm⟩

theorem pushFrontLabs_zero {c D : Nat} {nxt : Option Nat} {s s' : Core} {labs : List Nat}
    (h : (pushFrontLabs c D nxt 0).run s = .ok labs s') : labs = [] ∧ s' = s := by
  unfold pushFrontLabs at h; simp only [OM.Proof.run_pure] at h; injection h with h1 h2; exact ⟨h1.symm, h2.symm⟩

/-- The labels held in locals: `[l0]`, or `[l0, l1, l2]` when `uk = 3`. -/
def labsOf (L : Loc) : List Nat := if L "uk" = 1 then [L "l0"] else [L "l0", L "l1", L "l2"]

def centreG : Exp := .bin .shl 1 (Exp.monus (.prm .Bg) 1)

theorem centreG_ev {κ : Caps} {S0 : Core} {L : Loc} : centreG.ev κ S0 L = some (1 <<< (S0.P.B_g - 1)) := by
  have hm := Exp.ev_monus κ S0 L (a := .prm .Bg) (b := (1 : Exp)) (x := S0.P.B_g) (y := 1) (by simp [Exp.ev, PF.get]) rfl
  simp only [centreG, Exp.ev, Option.bind_some]
  rw [hm]; simp [OM.Machine.BinOp.eval, Nat.shiftLeft_eq]

/-- `pushBackLabs` after the last group of chunk `y` (locals `y uk`). -/
def labLS : Stm :=
  "D" ::= .prm .Dg ;; "B" ::= .prm .Bg ;;
  .ite (.cF .first "y" =ₑ 0) ("l0" ::= centreG) ("a" ::= .gF .lab (.cF .last "y") ;; afterS ;; "l0" ::= "lab") ;;
  .ite ("uk" =ₑ 3) ("a" ::= "l0" ;; afterS ;; "l1" ::= "lab" ;; "a" ::= "l1" ;; afterS ;; "l2" ::= "lab") .skip

/-- `pushFrontLabs` before the first group of chunk `y` (locals `y uk`). -/
def labRS : Stm :=
  "D" ::= .prm .Dg ;;
  .ite (.cF .first "y" =ₑ 0) ("m" ::= centreG) ("b" ::= .gF .lab (.cF .first "y") ;; beforeS ;; "m" ::= "lab") ;;
  .ite ("uk" =ₑ 3) ("l2" ::= "m" ;; "b" ::= "m" ;; beforeS ;; "l1" ::= "lab" ;; "b" ::= "l1" ;; beforeS ;; "l0" ::= "lab")
    ("l0" ::= "m")

theorem labLS_ok {κ : Caps} {s : Core} {L : Loc} {y k : Nat} {labs : List Nat} (hy : L "y" = y)
    (hk : (L "uk" = 1 ∧ k = 1) ∨ (L "uk" = 3 ∧ k = 3)) (hyT : y < κ.tbl .C) (hlT : (s.C.getX y).last < κ.tbl .G)
    (hlabs : (pushBackLabs (1 <<< (s.P.B_g - 1)) s.P.D_g s.P.B_g (if (s.C.getX y).first = NIL then none
      else some (s.Gs.getX (s.C.getX y).last).lab) k).run s = .ok labs s) :
    ∃ L' n, evalF κ labLS s L = .ok s L' n ∧ labsOf L' = labs ∧ L' "uk" = L "uk" ∧ n ≤ 150 ∧
      ∀ r, r ≠ "D" → r ≠ "B" → r ≠ "l0" → r ≠ "l1" → r ≠ "l2" → r ≠ "a" → r ≠ "v" → r ≠ "lab" → L' r = L r := by
  set c := 1 <<< (s.P.B_g - 1)
  set prev := if (s.C.getX y).first = NIL then none else some (s.Gs.getX (s.C.getX y).last).lab
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "D") (e := .prm .Dg) (v := s.P.D_g) (by simp [Exp.ev, PF.get])
  have a2 := evalF_assign_ok (κ := κ) (s := s) (L := upd L "D" s.P.D_g) (x := "B") (e := .prm .Bg) (v := s.P.B_g)
    (by simp [Exp.ev, PF.get])
  set L2 := upd (upd L "D" s.P.D_g) "B" s.P.B_g
  have h2 : ∀ r, r ≠ "D" → r ≠ "B" → L2 r = L r := fun r h1 h2 => by simp [L2, OM.Machine.State.upd, h1, h2]
  have h2y : L2 "y" = y := by rw [h2 "y" (by decide) (by decide), hy]
  -- the first label
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by rcases hk with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact ⟨_, rfl⟩
  obtain ⟨l0, rest, hlabs0, hrest, hnone, hsome⟩ := pushBackLabs_inv hlabs
  have b3 : ∃ L3 c3, evalF κ (.ite (.cF .first "y" =ₑ 0) ("l0" ::= centreG)
      ("a" ::= .gF .lab (.cF .last "y") ;; afterS ;; "l0" ::= "lab")) s L2 = .ok s L3 c3 ∧ L3 "l0" = l0 ∧
      (∀ r, r ≠ "l0" → r ≠ "a" → r ≠ "v" → r ≠ "lab" → L3 r = L2 r) ∧ c3 ≤ 40 := by
    by_cases hf : (s.C.getX y).first = NIL
    · have hl0 : l0 = c := hnone (by simp [prev, hf])
      have hc : (.cF .first "y" =ₑ 0 : Exp).ev κ s L2 = some 1 := by
        simp [Exp.cF, Exp.ev, OM.Machine.BinOp.eval, h2y, hyT, Fld.cap, Fld.get, CF.get]; simpa [NIL] using hf
      exact ⟨_, _, evalF_ite_t hc one_ne_zero (evalF_assign_ok centreG_ev), by simp [OM.Machine.State.upd, hl0, c],
        fun r h1 _ _ _ => by simp [OM.Machine.State.upd, h1], by simp [Exp.cost, centreG, Exp.cF]⟩
    · obtain ⟨hpa, hpb, hl0⟩ := hsome (s.Gs.getX (s.C.getX y).last).lab (by simp [prev, hf])
      have hc : (.cF .first "y" =ₑ 0 : Exp).ev κ s L2 = some 0 := by
        simp [Exp.cF, Exp.ev, OM.Machine.BinOp.eval, h2y, hyT, Fld.cap, Fld.get, CF.get]; simpa [NIL] using hf
      set p := (s.Gs.getX (s.C.getX y).last).lab
      have b1 := evalF_assign_ok (κ := κ) (s := s) (L := L2) (x := "a") (e := .gF .lab (.cF .last "y")) (v := p)
        (by simp [Exp.gF, Exp.cF, Exp.ev, h2y, hyT, hlT, Fld.cap, Fld.get, CF.get, GF.get]; rfl)
      obtain ⟨c2, b2, hc2⟩ := afterS_ok (κ := κ) (s := s) (L := upd L2 "a" p) (a := p) (D := s.P.D_g) (B := s.P.B_g)
        (by simp [OM.Machine.State.upd]) (by simp [OM.Machine.State.upd, L2]) (by simp [OM.Machine.State.upd, L2])
        hpa hpb
      have b3 := evalF_assign_ok (κ := κ) (s := s) (L := upd (upd (upd L2 "a" p) "v" (p + s.P.D_g)) "lab" (p + s.P.D_g))
        (x := "l0") (e := .var "lab") (v := p + s.P.D_g) (by simp [Exp.ev, OM.Machine.State.upd])
      exact ⟨_, _, evalF_ite_f hc (evalF_seq_ok2 b1 (evalF_seq_ok2 b2 b3)), by simp [OM.Machine.State.upd, hl0],
        fun r h1 h2 h3 h4 => by simp [OM.Machine.State.upd, h1, h2, h3, h4],
        by simp [Exp.cost, Exp.gF, Exp.cF] at hc2 ⊢; omega⟩
  obtain ⟨L3, c3, e3, h3l0, h3F, hc3⟩ := b3
  have h3uk : L3 "uk" = L "uk" := by
    rw [h3F "uk" (by decide) (by decide) (by decide) (by decide), h2 "uk" (by decide) (by decide)]
  have h3D : L3 "D" = s.P.D_g := by
    rw [h3F "D" (by decide) (by decide) (by decide) (by decide)]; simp [L2, OM.Machine.State.upd]
  have h3B : L3 "B" = s.P.B_g := by
    rw [h3F "B" (by decide) (by decide) (by decide) (by decide)]; simp [L2, OM.Machine.State.upd]
  have hfr : ∀ L' : Loc, (∀ r, r ≠ "l0" → r ≠ "l1" → r ≠ "l2" → r ≠ "a" → r ≠ "v" → r ≠ "lab" → L' r = L3 r) →
      ∀ r, r ≠ "D" → r ≠ "B" → r ≠ "l0" → r ≠ "l1" → r ≠ "l2" → r ≠ "a" → r ≠ "v" → r ≠ "lab" → L' r = L r :=
    fun L' hL' r h1 h2' h3 h4 h5 h6 h7 h8 => by
      rw [hL' r h3 h4 h5 h6 h7 h8, h3F r h3 h6 h7 h8, h2 r h1 h2']
  rcases hk with ⟨huk, hk'⟩ | ⟨huk, hk'⟩
  · obtain rfl : k' = 0 := by omega
    obtain ⟨rfl, -⟩ := pushBackLabs_zero hrest
    have hc : ("uk" =ₑ 3 : Exp).ev κ s L3 = some 0 := by simp [Exp.ev, OM.Machine.BinOp.eval, h3uk, huk]
    refine ⟨L3, _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 e3 (evalF_ite_f hc evalF_skip))),
      by simp [labsOf, h3uk, huk, h3l0, hlabs0], h3uk, by simp [Exp.cost] at hc3 ⊢; omega,
      hfr L3 fun _ _ _ _ _ _ _ => rfl⟩
  · obtain rfl : k' = 2 := by omega
    obtain ⟨l1, rest2, hr1, hrest2, -, hs1⟩ := pushBackLabs_inv hrest
    obtain ⟨hpa1, hpb1, hl1⟩ := hs1 l0 rfl
    obtain ⟨l2, rest3, hr2, hrest3, -, hs2⟩ := pushBackLabs_inv hrest2
    obtain ⟨hpa2, hpb2, hl2⟩ := hs2 l1 rfl
    obtain ⟨rfl, -⟩ := pushBackLabs_zero hrest3
    have hc : ("uk" =ₑ 3 : Exp).ev κ s L3 = some 1 := by simp [Exp.ev, OM.Machine.BinOp.eval, h3uk, huk]
    have b1 := evalF_assign_ok (κ := κ) (s := s) (L := L3) (x := "a") (e := .var "l0") (v := l0) (by simp [Exp.ev, h3l0])
    obtain ⟨c2, b2, hc2⟩ := afterS_ok (κ := κ) (s := s) (L := upd L3 "a" l0) (a := l0) (D := s.P.D_g) (B := s.P.B_g)
      (by simp [OM.Machine.State.upd]) (by simp [OM.Machine.State.upd, h3D]) (by simp [OM.Machine.State.upd, h3B])
      hpa1 hpb1
    set L5 := upd (upd (upd L3 "a" l0) "v" (l0 + s.P.D_g)) "lab" (l0 + s.P.D_g)
    have b3 := evalF_assign_ok (κ := κ) (s := s) (L := L5) (x := "l1") (e := .var "lab") (v := l1)
      (by simp [Exp.ev, L5, OM.Machine.State.upd, hl1])
    have b4 := evalF_assign_ok (κ := κ) (s := s) (L := upd L5 "l1" l1) (x := "a") (e := .var "l1") (v := l1)
      (by simp [Exp.ev, OM.Machine.State.upd])
    obtain ⟨c5, b5, hc5⟩ := afterS_ok (κ := κ) (s := s) (L := upd (upd L5 "l1" l1) "a" l1) (a := l1) (D := s.P.D_g)
      (B := s.P.B_g) (by simp [OM.Machine.State.upd]) (by simp [OM.Machine.State.upd, L5, h3D])
      (by simp [OM.Machine.State.upd, L5, h3B]) hpa2 hpb2
    set L6 := upd (upd (upd (upd L5 "l1" l1) "a" l1) "v" (l1 + s.P.D_g)) "lab" (l1 + s.P.D_g)
    have b6 := evalF_assign_ok (κ := κ) (s := s) (L := L6) (x := "l2") (e := .var "lab") (v := l2)
      (by simp [Exp.ev, L6, OM.Machine.State.upd, hl2])
    refine ⟨_, _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 e3 (evalF_ite_t hc one_ne_zero
      (evalF_seq_ok2 b1 (evalF_seq_ok2 b2 (evalF_seq_ok2 b3 (evalF_seq_ok2 b4 (evalF_seq_ok2 b5 b6)))))))),
      ?_, ?_, ?_, hfr _ fun r h3 h4 h5 h6 h7 h8 => by simp [L6, L5, OM.Machine.State.upd, h3, h4, h5, h6, h7, h8]⟩
    · simp [labsOf, L6, L5, OM.Machine.State.upd, h3uk, huk, h3l0, hlabs0, hr1, hr2]
    · simp [L6, L5, OM.Machine.State.upd, h3uk]
    · simp [Exp.cost] at hc2 hc3 hc5 ⊢; omega

end OM.Impl
