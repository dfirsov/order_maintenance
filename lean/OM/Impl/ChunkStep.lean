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

end OM.Impl
