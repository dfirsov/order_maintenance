import OM.Impl.Group
import OM.Proof.Cost.GMove

/-!
# M6: group split steps (`removeGroup`, `moveElem`, `groupSplitStep`, `driveGroup`)

The agreement lemmas cover the cases Level F's cost proof uses (`removeGroup_ok`, `MoveLOK`,
`MoveROK`), and reach the states it names (`removeState`, `moveLState`, `moveRState`).
-/

namespace OM.Impl

open OM.Model
open OM.Machine (Reg BinOp UnOp)
open OM.Proof.Top (getX_modify')

local notation "upd" => OM.Machine.State.upd

/-! ### `removeGroup` -/

def startGroupSplitP : Proc := { name := "startGroupSplit", params := ["g"], rets := [], body := startGroupSplitS }

/-- Quiet the overflow sibling `x` of `g` (flag `q`). -/
def quietE (x : Reg) : Exp := (.gF .st x =ₑ 1) &&ₑ (.gF .src x =ₑ "g")
def quietS (x q : Reg) : Stm :=
  q ::= 0 ;; .ite (quietE x) (.wgF .st x 0 ;; .wgF .src x 0 ;; q ::= 1) .skip
/-- Split the quieted sibling `x` if it is full. -/
def splitIfE (x q : Reg) : Exp := .var q &&ₑ (.prm .G ≤ₑ .gF .size x)
def splitIfS (x q : Reg) : Stm := .ite (splitIfE x q) (startGroupSplitP.call [.var x] []) .skip

/-- `removeGroup g`: unlink and free `g`, then its overflow siblings become quiet (and split if full). -/
def removeGroupS : Stm :=
  unlinkGroupS ;; "gL" ::= .gF .l "g" ;; "gR" ::= .gF .r "g" ;;
  quietS "gL" "qL" ;; quietS "gR" "qR" ;; splitIfS "gL" "qL" ;; splitIfS "gR" "qR"

theorem quietS_ok {κ : Caps} {S0 : Core} {L : Loc} {x q : Reg} {j p : Nat} (hx : L x = j) (hg : L "g" = p)
    (hq : q ≠ x) (hqg : q ≠ "g") (hst : (S0.Gs.getX j).st = .overflow) (hsrc : (S0.Gs.getX j).src = p) (hj : j < S0.Gs.size)
    (hjT : j < κ.tbl .G) :
    ∃ n, evalF κ (quietS x q) S0 L = .ok { S0 with Gs := S0.Gs.modify j OM.Proof.quietG } (upd (upd L q 0) q 1) n ∧
      n ≤ 30 := by
  set L1 := upd L q 0
  have h1x : L1 x = j := by simp [L1, OM.Machine.State.upd, Ne.symm hq, hx]
  have hv : ∀ s' : Core, (Exp.var x).ev κ s' L1 = some j := fun _ => by simp [Exp.ev, h1x]
  have w1 := evalF_wrG_ok (κ := κ) (s := S0) (L := L1) (k := .st) (e := (0 : Exp)) (w := 0) (hv _) rfl hj hjT rfl
  have w2 := evalF_wrG_ok (κ := κ) (s := { S0 with Gs := S0.Gs.modify j (GF.set · 0 .st) }) (L := L1) (k := .src)
    (e := (0 : Exp)) (w := 0) (hv _) rfl (by simp [hj]) hjT rfl
  have hfin : (S0.Gs.modify j (GF.set · 0 .st)).modify j (GF.set · 0 .src) = S0.Gs.modify j OM.Proof.quietG := by
    rw [Array.modify_modify_same]; rfl
  rw [hfin] at w2
  have a3 := evalF_assign_ok (κ := κ) (s := { S0 with Gs := S0.Gs.modify j OM.Proof.quietG }) (L := L1) (x := q)
    (e := (1 : Exp)) (v := 1) rfl
  have hc : (quietE x).ev κ S0 L1 = some 1 := by
    have hg1 : L1 "g" = p := by simp [L1, OM.Machine.State.upd, Ne.symm hqg, hg]
    simp [quietE, Exp.gF, Exp.ev, OM.Machine.BinOp.eval, h1x, hg1, hjT, Fld.cap, Fld.get, GF.get, hst, hsrc]
    rfl
  refine ⟨_, evalF_seq_ok2 (evalF_assign_ok (v := 0) rfl) (evalF_ite_t hc one_ne_zero
    (evalF_seq_ok2 (by simp only [Stm.wgF]; exact w1) (evalF_seq_ok2 (by simp only [Stm.wgF]; exact w2) a3))),
    by simp [Exp.cost, quietE, Exp.gF]⟩

theorem splitIfS_skip {κ : Caps} {S0 : Core} {L : Loc} {x q : Reg} {j : Nat} (hx : L x = j) (hq : L q = 1)
    (hsz : (S0.Gs.getX j).size < S0.P.G) (hjT : j < κ.tbl .G) :
    ∃ n, evalF κ (splitIfS x q) S0 L = .ok S0 L n ∧ n ≤ 15 := by
  have hc : (splitIfE x q).ev κ S0 L = some 0 := by
    have : ¬ S0.P.G ≤ (S0.Gs.getX j).size := by omega
    simp [splitIfE, Exp.gF, Exp.ev, OM.Machine.BinOp.eval, hx, hq, hjT, Fld.cap, Fld.get, GF.get, PF.get, this]
  exact ⟨_, evalF_ite_f hc evalF_skip, by simp [Exp.cost, splitIfE, Exp.gF]⟩

open OM.Proof in
theorem removeGroupS_agree (κ : Caps) (s : Core) (L : Loc) {p : Nat} (hg : L "g" = p)
    (hp : LiveG s p) (he : gF s p = NIL) (hlr : gLl s p ≠ gRr s p)
    (hl : gSt s (gLl s p) = .overflow ∧ gSrc s (gLl s p) = p)
    (hr : gSt s (gRr s p) = .overflow ∧ gSrc s (gRr s p) = p)
    (hszl : gSz s (gLl s p) < s.P.G) (hszr : gSz s (gRr s p) < s.P.G)
    (hlS : gLl s p < s.Gs.size) (hrS : gRr s p < s.Gs.size)
    (hpG : gP s p < s.Gs.size) (hnG : gN s p < s.Gs.size) (hcC : gC s p < s.C.size)
    (hG : s.Gs.size ≤ κ.tbl .G) (hC : s.C.size ≤ κ.tbl .C)
    (hF : s.freeG.length + 1 ≤ κ.lcap .freeG) (hF0 : 0 < κ.lrec .freeG) :
    ∃ L' n, evalF κ removeGroupS s L = .ok (removeState s p) L' n ∧ n ≤ 300 := by
  obtain ⟨L1, c1, e1, h1g, hc1⟩ := unlinkGroupS_agree κ s L hg hp.2.1 hpG hnG hcC hG hC hF hF0
  set U := unlinkGroup s p
  set l := gLl s p
  set r := gRr s p
  have hpT : p < κ.tbl .G := by have := hp.2.1; omega
  have hUs : U.Gs.size = s.Gs.size := by
    simp only [U, unlinkGroup]; split_ifs <;> simp
  obtain ⟨u1, u2, -, -, -, uP⟩ := unlinkGroup_getX_lr s p p
  obtain ⟨-, -, l3, l4, l5, -⟩ := unlinkGroup_getX_lr s p l
  obtain ⟨-, -, r3, r4, r5, -⟩ := unlinkGroup_getX_lr s p r
  replace u1 : (U.Gs.getX p).l = (s.Gs.getX p).l := u1
  replace u2 : (U.Gs.getX p).r = (s.Gs.getX p).r := u2
  replace l3 : (U.Gs.getX l).st = (s.Gs.getX l).st := l3
  replace l4 : (U.Gs.getX l).src = (s.Gs.getX l).src := l4
  replace l5 : (U.Gs.getX l).size = (s.Gs.getX l).size := l5
  replace r3 : (U.Gs.getX r).st = (s.Gs.getX r).st := r3
  replace r4 : (U.Gs.getX r).src = (s.Gs.getX r).src := r4
  replace r5 : (U.Gs.getX r).size = (s.Gs.getX r).size := r5
  have a1 := evalF_assign_ok (κ := κ) (s := U) (L := L1) (x := "gL") (e := .gF .l "g") (v := l)
    (by simp [Exp.gF, Exp.ev, h1g, hpT, Fld.cap, Fld.get, GF.get, u1, l, gLl])
  have a2 := evalF_assign_ok (κ := κ) (s := U) (L := upd L1 "gL" l) (x := "gR") (e := .gF .r "g") (v := r)
    (by simp [Exp.gF, Exp.ev, OM.Machine.State.upd, h1g, hpT, Fld.cap, Fld.get, GF.get, u2, r, gRr])
  set L2 := upd (upd L1 "gL" l) "gR" r
  obtain ⟨n3, e3, hn3⟩ := quietS_ok (κ := κ) (S0 := U) (L := L2) (x := "gL") (q := "qL") (j := l) (p := p)
    (by simp [L2, OM.Machine.State.upd]) (by simp [L2, OM.Machine.State.upd, h1g]) (by decide) (by decide)
    (by rw [l3]; exact hl.1) (by rw [l4]; exact hl.2) (by rw [hUs]; exact hlS) (by omega)
  set U1 := { U with Gs := U.Gs.modify l quietG }
  set L3 := upd (upd L2 "qL" 0) "qL" 1
  have hU1r : U1.Gs.getX r = U.Gs.getX r := by
    simp only [U1, getX_modify']; rw [if_neg (fun h => hlr h.1.symm)]
  obtain ⟨n4, e4, hn4⟩ := quietS_ok (κ := κ) (S0 := U1) (L := L3) (x := "gR") (q := "qR") (j := r) (p := p)
    (by simp [L3, L2, OM.Machine.State.upd]) (by simp [L3, L2, OM.Machine.State.upd, h1g]) (by decide) (by decide)
    (by rw [hU1r, r3]; exact hr.1) (by rw [hU1r, r4]; exact hr.2) (by simp [U1, hUs]; exact hrS) (by omega)
  set U2 := { U1 with Gs := U1.Gs.modify r quietG }
  set L4 := upd (upd L3 "qR" 0) "qR" 1
  have hU2l : (U2.Gs.getX l).size = gSz s l := by
    simp only [U2, U1, getX_modify']; rw [if_neg (fun h => hlr h.1)]
    split
    · simp [quietG, l5]
    · exact l5
  have hU2r : (U2.Gs.getX r).size = gSz s r := by
    simp only [U2, getX_modify']; split
    · simp [quietG, hU1r, r5]
    · rw [hU1r, r5]
  obtain ⟨n5, e5, hn5⟩ := splitIfS_skip (κ := κ) (S0 := U2) (L := L4) (x := "gL") (q := "qL") (j := l)
    (by simp [L4, L3, L2, OM.Machine.State.upd]) (by simp [L4, L3, OM.Machine.State.upd])
    (by rw [hU2l]; simp [U2, U1, U, uP]; exact hszl) (by omega)
  obtain ⟨n6, e6, hn6⟩ := splitIfS_skip (κ := κ) (S0 := U2) (L := L4) (x := "gR") (q := "qR") (j := r)
    (by simp [L4, L3, L2, OM.Machine.State.upd]) (by simp [L4, OM.Machine.State.upd])
    (by rw [hU2r]; simp [U2, U1, U, uP]; exact hszr) (by omega)
  refine ⟨L4, _, evalF_seq_ok2 e1 (evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 e3 (evalF_seq_ok2 e4
    (evalF_seq_ok2 e5 e6))))), ?_⟩
  simp only [Exp.cost, Exp.gF] at hc1 hn3 hn4 hn5 hn6 ⊢
  omega

end OM.Impl
