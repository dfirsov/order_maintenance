import OM.Impl.Elem

/-!
# M6: groups (`Model/Core.lean`: group splits)
-/

namespace OM.Impl

open OM.Model
open OM.Machine (Reg BinOp UnOp)

/-- `linkGroupPair`: link `gl`, `gr` around `g` (locals `g gl gr labL labR`). -/
def linkGroupPairS : Stm :=
  "gp" ::= .gF .prev "g" ;; "gn" ::= .gF .next "g" ;; "c" ::= .gF .chk "g" ;;
  .wgF .lab "gl" "labL" ;; .wgF .st "gl" 1 ;; .wgF .src "gl" "g" ;; .wgF .prev "gl" "gp" ;;
  .wgF .next "gl" "g" ;;
  .ite (!ₑ ("gp" =ₑ 0)) (.wgF .next "gp" "gl") .skip ;;
  .wgF .lab "gr" "labR" ;; .wgF .st "gr" 1 ;; .wgF .src "gr" "g" ;; .wgF .prev "gr" "g" ;;
  .wgF .next "gr" "gn" ;;
  .ite (!ₑ ("gn" =ₑ 0)) (.wgF .prev "gn" "gr") .skip ;;
  .ite (.cF .first "c" =ₑ "g") (.wcF .first "c" "gl") .skip ;;
  .wgF .prev "g" "gl" ;; .wgF .next "g" "gr" ;; .wgF .st "g" 2 ;; .wgF .l "g" "gl" ;; .wgF .r "g" "gr" ;;
  .ite (.cF .last "c" =ₑ "g") (.wcF .last "c" "gr") .skip ;;
  .ite ("gp" =ₑ 0) (.wsc .firstGroup "gl") .skip

theorem linkGroupPairS_agree (κ : Caps) (σ : Core) (L : Loc) {g gl gr labL labR : Nat} (hg : L "g" = g)
    (hgl : L "gl" = gl) (hgr : L "gr" = gr) (hlL : L "labL" = labL) (hlR : L "labR" = labR)
    (hgG : g < σ.Gs.size) (hglG : gl < σ.Gs.size) (hgrG : gr < σ.Gs.size)
    (hpG : (σ.Gs.getX g).prev < σ.Gs.size) (hnG : (σ.Gs.getX g).next < σ.Gs.size)
    (hcC : (σ.Gs.getX g).chk < σ.C.size) (hG : σ.Gs.size ≤ κ.tbl .G) (hC : σ.C.size ≤ κ.tbl .C) :
    ∃ L' n, evalF κ linkGroupPairS σ L = .ok (linkGroupPair σ g gl gr labL labR) L' n ∧ n ≤ 150 := by
  have h1 : g < κ.tbl .G := by omega
  have h2 : (σ.Gs.getX g).chk < κ.tbl .C := by omega
  by_cases hp0 : (σ.Gs.getX g).prev = 0 <;> by_cases hn0 : (σ.Gs.getX g).next = 0 <;>
    by_cases hf : (σ.C.getX (σ.Gs.getX g).chk).first = g <;> by_cases hl : (σ.C.getX (σ.Gs.getX g).chk).last = g
  all_goals dsl_simp [linkGroupPairS, Exp.gF, Exp.cF, Stm.wgF, Stm.wcF, GF.ok, hg, hgl, hgr, hlL, hlR, hgG, hglG,
    hgrG, hpG, hnG, hcC, h1, h2, hp0, hn0, hf, hl]
  sorry -- GOAL
  all_goals sorry

end OM.Impl
