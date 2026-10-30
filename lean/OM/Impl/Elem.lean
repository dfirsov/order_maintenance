import OM.Impl.ArrayLemmas
import OM.Impl.PQ
import OM.Impl.CM

/-!
# M6: elements (`Model/Core.lean`: insertion, deletion, order)
-/

namespace OM.Impl

open OM.Model
open OM.Machine (Reg BinOp UnOp)


/-- `linkElem`: link the new element `y` after `x` (locals `x g glast nx lab h`). -/
def linkElemS : Stm := cm{
  y := new E
  E[y].grp := g; E[y].lab := lab; E[y].h := h; E[y].prev := x
  E[y].next := nx
  if nx ≠ 0 then E[nx].prev := y
  E[x].next := y
  if S.tail = x then S.tail := y
  if glast = x then G[g].last := y
  G[g].size := G[g].size + 1
  S.count := S.count + 1 }

theorem linkElemS_agree (κ : Caps) (σ : Core) (L : Loc) {x lab hh : Nat} (hx : L "x" = x)
    (hg : L "g" = (σ.E.getX x).grp) (hgl : L "glast" = (σ.Gs.getX (σ.E.getX x).grp).last)
    (hnx : L "nx" = (σ.E.getX x).next) (hlab : L "lab" = lab) (hl : L "h" = hh)
    (hxE : x < σ.E.size) (hgG : (σ.E.getX x).grp < σ.Gs.size)
    (hnE : (σ.E.getX x).next = 0 ∨ (σ.E.getX x).next < σ.E.size)
    (hE : σ.E.size < κ.tbl .E) (hG : σ.Gs.size ≤ κ.tbl .G) :
    ∃ L' n, evalF κ linkElemS σ L = .ok (linkElem σ x σ.E.size lab hh) L' n ∧
      L' "y" = σ.E.size ∧ n ≤ 120 := by
  have hgC : (σ.E.getX x).grp < κ.tbl .G := by omega
  have hxs : x < σ.E.size + 1 := by omega
  have hxne : x ≠ σ.E.size := by omega
  have hxC : x < κ.tbl .E := by omega
  by_cases hn0 : (σ.E.getX x).next = 0 <;> by_cases ht : σ.tail = x <;>
    by_cases hlast : (σ.Gs.getX (σ.E.getX x).grp).last = x
  all_goals (try have hnlt : (σ.E.getX x).next < σ.E.size := by omega)
  all_goals (try have hnC : (σ.E.getX x).next < κ.tbl .E := by omega)
  all_goals (try have hnx' : (σ.E.getX x).next < σ.E.size + 1 := by omega)
  all_goals (try have hnle : (σ.E.getX x).next ≤ σ.E.size := by omega)
  all_goals simp [linkElemS, evalF, Exp.ev, Res.bind, Res.addCost, Fld.set, Fld.get, Fld.cap, EF.get, GF.get,
    SF.get, EF.ok, GF.ok, SF.ok, SF.set, Exp.eF, Exp.gF, Stm.weF, Stm.wgF, Exp.sc, Stm.wsc, OM.Machine.State.upd,
    hx, hg, hgl, hnx, hlab, hl, hxC, hgC, Tbl.size, Tbl.push, hE, Exp.cost, ht, hlast, hn0, hxs, hgG, pushCost,
    hnle]
  all_goals
    simp only [linkElem, NIL, Array.modify_modify_same, Array.modify_push_size, hn0, ht, bne_iff_ne, ne_eq,
      beq_iff_eq, not_true_eq_false, not_false_eq_true, if_true, if_false]
  all_goals
    congr 1
  all_goals (try (apply Array.modify_congr_getX; simp [GF.set, hlast]))

/-- The label of the new element, guarded. -/
def insertElemPre : Stm := cm{
  g := E[x].grp
  glast := G[g].last
  exlab := E[x].lab
  nx := E[x].next
  if x = glast then {
    v := exlab + P.De
    if 1 <<< P.Be ≤ v || v ≤ exlab then fail
    lab := v }
  else {
    b := E[nx].lab
    if b ≤ exlab + 1 then fail
    lab := (exlab + b) / 2 } }

/-- `insertElem x h`: a new element with handle `h` right after `x`. -/
def insertElemP : Proc where
  name := "insertElem"
  params := ["x", "h"]
  rets := ["y"]
  body := insertElemPre ;; linkElemS

theorem insertElem_agree (κ : Caps) (σ : Core) (L : Loc) {x hh : Nat} (hx : L "x" = x) (hl : L "h" = hh)
    (hxE : x < σ.E.size) (hgG : (σ.E.getX x).grp < σ.Gs.size)
    (hnE : (σ.E.getX x).next = 0 ∨ (σ.E.getX x).next < σ.E.size)
    (hE : σ.E.size < κ.tbl .E) (hG : σ.Gs.size ≤ κ.tbl .G) {y : Nat} {σ' : Core}
    (h : (insertElem x hh).run σ = .ok y σ') :
    ∃ L' n, evalF κ insertElemP.body σ L = .ok σ' L' n ∧ L' "y" = y ∧ n ≤ 200 := by
  unfold insertElem at h
  simp [OM.Model.between, OM.Model.after, OM.Model.guard, getE, getG, getP] at h
  have hgC : (σ.E.getX x).grp < κ.tbl .G := by omega
  have hxC : x < κ.tbl .E := by omega
  have hnC : (σ.E.getX x).next < κ.tbl .E := by omega
  -- the label and its guard, then the common linking
  suffices hpre : ∃ lab L1 c1, evalF κ insertElemPre σ L = .ok σ L1 c1 ∧
      L1 "x" = x ∧ L1 "g" = (σ.E.getX x).grp ∧ L1 "glast" = (σ.Gs.getX (σ.E.getX x).grp).last ∧
      L1 "nx" = (σ.E.getX x).next ∧ L1 "lab" = lab ∧ L1 "h" = hh ∧ c1 ≤ 80 ∧
      σ' = linkElem σ x σ.E.size lab hh ∧ y = σ.E.size by
    obtain ⟨lab, L1, c1, he, h1, h2, h3, h4, h5, h6, hc, rfl, rfl⟩ := hpre
    obtain ⟨L', n, he', hy, hn⟩ := linkElemS_agree κ σ L1 h1 h2 h3 h4 h5 h6 hxE hgG hnE hE hG
    simp only [insertElemP]
    rw [evalF_seq_ok he, he']
    exact ⟨L', c1 + n, rfl, hy, by omega⟩
  by_cases hlast : x = (σ.Gs.getX (σ.E.getX x).grp).last
  · rw [if_pos hlast] at h
    by_cases hg : 1 <<< σ.P.B_e ≤ (σ.E.getX x).lab + σ.P.D_e ∨ σ.P.D_e = 0
    · rw [if_pos hg] at h; simp at h
    · rw [if_neg hg] at h
      simp only [EStateM.Result.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hc1 : (x = (σ.Gs.getX (σ.E.getX x).grp).last) = True := eq_true hlast
      have hc2 : ((σ.E.getX x).lab + σ.P.D_e < 2 ^ σ.P.B_e ∧ ¬σ.P.D_e = 0) = True := by
        apply eq_true; rw [Nat.shiftLeft_eq, one_mul] at hg; omega
      refine ⟨(σ.E.getX x).lab + σ.P.D_e, ?_⟩
      simp [insertElemPre, hc1, hc2, evalF, Exp.ev, Res.bind, Res.addCost, Fld.get, Fld.cap, EF.get, GF.get,
        Exp.eF, Exp.gF, OM.Machine.State.upd, hx, hl, hxC, hgC, PF.get, Exp.cost]
  · rw [if_neg hlast] at h
    by_cases hg : (σ.E.getX (σ.E.getX x).next).lab ≤ (σ.E.getX x).lab + 1
    · rw [if_pos hg] at h; simp at h
    · rw [if_neg hg] at h
      simp only [EStateM.Result.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hc1 : (x = (σ.Gs.getX (σ.E.getX x).grp).last) = False := eq_false hlast
      have hc2 : ((σ.E.getX x).lab + 1 < (σ.E.getX (σ.E.getX x).next).lab) = True := by
        apply eq_true; omega
      refine ⟨((σ.E.getX x).lab + (σ.E.getX (σ.E.getX x).next).lab) / 2, ?_⟩
      simp [insertElemPre, hc1, hc2, evalF, Exp.ev, Res.bind, Res.addCost, Fld.get, Fld.cap, EF.get, GF.get,
        Exp.eF, Exp.gF, OM.Machine.State.upd, hx, hl, hxC, hgC, hnC, PF.get, Exp.cost]

def markDeadP : Proc where
  name := "markDead"
  params := ["x"]
  rets := []
  body := cm{ E[x].dead := 1 }

theorem markDead_agree (κ : Caps) (σ : Core) (L : Loc) {x : Nat} (hx : L "x" = x) (hxE : x < σ.E.size)
    (hE : σ.E.size ≤ κ.tbl .E) {σ' : Core} (h : (markDead x).run σ = .ok () σ') :
    ∃ L' n, evalF κ markDeadP.body σ L = .ok σ' L' n ∧ n ≤ 5 := by
  unfold markDead modE at h
  simp at h; subst h
  simp [markDeadP, evalF, Exp.ev, Fld.set, Stm.weF, EF.ok, hx, hxE, Exp.cost]
  rfl

/-- The key of element `e`: its chunk's tag, its group's label, its own label. -/
def keyS (e t g l : Reg) : Stm := cm{
  ‹g› := E[‹e›].grp
  ‹l› := E[‹e›].lab
  ‹t› := C[G[‹g›].chk].tag
  ‹g› := G[‹g›].lab }

def orderP : Proc where
  name := "order"
  params := ["x", "y"]
  rets := ["r"]
  body := cm{
    ‹keyS "x" "ta" "ga" "ea"›
    ‹keyS "y" "tb" "gb" "eb"›
    r := ta < tb || (ta = tb && (ga < gb || (ga = gb && ea < eb))) }

theorem order_agree (κ : Caps) (σ : Core) (L : Loc) {x y : Nat} (hx : L "x" = x) (hy : L "y" = y)
    (hxE : x < κ.tbl .E) (hyE : y < κ.tbl .E) (hxG : (σ.E.getX x).grp < κ.tbl .G)
    (hyG : (σ.E.getX y).grp < κ.tbl .G) (hxC : (σ.Gs.getX (σ.E.getX x).grp).chk < κ.tbl .C)
    (hyC : (σ.Gs.getX (σ.E.getX y).grp).chk < κ.tbl .C) {b : Bool} {σ' : Core}
    (h : (OM.Model.order x y).run σ = .ok b σ') :
    ∃ L' n, evalF κ orderP.body σ L = .ok σ' L' n ∧ L' "r" = b2n b ∧ n ≤ 80 := by
  unfold OM.Model.order key at h
  simp [getE, getG, getC] at h
  obtain ⟨rfl, rfl⟩ := h
  simp [orderP, keyS, evalF, Exp.ev, Res.bind, Res.addCost, Fld.get, Fld.cap, EF.get, GF.get, CF.get, Exp.eF,
    Exp.gF, Exp.cF, OM.Machine.State.upd, hx, hy, hxE, hyE, hxG, hyG, hxC, hyC, Exp.cost, keyLt, b2n]
  congr 1
  apply propext
  omega

end OM.Impl
