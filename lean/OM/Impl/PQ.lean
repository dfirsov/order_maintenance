import OM.Impl.Notation

/-!
# M6: the priority queue in the core language (`Model/PQ.lean`)
-/

namespace OM.Impl

open OM.Model
open OM.Machine (Reg BinOp UnOp)

def pqLinkAfterP : Proc where
  name := "pqLinkAfter"
  params := ["s", "p"]
  rets := []
  body :=
    .ite ("p" =ₑ 0) ("n" ::= .sc .pqLo) ("n" ::= .ar .nbNext "p") ;;
    .ite ("p" =ₑ 0) (.wsc .pqLo "s") (.war .nbNext "p" "s") ;;
    .war .nbPrev "s" "p" ;;
    .war .nbNext "s" "n" ;;
    .ite (!ₑ ("n" =ₑ 0)) (.war .nbPrev "n" "s") (.wsc .pqHi "s")

theorem pqLinkAfter_agree (κ : Caps) (σ : Core) (L : Loc) {s p : Nat} (hs : L "s" = s) (hp : L "p" = p)
    (hcs : s < κ.arr .nbPrev ∧ s < κ.arr .nbNext) (hcp : p < κ.arr .nbNext)
    (hcn : (if p == 0 then σ.pqLo else σ.nbNext.getX p) < κ.arr .nbPrev) {σ' : Core}
    (h : (pqLinkAfter s p).run σ = .ok () σ') :
    ∃ L' c, evalF κ pqLinkAfterP.body σ L = .ok σ' L' c ∧ c ≤ 60 := by
  unfold pqLinkAfter at h
  simp only [pqLinkAfterP]
  have hn := hcn
  by_cases hp0 : p = 0
  · subst hp0
    simp only [beq_self_eq_true, if_true] at hn
    by_cases hn0 : σ.pqLo = 0
    · simp [Exp.sc, Exp.ar, Stm.wsc, Stm.war, evalF, Exp.ev, Res.bind, Res.addCost, Fld.set, Fld.get,
        Fld.cap, SF.get, SF.set, AF.get, AF.set, SF.ok, OM.Machine.State.upd, hs, hp, hcs.1, hcs.2,
        hcp, hn0, hn, Exp.cost] at h ⊢
      cases h; first | rfl | exact ⟨_, _, rfl, by omega⟩
    · simp [Exp.sc, Exp.ar, Stm.wsc, Stm.war, evalF, Exp.ev, Res.bind, Res.addCost, Fld.set, Fld.get,
        Fld.cap, SF.get, SF.set, AF.get, AF.set, SF.ok, OM.Machine.State.upd, hs, hp, hcs.1, hcs.2,
        hcp, hn0, hn, Exp.cost] at h ⊢
      cases h; first | rfl | exact ⟨_, _, rfl, by omega⟩
  · have hpb : (p == 0) = false := by simp [hp0]
    rw [hpb] at hn; simp only [Bool.false_eq_true, if_false] at hn
    by_cases hn0 : σ.nbNext.getX p = 0
    · simp [Exp.sc, Exp.ar, Stm.wsc, Stm.war, evalF, Exp.ev, Res.bind, Res.addCost, Fld.set, Fld.get,
        Fld.cap, SF.get, SF.set, AF.get, AF.set, SF.ok, OM.Machine.State.upd, hs, hp, hcs.1, hcs.2,
        hcp, hp0, hn0, hn, Exp.cost] at h ⊢
      cases h; first | rfl | exact ⟨_, _, rfl, by omega⟩
    · simp [Exp.sc, Exp.ar, Stm.wsc, Stm.war, evalF, Exp.ev, Res.bind, Res.addCost, Fld.set, Fld.get,
        Fld.cap, SF.get, SF.set, AF.get, AF.set, SF.ok, OM.Machine.State.upd, hs, hp, hcs.1, hcs.2,
        hcp, hp0, hn0, hn, Exp.cost] at h ⊢
      cases h; first | rfl | exact ⟨_, _, rfl, by omega⟩

def pqAddP : Proc where
  name := "pqAdd"
  params := ["c", "s", "p"]
  rets := []
  body :=
    "hd" ::= .ar .pqHead "s" ;;
    .ite (!ₑ ("hd" =ₑ 0))
      (.war .pqNext "c" "hd" ;; .war .pqPrev "hd" "c" ;; .war .pqPrev "c" 0 ;; .war .pqHead "s" "c")
      (.war .pqNext "c" 0 ;; .war .pqPrev "c" 0 ;; .war .pqHead "s" "c" ;;
        pqLinkAfterP.call ["s", "p"] []) ;;
    .war .pqWhere "c" "s"

/-- The capacities `pqLinkAfter s p` needs in state `σ`. -/
def LinkCaps (κ : Caps) (σ : Core) (s p : Nat) : Prop :=
  (s < κ.arr .nbPrev ∧ s < κ.arr .nbNext) ∧ p < κ.arr .nbNext ∧
    (if p == 0 then σ.pqLo else σ.nbNext.getX p) < κ.arr .nbPrev

@[simp] theorem pqLinkAfterP_params : pqLinkAfterP.params = ["s", "p"] := rfl
@[simp] theorem pqLinkAfterP_rets : pqLinkAfterP.rets = [] := rfl

theorem pqAdd_agree (κ : Caps) (σ : Core) (L : Loc) {c s p : Nat} (hc : L "c" = c) (hs : L "s" = s)
    (hp : L "p" = p) (hcc : c < κ.arr .pqNext ∧ c < κ.arr .pqPrev ∧ c < κ.arr .pqWhere)
    (hcs : s < κ.arr .pqHead) (hhd : σ.pqHead.getX s < κ.arr .pqPrev)
    (hl : σ.pqHead.getX s = 0 → LinkCaps κ
      { σ with
        pqNext := σ.pqNext.setX c 0, pqPrev := σ.pqPrev.setX c 0, pqHead := σ.pqHead.setX s c } s p)
    {σ' : Core}
    (h : (pqAdd c s p).run σ = .ok () σ') :
    ∃ L' n, evalF κ pqAddP.body σ L = .ok σ' L' n ∧ n ≤ 140 := by
  unfold pqAdd at h
  by_cases hd0 : σ.pqHead.getX s = 0
  · have hl' := hl hd0
    simp [hd0] at h
    split at h
    · next u σ2 h2 =>
      cases h
      simp only [NIL] at h2
      obtain ⟨L2, n2, he2, hn2⟩ := pqLinkAfter_agree κ _
        (OM.Machine.State.setLocs (fun _ => 0) ["s", "p"] [s, p]) (by simp) (by simp) hl'.1 hl'.2.1 hl'.2.2 h2
      simp only [OM.Machine.State.setLocs] at he2
      simp [pqAddP, Proc.call, evalF, Exp.ev, evList, Res.bind, Res.addCost, Fld.set, Fld.get, Fld.cap,
        AF.get, AF.set, Exp.ar, Stm.war, OM.Machine.State.upd, hc, hs, hp, hcc.1, hcc.2.1, hcc.2.2, hcs,
        hd0, Exp.cost, costList, he2]
      omega
    · simp at h
  · simp [hd0] at h
    cases h
    simp [pqAddP, Proc.call, evalF, Exp.ev, evList, Res.bind, Res.addCost, Fld.set, Fld.get, Fld.cap,
      AF.get, AF.set, Exp.ar, Stm.war, OM.Machine.State.upd, hc, hs, hp, hcc.1, hcc.2.1, hcc.2.2, hcs,
      hd0, hhd, Exp.cost]

end OM.Impl
