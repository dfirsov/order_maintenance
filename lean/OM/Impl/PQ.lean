import OM.Impl.Notation

/-!
# M6: the priority queue in the core language (`Model/PQ.lean`)
-/

namespace OM.Impl

open OM.Model
open OM.Machine (Reg BinOp UnOp)

/-! ### Capacities

The queue's arrays are indexed by chunk (`pqNext`, `pqPrev`, `pqWhere`: capacity `κ.arr .pqNext`)
or by bucket (`pqHead`, `nbNext`, `nbPrev`: capacity `κ.arr .pqHead`), and hold chunks or
buckets. `PQCaps` says every stored value fits.
-/

abbrev Ccap (κ : Caps) : Nat := κ.arr .pqNext
abbrev Bcap (κ : Caps) : Nat := κ.arr .pqHead

structure PQCaps (κ : Caps) (σ : Core) : Prop where
  cC : κ.arr .pqPrev = Ccap κ ∧ κ.arr .pqWhere = Ccap κ
  cB : κ.arr .nbNext = Bcap κ ∧ κ.arr .nbPrev = Bcap κ
  next : ∀ i, σ.pqNext.getX i < Ccap κ
  prev : ∀ i, σ.pqPrev.getX i < Ccap κ
  head : ∀ i, σ.pqHead.getX i < Ccap κ
  where_ : ∀ i, σ.pqWhere.getX i < Bcap κ
  nbN : ∀ i, σ.nbNext.getX i < Bcap κ
  nbP : ∀ i, σ.nbPrev.getX i < Bcap κ
  lo : σ.pqLo < Bcap κ
  hi : σ.pqHi < Bcap κ

theorem getX_setX_lt {a : Array Nat} {i v B : Nat} (ha : ∀ j, a.getX j < B) (hv : v < B) (j : Nat) :
    (a.setX i v).getX j < B := by
  rw [OM.Proof.Top.getX_setX']; split
  · exact hv
  · exact ha j

namespace PQCaps
variable {κ : Caps} {σ : Core} (h : PQCaps κ σ)
include h

theorem sNext {i v : Nat} (hv : v < Ccap κ) : PQCaps κ { σ with pqNext := σ.pqNext.setX i v } :=
  { h with next := getX_setX_lt h.next hv }
theorem sPrev {i v : Nat} (hv : v < Ccap κ) : PQCaps κ { σ with pqPrev := σ.pqPrev.setX i v } :=
  { h with prev := getX_setX_lt h.prev hv }
theorem sHead {i v : Nat} (hv : v < Ccap κ) : PQCaps κ { σ with pqHead := σ.pqHead.setX i v } :=
  { h with head := getX_setX_lt h.head hv }
theorem sWhere {i v : Nat} (hv : v < Bcap κ) : PQCaps κ { σ with pqWhere := σ.pqWhere.setX i v } :=
  { h with where_ := getX_setX_lt h.where_ hv }
theorem sNbN {i v : Nat} (hv : v < Bcap κ) : PQCaps κ { σ with nbNext := σ.nbNext.setX i v } :=
  { h with nbN := getX_setX_lt h.nbN hv }
theorem sNbP {i v : Nat} (hv : v < Bcap κ) : PQCaps κ { σ with nbPrev := σ.nbPrev.setX i v } :=
  { h with nbP := getX_setX_lt h.nbP hv }
theorem sLo {v : Nat} (hv : v < Bcap κ) : PQCaps κ { σ with pqLo := v } := { h with lo := hv }
theorem sHi {v : Nat} (hv : v < Bcap κ) : PQCaps κ { σ with pqHi := v } := { h with hi := hv }
theorem sScan (v : Nat) : PQCaps κ { σ with pqScan := v } := { h with }

end PQCaps

/-- Prove `PQCaps κ σ'` for a state obtained from `σ` (with `hq : PQCaps κ σ`) by bounded writes. -/
macro "pq_caps " hq:term : tactic => `(tactic| (
  refine ⟨($hq).cC, ($hq).cB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try intro i) <;>
  simp only [OM.Proof.Top.getX_setX', NIL] <;> (repeat' split) <;>
  first
  | exact ($hq).next _
  | exact ($hq).prev _
  | exact ($hq).head _
  | exact ($hq).where_ _
  | exact ($hq).nbN _
  | exact ($hq).nbP _
  | exact ($hq).lo
  | exact ($hq).hi
  | omega))

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
    (hq : PQCaps κ σ) (hsB : s < Bcap κ) (hpB : p < Bcap κ) {σ' : Core}
    (h : (pqLinkAfter s p).run σ = .ok () σ') :
    (∃ L' c, evalF κ pqLinkAfterP.body σ L = .ok σ' L' c ∧ c ≤ 60) ∧ PQCaps κ σ' := by
  unfold pqLinkAfter at h
  simp only [pqLinkAfterP]
  have hcs : s < κ.arr .nbPrev ∧ s < κ.arr .nbNext := by rw [hq.cB.1, hq.cB.2]; exact ⟨hsB, hsB⟩
  have hcp : p < κ.arr .nbNext := by rw [hq.cB.1]; exact hpB
  by_cases hp0 : p = 0
  · subst hp0
    have hn : σ.pqLo < κ.arr .nbPrev := by rw [hq.cB.2]; exact hq.lo
    by_cases hn0 : σ.pqLo = 0
    · simp [Exp.sc, Exp.ar, Stm.wsc, Stm.war, evalF, Exp.ev, Res.bind, Res.addCost, Fld.set, Fld.get,
        Fld.cap, SF.get, SF.set, AF.get, AF.set, SF.ok, OM.Machine.State.upd, hs, hp, hcs.1, hcs.2,
        hcp, hn0, hn, Exp.cost] at h ⊢
      cases h
      exact ⟨by first | rfl | exact ⟨_, _, rfl, by omega⟩, by
        pq_caps hq⟩
    · simp [Exp.sc, Exp.ar, Stm.wsc, Stm.war, evalF, Exp.ev, Res.bind, Res.addCost, Fld.set, Fld.get,
        Fld.cap, SF.get, SF.set, AF.get, AF.set, SF.ok, OM.Machine.State.upd, hs, hp, hcs.1, hcs.2,
        hcp, hn0, hn, Exp.cost] at h ⊢
      cases h
      exact ⟨by first | rfl | exact ⟨_, _, rfl, by omega⟩, by
        pq_caps hq⟩
  · have hn : σ.nbNext.getX p < κ.arr .nbPrev := by rw [hq.cB.2]; exact hq.nbN p
    by_cases hn0 : σ.nbNext.getX p = 0
    · simp [Exp.sc, Exp.ar, Stm.wsc, Stm.war, evalF, Exp.ev, Res.bind, Res.addCost, Fld.set, Fld.get,
        Fld.cap, SF.get, SF.set, AF.get, AF.set, SF.ok, OM.Machine.State.upd, hs, hp, hcs.1, hcs.2,
        hcp, hp0, hn0, hn, Exp.cost] at h ⊢
      cases h
      exact ⟨by first | rfl | exact ⟨_, _, rfl, by omega⟩, by
        pq_caps hq⟩
    · simp [Exp.sc, Exp.ar, Stm.wsc, Stm.war, evalF, Exp.ev, Res.bind, Res.addCost, Fld.set, Fld.get,
        Fld.cap, SF.get, SF.set, AF.get, AF.set, SF.ok, OM.Machine.State.upd, hs, hp, hcs.1, hcs.2,
        hcp, hp0, hn0, hn, Exp.cost] at h ⊢
      cases h
      exact ⟨by first | rfl | exact ⟨_, _, rfl, by omega⟩, by
        pq_caps hq⟩

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

@[simp] theorem pqLinkAfterP_params : pqLinkAfterP.params = ["s", "p"] := rfl
@[simp] theorem pqLinkAfterP_rets : pqLinkAfterP.rets = [] := rfl

theorem pqAdd_agree (κ : Caps) (σ : Core) (L : Loc) {c s p : Nat} (hc : L "c" = c) (hs : L "s" = s)
    (hp : L "p" = p) (hq : PQCaps κ σ) (hcC : c < Ccap κ) (hsB : s < Bcap κ) (hpB : p < Bcap κ)
    {σ' : Core} (h : (pqAdd c s p).run σ = .ok () σ') :
    (∃ L' n, evalF κ pqAddP.body σ L = .ok σ' L' n ∧ n ≤ 140) ∧ PQCaps κ σ' := by
  have hcc : c < κ.arr .pqNext ∧ c < κ.arr .pqPrev ∧ c < κ.arr .pqWhere := by
    rw [hq.cC.1, hq.cC.2]; exact ⟨hcC, hcC, hcC⟩
  have hcs : s < κ.arr .pqHead := hsB
  have hhd : σ.pqHead.getX s < κ.arr .pqPrev := by rw [hq.cC.1]; exact hq.head s
  unfold pqAdd at h
  by_cases hd0 : σ.pqHead.getX s = 0
  · simp [hd0] at h
    split at h
    · next u σ2 h2 =>
      cases h
      simp only [NIL] at h2
      have hq1 : PQCaps κ
          { σ with
            pqHead := σ.pqHead.setX s c, pqNext := σ.pqNext.setX c 0, pqPrev := σ.pqPrev.setX c 0 } :=
        ((hq.sNext (i := c) (by omega)).sPrev (i := c) (by omega)).sHead (i := s) hcC
      obtain ⟨⟨L2, n2, he2, hn2⟩, hq2⟩ := pqLinkAfter_agree κ _
        (OM.Machine.State.setLocs (fun _ => 0) ["s", "p"] [s, p]) (by simp) (by simp) hq1 hsB hpB h2
      simp only [OM.Machine.State.setLocs] at he2
      refine ⟨?_, by pq_caps hq2⟩
      simp [pqAddP, Proc.call, evalF, Exp.ev, evList, Res.bind, Res.addCost, Fld.set, Fld.get, Fld.cap,
        AF.get, AF.set, Exp.ar, Stm.war, OM.Machine.State.upd, hc, hs, hp, hcc.1, hcc.2.1, hcc.2.2, hcs,
        hd0, Exp.cost, costList, he2]
      omega
    · simp at h
  · simp [hd0] at h
    cases h
    refine ⟨?_, by have := hq.head s; pq_caps hq⟩
    simp [pqAddP, Proc.call, evalF, Exp.ev, evList, Res.bind, Res.addCost, Fld.set, Fld.get, Fld.cap,
      AF.get, AF.set, Exp.ar, Stm.war, OM.Machine.State.upd, hc, hs, hp, hcc.1, hcc.2.1, hcc.2.2, hcs,
      hd0, hhd, Exp.cost]

def pqDelP : Proc where
  name := "pqDel"
  params := ["c"]
  rets := []
  body :=
    "s" ::= .ar .pqWhere "c" ;;
    .ite ("s" =ₑ 0) .fail .skip ;;
    .war .pqWhere "c" 0 ;;
    "nx" ::= .ar .pqNext "c" ;;
    "pv" ::= .ar .pqPrev "c" ;;
    .ite (!ₑ ("pv" =ₑ 0)) (.war .pqNext "pv" "nx") (.war .pqHead "s" "nx") ;;
    .ite (!ₑ ("nx" =ₑ 0)) (.war .pqPrev "nx" "pv") .skip ;;
    .ite (.ar .pqHead "s" =ₑ 0)
      ("p" ::= .ar .nbPrev "s" ;;
       "n" ::= .ar .nbNext "s" ;;
       .war .nbPrev "s" 0 ;;
       .war .nbNext "s" 0 ;;
       .ite (!ₑ ("p" =ₑ 0)) (.war .nbNext "p" "n") (.wsc .pqLo "n") ;;
       .ite (!ₑ ("n" =ₑ 0)) (.war .nbPrev "n" "p") (.wsc .pqHi "p"))
      .skip

@[simp] theorem pqAddP_params : pqAddP.params = ["c", "s", "p"] := rfl
@[simp] theorem pqAddP_rets : pqAddP.rets = [] := rfl
@[simp] theorem pqDelP_params : pqDelP.params = ["c"] := rfl
@[simp] theorem pqDelP_rets : pqDelP.rets = [] := rfl

theorem pqDel_agree (κ : Caps) (σ : Core) (L : Loc) {c : Nat} (hc : L "c" = c) (hq : PQCaps κ σ)
    (hcC : c < Ccap κ) {σ' : Core} (h : (pqDel c).run σ = .ok () σ') :
    (∃ L' n, evalF κ pqDelP.body σ L = .ok σ' L' n ∧ n ≤ 200) ∧ PQCaps κ σ' := by
  have hcc : c < κ.arr .pqNext ∧ c < κ.arr .pqPrev ∧ c < κ.arr .pqWhere := by
    rw [hq.cC.1, hq.cC.2]; exact ⟨hcC, hcC, hcC⟩
  have hs := hq.where_ c
  have hnx := hq.next c
  have hpv := hq.prev c
  have hB1 := hq.cB.1
  have hB2 := hq.cB.2
  have hC1 := hq.cC.1
  unfold pqDel at h
  generalize hsd : σ.pqWhere.getX c = sv at hs
  generalize hnxd : σ.pqNext.getX c = nx at hnx
  generalize hpvd : σ.pqPrev.getX c = pv at hpv
  by_cases hs0 : sv = 0
  · simp [hsd, hs0, OM.Model.guard] at h
  have hsB : sv < κ.arr .pqHead := hs
  have hbn := hq.nbN sv
  have hbp := hq.nbP sv
  have hhs := hq.head sv
  simp [hsd, hs0, hnxd, hpvd, NIL, OM.Proof.Top.getX_setX'] at h
  split_ifs at h with h1 h2 h3 h4 h5 <;> cases h
  all_goals refine ⟨?_, by pq_caps hq⟩
  all_goals simp [*, pqDelP, evalF, Exp.ev, Res.bind, Res.addCost, Fld.set, Fld.get, Fld.cap, AF.get, AF.set,
      SF.get, SF.set, SF.ok, Exp.ar, Stm.war, Exp.sc, Stm.wsc, OM.Machine.State.upd, Exp.cost,
      OM.Proof.Top.getX_setX']

/-- Insert `c` at bucket `s`. The downward scan for the predecessor bucket (Level F's slow path)
runs only if bucket `s - 1` is above `θ` and empty; it is never needed (K2), and costs `O(s)`. -/
def pqInsertScanP : Proc where
  name := "pqInsertScan"
  params := ["c", "s"]
  rets := []
  body :=
    "th" ::= .prm .theta ;;
    "p" ::= Exp.monus "s" 1 ;;
    .ite (("th" <ₑ "p") &&ₑ (.ar .pqHead "p" =ₑ 0))
      ("brk" ::= 0 ;;
       .loop "i" "s"
         (.ite (("brk" =ₑ 0) &&ₑ ("th" <ₑ "p") &&ₑ (.ar .pqHead "p" =ₑ 0))
           ("p" ::= Exp.monus "p" 1 ;; .wsc .pqScan (.sc .pqScan + 1))
           ("brk" ::= 1)))
      .skip ;;
    pqAddP.call ["c", "s", Exp.ifz ("th" <ₑ "p") "p"] []

/-- `pqInsertScan` when no scan is needed. -/
theorem pqInsertScan_agree (κ : Caps) (σ : Core) (L : Loc) {c s : Nat} (hc : L "c" = c) (hs : L "s" = s)
    (hq : PQCaps κ σ) (hcC : c < Ccap κ) (hsB : s < Bcap κ)
    (hfast : ¬(σ.P.theta < s - 1 ∧ σ.pqHead.getX (s - 1) = 0)) {σ' : Core}
    (h : (pqInsertScan c s).run σ = .ok () σ') :
    (∃ L' n, evalF κ pqInsertScanP.body σ L = .ok σ' L' n ∧ n ≤ 250) ∧ PQCaps κ σ' := by
  have hpB : s - 1 < κ.arr .pqHead := by show s - 1 < Bcap κ; omega
  -- Level F: the loop stops at once
  have hrun : (pqInsertScan c s).run σ = (pqAdd c s (if σ.P.theta < s - 1 then s - 1 else 0)).run σ := by
    unfold pqInsertScan
    rcases Nat.eq_zero_or_pos s with rfl | hs1
    · simp
    · obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
      simp only [OM.Proof.run_get_bind, List.range_succ_eq_map, List.forIn_cons]
      rw [OM.Proof.run_bind, OM.Proof.run_bind]
      have hc' : ¬((decide (k > σ.P.theta) && σ.pqHead.getX k == NIL) = true) := by
        simp only [Nat.add_sub_cancel] at hfast
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, NIL]
        exact hfast
      simp only [Nat.add_sub_cancel]
      rw [if_neg hc']
      simp
  rw [hrun] at h
  have hp' : (if σ.P.theta < s - 1 then s - 1 else 0) < Bcap κ := by split <;> omega
  obtain ⟨⟨L2, n2, he2, hn2⟩, hq2⟩ := pqAdd_agree κ σ
    (OM.Machine.State.setLocs (fun _ => 0) ["c", "s", "p"] [c, s, if σ.P.theta < s - 1 then s - 1 else 0])
    (by simp) (by simp) (by simp) hq hcC hsB hp' h
  simp only [OM.Machine.State.setLocs] at he2
  refine ⟨?_, hq2⟩
  have hm : (Exp.monus (.var "s") (.lit 1)).ev κ σ (OM.Machine.State.upd L "th" σ.P.theta) = some (s - 1) :=
    Exp.ev_monus κ σ _ (by simp [Exp.ev, OM.Machine.State.upd, hs]) (by simp [Exp.ev])
  have hfast' : ¬(σ.P.theta < s - 1 ∧ σ.pqHead.getX (s - 1) = 0) := hfast
  by_cases hlt : σ.P.theta < s - 1
  · have hh0 : σ.pqHead.getX (s - 1) ≠ 0 := fun e => hfast ⟨hlt, e⟩
    rw [if_pos hlt] at he2
    simp [pqInsertScanP, Proc.call, evalF, Exp.ev, evList, Res.bind, Res.addCost, Fld.get, Fld.cap,
      AF.get, Exp.ar, Exp.ifz, OM.Machine.State.upd, hc, hs, hm, hpB, hlt, hh0, Exp.cost, costList, he2,
      PF.get]
    omega
  · rw [if_neg hlt] at he2
    simp [pqInsertScanP, Proc.call, evalF, Exp.ev, evList, Res.bind, Res.addCost, Fld.get, Fld.cap,
      AF.get, Exp.ar, Exp.ifz, OM.Machine.State.upd, hc, hs, hm, hpB, hlt, Exp.cost, costList, he2, PF.get]
    omega

@[simp] theorem pqInsertScanP_params : pqInsertScanP.params = ["c", "s"] := rfl
@[simp] theorem pqInsertScanP_rets : pqInsertScanP.rets = [] := rfl

def pqAdjustP : Proc where
  name := "pqAdjust"
  params := ["c", "old", "new"]
  rets := []
  body :=
    "th" ::= .prm .theta ;;
    .ite (("old" ≤ₑ "th") &&ₑ ("th" <ₑ "new")) (pqInsertScanP.call ["c", "new"] [])
      (.ite (("new" ≤ₑ "th") &&ₑ ("th" <ₑ "old")) (pqDelP.call ["c"] [])
        (.ite (("th" <ₑ "old") &&ₑ ("th" <ₑ "new"))
          (.ite ("new" =ₑ Exp.var "old" + 1)
            ("alone" ::= ((.ar .pqHead "old" =ₑ "c") &&ₑ (.ar .pqNext "c" =ₑ 0)) ;;
             "p" ::= (Exp.ifz "alone" (.ar .nbPrev "old") + Exp.ifz (!ₑ "alone") "old") ;;
             pqDelP.call ["c"] [] ;;
             pqAddP.call ["c", "new", "p"] [])
            (.ite (Exp.var "new" + 1 =ₑ "old")
              ("p" ::= .ar .nbPrev "old" ;;
               pqDelP.call ["c"] [] ;;
               pqAddP.call ["c", "new", "p"] [])
              (pqDelP.call ["c"] [] ;; pqInsertScanP.call ["c", "new"] [])))
          .skip))

/-- `pqAdjust` for a `+1` change of size (the only one the algorithm makes). -/
theorem pqAdjust_agree (κ : Caps) (σ : Core) (L : Loc) {c old : Nat} (hc : L "c" = c)
    (ho : L "old" = old) (hn : L "new" = old + 1) (hq : PQCaps κ σ) (hcC : c < Ccap κ)
    (hnB : old + 1 < Bcap κ) {σ' : Core} (h : (pqAdjust c old (old + 1)).run σ = .ok () σ') :
    (∃ L' n, evalF κ pqAdjustP.body σ L = .ok σ' L' n ∧ n ≤ 700) ∧ PQCaps κ σ' := by
  have hoB : old < κ.arr .pqHead := by show old < Bcap κ; omega
  have hcN : c < κ.arr .pqNext := hcC
  have hbP : old < κ.arr .nbPrev := by rw [hq.cB.2]; show old < Bcap κ; omega
  unfold pqAdjust at h
  simp only [OM.Proof.run_getP_bind] at h
  rcases lt_trichotomy old σ.P.theta with hlt | heq | hgt
  · -- below the queue: nothing
    rw [if_neg (by simp; omega), if_neg (by simp; omega), if_neg (by simp; omega)] at h
    cases h
    refine ⟨?_, hq⟩
    have h1 : old + 1 ≤ σ.P.theta := hlt
    simp [pqAdjustP, evalF, Exp.ev, Res.bind, Res.addCost, OM.Machine.State.upd, hc, ho, hn, PF.get,
      Exp.cost, hlt, h1, Nat.le_of_lt hlt, Nat.not_lt.mpr (Nat.le_of_lt hlt)]
  · -- entering at bucket `θ + 1`
    rw [if_pos (by simp; omega)] at h
    obtain ⟨⟨L2, n2, he2, hn2⟩, hq2⟩ := pqInsertScan_agree κ σ
      (OM.Machine.State.setLocs (fun _ => 0) ["c", "s"] [c, old + 1]) (by simp) (by simp) hq hcC hnB
      (by simp; omega) h
    simp only [OM.Machine.State.setLocs] at he2
    rw [heq] at he2
    refine ⟨?_, hq2⟩
    simp [pqAdjustP, Proc.call, evalF, Exp.ev, evList, Res.bind, Res.addCost, OM.Machine.State.upd, hc, ho,
      hn, PF.get, Exp.cost, costList, he2, heq]
    omega
  · -- moving up one bucket
    rw [if_neg (by simp; omega), if_neg (by simp; omega), if_pos (by simp; omega)] at h
    simp only [OM.Proof.run_get_bind, beq_self_eq_true, if_true] at h
    obtain ⟨u, σ1, h1, h2⟩ := run_bind_ok h
    obtain ⟨⟨L1, n1, he1, hn1⟩, hq1⟩ := pqDel_agree κ σ
      (OM.Machine.State.setLocs (fun _ => 0) ["c"] [c]) (by simp) hq hcC h1
    simp only [OM.Machine.State.setLocs] at he1
    have hlt1 : ¬(old + 1 ≤ σ.P.theta) := by omega
    have hlt2 : ¬(old ≤ σ.P.theta) := by omega
    have hlt3 : ¬(old < σ.P.theta) := by omega
    by_cases ha : σ.pqHead.getX old = c ∧ σ.pqNext.getX c = 0
    · rw [if_pos (by simp [ha.1, ha.2, NIL])] at h2
      obtain ⟨⟨L2, n2, he2, hn2⟩, hq2⟩ := pqAdd_agree κ σ1
        (OM.Machine.State.setLocs (fun _ => 0) ["c", "s", "p"] [c, old + 1, σ.nbPrev.getX old])
        (by simp) (by simp) (by simp) hq1 hcC hnB (hq.nbP old) h2
      simp only [OM.Machine.State.setLocs] at he2
      refine ⟨?_, hq2⟩
      simp [pqAdjustP, Proc.call, evalF, Exp.ev, evList, Res.bind, Res.addCost, OM.Machine.State.upd, hc, ho,
        hn, PF.get, Exp.cost, costList, he1, he2, hgt, hlt1, hlt2, hlt3, Fld.get, Fld.cap, AF.get, Exp.ar, Exp.ifz,
        hoB, hcN, hbP, ha.1, ha.2]
      omega
    · rw [if_neg (by simpa [NIL] using ha)] at h2
      obtain ⟨⟨L2, n2, he2, hn2⟩, hq2⟩ := pqAdd_agree κ σ1
        (OM.Machine.State.setLocs (fun _ => 0) ["c", "s", "p"] [c, old + 1, old])
        (by simp) (by simp) (by simp) hq1 hcC hnB (by omega) h2
      simp only [OM.Machine.State.setLocs] at he2
      refine ⟨?_, hq2⟩
      have ha' : σ.pqHead.getX old = c → σ.pqNext.getX c ≠ 0 := fun e1 e2 => ha ⟨e1, e2⟩
      by_cases hh : σ.pqHead.getX old = c
      · simp [pqAdjustP, Proc.call, evalF, Exp.ev, evList, Res.bind, Res.addCost, OM.Machine.State.upd, hc,
          ho, hn, PF.get, Exp.cost, costList, he1, he2, hgt, hlt1, hlt2, hlt3, Fld.get, Fld.cap, AF.get, Exp.ar,
          Exp.ifz, hoB, hcN, hbP, hh, ha' hh]
        omega
      · simp [pqAdjustP, Proc.call, evalF, Exp.ev, evList, Res.bind, Res.addCost, OM.Machine.State.upd, hc,
          ho, hn, PF.get, Exp.cost, costList, he1, he2, hgt, hlt1, hlt2, hlt3, Fld.get, Fld.cap, AF.get, Exp.ar,
          Exp.ifz, hoB, hcN, hbP, hh]
        omega

def pqEnterIfAboveP : Proc where
  name := "pqEnterIfAbove"
  params := ["c"]
  rets := []
  body :=
    "s" ::= .rd (.c .size) "c" ;;
    .ite (.prm .theta <ₑ "s") (pqInsertScanP.call ["c", "s"] []) .skip

/-- `pqEnterIfAbove` for a chunk not above `θ` (every freshly quiet chunk: `c_max ≤ θ`). -/
theorem pqEnterIfAbove_agree (κ : Caps) (σ : Core) (L : Loc) {c : Nat} (hc : L "c" = c)
    (hcT : c < κ.tbl .C) (hle : (σ.C.getX c).size ≤ σ.P.theta) {σ' : Core}
    (h : (pqEnterIfAbove c).run σ = .ok () σ') :
    ∃ L' n, evalF κ pqEnterIfAboveP.body σ L = .ok σ' L' n ∧ n ≤ 20 := by
  unfold pqEnterIfAbove at h
  simp [OM.Proof.run_getC_bind, OM.Proof.run_getP_bind, Nat.not_lt.mpr hle] at h
  cases h
  have : ¬ σ.P.theta < (σ.C.getX c).size := by omega
  simp [pqEnterIfAboveP, evalF, Exp.ev, Res.bind, Res.addCost, OM.Machine.State.upd, hc, PF.get, Exp.cost,
    Fld.get, Fld.cap, CF.get, hcT, this]

def pqPopMaxP : Proc where
  name := "pqPopMax"
  params := []
  rets := ["c"]
  body :=
    "c" ::= .ar .pqHead (.sc .pqHi) ;;
    .ite ("c" =ₑ 0) .fail .skip ;;
    pqDelP.call ["c"] []

theorem pqPopMax_agree (κ : Caps) (σ : Core) (L : Loc) (hq : PQCaps κ σ) {c : Nat} {σ' : Core}
    (h : pqPopMax.run σ = .ok c σ') :
    (∃ L' n, evalF κ pqPopMaxP.body σ L = .ok σ' L' n ∧ L' "c" = c ∧ n ≤ 240) ∧ PQCaps κ σ' := by
  unfold pqPopMax at h
  have hhi : σ.pqHi < κ.arr .pqHead := hq.hi
  have hcC := hq.head σ.pqHi
  by_cases h0 : σ.pqHead.getX σ.pqHi = 0
  · simp [h0, OM.Model.guard, NIL] at h
  · simp [h0, NIL] at h
    obtain ⟨⟨u, h1⟩, rfl⟩ := h
    obtain ⟨⟨L1, n1, he1, hn1⟩, hq1⟩ := pqDel_agree κ σ
      (OM.Machine.State.setLocs (fun _ => 0) ["c"] [σ.pqHead.getX σ.pqHi]) (by simp) hq hcC h1
    simp only [OM.Machine.State.setLocs] at he1
    refine ⟨?_, hq1⟩
    simp [pqPopMaxP, Proc.call, evalF, Exp.ev, evList, Res.bind, Res.addCost, OM.Machine.State.upd,
      Exp.cost, costList, Fld.get, Fld.cap, AF.get, SF.get, Exp.ar, Exp.sc, hhi, h0, he1]
    omega

def pqEmptyP : Proc where
  name := "pqEmpty"
  params := []
  rets := ["r"]
  body := "r" ::= (.sc .pqHi =ₑ 0)

theorem pqEmpty_agree (κ : Caps) (σ : Core) (L : Loc) {b : Bool} {σ' : Core}
    (h : pqEmpty.run σ = .ok b σ') :
    ∃ L' n, evalF κ pqEmptyP.body σ L = .ok σ' L' n ∧ L' "r" = b2n b ∧ n ≤ 10 := by
  unfold pqEmpty at h
  simp at h; obtain ⟨rfl, rfl⟩ := h
  by_cases h0 : σ.pqHi = 0 <;>
    simp [pqEmptyP, evalF, Exp.ev, Res.addCost, OM.Machine.State.upd, Exp.cost, Fld.get, Fld.cap,
      SF.get, Exp.sc, h0, b2n]

end OM.Impl
