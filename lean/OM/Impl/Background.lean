import OM.Impl.Reservation

/-!
# M6: background work at Level M (`chunkSize`, `background`)

`background y` after inserting element `y`: the chunk of `y` grows by one, a full quiet group
starts its split, the group and chunk splits of `y` are driven, and the reservation runs. Each
part is a procedure, so that its locals stay apart; the agreement is stated along Level F's run,
given as a trace of the parts.
-/

namespace OM.Impl

open OM.Model
open OM.Proof.Top
open OM.Machine (Reg BinOp UnOp)

local notation "upd" => OM.Machine.State.upd

/-! ### `chunkSize c true` -/

def csP : Proc where
  name := "chunkSize"
  params := ["c"]
  rets := []
  body :=
    "old" ::= .cF .size "c" ;; "new" ::= "old" + 1 ;; .wcF .size "c" "new" ;;
    .ite (.cF .st "c" =ₑ 0) (pqAdjustP.call ["c", "old", "new"] []) .skip

theorem csP_agree {κ : Caps} {s : Core} {L : Loc} {c : Nat} (hc : L "c" = c) (hcs : c < s.C.size)
    (hcT : c < κ.tbl .C) (hq : PQCaps κ s) (hcC : c < Ccap κ) (hnB : (s.C.getX c).size + 1 < Bcap κ)
    {s' : Core} (h : (chunkSize c true).run s = .ok () s') :
    (∃ L' n, evalF κ csP.body s L = .ok s' L' n ∧ n ≤ 750) ∧ PQCaps κ s' := by
  set C := s.C.getX c
  unfold chunkSize at h
  simp only [OM.Proof.run_getC_bind, run_modC_bind] at h
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "old") (e := .cF .size "c") (v := C.size)
    (by simp [Exp.cF, Exp.ev, hc, hcT, Fld.cap, Fld.get, CF.get, C])
  have a2 := evalF_assign_ok (κ := κ) (s := s) (L := upd L "old" C.size) (x := "new") (e := "old" + 1) (v := C.size + 1)
    (by simp [Exp.ev, OM.Machine.State.upd, OM.Machine.BinOp.eval])
  set L2 := upd (upd L "old" C.size) "new" (C.size + 1)
  have h2c : L2 "c" = c := by simp [L2, OM.Machine.State.upd, hc]
  have w3 := evalF_wrC_ok (κ := κ) (s := s) (L := L2) (k := .size) (i := .var "c") (e := .var "new") (j := c)
    (w := C.size + 1) (by simp [Exp.ev, h2c]) (by simp [Exp.ev, L2, OM.Machine.State.upd]) hcs hcT rfl
  set s1 : Core := { s with C := s.C.modify c fun C' => { C' with size := C.size + 1 } }
  have hs1 : ({ s with C := s.C.modify c (CF.set · (C.size + 1) .size) } : Core) = s1 := rfl
  rw [hs1] at w3
  have hq1 : PQCaps κ s1 := { hq with }
  have hst : (s1.C.getX c).st = C.st := by simp only [s1, getX_modify', hcs, and_self, if_true]; rfl
  by_cases hQ : C.st = .quiet
  · have hQ' : (s.C.getX c).st = .quiet := hQ
    rw [if_pos (by simp [hQ'])] at h
    have h' : (pqAdjust c C.size (C.size + 1)).run s1 = .ok () s' := h
    obtain ⟨⟨La, na, ea, hna⟩, hq'⟩ := pqAdjust_agree κ s1
      (OM.Machine.State.setLocs (fun _ => 0) ["c", "old", "new"] [c, C.size, C.size + 1]) (c := c) (old := C.size)
      (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
      (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
      (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd]) hq1 hcC hnB h'
    have e4 := evalF_call_ok (q := pqAdjustP) (args := ["c", "old", "new"]) (ds := []) (L := L2)
      (by simp [evList, Exp.ev, h2c, L2, OM.Machine.State.upd, hc]) ea
    refine ⟨⟨_, _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 (by simp only [Stm.wcF]; exact w3)
      (evalF_ite_t (v := 1) (by simp [Exp.cF, Exp.ev, h2c, hcT, Fld.cap, Fld.get, CF.get, hst, hQ, St.toN,
        OM.Machine.BinOp.eval]) one_ne_zero e4))), ?_⟩, hq'⟩
    simp [Exp.cost, Exp.cF, costList] at hna ⊢; omega
  · have hQ' : ¬ (s.C.getX c).st = .quiet := hQ
    rw [if_neg (by simpa using hQ')] at h
    injection h with _ h; subst h
    have hst0 : (s1.C.getX c).st.toN ≠ 0 := by rw [hst]; cases hC : C.st <;> simp_all [St.toN]
    have hc0 : (Exp.cF .st "c" =ₑ 0 : Exp).ev κ s1 L2 = some 0 := by
      simp only [Exp.cF, Exp.ev, h2c, Option.bind_some, Fld.cap, hcT, if_true, Fld.get, CF.get]
      simp [OM.Machine.BinOp.eval, hst0]
    refine ⟨⟨_, _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 (by simp only [Stm.wcF]; exact w3)
      (evalF_ite_f hc0 evalF_skip))), ?_⟩, hq1⟩
    simp [Exp.cost, Exp.cF]

end OM.Impl
