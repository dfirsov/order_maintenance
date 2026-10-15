import OM.Impl.Cut
import OM.Impl.TopTab
import OM.Proof.Top.RunStart

/-!
# M6: `startDrain` at Level M

The program builds the side list of `v` first (in place), so until its last step its state is
Level F's stage with `v`'s side list already set: `φ X = X` with `side v := side`. Every stage after
the side list touches other nodes or other fields, so it commutes with `φ`, and the last step sets
`side v := side` anyway.
-/

namespace OM.Impl

open OM.Model
open OM.Proof.Top
open OM.Machine (Reg BinOp UnOp)

local notation "upd" => OM.Machine.State.upd

/-- Level F's state with `v`'s side list already set. -/
def phiS (v : Nat) (side : List (Nat × Side)) (X : Core) : Core :=
  { X with nodes := X.nodes.modify v fun n => { n with side := side } }

theorem put_side_phi (X : Core) (v : Nat) (side : List (Nat × Side)) :
    LK.put X v (encS side) .side = phiS v side X := put_side_encS X v side

theorem Array.modify_push_lt {α : Type} (a : Array α) (x : α) (f : α → α) {i : Nat} (hi : i < a.size) :
    (a.modify i f).push x = (a.push x).modify i f := by
  apply Array.ext
  · simp
  · intro j h1 h2
    simp only [Array.getElem_modify, Array.getElem_push]
    simp only [Array.size_push, Array.size_modify] at h1
    by_cases e : j = a.size
    · subst e; simp [show i ≠ a.size by omega]
    · have : j < a.size := by omega
      simp [this, Array.getElem_modify]

/-! ### Steps -/

theorem evalF_pushN_ok {κ : Caps} {s : Core} {L : Loc} {x : Reg} (h : s.nodes.size < κ.tbl .N) :
    evalF κ (.push .N x) s L = .ok { s with nodes := s.nodes.push default } (upd L x s.nodes.size) pushCost := by
  simp [evalF, Tbl.size, Tbl.push, h]

theorem evalF_wrN_ok {κ : Caps} {s : Core} {L : Loc} {k : NF} {i e : Exp} {j w : Nat} (hi : i.ev κ s L = some j)
    (he : e.ev κ s L = some w) (hj : j < s.nodes.size) (hc : j < κ.tbl .N) (hk : k.ok w = true) :
    evalF κ (.wr (.n k) i e) s L = .ok { s with nodes := s.nodes.modify j (NF.set · w k) } L (1 + i.cost + e.cost) := by
  simp [evalF, hi, he, Fld.set, hj, hk]

/-! ### Stage 1: the two new nodes -/

def newNodesS : Stm :=
  .push .N "v1" ;; .wr (.n .height) "v1" "h" ;; .push .N "v2" ;; .wr (.n .height) "v2" "h"

theorem newNodesS_ok {κ : Caps} {t : Core} {L : Loc} {v : Nat} {side : List (Nat × Side)}
    (hh : L "h" = sH t v) (hv : v < t.nodes.size) (hcap : t.nodes.size + 2 ≤ κ.tbl .N) :
    ∃ L', evalF κ newNodesS (phiS v side t) L = .ok (phiS v side (sd1 t v)) L' (2 * pushCost + 6) ∧
      L' "v1" = t.nodes.size ∧ L' "v2" = t.nodes.size + 1 ∧
      ∀ r, r ≠ "v1" → r ≠ "v2" → L' r = L r := by
  set N := t.nodes.size
  set S0 := phiS v side t
  have hs : S0.nodes.size = N := by simp [S0, phiS, N]
  have e1 := evalF_pushN_ok (κ := κ) (s := S0) (L := L) (x := "v1") (by omega)
  rw [hs] at e1
  set S1 := { S0 with nodes := S0.nodes.push default }
  set L1 := upd L "v1" N
  have e2 := evalF_wrN_ok (κ := κ) (s := S1) (L := L1) (k := .height) (i := .var "v1") (e := .var "h") (j := N)
    (w := sH t v) (by simp [Exp.ev, L1, OM.Machine.State.upd]) (by simp [Exp.ev, L1, OM.Machine.State.upd, hh])
    (by simp [S1, hs]) (by omega) rfl
  set S2 := { S1 with nodes := S1.nodes.modify N (NF.set · (sH t v) .height) }
  have hs2 : S2.nodes.size = N + 1 := by simp [S2, S1, hs]
  have e3 := evalF_pushN_ok (κ := κ) (s := S2) (L := L1) (x := "v2") (by omega)
  rw [hs2] at e3
  set S3 := { S2 with nodes := S2.nodes.push default }
  set L3 := upd L1 "v2" (N + 1)
  have e4 := evalF_wrN_ok (κ := κ) (s := S3) (L := L3) (k := .height) (i := .var "v2") (e := .var "h")
    (j := N + 1) (w := sH t v) (by simp [Exp.ev, L3, OM.Machine.State.upd])
    (by simp [Exp.ev, L3, L1, OM.Machine.State.upd, hh]) (by simp [S3, hs2]) (by omega) rfl
  refine ⟨L3, ?_, by simp [L3, L1, OM.Machine.State.upd], by simp [L3, OM.Machine.State.upd],
    fun r h1 h2 => by simp [L3, L1, OM.Machine.State.upd, h1, h2]⟩
  have hfin : { S3 with nodes := S3.nodes.modify (N + 1) (NF.set · (sH t v) .height) } = phiS v side (sd1 t v) := by
    simp only [S3, S2, S1, S0, phiS, sd1]
    congr 1
    apply Array.ext_getX
    · simp
    · intro j
      have hvN : v ≠ N := by omega
      have hvN1 : v ≠ N + 1 := by omega
      simp only [getX_modify', getX_push', Array.size_push, Array.size_modify]
      rcases (show j = N + 1 ∨ j = N ∨ j < N ∨ N + 1 < j by omega) with rfl | rfl | hj | hj
      · simp [Ne.symm hvN1, N]; rfl
      · simp [Ne.symm hvN, N]; rfl
      · simp [show j ≠ N by omega, show j ≠ N + 1 by omega, N, hv, show v ≤ t.nodes.size + 1 by omega]
      · simp [show j ≠ N by omega, show j ≠ N + 1 by omega, show j ≠ v by omega, N]
  rw [← hfin]
  exact (evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 e4))).trans (by simp [Exp.cost]; omega)

end OM.Impl
